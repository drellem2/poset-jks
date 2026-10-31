#!/usr/bin/env python3
"""Independent audit of notes/h_double_prime.md (claims L3, F, M, L, H'').

Imports nothing from the repository.  For every naturally labelled poset on
{0, ..., n-1} (x <_P y  =>  x < y) with 2 <= n <= NMAX it computes:

  * h_C(P) from the Moebius definition
        Omega_C(P, m) = sum_{pi in OP(P)} (-1)^{|pi|-1} mu(pi, 1hat) C(m, |pi|),
    cached by an isomorphism-invariant canonical form of the poset;
  * Lin P, the cyclic classes as C_n-orbits intersected with Lin P, and the
    pieces of each class from its cuts;
  * min-des, all-ascent classes (s >= 2 and every junction an ascent), d, s;
  * the checks listed in main().

Exit status 0 iff every claim line holds and every CONTROL line is refuted
at least once.
"""
import argparse
import sys
import time
from itertools import permutations
from math import comb, factorial


# ---------------------------------------------------------------- polynomials

def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, c in enumerate(a):
        r[i] += c
    for i, c in enumerate(b):
        r[i] += c
    return r


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def ppow(a, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, a)
    return r


def xpow(k):
    return [0] * k + [1]


def binom(t, k):
    """C(t, k) as a polynomial in t evaluated at integer t (any sign)."""
    if k < 0:
        return 0
    num = 1
    for i in range(k):
        num *= (t - i)
    return num // factorial(k)


# ---------------------------------------------------------------- posets

def naturally_labelled(n):
    """All naturally labelled posets on {0..n-1}, as tuples down[i] = bitmask
    of elements strictly below i (transitively closed).  Element n-1 is
    maximal, so it is added over an arbitrary down-set of the rest."""
    if n == 0:
        yield ()
        return
    for P in naturally_labelled(n - 1):
        m = n - 1
        for S in range(1 << m):
            ok = True
            for i in range(m):
                if S >> i & 1 and (P[i] & ~S):
                    ok = False
                    break
            if ok:
                yield P + (S,)


def up_from_down(down):
    n = len(down)
    up = [0] * n
    for y in range(n):
        for x in range(n):
            if down[y] >> x & 1:
                up[x] |= 1 << y
    return up


def canonical(down):
    """Canonical form: min over relabellings respecting a refined invariant
    partition of the sorted relation list.  Exact (brute force within
    classes), so iso classes are counted correctly."""
    n = len(down)
    up = up_from_down(down)
    inv = [(bin(down[i]).count('1'), bin(up[i]).count('1')) for i in range(n)]
    for _ in range(3):
        new = []
        for i in range(n):
            below = sorted(inv[j] for j in range(n) if down[i] >> j & 1)
            above = sorted(inv[j] for j in range(n) if up[i] >> j & 1)
            new.append((inv[i], tuple(below), tuple(above)))
        keys = sorted(set(new))
        inv = [keys.index(v) for v in new]
    groups = {}
    for i in range(n):
        groups.setdefault(inv[i], []).append(i)
    order = [groups[k] for k in sorted(groups)]
    best = None

    def rec(gi, assigned):
        nonlocal best
        if gi == len(order):
            pos = {}
            k = 0
            for blk in assigned:
                for e in blk:
                    pos[e] = k
                    k += 1
            rel = tuple(sorted((pos[x], pos[y]) for y in range(n)
                               for x in range(n) if down[y] >> x & 1))
            if best is None or rel < best:
                best = rel
            return
        for p in permutations(order[gi]):
            rec(gi + 1, assigned + [p])

    rec(0, [])
    return (n, best)


def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | (1 << first)] + p[i + 1:]
        yield p + [1 << first]


def h_C_moebius(down):
    """h-vector of Omega_C from the Moebius definition on OP(P)."""
    n = len(down)
    # OP(P): set partitions with acyclic quotient
    op = {}
    for p in set_partitions(list(range(n))):
        blocks = sorted(p)
        k = len(blocks)
        bid = [0] * n
        for b, B in enumerate(blocks):
            for i in range(n):
                if B >> i & 1:
                    bid[i] = b
        adj = [set() for _ in range(k)]
        for y in range(n):
            for x in range(n):
                if down[y] >> x & 1 and bid[x] != bid[y]:
                    adj[bid[x]].add(bid[y])
        # acyclicity
        indeg = [0] * k
        for a in range(k):
            for b in adj[a]:
                indeg[b] += 1
        stack = [a for a in range(k) if indeg[a] == 0]
        seen = 0
        while stack:
            a = stack.pop()
            seen += 1
            for b in adj[a]:
                indeg[b] -= 1
                if indeg[b] == 0:
                    stack.append(b)
        if seen == k:
            op[tuple(blocks)] = None
    top = ((1 << n) - 1,)
    assert top in op
    mu = {top: 1}
    for pi in sorted(op, key=len):          # fewer blocks = higher in the order
        if pi == top:
            continue
        s = 0
        for q in set_partitions(list(range(len(pi)))):
            if len(q) == len(pi):
                continue                    # rho = pi itself
            rho = []
            for Q in q:
                B = 0
                for i in range(len(pi)):
                    if Q >> i & 1:
                        B |= pi[i]
                rho.append(B)
            rho = tuple(sorted(rho))
            if rho in op:
                s += mu[rho]
        mu[pi] = -s
    vals = []
    for m in range(n + 2):
        vals.append(sum((-1) ** (len(pi) - 1) * mu[pi] * comb(m, len(pi))
                        for pi in op))
    # sum_m Omega(m) x^m = x h(x) / (1-x)^{n+1}
    ser = pmul(vals, ppow([1, -1], n + 1))[: n + 2]
    assert ser[0] == 0 and ser[n + 1] == 0, ser
    return ptrim(ser[1:]), vals


# ---------------------------------------------------------------- words

def lin_ext(down, n):
    out = []
    w = []

    def rec(used):
        if len(w) == n:
            out.append(tuple(w))
            return
        for x in range(n):
            if not used >> x & 1 and (down[x] & ~used) == 0:
                w.append(x)
                rec(used | (1 << x))
                w.pop()

    rec(0)
    return out


def components(down, n):
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for y in range(n):
        for x in range(n):
            if down[y] >> x & 1:
                parent[find(x)] = find(y)
    comps = {}
    for i in range(n):
        comps.setdefault(find(i), 0)
        comps[find(i)] |= 1 << i
    return list(comps.values())


def is_union_of_comps(mask, comps):
    return all((mask & C) in (0, C) for C in comps)


def cuts_of(w, comps):
    out = []
    mask = 0
    for p in range(1, len(w)):
        mask |= 1 << w[p - 1]
        if is_union_of_comps(mask, comps):
            out.append(p)
    return out


def des(w):
    return sum(1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def N_T(w, m, T, comps, n):
    """Proposition D summand, computed from the definition."""
    D = {i + 1 for i in range(n - 1) if w[i] > w[i + 1]}   # descent positions p: w_p > w_{p+1}
    mask = 0
    CT = set()
    for p in range(1, n):
        mask |= 1 << w[p - 1]
        if is_union_of_comps(mask, comps) and (mask & T) == T:
            CT.add(p)
    if CT & D:
        return 0
    c = len(CT)
    return binom(m + n - 1 - len(D) - c, n - c)


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=7)
    args = ap.parse_args()
    t0 = time.time()

    hcache = {}
    stats = {}
    fails = {}
    ctl = {}

    def claim(key, ok, info=None):
        stats.setdefault(key, [0, 0])
        stats[key][0] += 1
        if not ok:
            stats[key][1] += 1
            fails.setdefault(key, info)

    def control(key, refuted, info=None):
        ctl.setdefault(key, [0, 0, None])
        ctl[key][0] += 1
        if refuted:
            ctl[key][1] += 1
            if ctl[key][2] is None:
                ctl[key][2] = info

    per_n = {}
    maxA = 0
    first_example = None
    s_hist = {}

    for n in range(2, args.nmax + 1):
        tn = time.time()
        cnt = cnt_aa = 0
        for down in naturally_labelled(n):
            cnt += 1
            key = canonical(down)
            if key not in hcache:
                hcache[key] = h_C_moebius(down)
            h, omega = hcache[key]
            comps = components(down, n)
            L = lin_ext(down, n)
            Lset = set(L)
            seen = set()
            classes = []
            for w in L:
                if w in seen:
                    continue
                # class as C_n orbit intersected with Lin P
                orbit = {w[i:] + w[:i] for i in range(n)}
                kap = sorted(orbit & Lset)
                seen.update(kap)
                cuts = cuts_of(w, comps)
                # cut rotations must give the same set
                rot = sorted({w[p:] + w[:p] for p in [0] + cuts})
                claim('class = orbit cap Lin = cut rotations', rot == kap)
                bounds = [0] + cuts + [n]
                pieces = [w[bounds[i]:bounds[i + 1]] for i in range(len(bounds) - 1)]
                classes.append((kap, pieces))

            f = [0] * n
            hF = []           # Theorem F
            hF_s1 = []        # control: (1-x)^(s-1)
            hF_d = []         # control: x^d in place of x^(d-1)
            A = 0
            aa_list = []
            mindes_sum = 0
            for kap, pieces in classes:
                s = len(pieces)
                mdes = min(des(u) for u in kap)
                mindes_sum += mdes
                f[mdes] += 1
                d = sum(des(c) for c in pieces)
                deltas = [int(pieces[k][-1] > pieces[(k + 1) % s][0]) for k in range(s)] if s >= 2 else []
                allasc = s >= 2 and sum(deltas) == 0
                claim('class size = s', len(kap) == s)
                if s == 1:
                    s_hist['s=1 (never all-ascent)'] = s_hist.get('s=1 (never all-ascent)', 0) + 1
                if allasc:
                    A += 1
                    aa_list.append((d, s, kap, pieces))
                    s_hist[s] = s_hist.get(s, 0) + 1
                    # L3(a), (b)
                    claim('[aa-a] 1 <= d <= n-s', 1 <= d <= n - s, (down, pieces))
                    claim('[aa-b] every member has des = d', all(des(u) == d for u in kap), (down, pieces))
                    term = pmul(xpow(d - 1), padd([1], [-c for c in ppow([1, -1], s)]))
                    hF = padd(hF, term)
                    hF_s1 = padd(hF_s1, pmul(xpow(d - 1), padd([1], [-c for c in ppow([1, -1], s - 1)])))
                    hF_d = padd(hF_d, pmul(xpow(d), padd([1], [-c for c in ppow([1, -1], s)])))
                    # L3(c) for every component T, m = 0..n+1
                    for T in comps:
                        for m in range(n + 2):
                            lhs = sum(N_T(u, m, T, comps, n) for u in kap)
                            M = m + n - 1 - d
                            rhs = binom(m + n - d, n) - binom(m + n - d - s, n - s)
                            alt = sum(binom(M - i, n - i) for i in range(s))   # [AudH] sec. 2 form
                            claim('[aa-c] sum_kappa N_T = C(m+n-d,n) - C(m+n-d-s,n-s)', lhs == rhs, (down, pieces, T, m))
                            claim('[aa-c] = sum_i C(M-i,n-i) (audit form)', lhs == alt)
                            control('[ctl-aa-single] all-ascent class gives single binomial C(m+n-1-d,n)',
                                    lhs != binom(m + n - 1 - d, n))
                else:
                    hF = padd(hF, xpow(mdes))
                    hF_s1 = padd(hF_s1, xpow(mdes))
                    hF_d = padd(hF_d, xpow(mdes))
            f = ptrim(f)
            hF, hF_s1, hF_d = ptrim(hF), ptrim(hF_s1), ptrim(hF_d)
            info = (n, down, h, f, A)
            claim('[F] Moebius h_C = Theorem F', hF == h, info)
            jh = sum(j * c for j, c in enumerate(h))
            claim('[M] sum mindes - sum j h_j = A', mindes_sum - jh == A, info)
            claim('[iff] f == h_C  <=>  A == 0', (f == h) == (A == 0), info)
            claim('[sum] f(1) = h_C(1)', sum(f) == sum(h), info)
            control('[ctl-mindes-all] min-des = h_C on every natural labelling', f != h, info)
            control('[ctl-moment-0] sum mindes = sum j h_j', mindes_sum != jh, info)
            if A > 0:
                cnt_aa += 1
                maxA = max(maxA, A)
                if first_example is None:
                    first_example = info
                control('[ctl-F-s1] F with (1-x)^(s-1)', hF_s1 != h, info)
                control('[ctl-F-d] F with x^d for x^(d-1)', hF_d != h, info)
                # Corollary L
                d0 = min(d for d, s, _, _ in aa_list)
                hh = h + [0] * (n + 2)
                ff = f + [0] * (n + 2)
                claim('[L] agree below d0', all(hh[j] == ff[j] for j in range(d0)), info)
                pred = sum(s - 1 for d, s, _, _ in aa_list if d == d0)
                claim('[L] h_d0 - f_d0 = sum (s-1) > 0', hh[d0] - ff[d0] == pred and pred > 0, info)
                control('[ctl-L-s] h_d0 - f_d0 = sum s (not s-1)',
                        hh[d0] - ff[d0] != sum(s for d, s, _, _ in aa_list if d == d0), info)
                # end-to-end: Proposition D summed over all of Lin P equals Moebius Omega_C
                for T in comps:
                    for m in range(n + 2):
                        tot = sum(N_T(u, m, T, comps, n) for u in L)
                        claim('[D-e2e] sum_{Lin P} N_T = Moebius Omega_C (labellings with A>0)', tot == omega[m], (down, T, m))
            # instrument control on the Moebius side: des on Lin P = h_C iff connected
            if len(comps) == 1:
                e = [0] * n
                for w in L:
                    e[des(w)] += 1
                claim('[Mob-sanity] connected: des on Lin P = Moebius h_C (Stanley)', ptrim(e) == h, info)
            else:
                e = [0] * n
                for w in L:
                    e[des(w)] += 1
                control('[ctl-lin] des on Lin P = h_C for disconnected P', ptrim(e) != h, info)
        per_n[n] = (cnt, cnt_aa)
        print(f'INFO n={n}: {cnt} naturally labelled posets, {cnt_aa} with an all-ascent class, {time.time() - tn:.1f}s', flush=True)

    iso = {}
    for (k, _) in hcache:
        iso[k] = iso.get(k, 0) + 1
    print('INFO iso classes seen (n>=2):', ', '.join(f'n={k}: {iso[k]}' for k in sorted(iso)))
    print('INFO classes with s=1, and all-ascent classes by s:', s_hist)
    print('INFO largest A in one labelling:', maxA)
    if first_example:
        n, down, h, f, A = first_example
        rel = [(x, y) for y in range(n) for x in range(n) if down[y] >> x & 1]
        print(f'EXAMPLE first labelling with A>0: n={n} rel={rel} h_C={h} min-des={f} A={A}')
    ok = True
    for k, (tot, bad) in stats.items():
        tag = 'PASS' if bad == 0 else 'FAIL'
        ok &= bad == 0
        print(f'{tag} {k}: {tot} cases, {bad} failures' + (f'  first={fails[k]}' if bad else ''))
    for k, (tot, ref, ex) in ctl.items():
        tag = 'PASS CONTROL' if ref > 0 else 'FAIL CONTROL'
        ok &= ref > 0
        print(f'{tag} {k}: refuted on {ref} of {tot}')
    print(f'INFO total time {time.time() - t0:.1f}s')
    print('ALL PASS' if ok else 'SOME FAILURE')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
