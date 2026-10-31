"""Independent check of notes/linext_statistics.md (notes/audit_linext_statistics.md).

New code. It imports nothing from the repository.

Sections (each prints tagged lines; the script exits 0 iff every CLAIM line
holds and every CONTROL line is refuted somewhere):

  [omega]      Theorem Omega.  For every poset P with n <= NMAX (up to iso),
               every component T and every 0 <= m <= MMAX:
                 M(P,m) := sum_{pi in OP(P)} |mu(pi,1)| C(m,|pi|)       (Mobius side;
                 mu computed inside OP(P) by the recursion over [pi,1], no Lemma U)
               equals
                 D(P,T,m) := #{f : P -> [m] order-preserving : every nonempty upper
                             level set that is a union of components contains T}
               (direct enumeration).  Also: (-1)^{|pi|-1} mu(pi,1) = e_C(Q_pi) > 0,
               with e_C computed from rotations of words; leading coefficient.
  [omega-poly] same identity as polynomials: m = 0..n (degree <= n on both sides).
  [omega-des]  Corollary Omega-des, every natural labelling (n <= LMAX), every T,
               m = 0..n.
  [chi]        refutation: (-1)^{n-1} chi_P(-1) = e(P), chi_P(t)=sum mu(0,pi) t^{|pi|-1}.
  [kw]         refutation: #{w in Lin P : maj w = 1 mod n} = e_C(P).
  [sgn]        refutation: |I(P)| = e_C(P).
  [p3a]        maj(w_2..w_n w_1) = maj(w) - cdes(w) mod n on S_n.
  [p3b]        n prime: #{u in Lin(P)C_n : maj u = r} = e_C(P) for every r;
               composite n: fails somewhere.
  [p3']        disconnected, gcd(component sizes)=1  =>  maj equidistributed mod n.
  [p4]         |I(P)| = |[n; m_1..m_k]_{q=-1}| prod |I(T_i)|.
  [ctl-*]      positive controls that must fail.
"""

import argparse
import itertools
import math
import sys
from functools import lru_cache

FAILS = []
CONTROLS_UNREFUTED = []


def claim(tag, ok, msg):
    print(f"[{tag}] {'HOLDS' if ok else 'FAILS'}: {msg}")
    if not ok:
        FAILS.append(tag)


def control(tag, nfail, total, msg):
    print(f"[{tag}] CONTROL {'refuted' if nfail else 'NOT REFUTED'} on {nfail}/{total}: {msg}")
    if not nfail:
        CONTROLS_UNREFUTED.append(tag)


# ---------------------------------------------------------------- posets
# A poset on {0..n-1} is a frozenset of strict pairs (a,b), a<b, transitively closed
# (natural labelling: a <_P b implies a < b).

def gen_natural(n):
    """All naturally labelled posets on [n]: add n-1 as a maximal element above a down-set."""
    if n == 0:
        yield frozenset()
        return
    for R in gen_natural(n - 1):
        k = n - 1
        below = {i: {a for (a, b) in R if b == i} for i in range(k)}
        # down-sets of R on {0..k-1}
        for mask in range(1 << k):
            S = {i for i in range(k) if mask >> i & 1}
            if all(below[i] <= S for i in S):
                yield R | frozenset((i, k) for i in S)


def canon(n, R):
    """Canonical form: minimise the relation over relabellings that respect the
    (down-degree, up-degree) invariant classes (an exact iso-invariant refinement)."""
    inv = [(sum(1 for a, b in R if b == x), sum(1 for a, b in R if a == x)) for x in range(n)]
    classes = {}
    for x in range(n):
        classes.setdefault(inv[x], []).append(x)
    keys = sorted(classes)
    slots, start = [], 0
    for k in keys:
        slots.append((classes[k], list(range(start, start + len(classes[k])))))
        start += len(classes[k])
    best = None
    for choice in itertools.product(*[itertools.permutations(tg) for _, tg in slots]):
        p = [0] * n
        for (src, _), tg in zip(slots, choice):
            for x, y in zip(src, tg):
                p[x] = y
        key = tuple(sorted((p[a], p[b]) for (a, b) in R))
        if best is None or key < best:
            best = key
    return (tuple(inv[x] for x in sorted(range(n), key=lambda x: inv[x])), best)


def posets_up_to_iso(n):
    seen = {}
    for R in gen_natural(n):
        c = canon(n, R)
        if c not in seen:
            seen[c] = R
    return list(seen.values())


def components(n, R):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in R:
        parent[find(a)] = find(b)
    comps = {}
    for x in range(n):
        comps.setdefault(find(x), set()).add(x)
    return [frozenset(c) for c in comps.values()]


def is_union_of_components(S, comps):
    return all(c <= S or not (c & S) for c in comps)


def linext(n, R):
    """Linear extensions as tuples of labels."""
    below = [set() for _ in range(n)]
    for a, b in R:
        below[b].add(a)
    out = []

    def rec(w, used):
        if len(w) == n:
            out.append(tuple(w))
            return
        for x in range(n):
            if not (used >> x & 1) and all(used >> y & 1 for y in below[x]):
                w.append(x)
                rec(w, used | 1 << x)
                w.pop()
    rec([], 0)
    return out


def is_linext(w, R):
    pos = {x: i for i, x in enumerate(w)}
    return all(pos[a] < pos[b] for a, b in R)


def e_C_words(n, R):
    """Number of rotation classes of words (permutations of the ground set) meeting Lin P."""
    L = linext(n, R)
    classes = set()
    for w in L:
        classes.add(min(w[i:] + w[:i] for i in range(n)))
    return len(classes)


# ---------------------------------------------------------------- set partitions / OP(P)

def set_partitions(elems):
    elems = list(elems)
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def quotient_acyclic(blocks, R):
    """Is the quotient digraph P/pi acyclic? Returns (ok, edges between block indices)."""
    where = {}
    for i, B in enumerate(blocks):
        for x in B:
            where[x] = i
    k = len(blocks)
    E = set()
    for a, b in R:
        i, j = where[a], where[b]
        if i != j:
            E.add((i, j))
    indeg = [0] * k
    out = [[] for _ in range(k)]
    for i, j in E:
        out[i].append(j)
        indeg[j] += 1
    stack = [i for i in range(k) if indeg[i] == 0]
    seen = 0
    while stack:
        i = stack.pop()
        seen += 1
        for j in out[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                stack.append(j)
    return seen == k, E


def transitive_closure(k, E):
    reach = [set() for _ in range(k)]
    for i, j in E:
        reach[i].add(j)
    changed = True
    while changed:
        changed = False
        for i in range(k):
            new = set(reach[i])
            for j in reach[i]:
                new |= reach[j]
            if new != reach[i]:
                reach[i] = new
                changed = True
    return frozenset((i, j) for i in range(k) for j in reach[i])


def OP(n, R):
    """List of (partition as frozenset of frozensets, Q_pi as (k, R')) in OP(P)."""
    res = []
    for p in set_partitions(range(n)):
        blocks = [frozenset(B) for B in p]
        ok, E = quotient_acyclic(blocks, R)
        if ok:
            # relabel quotient naturally: topological order of blocks
            k = len(blocks)
            Q = transitive_closure(k, E)
            res.append((frozenset(blocks), (k, Q)))
    return res


def refines(p, q):
    """p <= q (p finer than q)."""
    return all(any(B <= C for C in q) for B in p)


def mobius_to_top(parts):
    """mu(pi, 1hat) computed inside the poset `parts` (ordered by refinement)."""
    top = max(parts, key=lambda p: -len(p))
    assert len(top) == 1
    order = sorted(parts, key=len)  # coarse first
    mu = {}
    for p in order:
        if p == top:
            mu[p] = 1
        else:
            mu[p] = -sum(mu[q] for q in mu if q != p and refines(p, q))
    return mu


def mobius_from_bottom(parts):
    order = sorted(parts, key=len, reverse=True)  # fine first
    bot = order[0]
    assert len(bot) == max(len(p) for p in parts)
    mu = {}
    for p in order:
        if p == bot:
            mu[p] = 1
        else:
            mu[p] = -sum(mu[q] for q in mu if q != p and refines(q, p))
    return mu


# ---------------------------------------------------------------- order-preserving maps

def op_maps(n, R, m):
    """Yield every order-preserving f : P -> {1..m} as a tuple indexed by element (labels natural)."""
    below = [[a for (a, b) in R if b == x] for x in range(n)]
    f = [0] * n

    def rec(x):
        if x == n:
            yield tuple(f)
            return
        lo = max([f[a] for a in below[x]], default=1)
        for v in range(lo, m + 1):
            f[x] = v
            yield from rec(x + 1)
    if n == 0:
        yield ()
        return
    yield from rec(0)


def omega_condition(f, comps, T):
    vals = sorted(set(f))
    for v in vals:
        U = frozenset(x for x in range(len(f)) if f[x] >= v)
        if is_union_of_components(U, comps) and not (T <= U):
            return False
    return True


# ---------------------------------------------------------------- statistics

def des_set(w):
    return [i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1]]


def maj(w):
    return sum(des_set(w))


def cdes(w):
    return len(des_set(w)) + (1 if w[-1] > w[0] else 0)


def sign(w):
    inv = sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if w[i] > w[j])
    return -1 if inv % 2 else 1


def qmultinomial_at(q, parts):
    """[n; m_1..m_k]_q as an exact integer polynomial evaluated at integer q (via polynomial arithmetic)."""
    def poly_mul(a, b):
        c = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i + j] += x * y
        return c

    def qfact(k):
        p = [1]
        for i in range(1, k + 1):
            p = poly_mul(p, [1] * i)  # [i]_q
        return p

    def poly_div(a, b):
        a = a[:]
        out = [0] * (len(a) - len(b) + 1)
        for i in range(len(out) - 1, -1, -1):
            c = a[i + len(b) - 1] // b[-1]
            out[i] = c
            for j, y in enumerate(b):
                a[i + j] -= c * y
        assert all(x == 0 for x in a)
        return out
    num = qfact(sum(parts))
    den = [1]
    for k in parts:
        den = poly_mul(den, qfact(k))
    P = poly_div(num, den)
    return sum(c * q ** i for i, c in enumerate(P))


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


# ---------------------------------------------------------------- sections

def sec_omega(posets, mmax, lmax):
    tot = bad = 0
    sign_bad = 0
    lead_bad = 0
    poly_tot = poly_bad = 0
    ctl_noT = ctl_mu0 = ctl_max = ctl_strict = 0
    ctl_tot = 0
    antichain_bad = 0
    tindep_bad = 0
    for n, R in posets:
        comps = components(n, R)
        ops = OP(n, R)
        parts = [p for p, _ in ops]
        mu1 = mobius_to_top(parts)
        mu0 = mobius_from_bottom(parts)
        # sign and e_C(Q_pi)
        for p, (k, Q) in ops:
            s = (-1) ** (len(p) - 1) * mu1[p]
            if not (s > 0 and s == e_C_words(k, Q)):
                sign_bad += 1
        Ms = lambda m: sum(abs(mu1[p]) * math.comb(m, len(p)) for p in parts)
        Msigned = lambda m: sum((-1) ** (len(p) - 1) * mu1[p] * math.comb(m, len(p)) for p in parts)
        # leading coefficient: coefficient of C(m,n) is the number of |pi|=n terms -> e_C(P)
        if sum(abs(mu1[p]) for p in parts if len(p) == n) != e_C_words(n, R):
            lead_bad += 1
        top_m = max(mmax, n)
        maps = {m: list(op_maps(n, R, m)) for m in range(0, top_m + 1)}
        counts_by_T = []
        for T in comps:
            vals = []
            for m in range(0, top_m + 1):
                D = sum(1 for f in maps[m] if omega_condition(f, comps, T))
                vals.append(D)
                if m <= mmax:
                    tot += 1
                    if D != Ms(m) or D != Msigned(m):
                        bad += 1
                poly_tot += 1
                if D != Ms(m):
                    poly_bad += 1
                # controls (only at m <= mmax)
                if m <= mmax:
                    ctl_tot += 1
                    if len(maps[m]) != Ms(m):
                        ctl_noT += 1
                    if sum(abs(mu0[p]) * math.comb(m, len(p)) for p in parts) != D:
                        ctl_mu0 += 1
                    Dmax = sum(1 for f in maps[m] if f and max(f[x] for x in T) == max(f))
                    if Dmax != D:
                        ctl_max += 1
                    # strict: also count the whole set P? use "union of components" incl. P minus T-check
                    # control: condition required on ALL nonempty upper level sets (not only unions of comps)
                    Dall = sum(1 for f in maps[m]
                               if all(T <= frozenset(x for x in range(n) if f[x] >= v) for v in set(f)))
                    if Dall != D:
                        ctl_strict += 1
            counts_by_T.append(tuple(vals))
        if len(set(counts_by_T)) != 1:
            tindep_bad += 1
        if not R:  # antichain: sum_j j^{n-1}
            for m in range(0, mmax + 1):
                if Ms(m) != sum(j ** (n - 1) for j in range(1, m + 1)):
                    antichain_bad += 1
    claim("omega", bad == 0, f"Mobius side = direct count on {tot - bad}/{tot} (P,T,m), n<=NMAX, m<={mmax}")
    claim("omega-poly", poly_bad == 0,
          f"identity at m=0..max(n,{mmax}) on {poly_tot - poly_bad}/{poly_tot} (P,T,m): equal as polynomials")
    claim("omega-sign", sign_bad == 0, "(-1)^{|pi|-1} mu(pi,1) = e_C(Q_pi) > 0 for every pi in OP(P), every P")
    claim("omega-lead", lead_bad == 0, "coefficient of C(m,n) is e_C(P) (so leading coeff e_C/n!)")
    claim("omega-Tindep", tindep_bad == 0, "direct count independent of the component T")
    claim("omega-antichain", antichain_bad == 0, "antichain: Omega_C = sum_{j<=m} j^{n-1}")
    control("ctl-noT", ctl_noT, ctl_tot, "drop the T condition (count all order-preserving maps)")
    control("ctl-mu0", ctl_mu0, ctl_tot, "use |mu(0,pi)| instead of |mu(pi,1)|")
    control("ctl-max", ctl_max, ctl_tot, "condition 'max f attained on T'")
    control("ctl-allsets", ctl_strict, ctl_tot, "require T in EVERY nonempty upper level set")


def sec_omega_des(lmax):
    tot = bad = 0
    ctl_tot = ctl_nomerge = ctl_nodrop = 0
    for n in range(1, lmax + 1):
        for R in gen_natural(n):
            # every natural labelling is produced by gen_natural (each labelled natural poset once)
            comps = components(n, R)
            L = linext(n, R)
            for T in comps:
                for m in range(0, n + 1):
                    D = sum(1 for f in op_maps(n, R, m) if omega_condition(f, comps, T))
                    s = 0
                    s_nomerge = 0
                    s_nodrop = 0
                    for w in L:
                        Des = set(des_set(w))
                        d = len(Des)
                        C = [p for p in range(1, n) if is_union_of_components(frozenset(w[:p]), comps)
                             and T <= frozenset(w[:p])]
                        c = len(C)
                        if not (set(C) & Des):
                            s += math.comb(m + n - 1 - d - c, n - c) if m + n - 1 - d - c >= 0 else 0
                            s_nomerge += math.comb(m + n - 1 - d, n) if m + n - 1 - d >= 0 else 0
                        s_nodrop += (math.comb(m + n - 1 - d - c, n - c) if m + n - 1 - d - c >= 0 else 0)
                    tot += 1
                    if s != D:
                        bad += 1
                    ctl_tot += 1
                    if s_nomerge != D:
                        ctl_nomerge += 1
                    if s_nodrop != D:
                        ctl_nodrop += 1
    claim("omega-des", bad == 0, f"Corollary Omega-des on {tot - bad}/{tot} (natural labelling, T, m<=n), n<={lmax}")
    control("ctl-des-nomerge", ctl_nomerge, ctl_tot, "Omega-des without the -c merging")
    control("ctl-des-nodrop", ctl_nodrop, ctl_tot, "Omega-des without dropping w with C_T(w) meeting Des(w)")


def sec_chi(posets):
    holds = 0
    tot = 0
    restr_bad = 0
    for n, R in posets:
        if n < 2:
            continue
        ops = OP(n, R)
        parts = [p for p, _ in ops]
        mu0 = mobius_from_bottom(parts)
        chi = sum(mu0[p] * (-1) ** (len(p) - 1) for p in parts)
        e = len(linext(n, R))
        tot += 1
        if (-1) ** (n - 1) * chi == e:
            holds += 1
            if R:
                print(f"  chi identity holds on non-antichain n={n} R={sorted(R)}")
        # restricted version: (-1)^n e(P) = sum_{sigma >= kappa} (-1)^{|sigma|} mu(0,sigma)
        kappa = frozenset(components(n, R))
        rs = sum((-1) ** len(p) * mu0[p] for p in parts if refines(kappa, p))
        if rs != (-1) ** n * e:
            restr_bad += 1
    nanti = sum(1 for n, R in posets if n >= 2 and not R)
    claim("chi-refute", holds == nanti,
          f"(-1)^(n-1) chi_P(-1) = e(P) holds on {holds}/{tot} posets (2<=n<=NMAX); antichains = {nanti}")
    claim("chi-restr", restr_bad == 0, "restricted sum over sigma >= kappa gives (-1)^n e(P) on every P (context)")


def sec_lin(posets7):
    kw_hold = sg_hold = tot = 0
    p3b_bad = p3b_tot = 0
    p3b_comp_fail = p3b_comp_tot = 0
    p3p_bad = p3p_tot = 0
    p3p_ctl = p3p_ctl_tot = 0
    p4_bad = p4_tot = 0
    for n, R in posets7:
        if n < 2:
            continue
        tot += 1
        L = linext(n, R)
        eC = e_C_words(n, R)
        comps = components(n, R)
        if sum(1 for w in L if maj(w) % n == 1 % n) == eC:
            kw_hold += 1
        I = sum(sign(w) for w in L)
        if abs(I) == eC:
            sg_hold += 1
        # Prop 3(b)
        orbit = set()
        for w in L:
            for i in range(n):
                orbit.add(w[i:] + w[:i])
        cnt = [0] * n
        for u in orbit:
            cnt[maj(u) % n] += 1
        okb = all(c == eC for c in cnt)
        if is_prime(n):
            p3b_tot += 1
            if not okb:
                p3b_bad += 1
        elif n in (4, 6):
            p3b_comp_tot += 1
            if not okb:
                p3b_comp_fail += 1
        # Prop 3'
        cntL = [0] * n
        for w in L:
            cntL[maj(w) % n] += 1
        equi = len(set(cntL)) == 1
        sizes = [len(c) for c in comps]
        if len(comps) >= 2 and math.gcd(*sizes) == 1:
            p3p_tot += 1
            if not equi:
                p3p_bad += 1
        if len(comps) == 1:
            p3p_ctl_tot += 1
            if not equi:
                p3p_ctl += 1
        # Prop 4
        if len(comps) >= 2:
            p4_tot += 1
            prod = 1
            for c in comps:
                lab = sorted(c)
                rel = {(lab.index(a), lab.index(b)) for (a, b) in R if a in c}
                prod *= abs(sum(sign(w) for w in linext(len(lab), frozenset(rel))))
            if abs(I) != abs(qmultinomial_at(-1, sizes)) * prod:
                p4_bad += 1
    nanti = sum(1 for n, R in posets7 if n >= 2 and not R)
    print(f"  ({tot} posets with 2<=n<=7; antichains {nanti})")
    claim("kw-refute", kw_hold < tot, f"#{{w in Lin P: maj = 1 mod n}} = e_C(P) holds on only {kw_hold}/{tot}")
    claim("sgn-refute", sg_hold < tot, f"|I(P)| = e_C(P) holds on only {sg_hold}/{tot}")
    claim("p3b", p3b_bad == 0, f"n prime: maj equidistributed on Lin(P)C_n with e_C per residue: {p3b_tot - p3b_bad}/{p3b_tot}")
    control("p3b-composite", p3b_comp_fail, p3b_comp_tot, "Prop 3(b) at composite n in {4,6}")
    claim("p3'", p3p_bad == 0, f"disconnected, gcd=1 => maj equidistributed mod n: {p3p_tot - p3p_bad}/{p3p_tot}")
    control("p3'-connected", p3p_ctl, p3p_ctl_tot, "maj equidistribution on connected P")
    claim("p4", p4_bad == 0, f"|I(P)| = |[n;m]_(-1)| prod |I(T_i)| on {p4_tot - p4_bad}/{p4_tot} disconnected P")
    return kw_hold, sg_hold, tot


def sec_p3a(nmax):
    bad = tot = 0
    ctl = 0
    for n in range(2, nmax + 1):
        for w in itertools.permutations(range(n)):
            r = w[1:] + w[:1]
            tot += 1
            if (maj(r) - maj(w) + cdes(w)) % n != 0 or cdes(r) != cdes(w):
                bad += 1
            if (maj(r) - maj(w) + len(des_set(w))) % n != 0:
                ctl += 1
    claim("p3a", bad == 0, f"maj(rotation) = maj - cdes mod n and cdes rotation-invariant: {tot - bad}/{tot}, n<={nmax}")
    control("p3a-des", ctl, tot, "same with des in place of cdes")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--mmax", type=int, default=4)
    ap.add_argument("--lmax", type=int, default=5)
    ap.add_argument("--n7", type=int, default=7, help="largest n for the cheap Lin-P sections")
    a = ap.parse_args()
    posets = [(n, R) for n in range(1, a.nmax + 1) for R in posets_up_to_iso(n)]
    print(f"posets up to iso, 1<=n<={a.nmax}: {len(posets)} "
          f"(by n: {[sum(1 for k, _ in posets if k == n) for n in range(1, a.nmax + 1)]})")
    sec_omega(posets, a.mmax, a.lmax)
    sec_omega_des(a.lmax)
    sec_chi(posets)
    posets7 = [(n, R) for n in range(1, a.n7 + 1) for R in posets_up_to_iso(n)]
    sec_lin(posets7)
    sec_p3a(a.n7)
    # explicit small examples from the note
    R = frozenset({(0, 1)})
    L = linext(3, R)
    print(f"[ex] C2+C1: Lin={L}, maj={[maj(w) for w in L]}, e_C={e_C_words(3, R)}")
    R3 = frozenset({(0, 1), (0, 2), (1, 2)})
    parts = [p for p, _ in OP(3, R3)]
    mu0 = mobius_from_bottom(parts)
    print(f"[ex] C3: chi coefficients by |pi|: {sorted((len(p), mu0[p]) for p in parts)}")
    print(f"SUMMARY: {len(FAILS)} failed claims {FAILS}; unrefuted controls {CONTROLS_UNREFUTED}")
    sys.exit(0 if not FAILS and not CONTROLS_UNREFUTED else 1)


if __name__ == "__main__":
    main()
