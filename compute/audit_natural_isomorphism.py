#!/usr/bin/env python3
"""Independent audit script for notes/natural_isomorphism.md (Theorem Psi,
Theorem 1, Theorem 2).  Written for notes/audit_natural_isomorphism.md.

It does NOT import compute/natural_isomorphism.py, nor any other module of
this repo: posets, linear extensions, components, cuts, shuffles, combs and
the rank arithmetic are all re-implemented here.

Conventions.  A word / permutation is a tuple w = (w_1, ..., w_n) of the
letters 0..n-1.  Right multiplication by gamma^k rotates LEFT by k:
w gamma^k = w_{k+1} .. w_n w_1 .. w_k.  e_zeta = (1/n) sum_j zeta^{-j} gamma^j,
so w e_zeta = (1/n) sum_j zeta^{-j} w gamma^j.  Left multiplication by
g in S_n relabels letters: (g w)_i = g[w_i].

Membership in Sh_n (span of proper shuffles) is tested by pairing with the
(n-1)! left combs [..[[0, t_2], t_3], .., t_n].  By Ree's theorem
(Lie_n^perp = Sh_n) and the comb basis of Lie_n, the kernel of the pairing
is exactly Sh_n.  [sh] re-checks this without Ree for n <= 5: every proper
shuffle pairs to 0 with every comb, the combs have rank (n-1)!, and the
proper shuffles span a space of dimension n! - (n-1)!.

Arithmetic is modulo primes p = 1 (mod 60), zeta of exact order n mod p.
Full rank mod p implies full rank over Q(zeta) (reduction modulo a prime of
Z[zeta] above p is a ring map, so a nonzero minor stays nonzero).  A
nonzero coordinate mod p likewise certifies a nonzero element over Q(zeta).
Vanishings mod p are only evidence; each one used is checked at two primes.

Sections:
  [enum] poset counts 1,2,5,16,63,318 (n=1..6), own enumerator
  [sh]   comb-pairing kernel = Sh_n, without Ree (n <= 5)
  [cut]  Lemma 4: w gamma^k in Lin P  <=>  k is a cut (prefix = union of comps)
  [psi0] Lemma Psi.0: s_lam(w gamma^m) = lam(w_1..w_m) s_lam(w), random lam
  [con]  the contraction claim in Step 1:
         E_{a,x} s_lam(v) = +- s_lam'(v \\ x), lam'(a) = lam(a) lam(x)
  [psi]  Theorem Psi with lam = zeta for EVERY primitive zeta, and for
         random admissible lam: the class sums are independent mod Sh;
         also dim M_P = rank(Lin P mod Sh) = e_C(P) = dim L_P
  [ctl]  positive controls: lam == 1 (inadmissible) must drop rank on the
         antichain; a non-primitive root must drop rank somewhere
  [equi] pr_P(g y) = g pr_P(y) for g in Aut(P), y in L_P (equivariance) and
         pr_{sP}(s y) = s pr_P(y) for random relabelings s (naturality)
  [ext]  R_P e_zeta = 0  <=>  P connected or n <= 2 ; the witness
         coefficient of u = t_1 s t_2..t_b in (s sh t) e_zeta is 1/n
  [prc]  Prop. C / C' escape: (i) the uniform map y -> y mod Sh sends
         L_P onto M_P for how many P; (ii) Theta is not extension-natural:
         for disconnected P, pr_P(w e_zeta) - pr_{C_w}(w e_zeta) not in Sh
  [lie]  Cor. Psi.2: rank Lie_n e_zeta = (n-1)! for every primitive zeta
  [sum]  Conjecture 3.3 (phi_Sigma invertible) for disconnected P

Run from compute/:
    python3 audit_natural_isomorphism.py --nmax 6 > output/audit_natural_isomorphism.txt
Exit status 0 iff every check passes; the last line is ALL CHECKS PASSED.
"""

import argparse
import itertools
import random
import sys

# ---------------------------------------------------------------------------
# primes and roots of unity


def is_prime(m):
    if m < 2:
        return False
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return True


def prime_1_mod(mod, start):
    p = start - start % mod + 1
    while not is_prime(p):
        p += mod
    return p


def element_of_order(n, p):
    """Some element of exact multiplicative order n mod p (n | p-1)."""
    for g in range(2, p):
        z = pow(g, (p - 1) // n, p)
        if all(pow(z, n // q, p) != 1 for q in range(2, n + 1)
               if n % q == 0 and is_prime(q)):
            return z
    raise ValueError


def primitive_roots(n, p):
    z = element_of_order(n, p)
    return [pow(z, k, p) for k in range(1, n + 1) if gcd(k, n) == 1]


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a


PRIMES = [prime_1_mod(60, 10**9), prime_1_mod(60, 3 * 10**9)]

# ---------------------------------------------------------------------------
# posets: frozenset of pairs (a, b) meaning a < b, transitively closed


def closure(rel):
    rel = set(rel)
    while True:
        new = {(a, d) for (a, b) in rel for (c, d) in rel if b == c} - rel
        if not new:
            return frozenset(rel)
        rel |= new


def canon(rel, n, perms):
    return min(tuple(sorted((p[a], p[b]) for a, b in rel)) for p in perms)


def enumerate_posets(nmax):
    """Unlabeled posets by size: every poset on [n] is a poset on [n-1] plus
    a new maximal element n-1 whose strict down-set is an order ideal."""
    out = {1: [frozenset()]}
    for n in range(2, nmax + 1):
        perms = list(itertools.permutations(range(n)))
        seen = {}
        for rel in out[n - 1]:
            m = n - 1
            for mask in range(1 << m):
                D = {i for i in range(m) if mask >> i & 1}
                if any(a not in D for (a, b) in rel if b in D):
                    continue  # not down-closed
                new = frozenset(rel | {(d, m) for d in D})
                c = canon(new, n, perms)
                if c not in seen:
                    seen[c] = frozenset(c)
        out[n] = list(seen.values())
    return out


def linear_extensions(rel, n):
    below = {b: {a for (a, c) in rel if c == b} for b in range(n)}
    res = []

    def rec(pref, used):
        if len(pref) == n:
            res.append(tuple(pref))
            return
        for x in range(n):
            if x not in used and below[x] <= used:
                used.add(x)
                pref.append(x)
                rec(pref, used)
                pref.pop()
                used.remove(x)
    rec([], set())
    return res


def components(rel, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for a, b in rel:
        parent[find(a)] = find(b)
    comp = {}
    for x in range(n):
        comp.setdefault(find(x), set()).add(x)
    return [frozenset(c) for c in comp.values()]


def is_union_of(S, comps):
    return all(c <= S or not (c & S) for c in comps)


def cuts(w, comps):
    return [k for k in range(len(w)) if is_union_of(set(w[:k]), comps)]


def rot(w, k):
    return w[k:] + w[:k]


def classes(lin, comps):
    """Cyclic classes: {w gamma^k : k a cut}; returns list of reps."""
    seen, reps = set(), []
    for w in lin:
        if w in seen:
            continue
        reps.append(w)
        for k in cuts(w, comps):
            seen.add(rot(w, k))
    return reps


def automorphisms(rel, n):
    return [g for g in itertools.permutations(range(n))
            if {(g[a], g[b]) for a, b in rel} == set(rel)]


def act(g, w):
    return tuple(g[x] for x in w)


# ---------------------------------------------------------------------------
# vectors (dict word -> coeff mod p), shuffles, combs


def add(v, w, c, p):
    v[w] = (v.get(w, 0) + c) % p


def shuffle(u, v):
    if not u:
        return [v]
    if not v:
        return [u]
    return [(u[0],) + z for z in shuffle(u[1:], v)] + \
           [(v[0],) + z for z in shuffle(u, v[1:])]


def left_comb(letters):
    vec = {(letters[0],): 1}
    for b in letters[1:]:
        new = {}
        for w, c in vec.items():
            new[w + (b,)] = new.get(w + (b,), 0) + c
            new[(b,) + w] = new.get((b,) + w, 0) - c
        vec = new
    return vec


_COMBS = {}


def combs(n):
    if n not in _COMBS:
        _COMBS[n] = [left_comb((0,) + t)
                     for t in itertools.permutations(range(1, n))]
    return _COMBS[n]


def comb_coords(vec, n, p):
    """Pairing with the left combs: kernel = Sh_n (Ree; re-checked in [sh])."""
    return [sum(vec.get(w, 0) * c for w, c in cb.items()) % p
            for cb in combs(n)]


def rank(rows, p):
    rows = [list(r) for r in rows if any(x % p for x in r)]
    if not rows:
        return 0
    r, ncol = 0, len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [x * inv % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def in_sh(vec, n, p):
    return not any(comb_coords(vec, n, p))


# ---------------------------------------------------------------------------
# the objects of Theorem Psi


def s_lam(w, lam, comps, p):
    """s_lam(w) = sum_{k cut} lam(w_1..w_k)^{-1} w gamma^k."""
    v = {}
    for k in cuts(w, comps):
        ph = 1
        for x in w[:k]:
            ph = ph * lam[x] % p
        add(v, rot(w, k), pow(ph, p - 2, p), p)
    return v


def we_zeta(w, z, p):
    """n * w e_zeta = sum_j zeta^{-j} w gamma^j."""
    n = len(w)
    zi = pow(z, p - 2, p)
    return {rot(w, j): pow(zi, j, p) for j in range(n)}


def truncate(vec, linset):
    return {w: c for w, c in vec.items() if w in linset}


def admissible(lam, comps, n, p):
    tot = 1
    for x in range(n):
        tot = tot * lam[x] % p
    if tot != 1:
        return False
    c = len(comps)
    for mask in range(1, (1 << c) - 1):
        ph = 1
        for i in range(c):
            if mask >> i & 1:
                for x in comps[i]:
                    ph = ph * lam[x] % p
        if ph == 1:
            return False
    return True


def random_admissible(comps, n, p, rng):
    while True:
        lam = [rng.randrange(1, p) for _ in range(n)]
        tot = 1
        for x in lam[:-1]:
            tot = tot * x % p
        lam[-1] = pow(tot, p - 2, p)
        if admissible(lam, comps, n, p):
            return lam


def psi_rank(rel, n, lam, p, comps=None, lin=None):
    comps = comps or components(rel, n)
    lin = lin or linear_extensions(rel, n)
    reps = classes(lin, comps)
    rows = [comb_coords(s_lam(w, lam, comps, p), n, p) for w in reps]
    return rank(rows, p), len(reps)


# ---------------------------------------------------------------------------
# checks


class Report:
    def __init__(self):
        self.ok = True

    def line(self, tag, msg, good):
        print(f"[{tag}] {msg}: {'OK' if good else 'FAIL'}")
        sys.stdout.flush()
        self.ok &= bool(good)


def check_enum(posets, nmax, rep):
    known = [1, 2, 5, 16, 63, 318, 2045]
    got = [len(posets[n]) for n in range(1, nmax + 1)]
    rep.line("enum", f"poset counts n=1..{nmax}: {got}",
             got == known[:nmax])


def check_sh(nsh, rep):
    p = PRIMES[0]
    for n in range(2, nsh + 1):
        letters = tuple(range(n))
        kill = True
        gens = []
        for k in range(1, n):
            for S in itertools.combinations(letters, k):
                T = tuple(x for x in letters if x not in S)
                for u in itertools.permutations(S):
                    for v in itertools.permutations(T):
                        vec = {}
                        for z in shuffle(u, v):
                            add(vec, z, 1, p)
                        if any(comb_coords(vec, n, p)):
                            kill = False
                        gens.append(vec)
        allw = list(itertools.permutations(letters))
        idx = {w: i for i, w in enumerate(allw)}
        rows = []
        for vec in gens:
            r = [0] * len(allw)
            for w, c in vec.items():
                r[idx[w]] = c
            rows.append(r)
        dsh = rank(rows, p)
        crows = []
        for cb in combs(n):
            r = [0] * len(allw)
            for w, c in cb.items():
                r[idx[w]] = c % p
            crows.append(r)
        dc = rank(crows, p)
        f = 1
        for i in range(2, n + 1):
            f *= i
        good = kill and dc == f // n and dsh == f - f // n
        rep.line("sh", f"n={n}: combs kill all proper shuffles={kill}, "
                 f"rank combs={dc}=(n-1)!, dim Sh={dsh}=n!-(n-1)!", good)


def check_cut(posets, nmax, rep):
    bad = tot = 0
    for n in range(1, nmax + 1):
        for rel in posets[n]:
            comps = components(rel, n)
            lin = linear_extensions(rel, n)
            ls = set(lin)
            for w in lin:
                c = set(cuts(w, comps))
                for k in range(n):
                    tot += 1
                    if (rot(w, k) in ls) != (k in c):
                        bad += 1
    rep.line("cut", f"Lemma 4, {tot} (P, w, k), n<={nmax}: {bad} mismatches",
             bad == 0)


def check_psi0(posets, nmax, rep, rng):
    p = PRIMES[0]
    bad = tot = 0
    for n in range(2, nmax + 1):
        for rel in posets[n]:
            comps = components(rel, n)
            lam = random_admissible(comps, n, p, rng)
            for w in linear_extensions(rel, n):
                base = s_lam(w, lam, comps, p)
                for m in cuts(w, comps):
                    ph = 1
                    for x in w[:m]:
                        ph = ph * lam[x] % p
                    other = s_lam(rot(w, m), lam, comps, p)
                    tot += 1
                    if other != {u: c * ph % p for u, c in base.items()}:
                        bad += 1
    rep.line("psi0", f"Lemma Psi.0, {tot} (P, w, cut), n<={nmax}: "
             f"{bad} failures", bad == 0)


def E(vec, a, x, p):
    out = {}
    for w, c in vec.items():
        i = w.index(x)
        j = w.index(a)
        if j == i + 1:
            add(out, w[:i] + w[i + 1:], c, p)
        elif j == i - 1:
            add(out, w[:i] + w[i + 1:], -c, p)
    return {w: c for w, c in out.items() if c}


def quotient(rel, n, a, x):
    """P/{a,x} on letters != x, relabeled to 0..n-2; returns (rel', f)."""
    keep = [y for y in range(n) if y != x]
    f = {y: i for i, y in enumerate(keep)}
    f[x] = f[a]
    img = {(f[u], f[v]) for u, v in rel if f[u] != f[v]}
    return closure(img), f


def check_contraction(posets, nmax, rep, rng, control=False):
    """control=True uses the WRONG weight lam'(a) = lam(a); it must fail."""
    p = PRIMES[0]
    bad = tot = 0
    for n in range(3, nmax + 1):
        for rel in posets[n]:
            comps = components(rel, n)
            lam = random_admissible(comps, n, p, rng)
            lin = linear_extensions(rel, n)
            pairs = {(w[i], w[i + 1]) for w in lin for i in range(n - 1)}
            for (y, z) in pairs:
                for (a, x) in ((z, y), (y, z)):
                    Q, f = quotient(rel, n, a, x)
                    qcomps = components(Q, n - 1)
                    lam2 = [0] * (n - 1)
                    for u in range(n):
                        if u != x:
                            lam2[f[u]] = lam[u]
                    lam2[f[a]] = lam[a] * (1 if control else lam[x]) % p
                    if not control and not admissible(lam2, qcomps, n - 1, p):
                        bad += 1
                        continue
                    for v in lin:
                        i, j = v.index(x), v.index(a)
                        if abs(i - j) != 1:
                            continue
                        sign = 1 if j == i + 1 else -1
                        vq = tuple(f[u] for u in v if u != x)
                        lhs = E(s_lam(v, lam, comps, p), a, x, p)
                        rhs = {u: sign * c % p for u, c in
                               s_lam(vq, lam2, qcomps, p).items()}
                        rhs = {u: c for u, c in rhs.items() if c}
                        # lhs is on letters != x; relabel by f
                        lhs = {tuple(f[t] for t in u): c for u, c in lhs.items()}
                        tot += 1
                        if lhs != rhs:
                            bad += 1
    if control:
        rep.line("ctl", f"wrong weight lam'(a) = lam(a) breaks the Step-1 "
                 f"claim in {bad}/{tot} cases", bad > 0)
        return
    rep.line("con", f"Step-1 claim E(s_lam(v)) = +-s_lam'(v\\x) and lam' "
             f"admissible, {tot} cases, 3<=n<={nmax}: {bad} failures",
             bad == 0)


def check_psi(posets, nmax, rep, rng, nrand):
    for n in range(2, nmax + 1):
        okz = okr = okdim = 0
        for rel in posets[n]:
            comps = components(rel, n)
            lin = linear_extensions(rel, n)
            ec = len(classes(lin, comps))
            good_z = True
            for p in PRIMES:
                for z in primitive_roots(n, p):
                    lam = [z] * n
                    r, e = psi_rank(rel, n, lam, p, comps, lin)
                    good_z &= (r == e)
            okz += good_z
            p = PRIMES[0]
            good_r = True
            for _ in range(nrand):
                lam = random_admissible(comps, n, p, rng)
                r, e = psi_rank(rel, n, lam, p, comps, lin)
                good_r &= (r == e)
            okr += good_r
            # dim M_P = rank of Lin P mod Sh; dim L_P = #classes (disjoint
            # rotation orbits) -- recompute L_P's rank directly as well
            dm = rank([comb_coords({w: 1}, n, p) for w in lin], p)
            allw = sorted({rot(w, j) for w in lin for j in range(n)})
            idx = {w: i for i, w in enumerate(allw)}
            z = element_of_order(n, p)
            lrows = []
            for w in lin:
                r_ = [0] * len(allw)
                for u, c in we_zeta(w, z, p).items():
                    r_[idx[u]] = c
                lrows.append(r_)
            dl = rank(lrows, p)
            okdim += (dm == ec == dl)
        N = len(posets[n])
        rep.line("psi", f"n={n}: {N} posets; class sums independent mod Sh "
                 f"for every primitive zeta at 2 primes: {okz}/{N}; "
                 f"{nrand} random admissible lam: {okr}/{N}; "
                 f"dim M_P = e_C = dim L_P: {okdim}/{N}",
                 okz == okr == okdim == N)


def check_controls(posets, nmax, rep):
    p = PRIMES[0]
    anti_drop = []
    for n in range(2, nmax + 1):
        rel = frozenset()
        r, e = psi_rank(rel, n, [1] * n, p)
        anti_drop.append(r < e)
    rep.line("ctl", f"lam == 1 drops rank on the antichain, n=2..{nmax}: "
             f"{anti_drop}", all(anti_drop))
    # a root of unity of order d | n, 1 < d < n, is inadmissible; count drops
    drops = {}
    for n in range(4, nmax + 1):
        for d in range(2, n):
            if n % d:
                continue
            z = element_of_order(d, p)
            cnt = sum(1 for rel in posets[n]
                      if (lambda re: re[0] < re[1])(
                          psi_rank(rel, n, [z] * n, p)))
            drops[(n, d)] = cnt
    rep.line("ctl", "non-primitive root (order d | n): #posets with rank "
             f"drop {drops}", all(v > 0 for v in drops.values()))


def check_equi(posets, nmax, rep, rng):
    p = PRIMES[0]
    bad = tot = 0
    for n in range(2, nmax + 1):
        z = element_of_order(n, p)
        for rel in posets[n]:
            lin = linear_extensions(rel, n)
            ls = set(lin)
            for g in automorphisms(rel, n):
                for w in lin:
                    y = we_zeta(w, z, p)
                    gy = {act(g, u): c for u, c in y.items()}
                    lhs = truncate(gy, ls)
                    rhs = {act(g, u): c for u, c in truncate(y, ls).items()}
                    tot += 1
                    bad += lhs != rhs
            s = list(range(n))
            rng.shuffle(s)
            srel = frozenset((s[a], s[b]) for a, b in rel)
            sls = set(linear_extensions(srel, n))
            for w in lin:
                y = we_zeta(w, z, p)
                sy = {act(s, u): c for u, c in y.items()}
                lhs = truncate(sy, sls)
                rhs = {act(s, u): c for u, c in truncate(y, ls).items()}
                tot += 1
                bad += lhs != rhs
    rep.line("equi", f"pr commutes with Aut(P) and with relabelings, "
             f"{tot} cases, n<={nmax}: {bad} failures", bad == 0)


def check_ext(posets, nmax, rep):
    for n in range(2, nmax + 1):
        agree = 0
        wit_bad = wit_tot = 0
        for rel in posets[n]:
            comps = components(rel, n)
            conn = len(comps) == 1
            nonzero_at = []
            for p in PRIMES:
                z = element_of_order(n, p)
                nz = False
                for k in range(1, len(comps)):
                    for cs in itertools.combinations(comps, k):
                        S = frozenset().union(*cs)
                        T = frozenset(range(n)) - S
                        if len(T) < 2 and len(S) >= 2:
                            S, T = T, S
                        rS = frozenset((a, b) for a, b in rel if a in S)
                        rT = frozenset((a, b) for a, b in rel if a in T)
                        for s in linear_extensions_on(rS, sorted(S)):
                            for t in linear_extensions_on(rT, sorted(T)):
                                y = {}
                                for zz in shuffle(s, t):
                                    for u, c in we_zeta(zz, z, p).items():
                                        add(y, u, c, p)
                                if any(y.values()):
                                    nz = True
                                if len(t) >= 2 and p == PRIMES[0]:
                                    u = (t[0],) + s + t[1:]
                                    wit_tot += 1
                                    # n * coefficient must be exactly 1
                                    wit_bad += y.get(u, 0) != 1
                nonzero_at.append(nz)
            expect_zero = conn or n <= 2
            agree += (not any(nonzero_at)) == expect_zero and \
                nonzero_at[0] == nonzero_at[1]
        N = len(posets[n])
        rep.line("ext", f"n={n}: R_P e_zeta = 0 <=> (connected or n<=2): "
                 f"{agree}/{N}; witness coeff = 1/n: "
                 f"{wit_tot - wit_bad}/{wit_tot}",
                 agree == N and wit_bad == 0)


def linear_extensions_on(rel, letters):
    m = len(letters)
    f = {x: i for i, x in enumerate(letters)}
    r = frozenset((f[a], f[b]) for a, b in rel)
    return [tuple(letters[i] for i in w) for w in linear_extensions(r, m)]


def check_prc(posets, nmax, rep):
    """(i) uniform y -> y mod Sh vs M_P;  (ii) Theta vs extension to C_w."""
    p = PRIMES[0]
    for n in range(3, nmax + 1):
        z = element_of_order(n, p)
        uniform_ok = 0
        nat_fail_P = 0
        ndisc = 0
        chains_uniform_fail = True
        for rel in posets[n]:
            comps = components(rel, n)
            lin = linear_extensions(rel, n)
            ls = set(lin)
            M = [comb_coords({w: 1}, n, p) for w in lin]
            rM = rank(M, p)
            reps = classes(lin, comps)
            Lq = [comb_coords(we_zeta(w, z, p), n, p) for w in reps]
            same = rank(M + Lq, p) == rM == rank(Lq, p)
            uniform_ok += same
            if len(rel) == n * (n - 1) // 2 and same:
                chains_uniform_fail = False
            if len(comps) > 1:
                ndisc += 1
                # Theta extension-natural along P -> C_w would need
                # pr_P(w e_zeta) - pr_{C_w}(w e_zeta) = pr_P(w e) - w/n in Sh
                fails = 0
                for w in lin:
                    d = truncate(we_zeta(w, z, p), ls)
                    add(d, w, -1, p)
                    fails += not in_sh(d, n, p)
                nat_fail_P += fails > 0
        N = len(posets[n])
        rep.line("prc", f"n={n}: uniform map y -> y mod Sh carries L_P onto "
                 f"M_P for {uniform_ok}/{N} posets (chain: no); Theta not "
                 f"natural along some P -> C_w for {nat_fail_P}/{ndisc} "
                 f"disconnected P", chains_uniform_fail
                 and nat_fail_P == ndisc)


def check_lie(nmax, rep):
    for n in range(2, nmax + 1):
        good = True
        for p in PRIMES:
            for z in primitive_roots(n, p):
                allw = list(itertools.permutations(range(n)))
                rows = []
                for cb in combs(n):
                    y = {}
                    for w, c in cb.items():
                        for u, d in we_zeta(w, z, p).items():
                            add(y, u, c * d, p)
                    rows.append([y.get(u, 0) for u in allw])
                f = 1
                for i in range(2, n):
                    f *= i
                good &= rank(rows, p) == f
        rep.line("lie", f"n={n}: rank Lie_n e_zeta = (n-1)! for every "
                 f"primitive zeta, 2 primes", good)


def first_block_contains(w, comps, C):
    for k in cuts(w, comps)[1:] + [len(w)]:
        return C <= set(w[:k])


def check_sum(posets, nmax, rep):
    """phi_Sigma = sum_i phi_i : M_P -> L_P invertible (Conj. 3.3)."""
    p = PRIMES[0]
    for n in range(2, nmax + 1):
        z = element_of_order(n, p)
        ok = tot = 0
        for rel in posets[n]:
            comps = components(rel, n)
            if len(comps) < 2:
                continue
            tot += 1
            lin = linear_extensions(rel, n)
            reps = classes(lin, comps)
            # L-coordinates: class rep r; b = r gamma^k -> b e = zeta^k r e
            where = {}
            for r in reps:
                for k in cuts(r, comps):
                    where[rot(r, k)] = (r, k)
            ridx = {r: i for i, r in enumerate(reps)}
            Bs = [[w for w in lin if first_block_contains(w, comps, C)]
                  for C in comps]
            # basis of M_P: B_0; express each element of B_0 in each B_i
            coords = {w: comb_coords({w: 1}, n, p) for w in lin}
            e = len(reps)
            total = [[0] * e for _ in range(e)]
            for B in Bs:
                assert len(B) == e
                # solve x = sum_b c_b b (mod Sh) for x in B_0
                for row_i, x in enumerate(Bs[0]):
                    c = solve([coords[b] for b in B], coords[x], p)
                    for b, cb in zip(B, c):
                        r, k = where[b]
                        total[row_i][ridx[r]] = (total[row_i][ridx[r]] +
                                                 cb * pow(z, k, p)) % p
            ok += rank(total, p) == e
        rep.line("sum", f"n={n}: phi_Sigma invertible for {ok}/{tot} "
                 f"disconnected posets", ok == tot)


def solve(cols, target, p):
    """Find c with sum_j c_j cols[j] = target (vectors mod p)."""
    m, k = len(target), len(cols)
    A = [[cols[j][i] for j in range(k)] + [target[i]] for i in range(m)]
    piv_cols, r = [], 0
    for c in range(k):
        piv = next((i for i in range(r, m) if A[i][c] % p), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        piv_cols.append(c)
        r += 1
    assert all(A[i][k] % p == 0 for i in range(r, m)), "inconsistent"
    sol = [0] * k
    for i, c in enumerate(piv_cols):
        sol[c] = A[i][k]
    return sol


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--nsh", type=int, default=5)
    ap.add_argument("--ncon", type=int, default=5)
    ap.add_argument("--nsum", type=int, default=5)
    ap.add_argument("--nrand", type=int, default=3)
    ap.add_argument("--seed", type=int, default=20261030)
    a = ap.parse_args(argv)
    rng = random.Random(a.seed)
    rep = Report()
    print(f"primes {PRIMES}, seed {a.seed}")
    posets = enumerate_posets(a.nmax)
    check_enum(posets, a.nmax, rep)
    check_sh(a.nsh, rep)
    check_cut(posets, a.nmax, rep)
    check_psi0(posets, min(a.nmax, 5), rep, rng)
    check_contraction(posets, min(a.nmax, a.ncon), rep, rng)
    check_contraction(posets, min(a.nmax, 4), rep, rng, control=True)
    check_psi(posets, a.nmax, rep, rng, a.nrand)
    check_controls(posets, a.nmax, rep)
    check_equi(posets, min(a.nmax, 5), rep, rng)
    check_ext(posets, a.nmax, rep)
    check_prc(posets, a.nmax, rep)
    check_lie(a.nmax, rep)
    check_sum(posets, min(a.nmax, a.nsum), rep)
    print("ALL CHECKS PASSED" if rep.ok else "SOME CHECKS FAILED")
    return 0 if rep.ok else 1


if __name__ == "__main__":
    sys.exit(main())
