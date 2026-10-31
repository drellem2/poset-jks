"""Independent audit of notes/per_cone_vanishing.md.

Self-contained: imports nothing from the other scripts of compute/.

Checks
  [PAL]   Lemma Pal on every anti-automorphism of every poset with n <= 7,
          by an exhaustive search for palindromic linear extensions (and, for
          n <= 6, by listing all linear extensions).
  [TA]    Theorem TA, its sign rule and the closed formula (3.3)-(3.5),
          against chi_{C_P}(-tau) computed from the faces of C_P
          (ordered set partitions compatible with P), with det(-tau) taken
          as a matrix determinant on R^n_0.  All posets 3 <= n <= 6, all
          anti-automorphisms; n = 7 all anti-automorphisms; random
          tau-invariant posets with n = 8, 9.
  [E]     Lemma E (i)-(iii) by brute force on small unit systems.
  [CO]    The element a of sec. 3.6 is uncomplemented in Lambda(V)^g, on every
          pair where (TA4) fails; Lambda(V) is join-closed but not
          intersection-closed.
  [COR]   Cor. 3.5: (a) on all labelled posets n <= 5; (c) via Formula Z
          index sets Z*(C_P, -tau) and mu_{L(A)^g}(0, X).
  [M]     Lemma M, Theorem Cr, Crapo's theorem and "Z* = complements of U"
          on every symmetry of A_2, A_3, B_2, B_3, D_4, generic 4 planes in
          R^3, generic 5 hyperplanes in R^4, B_3 minus a plane, A_3 minus a
          plane.  m_X(all) is computed from its definition,
          (-1)^{dim U} mu of the intersection lattice of {H cap U : H >= X}.

Usage:  python3 audit_per_cone_vanishing.py [--quick]
"""

import itertools
import math
import random
import sys
from fractions import Fraction as Fr
from functools import lru_cache

# ---------------------------------------------------------------------------
# generic helpers

def mobius_numbers(n):
    if n == 1:
        return 1
    res, k, x = 1, 2, n
    while k * k <= x:
        if x % k == 0:
            x //= k
            if x % k == 0:
                return 0
            res = -res
        k += 1
    if x > 1:
        res = -res
    return res


def mu_bottom_top(elems, leq, bottom, top):
    """mu(bottom, top) in the finite poset elems with order leq."""
    elems = [e for e in elems if leq(bottom, e) and leq(e, top)]
    mu = {}
    # process in an order compatible with leq: sort by number of elements below
    below = {e: [f for f in elems if f != e and leq(f, e)] for e in elems}
    for e in sorted(elems, key=lambda e: len(below[e])):
        mu[e] = 1 if e == bottom else -sum(mu[f] for f in below[e])
    return mu[top]


def mu_from(elems, leq, x):
    """dict y -> mu(x, y) for y >= x."""
    up = [e for e in elems if leq(x, e)]
    below = {e: [f for f in up if f != e and leq(f, e)] for e in up}
    mu = {}
    for e in sorted(up, key=lambda e: len(below[e])):
        mu[e] = 1 if e == x else -sum(mu[f] for f in below[e])
    return mu


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def mu_pi_top(nblocks):
    """mu_Pi(pi, 1hat) for a partition with nblocks blocks."""
    return (-1) ** (nblocks - 1) * math.factorial(nblocks - 1)


def det(mat):
    m = [[Fr(x) for x in row] for row in mat]
    n, d = len(m), Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for r in range(c + 1, n):
            f = m[r][c] / m[c][c]
            if f:
                for k in range(c, n):
                    m[r][k] -= f * m[c][k]
    return d


def rank(rows):
    m = [[Fr(x) for x in r] for r in rows]
    if not m:
        return 0
    rk, ncol = 0, len(m[0])
    for c in range(ncol):
        p = next((r for r in range(rk, len(m)) if m[r][c] != 0), None)
        if p is None:
            continue
        m[rk], m[p] = m[p], m[rk]
        for r in range(len(m)):
            if r != rk and m[r][c] != 0:
                f = m[r][c] / m[rk][c]
                for k in range(c, ncol):
                    m[r][k] -= f * m[rk][k]
        rk += 1
    return rk


def nullspace(rows, ncol):
    """basis of {x : r.x = 0 for r in rows}."""
    m = [[Fr(x) for x in r] for r in rows]
    piv, rk = [], 0
    for c in range(ncol):
        p = next((r for r in range(rk, len(m)) if m[r][c] != 0), None)
        if p is None:
            continue
        m[rk], m[p] = m[p], m[rk]
        pv = m[rk][c]
        m[rk] = [x / pv for x in m[rk]]
        for r in range(len(m)):
            if r != rk and m[r][c] != 0:
                f = m[r][c]
                m[r] = [a - f * b for a, b in zip(m[r], m[rk])]
        piv.append(c)
        rk += 1
    free = [c for c in range(ncol) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * ncol
        v[f] = Fr(1)
        for i, c in enumerate(piv):
            v[c] = -m[i][f]
        basis.append(v)
    return basis


def matinv(mat):
    n = len(mat)
    m = [[Fr(x) for x in row] + [Fr(int(i == j)) for j in range(n)]
         for i, row in enumerate(mat)]
    for c in range(n):
        p = next(r for r in range(c, n) if m[r][c] != 0)
        m[c], m[p] = m[p], m[c]
        pv = m[c][c]
        m[c] = [x / pv for x in m[c]]
        for r in range(n):
            if r != c and m[r][c] != 0:
                f = m[r][c]
                m[r] = [a - f * b for a, b in zip(m[r], m[c])]
    return [row[n:] for row in m]


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


# ---------------------------------------------------------------------------
# posets on {0..n-1}: lt[i] = bitmask of j with i < j  (transitively closed)

class Poset:
    def __init__(self, n, rel):
        """rel: iterable of pairs (i, j) meaning i < j; closed transitively."""
        self.n = n
        up = [0] * n
        for i, j in rel:
            up[i] |= 1 << j
        changed = True
        while changed:
            changed = False
            for i in range(n):
                new = up[i]
                for j in range(n):
                    if up[i] >> j & 1:
                        new |= up[j]
                if new != up[i]:
                    up[i] = new
                    changed = True
        if any(up[i] >> i & 1 for i in range(n)):
            raise ValueError("cyclic relation")
        self.up = up
        self.down = [sum(1 << i for i in range(n) if up[i] >> j & 1)
                     for j in range(n)]

    def lt(self, i, j):
        return bool(self.up[i] >> j & 1)

    def relations(self):
        return [(i, j) for i in range(self.n) for j in range(self.n)
                if self.lt(i, j)]

    def comparable(self, i, j):
        return self.lt(i, j) or self.lt(j, i)

    def components(self):
        n, seen, comps = self.n, set(), []
        for s in range(n):
            if s in seen:
                continue
            stack, comp = [s], set()
            while stack:
                x = stack.pop()
                if x in comp:
                    continue
                comp.add(x)
                stack += [y for y in range(n) if self.comparable(x, y)]
            seen |= comp
            comps.append(frozenset(comp))
        return comps

    def restrict(self, sub):
        sub = sorted(sub)
        idx = {x: k for k, x in enumerate(sub)}
        return Poset(len(sub), [(idx[i], idx[j]) for i in sub for j in sub
                                if self.lt(i, j)]), sub


def is_anti(P, t):
    return all(P.lt(t[j], t[i]) == P.lt(i, j)
               for i in range(P.n) for j in range(P.n))


def anti_automorphisms(P):
    """all bijections t with i < j  <=>  t(j) < t(i)."""
    n = P.n
    dn = [bin(P.down[i]).count("1") for i in range(n)]
    upc = [bin(P.up[i]).count("1") for i in range(n)]
    out, t, used = [], [None] * n, [False] * n

    def rec(i):
        if i == n:
            out.append(tuple(t))
            return
        for y in range(n):
            if used[y] or dn[i] != upc[y] or upc[i] != dn[y]:
                continue
            ok = True
            for j in range(i):
                if P.lt(j, i) != P.lt(y, t[j]) or P.lt(i, j) != P.lt(t[j], y):
                    ok = False
                    break
            if ok:
                t[i], used[y] = y, True
                rec(i + 1)
                used[y] = False
        t[i] = None

    rec(0)
    return out


def canonical(P):
    """canonical form of P up to isomorphism (cell refinement + brute force)."""
    n = P.n
    col = [(bin(P.down[i]).count("1"), bin(P.up[i]).count("1")) for i in range(n)]
    for _ in range(n):
        new = [(col[i],
                tuple(sorted(col[j] for j in range(n) if P.lt(j, i))),
                tuple(sorted(col[j] for j in range(n) if P.lt(i, j))))
               for i in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    keys = sorted(set(col))
    cells = [[i for i in range(n) if col[i] == k] for k in keys]
    best = None
    for perms in itertools.product(*[itertools.permutations(c) for c in cells]):
        order = [x for p in perms for x in p]
        pos = {x: k for k, x in enumerate(order)}
        code = tuple(sorted((pos[i], pos[j]) for i, j in P.relations()))
        if best is None or code < best:
            best = code
    return (n, best)


def all_posets(nmax):
    """unlabelled posets with n = 0..nmax, as Poset objects (one per class)."""
    levels = {0: [Poset(0, [])]}
    for n in range(1, nmax + 1):
        seen, out = set(), []
        for Q in levels[n - 1]:
            m = n - 1
            # order ideals of Q = down-closed subsets
            for mask in range(1 << m):
                if any(mask >> i & 1 and (Q.down[i] & ~mask) for i in range(m)):
                    continue
                rel = Q.relations() + [(i, m) for i in range(m) if mask >> i & 1]
                P = Poset(n, rel)
                c = canonical(P)
                if c not in seen:
                    seen.add(c)
                    out.append(P)
        levels[n] = out
    return levels


def all_labelled_posets(n, levels):
    """every labelled poset on {0..n-1}: all relabellings of the classes."""
    seen, out = set(), []
    for Q in levels[n]:
        for perm in itertools.permutations(range(n)):
            P = Poset(n, [(perm[i], perm[j]) for i, j in Q.relations()])
            key = tuple(P.up)
            if key not in seen:
                seen.add(key)
                out.append(P)
    return out


# ---------------------------------------------------------------------------
# palindromic linear extensions

def pal_count(P, t, elems=None):
    """number of linear extensions w of P|elems with t(w_i) = w_{n+1-i}.
    Exhaustive: w_1 runs over all minimal elements of what is left."""
    if elems is None:
        elems = range(P.n)
    full = sum(1 << x for x in elems)

    @lru_cache(maxsize=None)
    def cnt(R):
        if R == 0:
            return 1
        if R & (R - 1) == 0:
            x = R.bit_length() - 1
            return 1 if t[x] == x else 0
        tot = 0
        for x in range(P.n):
            if not R >> x & 1 or P.down[x] & R:
                continue
            y = t[x]
            # both t(w_1) = w_n and t(w_n) = w_1 are required
            if y == x or t[y] != x or not R >> y & 1 or P.up[y] & R:
                continue
            tot += cnt(R & ~(1 << x) & ~(1 << y))
        return tot

    return cnt(full)


def linear_extensions(P, elems=None):
    elems = list(range(P.n)) if elems is None else list(elems)
    if not elems:
        yield []
        return
    S = set(elems)
    for x in elems:
        if not any(P.lt(y, x) for y in S if y != x):
            for w in linear_extensions(P, [e for e in elems if e != x]):
                yield [x] + w


def pal_brute(P, t):
    n = P.n
    return sum(1 for w in linear_extensions(P)
               if all(t[w[i]] == w[n - 1 - i] for i in range(n)))


def pal_predicted(t):
    n = len(t)
    inv = all(t[t[i]] == i for i in range(n))
    return inv and sum(t[i] == i for i in range(n)) <= 1


def check_pal(levels, brute_upto):
    stats = {"pairs": 0, "exists": 0, "involution_not_pal": 0, "non_inv": 0}
    for n, posets in levels.items():
        for P in posets:
            for t in anti_automorphisms(P):
                stats["pairs"] += 1
                c = pal_count(P, t)
                if n <= brute_upto:
                    assert c == pal_brute(P, t), (P.relations(), t)
                pred = pal_predicted(t)
                assert (c > 0) == pred, ("Lemma Pal fails", n, P.relations(), t, c)
                stats["exists"] += c > 0
                if not all(t[t[i]] == i for i in range(n)):
                    stats["non_inv"] += 1
                elif not pred:
                    stats["involution_not_pal"] += 1
    return stats


# ---------------------------------------------------------------------------
# type A: chi_{C_P}(-tau) from the faces of C_P

def ordered_set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    for p in set_partitions(items):
        for perm in itertools.permutations(p):
            yield [frozenset(b) for b in perm]


def faces_of_cone(P):
    """faces of the closed cone |C_P| of the braid arrangement in R^n_0:
    ordered set partitions B_1 < ... < B_k (x constant on blocks,
    increasing) such that i <_P j implies blk(i) <= blk(j)."""
    rel = P.relations()
    for op in ordered_set_partitions(range(P.n)):
        blk = {}
        for k, b in enumerate(op):
            for x in b:
                blk[x] = k
        if all(blk[i] <= blk[j] for i, j in rel):
            yield op


def act_face(t, eps, op):
    """g = eps * t: (g x)_{t(i)} = eps x_i.  Image of the face op."""
    img = [frozenset(t[x] for x in b) for b in op]
    return img if eps == 1 else img[::-1]


def det_on_sum_zero(t, eps):
    """det of g = eps * t on R^n_0, basis e_i - e_{n-1}."""
    n = len(t)
    # g(e_i) = eps e_{t(i)}; express g(e_i - e_{n-1}) in the basis
    cols = []
    for i in range(n - 1):
        v = [0] * n
        v[t[i]] += eps
        v[t[n - 1]] -= eps
        # v has sum 0; coordinates in basis b_j = e_j - e_{n-1}: c_j = v_j
        cols.append(v[:n - 1])
    mat = [[cols[j][i] for j in range(n - 1)] for i in range(n - 1)]
    return det(mat)


def partition_leq_flat(p, q):
    """X_p subset X_q  iff  p is coarser than q (every block of q in a block of p)."""
    return all(any(b <= a for a in p) for b in q)


def chi_face_poset(P, t, eps=-1, check_stable=True):
    """(-1)^d det(g) mu(Lambda(V)^g), Lambda(V) = spans of faces of V."""
    n = P.n
    faces = list(faces_of_cone(P))
    if check_stable:
        fs = {tuple(f) for f in faces}
        assert all(tuple(act_face(t, eps, f)) in fs for f in faces), "g V != V"
    lam = {frozenset(f) for f in faces}
    fixed = [p for p in lam if frozenset(frozenset(t[x] for x in b) for b in p) == p]
    bottom = frozenset([frozenset(range(n))])
    top = frozenset(frozenset([i]) for i in range(n))
    mu = mu_bottom_top(fixed, partition_leq_flat, bottom, top)
    return (-1) ** (n - 1) * det_on_sum_zero(t, eps) * mu


def tau_stable_partitions(n, t):
    """all partitions of {0..n-1} stable under the permutation t."""
    out = []

    def rec(unassigned, blocks):
        if not unassigned:
            out.append(frozenset(blocks))
            return
        x = min(unassigned)
        rest = sorted(unassigned - {x})
        for r in range(len(rest) + 1):
            for comb in itertools.combinations(rest, r):
                B = frozenset((x,) + comb)
                orbit, C, ok = [], B, True
                while True:
                    orbit.append(C)
                    C = frozenset(t[y] for y in C)
                    if C == B:
                        break
                    if C & B or not C <= unassigned:
                        ok = False
                        break
                if not ok:
                    continue
                # images must be pairwise disjoint
                if sum(len(c) for c in orbit) != len(frozenset().union(*orbit)):
                    continue
                rec(unassigned - frozenset().union(*orbit), blocks + orbit)

    rec(frozenset(range(n)), [])
    return out


def has_face_with_span(P, p):
    """is there an ordering of the blocks of p compatible with P (a face)?"""
    blocks = list(p)
    idx = {x: k for k, b in enumerate(blocks) for x in b}
    k = len(blocks)
    succ = [set() for _ in range(k)]
    for i, j in P.relations():
        if idx[i] != idx[j]:
            succ[idx[i]].add(idx[j])
    indeg = [0] * k
    for a in range(k):
        for b in succ[a]:
            indeg[b] += 1
    queue = [a for a in range(k) if indeg[a] == 0]
    done = 0
    while queue:
        a = queue.pop()
        done += 1
        for b in succ[a]:
            indeg[b] -= 1
            if indeg[b] == 0:
                queue.append(b)
    return done == k


def chi_stable_spans(P, t, eps=-1):
    """the same chi, for larger n: Lambda(V)^g = g-stable flats that are spans
    of faces; a face with span X_p is an ordering of the blocks of p."""
    n = P.n
    fixed = [p for p in tau_stable_partitions(n, t) if has_face_with_span(P, p)]
    bottom = frozenset([frozenset(range(n))])
    top = frozenset(frozenset([i]) for i in range(n))
    mu = mu_bottom_top(fixed, partition_leq_flat, bottom, top)
    return (-1) ** (n - 1) * det_on_sum_zero(t, eps) * mu


# ---------------------------------------------------------------------------
# the closed formula of sec. 3 and the conditions TA1-TA4

def cycles(t):
    n, seen, out = len(t), set(), []
    for i in range(n):
        if i in seen:
            continue
        c, x = [], i
        while x not in c:
            c.append(x)
            x = t[x]
        seen |= set(c)
        out.append(c)
    return out


def tpow(t, k):
    n = len(t)
    out = list(range(n))
    for _ in range(k):
        out = [t[x] for x in out]
    return tuple(out)


def ta1_m(t):
    """m if the cycle lengths lie in {m, 2m}, m odd squarefree; else None."""
    lens = {len(c) for c in cycles(t)}
    odd = {l for l in lens if l % 2}
    if len(odd) > 1:
        return None
    m = odd.pop() if odd else min(lens) // 2
    if m % 2 == 0 or mobius_numbers(m) == 0 or not lens <= {m, 2 * m}:
        return None
    return m


def ta_conditions(P, t):
    m = ta1_m(t)
    comps = P.components()
    res = {"TA1": m is not None}
    if m is None:
        return res, m
    odd_pts = {x for c in cycles(t) if len(c) % 2 for x in c}

    def img(K, k):
        return frozenset(tpow(t, k)[x] for x in K)

    def orbit_len(K):
        s, C = 1, img(K, 1)
        while C != K:
            C, s = img(C, 1), s + 1
        return s

    res["TA2"] = all(orbit_len(K) in (m, 2 * m) for K in comps)
    res["TA3"] = all(len((K | img(K, m)) & odd_pts) <= 1 for K in comps)
    lens = {len(c) for c in cycles(t)}
    has_odd, has_even = any(l % 2 for l in lens), any(l % 2 == 0 for l in lens)
    isolated = {x for K in comps if len(K) == 1 for x in K}
    res["TA4"] = (not (has_odd and has_even)) or any(
        not set(c) <= isolated for c in cycles(t) if len(c) % 2)
    return res, m


def connected_count(h):
    """c(S) of Lemma E for weights h (tuple), via E(i) (Mobius inversion)."""
    units = list(range(len(h)))
    tot = 0
    for pi in set_partitions(units):
        term = mu_pi_top(len(pi))
        for B in pi:
            term *= math.factorial(sum(h[u] for u in B))
        tot += term
    return tot


def closed_formula(P, t, detail=False):
    """chi_{C_P}(-tau) by (3.3)-(3.5) of the note, computed literally."""
    res, m = ta_conditions(P, t)
    if not res["TA1"] or not res["TA2"]:
        return (0, None) if detail else 0
    n = P.n
    comps = P.components()
    tm = tpow(t, m)
    odd_pts = {x for c in cycles(t) if len(c) % 2 for x in c}
    blocks = {frozenset(K | frozenset(tm[x] for x in K)) for K in comps}
    # units: tau-orbits of rho_0 blocks
    units, seen = [], set()
    for b in sorted(blocks, key=sorted):
        if b in seen:
            continue
        orb, C = [], b
        while C not in orb:
            orb.append(C)
            C = frozenset(t[x] for x in C)
        seen |= set(orb)
        assert len(orb) == m
        units.append(orb)
    N = len(units)
    h = [len(u[0]) // 2 for u in units]
    pal = [pal_count(P, tm, u[0]) for u in units]
    marked = [bool(u[0] & odd_pts) for u in units]
    # Phi = sum_pi mu(pi,1) prod Ftilde(B), Ftilde(B) = H(B)! [|B cap F| <= 1]
    Phi = 0
    for pi in set_partitions(range(N)):
        term = mu_pi_top(len(pi))
        for B in pi:
            if sum(marked[u] for u in B) > 1:
                term = 0
                break
            term *= math.factorial(sum(h[u] for u in B))
        Phi += term
    Sm = Fr(mobius_numbers(m) * m ** (N - 1) * Phi)
    for u in range(N):
        Sm *= Fr(pal[u], math.factorial(h[u]))
    S2m = Fr(0)
    orbit2m = all(
        frozenset(tm[x] for x in K) != K for K in comps)
    if not odd_pts and orbit2m:
        c = connected_count(tuple(h))
        prod = Fr(1)
        for u in units:
            b = u[0]
            K = next(K for K in comps if K <= b)
            Q, sub = P.restrict(K)
            prod *= Fr(sum(1 for _ in linear_extensions(Q)), math.factorial(len(K)))
        S2m = -mobius_numbers(m) * (2 * m) ** (N - 1) * c * prod
    val = Sm + S2m
    assert val.denominator == 1
    if detail:
        return int(val), {"m": m, "N": N, "h": h, "pal": pal, "marked": marked,
                          "Phi": Phi, "S2m": S2m, "case":
                          "I" if odd_pts else ("IIb" if orbit2m else "IIa")}
    return int(val)


def phi_closed_E3(h, marked):
    """right side of Lemma E(iii)."""
    F = [u for u in range(len(h)) if marked[u]]
    T = [u for u in range(len(h)) if not marked[u]]
    k = len(F)
    if k == 0:
        return connected_count(tuple(h))
    tot = 0
    for assign in itertools.product(range(k), repeat=len(T)):
        term = 1
        for a, f in enumerate(F):
            group = [f] + [T[i] for i in range(len(T)) if assign[i] == a]
            term *= connected_count(tuple(h[u] for u in group))
        tot += term
    return (-1) ** (k - 1) * math.factorial(k - 1) * tot


def predicted_sign(t, m):
    k = sum(1 for c in cycles(t) if len(c) % 2)
    return mobius_numbers(m) * ((-1) ** (k - 1) if k >= 1 else 1)


def check_one_pair(P, t, chi):
    """compare chi (from faces) with Theorem TA, closed formula, sign rule."""
    res, m = ta_conditions(P, t)
    allok = all(res.get(k, False) for k in ("TA1", "TA2", "TA3", "TA4"))
    cf, det_ = closed_formula(P, t, detail=True)
    assert cf == chi, ("closed formula", P.relations(), t, cf, chi)
    assert (chi != 0) == allok, ("Theorem TA", P.relations(), t, res, chi)
    if chi != 0:
        assert (chi > 0) == (predicted_sign(t, m) > 0), ("sign", P.relations(), t)
    if det_ is not None:
        e3 = phi_closed_E3(det_["h"], det_["marked"])
        assert e3 == det_["Phi"], ("Lemma E(iii)", det_)
    return res, det_


def check_ta_exhaustive(levels, nmin, nmax, face_upto):
    stats = {}
    for n in range(nmin, nmax + 1):
        st = {"pairs": 0, "nonzero": 0, "cases": set(), "fail": {},
              "mixed_odd_even": 0, "isolated_fixed": 0}
        for P in levels[n]:
            for t in anti_automorphisms(P):
                st["pairs"] += 1
                if n <= face_upto:
                    chi = chi_face_poset(P, t)
                    chi2 = chi_stable_spans(P, t)
                    assert chi == chi2, ("two face models", P.relations(), t)
                else:
                    chi = chi_stable_spans(P, t)
                res, det_ = check_one_pair(P, t, chi)
                st["nonzero"] += chi != 0
                if det_:
                    st["cases"].add(det_["case"])
                first_fail = next((k for k in ("TA1", "TA2", "TA3", "TA4")
                                   if not res.get(k, False)), None)
                if first_fail:
                    st["fail"][first_fail] = st["fail"].get(first_fail, 0) + 1
                lens = {len(c) for c in cycles(t)}
                if any(l % 2 for l in lens) and any(l % 2 == 0 for l in lens):
                    st["mixed_odd_even"] += 1
                iso = {x for K in P.components() if len(K) == 1 for x in K}
                if any(t[x] == x for x in iso):
                    st["isolated_fixed"] += 1
        stats[n] = st
    return stats


def random_invariant_poset(n, t, rng, tries=6):
    """random poset on {0..n-1} for which t is an anti-automorphism."""
    order = len(cycles(t)) and math.lcm(*[len(c) for c in cycles(t)])
    rel = set()
    for _ in range(rng.randint(1, tries)):
        i, j = rng.sample(range(n), 2)
        new = set()
        for k in range(2 * order):
            tk = tpow(t, k)
            a, b = tk[i], tk[j]
            new.add((a, b) if k % 2 == 0 else (b, a))
        try:
            P = Poset(n, rel | new)
        except ValueError:
            continue
        rel = set(P.relations())
    P = Poset(n, rel)
    assert is_anti(P, t)
    return P


def perm_of_type(n, lens, rng):
    pts = list(range(n))
    rng.shuffle(pts)
    t = [None] * n
    k = 0
    for l in lens:
        c = pts[k:k + l]
        for a in range(l):
            t[c[a]] = c[(a + 1) % l]
        k += l
    return tuple(t)


def check_ta_random(specs, rng):
    stats = []
    for n, lens, count in specs:
        nz = 0
        for _ in range(count):
            t = perm_of_type(n, lens, rng)
            P = random_invariant_poset(n, t, rng)
            chi = chi_stable_spans(P, t)
            check_one_pair(P, t, chi)
            nz += chi != 0
        stats.append((n, lens, count, nz))
    return stats


# ---------------------------------------------------------------------------
# sec. 3.6: the uncomplemented element, and lattice facts on Lambda(V)

def join_part(p, q, n):
    parent = list(range(n))

    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for blk in list(p) + list(q):
        b = sorted(blk)
        for y in b[1:]:
            parent[f(y)] = f(b[0])
    groups = {}
    for x in range(n):
        groups.setdefault(f(x), set()).add(x)
    return frozenset(frozenset(g) for g in groups.values())


def meet_part(p, q):
    return frozenset(a & b for a in p for b in q if a & b)


def lattice_complements(elems, leq, a, bottom, top):
    """complements of a in a finite lattice given as a list with leq."""
    def meet(x, y):
        lows = [z for z in elems if leq(z, x) and leq(z, y)]
        return next(z for z in lows if all(leq(w, z) for w in lows))

    def join(x, y):
        ups = [z for z in elems if leq(x, z) and leq(y, z)]
        return next(z for z in ups if all(leq(z, w) for w in ups))
    return [x for x in elems if meet(x, a) == bottom and join(x, a) == top]


def check_crapo_element(levels, nmax):
    """for every pair (P, tau) with (TA1)-(TA3) true and (TA4) false: the
    element a (block Q = non-odd points, singletons on odd points) lies in
    Lambda(C_P)^g and has no complement there (computed in the lattice
    itself, with meets and joins found by search)."""
    count = 0
    for n in range(3, nmax + 1):
        for P in levels[n]:
            for t in anti_automorphisms(P):
                res, m = ta_conditions(P, t)
                if not (res["TA1"] and res["TA2"] and res["TA3"]) or res["TA4"]:
                    continue
                fixed = [p for p in tau_stable_partitions(n, t)
                         if has_face_with_span(P, p)]
                odd = {x for c in cycles(t) if len(c) % 2 for x in c}
                Q = frozenset(range(n)) - odd
                a = frozenset([Q] + [frozenset([x]) for x in odd])
                assert a in fixed
                # Lambda order: X_p <= X_q iff p coarser than q
                bottom = frozenset([frozenset(range(n))])
                top = frozenset(frozenset([i]) for i in range(n))
                comp = lattice_complements(fixed, partition_leq_flat, a, bottom, top)
                assert comp == [], (P.relations(), t, comp)
                count += 1
    return count


def check_lambda_lattice(levels, nmax):
    """Lambda(C_P) (as partitions, X_p <= X_q iff p coarser) is closed under
    the flat-closure of sums, X_p v X_q = X_{p meet q} (common refinement);
    report how often it is NOT closed under intersection X_{p join q}."""
    not_int_closed = 0
    total = 0
    example = None
    for n in range(2, nmax + 1):
        for P in levels[n]:
            lam = {frozenset(f) for f in faces_of_cone(P)}
            total += 1
            bad = False
            for p in lam:
                for q in lam:
                    assert meet_part(p, q) in lam
                    if join_part(p, q, n) not in lam:
                        bad = True
                        if example is None:
                            example = (P.relations(), p, q)
            not_int_closed += bad
    return total, not_int_closed, example


# ---------------------------------------------------------------------------
# Cor. 3.5: (a) on labelled posets, (c) via Formula Z index sets

def check_cor35a(levels, nmax):
    keys = {}
    pairs = 0
    for n in range(3, nmax + 1):
        for P in all_labelled_posets(n, levels):
            comps = frozenset(P.components())
            for t in anti_automorphisms(P):
                chi = chi_face_poset(P, t, check_stable=False)
                pairs += 1
                k = (n, comps, t)
                keys.setdefault(k, set()).add(chi != 0)
                sg = keys.setdefault(("sign", n, t), set())
                if chi:
                    sg.add(chi > 0)
    bad = [k for k, v in keys.items() if len(v) > 1]
    return pairs, len([k for k in keys if k[0] != "sign"]), bad


def zstar_nonzero_mu(P, t):
    """does Z*(C_P, -tau) contain an X with mu_{L(A)^g}(0, X) != 0?"""
    n = P.n
    comps = P.components()
    stable = tau_stable_partitions(n, t)
    # U = Fix(-tau) on R^n_0: x_{t(i)} = -x_i, sum x = 0
    rows = [[1] * n]
    for i in range(n):
        r = [0] * n
        r[t[i]] += 1
        r[i] += 1
        rows.append(r)
    Ub = nullspace(rows, n)
    bottom = frozenset([frozenset(range(n))])
    for rho in stable:
        if not all(any(K <= B for B in rho) for K in comps):
            continue  # X_rho not inside L
        Xb = []
        blocks = list(rho)
        for B in blocks[1:]:
            v = [Fr(0)] * n
            for x in B:
                v[x] += Fr(1, len(B))
            for x in blocks[0]:
                v[x] -= Fr(1, len(blocks[0]))
            Xb.append(v)
        if rank(Xb + Ub) != len(Xb) + len(Ub):
            continue  # X cap U != 0
        span = Xb + Ub
        if any(all(v[i] == v[j] for v in span)
               for i in range(n) for j in range(i + 1, n)):
            continue  # X + U in a hyperplane
        coarser = [s for s in stable if partition_leq_flat(s, rho)]
        mu = mu_bottom_top(coarser, partition_leq_flat, bottom, rho)
        if mu != 0:
            return True
    return False


def check_cor35c(levels, nmax):
    """cancellation (chi = 0 and Z* carries a nonzero mu) vs the note's
    description '(TA1)-(TA3) hold and (TA4) fails'."""
    canc = {"TA4 fails": 0, "TA2 fails": 0, "TA3 fails": 0, "TA1 fails": 0}
    ta4_fail_no_mu = 0
    for n in range(3, nmax + 1):
        for P in levels[n]:
            for t in anti_automorphisms(P):
                chi = chi_stable_spans(P, t)
                if chi != 0:
                    continue
                res, m = ta_conditions(P, t)
                first = next(k for k in ("TA1", "TA2", "TA3", "TA4")
                             if not res.get(k, False))
                nz = zstar_nonzero_mu(P, t)
                if nz:
                    canc[first + " fails"] += 1
                elif first == "TA4":
                    ta4_fail_no_mu += 1
    return canc, ta4_fail_no_mu


# ---------------------------------------------------------------------------
# Lemma E by brute force

def connected_brute(h):
    pts = [u for u, hu in enumerate(h) for _ in range(hu)]
    N = len(h)
    tot = 0
    for perm in itertools.permutations(range(len(pts))):
        parent = list(range(N))

        def f(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for i, j in enumerate(perm):
            a, b = f(pts[i]), f(pts[j])
            if a != b:
                parent[a] = b
        tot += len({f(u) for u in range(N)}) == 1
    return tot


def check_lemma_E():
    cnt = 0
    for N in range(1, 4):
        for h in itertools.product(range(0, 3), repeat=N):
            if sum(h) > 6:
                continue
            c = connected_brute(h)
            assert c == connected_count(h), h
            assert (c > 0) == (N == 1 or all(x >= 1 for x in h)), h
            cnt += 1
    for N in range(1, 6):
        for h in itertools.product(range(0, 3), repeat=N):
            for marked in itertools.product([False, True], repeat=N):
                Phi = 0
                for pi in set_partitions(range(N)):
                    term = mu_pi_top(len(pi))
                    for B in pi:
                        if sum(marked[u] for u in B) > 1:
                            term = 0
                            break
                        term *= math.factorial(sum(h[u] for u in B))
                    Phi += term
                assert Phi == phi_closed_E3(h, marked), (h, marked)
                cnt += 1
    return cnt


# ---------------------------------------------------------------------------
# general arrangements: Lemma M, Theorem Cr, Crapo

class Arrangement:
    def __init__(self, name, normals):
        self.name = name
        self.normals = [tuple(Fr(x) for x in v) for v in normals]
        self.d = len(normals[0])
        self.nh = len(normals)
        assert rank(self.normals) == self.d, "not essential"
        self._flats()

    def closure(self, S):
        rows = [self.normals[i] for i in S]
        r = rank(rows)
        return frozenset(i for i in range(self.nh)
                         if rank(rows + [self.normals[i]]) == r)

    def _flats(self):
        top = frozenset()           # R^d: no hyperplane contains it
        flats = {top}
        frontier = [top]
        while frontier:
            new = []
            for S in frontier:
                for i in range(self.nh):
                    if i not in S:
                        T = self.closure(S | {i})
                        if T not in flats:
                            flats.add(T)
                            new.append(T)
            frontier = new
        self.flats = list(flats)
        self.top = top
        self.bottom = frozenset(range(self.nh))

    def basis(self, S):
        return nullspace([self.normals[i] for i in S], self.d)

    @staticmethod
    def leq(X, Y):          # X subset Y as subspaces
        return Y <= X

    def symmetries(self):
        """all N with alpha_i N = +- alpha_{sigma(i)}; returns (G, sigma),
        G = N^{-1} the matrix of g on column vectors."""
        idx = []
        for i in range(self.nh):
            if rank([self.normals[j] for j in idx + [i]]) == len(idx) + 1:
                idx.append(i)
            if len(idx) == self.d:
                break
        B = [list(self.normals[i]) for i in idx]
        Binv = matinv(B)
        lookup = {}
        for j, v in enumerate(self.normals):
            lookup[v] = (j, 1)
            lookup[tuple(-x for x in v)] = (j, -1)
        out = []
        for targets in itertools.permutations(range(self.nh), self.d):
            for signs in itertools.product([1, -1], repeat=self.d):
                T = [[s * x for x in self.normals[j]] for j, s in zip(targets, signs)]
                N = matmul(Binv, T)        # B N = T
                sigma = []
                ok = True
                for v in self.normals:
                    w = tuple(sum(v[k] * N[k][c] for k in range(self.d))
                              for c in range(self.d))
                    if w not in lookup:
                        ok = False
                        break
                    sigma.append(lookup[w][0])
                if ok and len(set(sigma)) == self.nh and det(N) != 0:
                    out.append((matinv(N), tuple(sigma)))
        return out


def flat_image(sigma, S):
    return frozenset(sigma[i] for i in S)


def check_lemma_M(arr):
    stats = {"elements": 0, "terms": 0, "U_flat": 0, "crapo_checks": 0}
    syms = arr.symmetries()
    d = arr.d
    for G, sigma in syms:
        stats["elements"] += 1
        M = [S for S in arr.flats if flat_image(sigma, S) == S]
        leq = Arrangement.leq
        rowsU = [[G[i][j] - (1 if i == j else 0) for j in range(d)] for i in range(d)]
        Ub = nullspace(rowsU, d)
        dimU = len(Ub)

        def meets_U_zero(S):
            Xb = arr.basis(S)
            return rank(Xb + Ub) == len(Xb) + dimU if (Xb or Ub) else True

        def sum_in_hyperplane(S):
            span = arr.basis(S) + Ub
            return any(all(sum(a * b for a, b in zip(arr.normals[h], v)) == 0
                           for v in span) for h in range(arr.nh))
        Zset = [S for S in M if meets_U_zero(S)]
        Zstar = [S for S in Zset if not sum_in_hyperplane(S)]
        mu0 = mu_from(M, leq, arr.bottom)
        mutop = {Z: mu_bottom_top(M, leq, Z, arr.top) for Z in M}
        chi_all = (-1) ** d * det(G) * mu0[arr.top]
        # m_X(all) from its definition: (-1)^{dim U} mu(L(A_X|_U))
        mX = {}
        for X in Zstar:
            if dimU == 0:
                mX[X] = 1
                continue
            forms = [tuple(sum(arr.normals[h][k] * u[k] for k in range(d))
                           for u in Ub) for h in sorted(X)]
            sub = Arrangement.__new__(Arrangement)
            sub.normals, sub.d, sub.nh = forms, dimU, len(forms)
            assert rank(forms) == dimU
            sub._flats()
            m = (-1) ** dimU * mu_bottom_top(sub.flats, Arrangement.leq,
                                              sub.bottom, sub.top)
            assert m >= 1
            mX[X] = m
            # Lemma M
            rhs = (-1) ** dimU * sum(mutop[Z] for Z in Zset if leq(X, Z))
            assert m == rhs, (arr.name, "Lemma M", X, m, rhs)
            stats["terms"] += 1
        if dimU == 0:
            for X in Zstar:
                rhs = sum(mutop[Z] for Z in Zset if leq(X, Z))
                assert rhs == 1
                stats["terms"] += 1
        # Formula Z on all chambers, and Theorem Cr
        assert chi_all == sum(mu0[X] * mX[X] for X in Zstar), arr.name
        cr = (-1) ** dimU * sum(mu0[X] * mutop[Z] for X in Zstar for Z in Zstar
                                if leq(X, Z))
        assert chi_all == cr, (arr.name, "Cr")
        # (b): antichain case
        if not any(X != Z and leq(X, Z) for X in Zstar for Z in Zstar):
            for X in Zstar:
                assert mX[X] == (-1) ** dimU * mutop[X]
        # (a): U a flat => Z* = complements of U in M
        Uflat = frozenset(h for h in range(arr.nh)
                          if all(sum(a * b for a, b in zip(arr.normals[h], u)) == 0
                                 for u in Ub))
        if dimU == len(arr.basis(Uflat)):
            stats["U_flat"] += 1
            assert Uflat in M
            comp = [X for X in M if arr.closure(X | Uflat) == arr.bottom
                    and not (X & Uflat)]
            assert sorted(map(sorted, comp)) == sorted(map(sorted, Zstar)), arr.name
            assert (-1) ** d * det(G) == (-1) ** dimU
        # Crapo's theorem in M, for every element a of M
        for a in M:
            comp = [X for X in M if arr.closure(X | a) == arr.bottom and not (X & a)]
            s = sum(mu0[X] * mutop[Z]
                    for X in comp for Z in comp if leq(X, Z))
            assert s == mu0[arr.top], (arr.name, "Crapo")
            stats["crapo_checks"] += 1
    return stats


def arrangements(quick):
    A2 = [(1, 0), (0, 1), (1, 1)]
    A3 = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (0, 1, 1), (1, 1, 1)]
    B2 = [(1, 0), (0, 1), (1, 1), (1, -1)]
    B3 = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, -1, 0), (1, 0, 1),
          (1, 0, -1), (0, 1, 1), (0, 1, -1)]
    gen4 = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1)]
    gen5 = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (1, 1, 1, 1)]
    B3m = [v for v in B3 if v != (0, 0, 1)]
    A3m = [v for v in A3 if v != (1, 1, 1)]
    D4 = [v for i in range(4) for j in range(i + 1, 4) for s in (1, -1)
          for v in [tuple(1 if k == i else (s if k == j else 0) for k in range(4))]]
    out = [("A_2", A2), ("B_2", B2), ("A_3", A3), ("generic 4 in R^3", gen4),
           ("B_3 minus a plane", B3m), ("A_3 minus a plane", A3m)]
    if not quick:
        out += [("B_3", B3), ("generic 5 in R^4", gen5), ("D_4", D4)]
    return out


# ---------------------------------------------------------------------------

def main():
    quick = "--quick" in sys.argv
    ok = True
    pal_n = 6 if quick else 7
    levels = all_posets(pal_n)
    print("unlabelled posets n=0..%d:" % pal_n, [len(levels[n]) for n in range(pal_n + 1)])
    assert [len(levels[n]) for n in range(min(pal_n, 7) + 1)] == \
        [1, 1, 2, 5, 16, 63, 318, 2045][:pal_n + 1]

    st = check_pal(levels, brute_upto=6)
    print("[PAL] Lemma Pal on all anti-automorphisms, n <= %d: %s" % (pal_n, st))

    print("[E] Lemma E (i)-(iii) brute force cases:", check_lemma_E())

    ta_max = 6 if quick else 7
    face_upto = 5 if quick else 6
    st = check_ta_exhaustive(levels, 3, ta_max, face_upto)
    for n, s in st.items():
        print("[TA] n=%d: pairs=%d nonzero=%d cases=%s first failing condition=%s "
              "mixed odd/even=%d isolated fixed point=%d" % (
                  n, s["pairs"], s["nonzero"], sorted(s["cases"]), s["fail"],
                  s["mixed_odd_even"], s["isolated_fixed"]))

    rng = random.Random(20261031)
    specs = [(8, (2, 2, 2, 1, 1), 40), (8, (2, 2, 2, 2), 40), (8, (2, 2, 1, 1, 1, 1), 40),
             (9, (6, 3), 30), (9, (3, 3, 3), 20), (7, (6, 1), 20), (9, (2, 2, 2, 2, 1), 30)]
    if quick:
        specs = [(s[0], s[1], max(3, s[2] // 10)) for s in specs]
    for n, lens, count, nz in check_ta_random(specs, rng):
        print("[TA] random n=%d tau of type %s: %d posets, %d nonzero" % (n, lens, count, nz))

    print("[CO] (TA4)-zeros with the element a uncomplemented in Lambda(V)^g:",
          check_crapo_element(levels, 6 if quick else 7))
    tot, bad, ex = check_lambda_lattice(levels, 5)
    print("[CO] Lambda(C_P), n <= 5: %d posets, all join-closed; %d not closed "
          "under intersection, e.g. P=%s, X_p, X_q with p=%s q=%s" % (
              tot, bad, ex[0], [sorted(b) for b in ex[1]], [sorted(b) for b in ex[2]]))

    pairs, nkeys, bad = check_cor35a(levels, 4 if quick else 5)
    print("[COR] Cor. 3.5(a)/(b) on all labelled posets: %d pairs, %d keys "
          "(comp(P), tau), inconsistent keys: %d" % (pairs, nkeys, len(bad)))
    ok &= not bad
    canc, nomu = check_cor35c(levels, 5 if quick else 6)
    print("[COR] Cor. 3.5(c): cancelling pairs by first failing condition:", canc,
          "; (TA4)-zeros with no nonzero mu on Z*:", nomu)

    for name, normals in arrangements(quick):
        arr = Arrangement(name, normals)
        st = check_lemma_M(arr)
        print("[M] %s: %d flats, %s" % (name, len(arr.flats), st))

    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
