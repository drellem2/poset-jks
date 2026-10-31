"""Checks behind notes/prior_art_per_cone_vanishing.md.

Plain Python 3, exact arithmetic, no imports from other scripts.

(BW) Theorem Cr as a Bjorner-Walker split.  For the braid arrangement in
     R^n_0 and g = eps * w (w in S_n, eps = +-1), with M = L(A)^g, U = Fix g
     and Z* = {X in M : X cap U = 0, X + U in no hyperplane}:
       - Z* is convex in M;
       - mu(M) = mu_{M \\ Z*}(0, 1) + sum_{X <= Z in Z*} mu_M(0, X) mu_M(Z, 1)
         (the Bjorner-Walker form of Crapo's formula for a convex subset);
       - mu_{M \\ Z*}(0, 1) = 0.
     Checked for every g in +-S_n, 3 <= n <= 6, with U != 0 and R^d not in Z*.
     Control: removing one element of Z* from the convex set must break the
     third statement on some pair.

(CL) The converse of Crapo's corollary fails for general finite lattices:
     an exhaustive search for the smallest complemented lattice with
     mu(0, 1) = 0.  Lattices are enumerated as labelled posets on the k
     middle elements (k <= 6), so isomorphic copies repeat.

Exit status 0 iff every check passes.
"""

import itertools
import sys
from fractions import Fraction


def set_partitions(s):
    if not s:
        yield []
        return
    first = s[0]
    for p in set_partitions(s[1:]):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def rank(vectors):
    m = [list(map(Fraction, v)) for v in vectors]
    r = 0
    cols = len(m[0]) if m else 0
    for c in range(cols):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def coarser(a, b):
    """X_a subset X_b, i.e. partition a is coarser than b."""
    return all(any(y <= x for x in a) for y in b)


def mobius_from(elems, bot):
    """mu(bot, z) for z in elems, in the order 'coarser = smaller'."""
    mu = {}
    for z in sorted(elems, key=len):
        if not coarser(bot, z):
            continue
        mu[z] = 1 if z == bot else -sum(v for w, v in mu.items() if coarser(w, z) and w != z)
    return mu


def fixed_space(n, perm, eps):
    """A spanning set of U = Fix(g) inside R^n_0, (g x)_{perm(i)} = eps x_i."""
    seen, vecs = set(), []
    for i in range(n):
        if i in seen:
            continue
        cyc, j = [i], perm[i]
        while j != i:
            cyc.append(j)
            j = perm[j]
        seen |= set(cyc)
        if eps ** len(cyc) == 1:
            v = [0] * n
            for k, c in enumerate(cyc):
                v[c] = eps ** k
            vecs.append(v)
    sums = [sum(v) for v in vecs]
    piv = next((k for k in range(len(vecs)) if sums[k] != 0), None)
    if piv is None:
        return vecs
    return [[Fraction(a) - Fraction(sums[k], sums[piv]) * b for a, b in zip(v, vecs[piv])]
            for k, v in enumerate(vecs) if k != piv]


def check_bw(n, control=False):
    pts = list(range(n))
    allp = [frozenset(frozenset(b) for b in p) for p in set_partitions(pts)]
    bot = frozenset([frozenset(pts)])
    top = frozenset(frozenset([x]) for x in pts)
    tested = bad = nonempty = nonzero = 0
    for perm in itertools.permutations(pts):
        for eps in (1, -1):
            U = fixed_space(n, perm, eps)
            dU = rank(U) if U else 0
            if dU == 0:
                continue
            M = [p for p in allp
                 if frozenset(frozenset(perm[x] for x in b) for b in p) == p]

            def in_z(p):
                vs = [[Fraction(int(x in b)) - Fraction(len(b), n) for x in pts] for b in p]
                if rank(vs + U) != len(p) - 1 + dU:
                    return False
                return not any(all(u[i] == u[j] for u in U)
                               for b in p for i, j in itertools.combinations(sorted(b), 2))

            Z = [p for p in M if in_z(p)]
            if top in Z:
                continue
            tested += 1
            nonempty += bool(Z)
            convex = all(in_z(y) for x in Z for z in Z if coarser(x, z)
                         for y in M if coarser(x, y) and coarser(y, z))
            mu = mobius_from(M, bot)
            nonzero += mu[top] != 0
            K = Z[:-1] if control else Z
            rest = mobius_from([p for p in M if p not in K], bot)
            split = sum(mu[x] * mobius_from([p for p in M if coarser(z, p)], z)[top]
                        for x in Z for z in Z if coarser(x, z))
            if not (convex and rest[top] == 0 and mu[top] == split):
                bad += 1
    return tested, nonempty, nonzero, bad


def smallest_complemented_mu_zero(kmax=6):
    for k in range(1, kmax + 1):
        pairs = [(i, j) for i in range(k) for j in range(i + 1, k)]
        hits = []
        for mask in range(1 << len(pairs)):
            R = {p for b, p in enumerate(pairs) if mask >> b & 1}
            if any((i, j) in R and (j, l) in R and (i, l) not in R
                   for i in range(k) for j in range(k) for l in range(k)):
                continue
            n, B, T = k + 2, k, k + 1

            def le(x, y):
                return x == y or x == B or y == T or (x, y) in R

            def bound(x, y, up):
                c = [z for z in range(n) if (le(x, z) and le(y, z) if up else le(z, x) and le(z, y))]
                m = [z for z in c if all((le(z, w) if up else le(w, z)) for w in c)]
                return m[0] if m else None

            J = {(x, y): bound(x, y, True) for x in range(n) for y in range(n)}
            Mt = {(x, y): bound(x, y, False) for x in range(n) for y in range(n)}
            if None in J.values() or None in Mt.values():
                continue
            if not all(any(J[x, y] == T and Mt[x, y] == B for y in range(n)) for x in range(n)):
                continue
            mu = {B: 1}
            for z in list(range(k)) + [T]:
                mu[z] = -sum(v for w, v in mu.items() if le(w, z) and w != z)
            if mu[T] == 0:
                hits.append(sorted(R))
        if hits:
            return k + 2, len(hits), hits[0]
    return None


def main():
    ok = True
    for n in (3, 4, 5, 6):
        t, ne, nz, bad = check_bw(n)
        print(f"BW n={n}: pairs {t} (Z* nonempty {ne}, mu(M) != 0 {nz}), failures {bad}")
        ok &= bad == 0
    for n in (4, 5):
        t, _, _, bad = check_bw(n, control=True)
        print(f"BW control n={n}: shrink Z* by one element -> failures {bad} (must be > 0)")
        ok &= bad > 0
    res = smallest_complemented_mu_zero()
    print(f"CL: smallest complemented lattice with mu = 0: {res[0]} elements, "
          f"{res[1]} labelled copies, e.g. middle relations {res[2]}" if res else "CL: none found")
    ok &= res is not None and res[0] == 8
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
