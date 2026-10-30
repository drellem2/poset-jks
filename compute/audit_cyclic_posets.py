#!/usr/bin/env python3
"""Independent audit brute force for notes/cyclic_compatible_posets_bn.md.

Written from scratch; does not import or reuse compute/cyclic_posets.py.
Labels are 1..n as in the note.  A poset is a frozenset of strict relations
(x, y) meaning x <_P y (transitively closed).

    L_c = (c+1, ..., n, 1, ..., c),  c in {0, ..., n-1}
    B_n = posets on [n] with some L_c a linear extension
    C(P) = {c : L_c in Lin(P)}
    e_C(P) = number of rotation classes {w o gamma^j} of words meeting Lin(P)

Usage:
    python3 compute/audit_cyclic_posets.py          # all checks, n <= 6
    python3 compute/audit_cyclic_posets.py --b8     # also a_7, a_8, b_7, b_8
"""
import cmath
import sys
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial, gcd


# ---------------------------------------------------------------- posets
def all_posets(n):
    """All labeled posets on [n]: insert n into a poset on [n-1] with a
    down-set D (order ideal) and an up-set U (filter) such that D < U
    already holds pairwise.  Each poset on [n] arises once (from its
    restriction to [n-1])."""
    if n == 0:
        return [frozenset()]
    out = []
    old = list(range(1, n))
    for P in all_posets(n - 1):
        below = {x: {a for (a, b) in P if b == x} for x in old}
        above = {x: {b for (a, b) in P if a == x} for x in old}
        ideals = [set(S) for r in range(n) for S in combinations(old, r)
                  if all(below[x] <= set(S) for x in S)]
        filters = [set(S) for r in range(n) for S in combinations(old, r)
                   if all(above[x] <= set(S) for x in S)]
        for D in ideals:
            for U in filters:
                if D & U:
                    continue
                if all((d, u) in P for d in D for u in U):
                    out.append(P | {(d, n) for d in D} | {(n, u) for u in U})
    return out


def is_ext(P, word):
    pos = {x: i for i, x in enumerate(word)}
    return all(pos[x] < pos[y] for (x, y) in P)


def L(n, c):
    return tuple(list(range(c + 1, n + 1)) + list(range(1, c + 1)))


def C(P, n):
    return frozenset(c for c in range(n) if is_ext(P, L(n, c)))


def relabel(P, f):
    """i <_{fP} j  iff  f^{-1} i <_P f^{-1} j, f a dict on [n]."""
    return frozenset((f[x], f[y]) for (x, y) in P)


def sigma_pow(n, k):
    return {i: (i - 1 + k) % n + 1 for i in range(1, n + 1)}


def lin_exts(P, n):
    below = {x: {a for (a, b) in P if b == x} for x in range(1, n + 1)}
    out = []

    def rec(placed, word):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(1, n + 1):
            if x not in placed and below[x] <= placed:
                rec(placed | {x}, word + [x])
    rec(frozenset(), [])
    return out


def rot_class(w):
    return min(w[j:] + w[:j] for j in range(len(w)))


def mobius(m):
    res, p = 1, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    return -res if m > 1 else res


def log_coeffs(a, N):
    """n [x^n] log A via power series log: log A = sum (-1)^{k+1} (A-1)^k / k."""
    f = [Fraction(0)] + [Fraction(a[i]) for i in range(1, N + 1)]
    res = [Fraction(0)] * (N + 1)
    powk = [Fraction(1)] + [Fraction(0)] * N
    for k in range(1, N + 1):
        powk = [sum(powk[i] * f[m - i] for i in range(m + 1)) for m in range(N + 1)]
        for m in range(N + 1):
            res[m] += Fraction((-1) ** (k + 1), k) * powk[m]
    return [None] + [m * res[m] for m in range(1, N + 1)]


def irreducible(P, order):
    """P on the set `order` (listed in its linear order, an extension of P)."""
    k = len(order)
    for j in range(1, k):
        left, right = set(order[:j]), set(order[j:])
        if any((x in left and y in right) or (x in right and y in left) for (x, y) in P):
            continue
        return False
    return True


# ---------------------------------------------------------------- checks
def main(NMAX=6):
    posets = {n: all_posets(n) for n in range(0, NMAX + 1)}
    natural = {n: [P for P in posets[n] if is_ext(P, L(n, 0))] for n in posets}
    a = [len(natural[n]) for n in range(NMAX + 1)]
    print("#posets           :", [len(posets[n]) for n in range(1, NMAX + 1)])
    print("a_n (natural)     :", a[1:])
    blog = log_coeffs(a, NMAX)
    print("n[x^n] log A      :", [int(x) for x in blog[1:]])

    B = {}
    for n in range(1, NMAX + 1):
        B[n] = {P for P in posets[n] if C(P, n)}
    b = [None] + [len(B[n]) for n in range(1, NMAX + 1)]
    print("b_n = |B_n|       :", b[1:])
    assert all(b[n] == blog[n] for n in range(1, NMAX + 1))

    # Lemma 1(a),(b),(c)
    for n in range(1, NMAX + 1):
        tot = 0
        for P in B[n]:
            S = C(P, n)
            tot += len(S)
            for c, c2 in combinations(sorted(S), 2):
                arc1 = set(range(c + 1, c2 + 1))
                arc2 = set(range(1, n + 1)) - arc1
                assert not any((x in arc1) != (y in arc1) for (x, y) in P)
        assert tot == n * a[n]
        for P in natural[n]:
            lin = {0} | {c for c in range(1, n)
                         if not any(x <= c < y for (x, y) in P)}
            assert C(P, n) == lin
        assert n * sum(Fraction(1, len(C(P, n))) for P in natural[n]) == b[n]
    print("Lemma 1(a)(b)(c)  : ok for n <=", NMAX)

    # Lemma 2: A = 1/(1-I) with i_k counted directly
    i = [0] + [sum(1 for P in natural[k] if irreducible(P, list(range(1, k + 1))))
               for k in range(1, NMAX + 1)]
    print("i_k (irreducible) :", i[1:])
    # coefficients of 1/(1-I)
    inv = [1] + [0] * NMAX
    for m in range(1, NMAX + 1):
        inv[m] = sum(i[k] * inv[m - k] for k in range(1, m + 1))
    assert inv == a
    print("Lemma 2 A=1/(1-I) : ok")

    # Lemma 3 + Theorem: build cyclic factorizations explicitly, compare
    for n in range(1, NMAX + 1):
        factorizations = {}
        for m in range(1, n + 1):
            for S in combinations(range(n), m):
                arcs = []
                for t in range(m):
                    s, s2 = S[t], S[(t + 1) % m]
                    length = (s2 - s) % n or n
                    arcs.append([(s + r - 1) % n + 1 for r in range(1, length + 1)])
                choices = [[]]
                for arc in arcs:
                    k = len(arc)
                    pieces = [frozenset((arc[x - 1], arc[y - 1]) for (x, y) in Q)
                              for Q in natural[k] if irreducible(Q, list(range(1, k + 1)))]
                    choices = [ch + [q] for ch in choices for q in pieces]
                for ch in choices:
                    real = frozenset().union(*ch)
                    key = (frozenset(S), tuple(ch))
                    assert key not in factorizations
                    factorizations[key] = real
        nf = len(factorizations)
        assert nf == blog[n], (n, nf)
        reals = list(factorizations.values())
        assert len(set(reals)) == nf             # realization injective
        assert set(reals) == B[n]                # ... and onto B_n
        for (S, ch), P in factorizations.items():
            assert C(P, n) == S                  # inverse recovers the cut set
            # pieces recovered as restrictions
            Sl = sorted(S)
            for t, piece in enumerate(ch):
                s, s2 = Sl[t], Sl[(t + 1) % len(Sl)]
                length = (s2 - s) % n or n
                arc = {(s + r - 1) % n + 1 for r in range(1, length + 1)}
                assert piece == frozenset((x, y) for (x, y) in P if x in arc and y in arc)
        print(f"n={n}: #cyclic factorizations = {nf}; realization is a bijection onto B_n")

    # Proposition 1: sum_P e_C(P) = (n-1)! b_n
    sums = []
    for n in range(1, NMAX + 1):
        s = sum(len({rot_class(w) for w in lin_exts(P, n)}) for P in posets[n])
        sums.append(s)
        assert s == factorial(n - 1) * b[n]
    print("sum_P e_C(P)      :", sums, "= (n-1)! b_n")

    # Proposition 2
    for n in range(1, NMAX + 1):
        fix = [sum(1 for P in B[n] if relabel(P, sigma_pow(n, k)) == P) for k in range(n)]
        assert fix == [b[gcd(k, n)] for k in range(n)]
        fixed1 = [P for P in B[n] if relabel(P, sigma_pow(n, 1)) == P]
        assert fixed1 == [frozenset()]
        free = sum(1 for P in B[n]
                   if all(relabel(P, sigma_pow(n, k)) != P for k in range(1, n)))
        assert free == sum(mobius(n // d) * b[d] for d in range(1, n + 1) if n % d == 0)
        assert free % n == 0
        print(f"n={n}: #Fix(sigma^k) = {fix}; free orbits = {free // n}")

    # Section 5 convention check (n <= 5): trace of tau on the direct sum of
    # Lie(P) = span{w e_zeta : w in Lin(P)} in C[S_n], computed from the
    # left-multiplication action, against the character of
    # Ind_{C_n}^{S_n}(zeta (x) C[B_n]) read off from the divisor-sum formula.
    for n in range(1, min(NMAX, 5) + 1):
        zeta = cmath.exp(2j * cmath.pi / n)
        cls = {}
        for P in posets[n]:
            cls[P] = {rot_class(w) for w in lin_exts(P, n)}
        for tau_t in permutations(range(1, n + 1)):
            tau = {x + 1: tau_t[x] for x in range(n)}
            tr = 0
            for P in posets[n]:
                if relabel(P, tau) != P:
                    continue
                for w in cls[P]:                      # w = representative of coset O
                    tw = tuple(tau[x] for x in w)      # tau o w
                    for j in range(n):                 # tau o w = w o gamma^j ?
                        if tw == w[j:] + w[:j]:
                            tr += zeta ** j            # tau w e = w gamma^j e = zeta^j w e
                            break
            # cycle type of tau
            seen, ct = set(), []
            for x in range(1, n + 1):
                if x not in seen:
                    l, y = 0, x
                    while y not in seen:
                        seen.add(y); y = tau[y]; l += 1
                    ct.append(l)
            d = ct[0]
            if all(l == d for l in ct):
                pred = Fraction(d ** (n // d) * factorial(n // d) * mobius(d) * b[n // d], n)
            else:
                pred = 0
            assert abs(tr - float(pred)) < 1e-6, (n, tau_t, tr, pred)
        print(f"n={n}: character of (+)_P Lie(P) == (1/n) sum_d mu(d) b_(n/d) p_d^(n/d)")
    print("ALL AUDIT CHECKS PASSED")


def natural_up_to(N):
    """Naturally labeled posets as tuples of down-set bitmasks (bit x-1 for x)."""
    level = [()]
    yield 0, level
    for k in range(1, N + 1):
        new = []
        for P in level:
            for D in range(1 << (k - 1)):
                if all(not (D >> x) & 1 or (P[x] & ~D) == 0 for x in range(k - 1)):
                    new.append(P + (D,))
        level = new
        yield k, level


def big(N=8):
    """a_n by enumeration and b_n = n sum_{Q natural} 1/|C(Q)| (Lemma 1(c)),
    with C(Q) found by testing each rotated word directly."""
    a = [1]
    bc = [None]
    for k, level in natural_up_to(N):
        if k == 0:
            continue
        s = Fraction(0)
        words = [L(k, c) for c in range(k)]
        for P in level:
            cnt = 0
            for w in words:
                seen, ok = 0, True
                for x in w:
                    if P[x - 1] & ~seen:
                        ok = False
                        break
                    seen |= 1 << (x - 1)
                cnt += ok
            s += Fraction(1, cnt)
        a.append(len(level))
        bc.append(k * s)
        print(f"n={k}: a_n = {len(level)}, n*sum 1/|C| = {k * s}", flush=True)
    blog = log_coeffs(a, N)
    print("n[x^n] log A:", [int(x) for x in blog[1:]])
    assert all(bc[n] == blog[n] for n in range(1, N + 1))
    print("b_n via Lemma 1(c) == n[x^n] log A for n <=", N)


if __name__ == "__main__":
    if "--b8" in sys.argv:
        big(8)
    else:
        main()
