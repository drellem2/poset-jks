#!/usr/bin/env python3
"""Brute-force checks for the cyclic-compatible poset counts b_n.

Definitions (elements are 0..n-1 internally, i.e. label i+1 in the note):
  * a poset is stored as a tuple `down` with down[i] = bitmask of the
    elements strictly below i (transitively closed);
  * a_n = number of naturally labeled posets on [n] (the identity word
    1 2 ... n is a linear extension);
  * L_c (c in Z/n) is the rotated word c+1, c+2, ..., n, 1, ..., c;
  * B_n = labeled posets on [n] having some L_c as a linear extension;
  * C(P) = {c : L_c is a linear extension of P};
  * e_C(P) = number of C_n-orbits (rotation classes of words) in S_n that
    meet Lin(P).

Checks performed (see notes/cyclic_compatible_posets_bn.md):
  1. a_n against OEIS A006455.
  2. b_n = |B_n| by explicit construction of B_n as a set (n <= NMAX_SET),
     and, for n <= NMAX_ALL, by scanning *all* labeled posets on [n].
  3. b_n = n * sum_{P natural} 1/|C(P)|  (n <= NMAX).
  4. b_n = n [x^n] log A(x)  (exact rational arithmetic).
  5. sum over all labeled P on [n] of e_C(P) == (n-1)! b_n  (n <= NMAX_ALL).
  6. C_n acting on B_n by relabeling i -> i+1: #Fix(sigma^k) == b_gcd(k,n),
     the antichain is the only sigma-fixed point, and b_p = 1 mod p.

Usage: python3 compute/cyclic_posets.py [NMAX]   (default NMAX=7; 8 takes a
few minutes and only runs checks 1, 3, 4).
"""
import sys
from fractions import Fraction
from itertools import permutations
from math import factorial, gcd

A006455 = [1, 1, 2, 7, 40, 357, 4824, 96428, 2800472]
A001035 = [1, 1, 3, 19, 219, 4231, 130023]
NOTE_B = [None, 1, 3, 16, 131, 1561, 26532, 637890, 21580043]
NMAX_SET = 7   # build B_n explicitly as a set of posets
NMAX_ALL = 6   # enumerate all labeled posets on [n]


def natural_posets(n):
    """Yield all naturally labeled posets on n elements (as `down` tuples).

    Element k is added on top of a naturally labeled poset on 0..k-1 with an
    arbitrary order ideal D as its strict down-set; every naturally labeled
    poset arises exactly once this way."""
    if n == 0:
        yield ()
        return
    for P in natural_posets(n - 1):
        k = n - 1
        for D in range(1 << k):
            ok = True
            m = D
            while m:
                i = (m & -m).bit_length() - 1
                m &= m - 1
                if P[i] & ~D:
                    ok = False
                    break
            if ok:
                yield P + (D,)


def relabel(P, perm):
    """Image of P under the relabeling i -> perm[i]."""
    n = len(P)
    Q = [0] * n
    for i in range(n):
        m, img = P[i], 0
        while m:
            j = (m & -m).bit_length() - 1
            m &= m - 1
            img |= 1 << perm[j]
        Q[perm[i]] = img
    return tuple(Q)


def rot_word(n, c):
    """L_c as a list of elements (0-based): c, c+1, ..., n-1, 0, ..., c-1."""
    return [(c + t) % n for t in range(n)]


def is_extension(P, word):
    seen = 0
    for x in word:
        if P[x] & ~seen:
            return False
        seen |= 1 << x
    return True


def cuts(P):
    n = len(P)
    return [c for c in range(n) if is_extension(P, rot_word(n, c))]


def linear_extensions(P):
    n = len(P)
    full = (1 << n) - 1
    out = []

    def rec(seen, word):
        if seen == full:
            out.append(tuple(word))
            return
        for x in range(n):
            if not (seen >> x) & 1 and not (P[x] & ~seen):
                word.append(x)
                rec(seen | (1 << x), word)
                word.pop()

    rec(0, [])
    return out


def e_C(P):
    """Number of rotation classes of words meeting Lin(P)."""
    classes = set()
    for w in linear_extensions(P):
        i = w.index(0)
        classes.add(w[i:] + w[:i])
    return len(classes)


def log_coeffs(a, N):
    """b_n = n [x^n] log A(x), from n a_n = sum_{k=1}^n b_k a_{n-k}."""
    b = [None] * (N + 1)
    for n in range(1, N + 1):
        b[n] = n * a[n] - sum(b[k] * a[n - k] for k in range(1, n))
    # cross-check with an explicit rational power-series log
    L = [Fraction(0)] * (N + 1)
    for n in range(1, N + 1):  # L' = A'/A  <=>  n a_n = sum k L_k a_{n-k}
        L[n] = Fraction(n * a[n] - sum(k * L[k] * a[n - k] for k in range(1, n)), n)
    assert all(n * L[n] == b[n] for n in range(1, N + 1))
    return b


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    a = [1]
    by_cuts = [None]
    nat = {}
    for n in range(1, NMAX + 1):
        cnt, s = 0, Fraction(0)
        keep = n <= NMAX_SET
        lst = []
        for P in natural_posets(n):
            cnt += 1
            # C(P) for natural P: 0 plus the linear cuts (no relation crosses)
            s += Fraction(1, len(cuts(P)))
            if keep:
                lst.append(P)
        a.append(cnt)
        by_cuts.append(n * s)
        if keep:
            nat[n] = lst
        print(f"n={n}: a_n={cnt} (A006455: {A006455[n]})  "
              f"n*sum 1/|C(P)| = {n * s}", flush=True)
        assert cnt == A006455[n]
        assert (n * s).denominator == 1
    b = log_coeffs(a, NMAX)
    print("b_n = n[x^n] log A :", b[1:])
    print("note's values      :", NOTE_B[1:NMAX + 1])
    for n in range(1, NMAX + 1):
        assert b[n] == by_cuts[n] == NOTE_B[n], n

    for n in range(1, min(NMAX, NMAX_SET) + 1):
        sigma = [(i + 1) % n for i in range(n)]
        # P has L_c as an extension iff P = rho_c(Q), Q natural, where
        # rho_c relabels i -> i + c mod n.
        B = set()
        for c in range(n):
            rho = [(i + c) % n for i in range(n)]
            for Q in nat[n]:
                B.add(relabel(Q, rho))
        assert len(B) == b[n]
        # sanity: every member of B really has some L_c as an extension
        assert all(cuts(P) for P in B)
        # C_n action on B_n
        fix = []
        for k in range(n):
            pk = [(i + k) % n for i in range(n)]
            fix.append(sum(1 for P in B if relabel(P, pk) == P))
        assert all(fix[k] == b[gcd(k, n)] for k in range(n)), fix
        antichain = tuple([0] * n)
        fixed1 = [P for P in B if relabel(P, sigma) == P]
        assert fixed1 == [antichain]
        prim = sum(1 for P in B if all(relabel(P, [(i + k) % n for i in range(n)]) != P
                                       for k in range(1, n)))
        assert prim % n == 0
        print(f"n={n}: |B_n| (explicit set) = {len(B)}; #Fix(sigma^k), k=0..n-1 = {fix}; "
              f"sigma-fixed = antichain only; free orbits = {prim // n}; "
              f"(b_n-1)/n = {Fraction(b[n] - 1, n)}", flush=True)

        if n <= NMAX_ALL:
            allP = set()
            for Q in nat[n]:
                for perm in permutations(range(n)):
                    allP.add(relabel(Q, perm))
            compat = sum(1 for P in allP if cuts(P))
            tot = sum(e_C(P) for P in allP)
            print(f"n={n}: all labeled posets = {len(allP)} (A001035: {A001035[n]}); compatible = {compat}; "
                  f"sum e_C = {tot} = (n-1)! b_n = {factorial(n - 1) * b[n]}", flush=True)
            assert len(allP) == A001035[n]
            assert compat == b[n]
            assert tot == factorial(n - 1) * b[n]
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
