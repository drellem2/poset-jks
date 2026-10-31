#!/usr/bin/env python3
"""Unit tests for reciprocity_omega_c.py.  Run from compute/:

    python3 -m unittest test_reciprocity_omega_c
"""

import unittest
from itertools import product
from math import comb

import h_vector_omega_c as H
import reciprocity_omega_c as R


def omegabar_literal(rel, n, T, m):
    """Literal count of strict f : P -> [m] with D_T, all maps (not surjective)."""
    P = R.Poset(frozenset(rel), n)
    cnt = 0
    for f in product(range(1, m + 1), repeat=n):
        if any(f[a] >= f[b] for a, b in rel):
            continue
        A, B = R.intervals(P, f)
        if R.brute(A, B, T, weak=False):
            cnt += 1
    return cnt


def recip(rel, n, m):
    a, _ = H.omega_c_coeffs(frozenset(rel), n)
    return (-1) ** n * R.omega_values(a, [-m])[0]


class Reciprocity(unittest.TestCase):
    def test_antichain_2(self):
        # OmegaBar_C(A_2, m) = C(m, 2): the anchor strictly above the other point
        for m in range(1, 6):
            self.assertEqual(recip([], 2, m), comb(m, 2))
            self.assertEqual(omegabar_literal([], 2, 1, m), comb(m, 2))

    def test_antichain_sum_of_powers(self):
        # n >= 2 (for n = 1, D_T is vacuous and OmegaBar_C = m)
        self.assertEqual([recip([], 1, m) for m in range(1, 4)], [1, 2, 3])
        for n in range(2, 5):
            for m in range(1, 5):
                self.assertEqual(recip([], n, m), sum(j ** (n - 1) for j in range(1, m)))

    def test_small_literal_all_T(self):
        cases = [([(0, 1)], 3), ([(0, 1), (2, 3)], 4), ([(0, 1), (1, 2), (0, 2)], 4),
                 ([(0, 2), (1, 2)], 4)]
        for rel, n in cases:
            P = R.Poset(frozenset(rel), n)
            for T in range(P.r):
                for m in range(1, 5):
                    self.assertEqual(omegabar_literal(rel, n, T, m), recip(rel, n, m))

    def test_naive_control_fails(self):
        # strict maps with the Omega_C anchoring give C(m+1, 2) on A_2, not C(m, 2)
        P = R.Poset(frozenset(), 2)
        cnt = sum(1 for f in product(range(1, 4), repeat=2)
                  if R.brute(*R.intervals(P, f), 1, True))
        self.assertEqual(cnt, comb(4, 2))
        self.assertNotEqual(cnt, recip([], 2, 3))

    def test_c2c2_values(self):
        self.assertEqual([recip([(0, 1), (2, 3)], 4, m) for m in range(1, 6)],
                         [0, 1, 8, 31, 85])

    def test_criteria_match_bruteforce(self):
        P = R.Poset(frozenset([(0, 1)]), 4)   # C_2 + A_2
        for f in product(range(1, 4), repeat=4):
            if f[0] > f[1]:
                continue
            A, B = R.intervals(P, f)
            M = max(f)
            for T in range(P.r):
                self.assertEqual(R.anchored(A, B, T, M), R.brute(A, B, T, True))
                self.assertEqual(R.dual_ok(A, B, T, M), R.brute(A, B, T, False))


if __name__ == "__main__":
    unittest.main()
