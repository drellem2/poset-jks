#!/usr/bin/env python3
"""Unit tests for palindromic_h_c.py.  Run from compute/:

    python3 -m unittest test_palindromic_h_c
"""

import unittest
from itertools import product

import palindromic_h_c as S
import reciprocity_omega_c as R


def disjoint(*parts):
    """Disjoint union of (rel, n) pairs."""
    rel, off = [], 0
    for r, n in parts:
        rel += [(a + off, b + off) for a, b in r]
        off += n
    return frozenset(rel), off


def chain(k):
    return [(a, b) for a in range(k) for b in range(a + 1, k)], k


def omegabar_literal(rel, n, T, m):
    """Strict f : P -> [m] with D_T, all maps, D_T by brute force over U."""
    P = R.Poset(frozenset(rel), n)
    cnt = 0
    for f in product(range(1, m + 1), repeat=n):
        if any(f[a] >= f[b] for a, b in rel):
            continue
        A, B = R.intervals(P, f)
        if R.brute(A, B, T, weak=False):
            cnt += 1
    return cnt


def h(rel, n):
    return S.h_TheoremH(frozenset(rel), n)


class Examples(unittest.TestCase):
    def test_vectors(self):
        self.assertEqual(h(*disjoint(chain(3), chain(3))), [1, 8, 9, 1])
        self.assertEqual(h(*disjoint(chain(3), chain(1))), [1, 2])
        self.assertEqual(h(*disjoint(chain(2), chain(2))), [1, 3, 1])
        self.assertEqual(h([], 4), [1, 4, 1])

    def test_bplus_every_T(self):
        rel, n = disjoint(chain(3), chain(2), chain(1))
        P = S.Poset(rel, n)
        for T in range(P.r):
            self.assertEqual(S.h_Bplus(P, T), h(rel, n))

    def test_strict_maps_literal(self):
        for rel, n in [chain(3), ([(0, 1), (0, 2)], 3), ([(0, 2), (1, 2), (1, 3)], 4)]:
            P = S.Poset(frozenset(rel), n)
            for m in range(1, 6):
                lit = sum(1 for f in product(range(1, m + 1), repeat=n)
                          if all(f[a] < f[b] for a, b in rel))
                self.assertEqual(P.strict_maps(m), lit)


class ProofSteps(unittest.TestCase):
    def test_top_with_isolated_point(self):
        # C_3 + C_1, L = 3: h_d = OmegaBar_C(P, 3) = (L - 1)^1 * 1 = 2
        rel, n = disjoint(chain(3), chain(1))
        self.assertEqual(omegabar_literal(rel, n, 0, 3), 2)

    def test_DT_automatic_at_L_plus_1(self):
        # C_3 + C_3: every strict map into [4] satisfies D_T, so the count is
        # sbar(C_3, 4)^2 = 16 = h_2 + 7 h_3
        rel, n = disjoint(chain(3), chain(3))
        allstrict = S.Poset(rel, n).strict_maps(4)
        self.assertEqual(allstrict, 16)
        self.assertEqual(omegabar_literal(rel, n, 0, 4), 16)
        hh = h(rel, n)
        self.assertEqual(hh[2] + 7 * hh[3], 16)

    def test_control_L2_not_automatic(self):
        # C_2 + C_2 at m = L + 1 = 3: D_T cuts 9 strict maps down to 8
        rel, n = disjoint(chain(2), chain(2))
        self.assertEqual(S.Poset(rel, n).strict_maps(3), 9)
        self.assertEqual(omegabar_literal(rel, n, 0, 3), 8)

    def test_gap_formula(self):
        # three chains C_3: h_{d-1} - h_1 = 4^3 - 4^3 + 2^2 - 1 = 3
        rel, n = disjoint(chain(3), chain(3), chain(3))
        hh = h(rel, n)
        d = len(hh) - 1
        self.assertEqual(d, n - 3)
        self.assertEqual(hh[d], 1)
        self.assertEqual(hh[d - 1] - hh[1], 3)


if __name__ == "__main__":
    unittest.main()
