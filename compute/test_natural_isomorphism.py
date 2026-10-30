#!/usr/bin/env python3
"""Tests for natural_isomorphism.py.  Run: python3 -m unittest test_natural_isomorphism"""

import unittest

import poset_jks_check as pj
import natural_isomorphism as ni
from splitting_cycles import root_of_unity


class NaturalIsomorphism(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.posets = pj.unlabeled_posets_by_extension(4)

    def test_all_sections_n4(self):
        self.assertEqual(ni.main(["--nmax", "4"]), 0)

    def test_ext_control_two_chains(self):
        # two 2-chains: R_P e_zeta != 0 (Theorem 1); the shuffle 01 ш 23
        # has coefficient 1/n at the witness word u = 2 0 1 3
        p, n = ni.P1, 4
        z = root_of_unity(n, p)
        v = ni.times_e_zeta({w: 1 for w in ni.shuffles((0, 1), (2, 3))}, n, z, p)
        self.assertEqual(v[(2, 0, 1, 3)], pow(n, p - 2, p))

    def test_ext_n2_degenerate(self):
        # n = 2: (01 + 10) e_zeta = 0 with zeta = -1
        p = ni.P1
        z = root_of_unity(2, p)
        self.assertEqual(ni.times_e_zeta({(0, 1): 1, (1, 0): 1}, 2, z, p), {})

    def test_psi_control_wrong_phase(self):
        # positive control for [psi]: with the phases dropped (lam = 1) the
        # antichain on 3 letters loses rank, so the rank test can fail
        rk, e = ni.weighted_rank(frozenset(), 3, [1, 1, 1], ni.P1)
        self.assertLess(rk, e)
        p = ni.P1
        z = root_of_unity(3, p)
        rk, e = ni.weighted_rank(frozenset(), 3, [z, z, z], p)
        self.assertEqual(rk, e)

    def test_cobracket_descends_only_equal_connected(self):
        out = []
        self.assertTrue(ni.check_coproducts(self.posets, 4, out))
        self.assertIn("(1 such pairs)", out[-1])


if __name__ == "__main__":
    unittest.main()
