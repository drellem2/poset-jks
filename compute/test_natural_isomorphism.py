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

    def test_wgt_reps_lie_in_lin_p(self):
        # every class representative used by [wgt] is a linear extension
        for rel in self.posets[4]:
            lin = pj.linear_extensions(rel, 4)
            reps = ni.lin_class_reps(lin)
            self.assertTrue(set(reps) <= set(lin))
            self.assertEqual(sorted(map(pj.class_rep, reps)), pj.cyclic_classes(lin))

    def test_wgt_lam1_drops_for_all_disconnected(self):
        # lam = 1: sum_C s_1(C) = sum Lin P lies in Sh, so every disconnected
        # P drops (audit section 5); the true counts are 6/6 at n = 4
        out = []
        self.assertTrue(ni.check_weights(self.posets, 4, out))
        self.assertIn("rank drops for 6/6 disconnected P", out[-1])

    def test_wgt_control_least_rotation_reps_fail(self):
        # positive control: the old representative (least rotation, which
        # need not lie in Lin P) misses the lam = 1 drop on some disconnected
        # P at n = 4 (the defective 5/6), and check_weights must then fail
        out = []
        self.assertFalse(ni.check_weights(self.posets, 4, out, reps_fn=pj.cyclic_classes))
        self.assertIn("rank drops for 5/6 disconnected P", out[-1])
        missed = []
        for rel in self.posets[4]:
            if len(ni.components(rel, 4)) > 1:
                rk, e = ni.weighted_rank(rel, 4, [1] * 4, ni.P1, pj.cyclic_classes)
                if rk == e:
                    missed.append(rel)
        self.assertEqual(len(missed), 1)
        rk, e = ni.weighted_rank(missed[0], 4, [1] * 4, ni.P1)
        self.assertLess(rk, e)

    def test_cobracket_descends_only_equal_connected(self):
        out = []
        self.assertTrue(ni.check_coproducts(self.posets, 4, out))
        self.assertIn("(1 such pairs)", out[-1])


if __name__ == "__main__":
    unittest.main()
