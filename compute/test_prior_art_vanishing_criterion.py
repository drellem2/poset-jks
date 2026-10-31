"""Unit tests for prior_art_vanishing_criterion.py: positive and negative controls."""

import io
import unittest
from contextlib import redirect_stdout

import prior_art_vanishing_criterion as p


class TestPrimitives(unittest.TestCase):
    def test_fixed_lattice_sizes(self):
        # Pi_4 has 15 elements (Bell number); the 4-cycle (0 1 2 3) fixes three:
        # the finest, the coarsest, and {0,2}|{1,3}
        self.assertEqual(len(p.FixedLattice(p.perm_of_type([1, 1, 1, 1])).elems), 15)
        self.assertEqual(len(p.FixedLattice(p.perm_of_type([4])).elems), 3)

    def test_mu_partition_lattice(self):
        for n, val in ((3, 2), (4, -6), (5, 24)):
            L = p.FixedLattice(p.perm_of_type([1] * n))
            self.assertEqual(L.mu_to_top(L.bot), val)

    def test_stanley_lemma_7_1(self):
        # mu(Pi_n^w) = (-1)^(r-1) mu(o) (r-1)! o^(r-1) for r cycles of length o, else 0
        for ct, val in (([2, 2], 2), ([3, 3], 3), ([2, 2, 2], -8), ([4], 0), ([2, 1], 0)):
            L = p.FixedLattice(p.perm_of_type(ct))
            self.assertEqual(L.mu_to_top(L.bot), val, ct)


class TestClaims(unittest.TestCase):
    def test_hanlon_identity(self):
        for ct in ([2, 2], [3, 3], [2, 2, 2], [6], [3, 2, 1]):
            ok, nc, mus, _ = p.check_hanlon(ct)
            self.assertTrue(ok, ct)
        self.assertEqual(p.check_hanlon([2, 2, 2])[1], 4)  # o^(r-1) = 2^2

    def test_hanlon_needs_meet_condition(self):
        # negative control: summing over all X with X + U in no hyperplane breaks it
        self.assertFalse(p.check_hanlon_wrong_index([2, 2]))
        self.assertFalse(p.check_hanlon_wrong_index([2, 2, 2]))

    def test_minus_rule(self):
        for ct, val in (([2, 1], True), ([3, 3], True), ([2, 2, 1, 1], True),
                        ([4], False), ([3, 1], False), ([3, 3, 1], False)):
            self.assertEqual(p.some_cone_minus(ct), val, ct)
            self.assertEqual(p.rule_minus(ct), val, ct)

    def test_minus_rule_exceeds_all_chambers(self):
        # -(2,1) is nonzero on some cone while mu(Pi_3^w) = 0 for w = (2,1)
        self.assertTrue(p.some_cone_minus([2, 1]))
        self.assertFalse(p.rule_all_chambers([2, 1]))

    def test_main_quick(self):
        with redirect_stdout(io.StringIO()) as out:
            fails = p.main(6)
        self.assertEqual(fails, 0)
        self.assertIn("ALL CHECKS PASSED", out.getvalue())


if __name__ == "__main__":
    unittest.main()
