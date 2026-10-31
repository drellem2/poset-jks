"""Unit tests for audit_mo17370.py (positive and negative controls)."""

import unittest

import audit_mo17370 as A


class Controls(unittest.TestCase):
    def test_hand_controls(self):
        out = []
        self.assertTrue(A.controls(out))

    def test_r4_tree(self):
        out = []
        self.assertTrue(A.r4(out))

    def test_core_does_not_overshrink(self):
        # Pi_4 proper part is a wedge of six circles: never a one-point core
        allp = list(A.set_partitions(4))
        L, _ = A.build_M(4, frozenset(), (0, 1, 2, 3), allp)
        self.assertNotEqual(len(A.stong_core(L, A.proper_part(L))), 1)

    def test_empty_proper_part_is_not_contractible(self):
        # M = {0, 1}: mu = -1, proper part empty (S^-1); must not count as a point
        L = A.lattice_from_masks([0, 1])
        self.assertEqual(A.mobius(L), -1)
        self.assertEqual(len(A.stong_core(L, A.proper_part(L))), 0)

    def test_sweep_n5(self):
        out = []
        self.assertTrue(A.sweep(5, 6000, out))
        self.assertIn('[E1] zeros: 126', out)


if __name__ == '__main__':
    unittest.main()
