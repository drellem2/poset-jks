"""Tests for quotient_categories.py, with positive and negative controls (run from compute/)."""

import unittest

import quotient_categories as qc


class Instruments(unittest.TestCase):
    def test_controls(self):
        self.assertTrue(qc.part_ctl([]))

    def test_torsion_detector_rp2(self):
        out = []
        qc.part_ctl(out)
        self.assertTrue(any("RP^2" in l and l.endswith("True") for l in out))


class Mixed(unittest.TestCase):
    def test_claw_poset_is_mixed_graph(self):
        # K_3 with arcs 0->1, 0->2: OP(claw) = Pi_3; pointed, #V = 2 = m.
        good, why, info = qc.check_mixed(3, [(0, 1), (0, 2), (1, 2)], [(0, 1), (0, 2)])
        self.assertTrue(good, why)
        self.assertEqual(info, (True, 2, 2))

    def test_undirected_triangle_is_folkman(self):
        # Pi_3: not pointed, m = 2, #V = 6 acyclic orientations.
        good, why, info = qc.check_mixed(3, [(0, 1), (0, 2), (1, 2)], [])
        self.assertTrue(good, why)
        self.assertEqual(info, (False, 2, 6))

    def test_geometric_equals_combinatorial_path(self):
        e, a = [(0, 1), (1, 2), (2, 3)], [(0, 1)]
        self.assertEqual(qc.mixed_lambda_geometric(4, e, a),
                         qc.mixed_lambda_combinatorial(4, e, a))


class Fixed(unittest.TestCase):
    def test_fix_small(self):
        self.assertTrue(qc.part_fix([], 4))


class DDivisible(unittest.TestCase):
    def test_small_cases(self):
        self.assertTrue(qc.part_ddiv([], [(4, 2), (6, 3)]))

    def test_beta_control(self):
        # descent counts: permutations of [3] with descent set {2} are 132, 231
        self.assertEqual(qc.beta_descent(3, [2]), 2)
        self.assertEqual(qc.beta_descent(4, [2]), 5)


class Negative(unittest.TestCase):
    def test_matching_lattice_has_torsion(self):
        self.assertTrue(qc.part_neg([]))


class Groups(unittest.TestCase):
    def test_a4(self):
        self.assertTrue(qc.part_gset([], True))


if __name__ == "__main__":
    unittest.main()
