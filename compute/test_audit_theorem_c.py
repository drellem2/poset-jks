"""Unit tests for audit_theorem_c.py.
Run (from compute/): python3 -m unittest test_audit_theorem_c"""

import random
import unittest

import audit_theorem_c as a


class TestAuditTheoremC(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_controls_fire(self):
        self.assertTrue(a.controls(log=lambda s: None))
        self.assertEqual(a.FAIL, [])

    def test_exact_rank(self):
        self.assertEqual(a.rank_exact([{0: 2, 1: 4}, {0: 1, 1: 2}, {1: 3}]), 2)
        self.assertEqual(a.rank_exact([{0: a.P}]), 1)
        self.assertEqual(a.rank_mod([{0: a.P}]), 0)

    def test_counts(self):
        B4 = a.Arr("B4", a.B(4))
        self.assertEqual(len(B4.chambers), 384)
        self.assertTrue(a.euler_ok(B4))
        self.assertTrue(B4.simplicial())

    def test_r4_spanning_and_q(self):
        R4 = a.Arr("R4", a.random_arr(4, 9, seed=11))
        self.assertFalse(R4.simplicial())
        cones = a.sample_cones(R4, 6, 1, nonpointed=True)
        self.assertEqual(a.check_cones(R4, cones, exact=True, log=lambda s: None), 0)
        lunes = a.lune_checks(R4, log=lambda s: None)
        self.assertEqual(a.q_check(R4, lunes, cones, exact=True, log=lambda s: None), 0)
        self.assertEqual(a.FAIL, [])

    def test_braid_sign(self):
        for n in (3, 4):
            self.assertEqual(len(a.braid_sign(n)), 1)
            self.assertEqual(a.braid_det(n), {-1})
        self.assertGreater(len(a.braid_sign(4, twist=False)), 1)
        self.assertEqual(a.FAIL, [])

    def test_equivariance_b3(self):
        B3 = a.Arr("B3", a.B(3))
        gs = a.signed_perms(3, random.Random(1), 12)
        self.assertEqual(a.equivariance(B3, gs, B3.chambers[:8]), 0)
        self.assertGreater(a.equivariance(B3, gs, B3.chambers[:8], twist=False), 0)


if __name__ == "__main__":
    unittest.main()
