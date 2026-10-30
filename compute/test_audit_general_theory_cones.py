"""Unit tests for audit_general_theory_cones.py (mg-7ab20).
Run (from compute/): python3 -m unittest test_audit_general_theory_cones"""

import unittest

import audit_general_theory_cones as a


class TestAuditGeneralTheoryCones(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_controls_fire(self):
        self.assertTrue(a.controls(log=lambda s: None))

    def test_face_counts(self):
        # Zaslavsky: A_3 has 24 chambers and 75 faces; B_3 has 48 and 147
        A = a.Arr("A3", a.braid(4)[0])
        self.assertEqual((len(A.chambers), len(A.faces)), (24, 75))
        B, _, _, _, _ = a.arrangements()
        A = a.Arr("B3", B(3))
        self.assertEqual((len(A.chambers), len(A.faces)), (48, 147))

    def test_small_arrangements_pass(self):
        B, _, generic5, _, _ = a.arrangements()
        for name, N in (("A2", a.braid(3)[0]), ("B2", B(2)), ("A3", a.braid(4)[0]),
                        ("generic5", generic5)):
            a.audit_arr(a.Arr(name, N), log=lambda s: None)
        self.assertEqual(a.FAIL, [])

    def test_braid_n4(self):
        a.audit_braid(4, log=lambda s: None)
        self.assertEqual(a.FAIL, [])

    def test_equivariance_b2(self):
        B, _, _, _, _ = a.arrangements()
        self.assertEqual(a.check_equivariance(a.Arr("B2", B(2))), 64)
        self.assertEqual(a.FAIL, [])

    def test_e_C(self):
        # 2-antichain: Lin = {01, 10}, one cyclic class; 3-chain: e_C = 1
        self.assertEqual(a.e_C(range(2), frozenset()), 1)
        self.assertEqual(a.e_C(range(3), frozenset({(0, 1), (1, 2), (0, 2)})), 1)
        self.assertEqual(a.e_C(range(3), frozenset()), 2)


if __name__ == "__main__":
    unittest.main()
