"""Unit tests for audit_cone_lune.py (mg-52a16).  Run: python3 -m unittest test_audit_cone_lune"""

import unittest
from fractions import Fraction

import audit_cone_lune as a


class TestAuditConeLune(unittest.TestCase):
    def test_controls_fire(self):
        self.assertTrue(a.controls())

    def test_sign_q5(self):
        # 1 - (sqrt5 - 1) / 2 * 2 = 2 - sqrt5 < 0; 3 - sqrt5 > 0
        self.assertEqual(a.sign_pair(2, -1), -1)
        self.assertEqual(a.sign_pair(3, -1), 1)
        self.assertEqual(a.sign(a.Q5(Fraction(1, 2), Fraction(1, 2)) - a.Q5(1)), 1)

    def test_h3_counts(self):
        A = a.Arr("H3", a.h3(), "Q5")
        self.assertEqual(len(A.lines), 31)        # 6 + 10 + 15 rotation axes
        self.assertEqual(len(A.topes), 120)
        self.assertEqual(len(A.cov), 1 + 62 + 180 + 120)

    def test_small_arrangement_passes(self):
        A = a.Arr("A1xA2", [(1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 1)])
        self.assertTrue(a.audit(A))

    def test_braid_n3_counterexample_cone(self):
        # essential A_2: the cone {x1 <= x2, x1 <= x3} is pointed, has two
        # chambers, and its chamber sum is not in Lune (printed Ex. 10.9 fails).
        A = a.Arr("A2", [(1, 0), (0, 1), (1, 1)])
        L = a.lunes(A)
        lie = a.lie_basis(sorted(L.values(), key=sorted), len(A.topes))
        V = frozenset(i for i, C in enumerate(A.topes) if C[0] == 1 and C[2] == 1)
        self.assertEqual(len(V), 2)
        self.assertTrue(a.is_pointed(A, V))
        self.assertTrue(any(sum(b[i] for i in V) for b in lie))

    def test_not_essential_rejected(self):
        with self.assertRaises(AssertionError):
            a.Arr("A2 in R^3", [(1, -1, 0), (0, 1, -1), (1, 0, -1)])


if __name__ == "__main__":
    unittest.main()
