"""Unit tests for cyclic_sieving_gcd.py.
Run (from compute/): python3 -m unittest test_cyclic_sieving_gcd"""

import cmath
import math
import unittest
from fractions import Fraction

import cyclic_sieving_gcd as c


class TestGcd(unittest.TestCase):
    def setUp(self):
        c.FAIL.clear()

    def test_closed_form_matches_star_k2(self):
        # (star) for k = 2: X = ((c_2 + c_1) + (c_2 - c_1) q)/2; T = C_2: c_1 = 1, c_2 = 5
        self.assertEqual(c.X_closed([2], [2]), [3, 2])

    def test_closed_form_matches_molien(self):
        X, _, _ = c.molien_brute(["pt", "C2"], [2, 2])
        self.assertEqual(c.X_closed([2, 2], [1, 2]), X)

    def test_antichain_ratio(self):
        A = c.A_coeffs([8], [1])
        for d in A:
            self.assertEqual(A[d] / A[1], c.phi(d))

    def test_phase_identity(self):
        X = c.X_closed([4, 4], [1, 2], Fraction(3))
        exact = c.peval(X, cmath.exp(2j * math.pi / 6))
        val, _ = c.phase_value([4, 4], [1, 2], Fraction(3), 6)
        self.assertLess(abs(exact - val), 1e-9 * abs(exact))

    def test_sin_interval(self):
        for d, e in [(1, 6), (1, 7), (3, 6), (2, 15), (5, 12)]:
            lo, hi = c.sin_interval(d, e)
            self.assertLessEqual(lo, math.sin(math.pi * d / e) + 1e-15)
            self.assertGreaterEqual(hi, math.sin(math.pi * d / e) - 1e-15)
            self.assertLess(hi - lo, Fraction(1, 10 ** 15))

    def test_Dminus(self):
        self.assertEqual(c.Dminus(8, 4), [4])
        self.assertEqual(c.Dminus(5, 5), [])          # A_5 at e = 6: d = 5 has the phase of d = 1
        self.assertEqual(c.Dminus(12, 6), [2, 6])

    def test_A3_is_the_exception(self):
        X = c.X_closed([3], [1])
        self.assertEqual(X, [1, 0, 0, 1])
        self.assertTrue(c.phi_divides(X, 6))
        self.assertNotIn(6, c.element_orders([3]))

    def test_bad_es(self):
        self.assertEqual(c.bad_es([5]), [6])
        self.assertEqual(c.bad_es([4, 4]), [6, 12])
        self.assertEqual(c.bad_es([3]), [])

    def test_no_vanishing_small(self):
        for ks, ms in [([5], [1]), ([4, 4], [1, 3]), ([6, 6], [2, 3]), ([3, 3], [1, 2])]:
            X = c.X_closed(ks, ms)
            for e in c.bad_es(ks):
                self.assertFalse(c.phi_divides(X, e))


if __name__ == "__main__":
    unittest.main()
