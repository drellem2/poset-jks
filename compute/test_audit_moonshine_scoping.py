"""Unit tests for audit_moonshine_scoping.py: positive and negative controls."""

import unittest
from fractions import Fraction

import audit_moonshine_scoping as a


class TestWitt(unittest.TestCase):
    def test_natural_posets(self):
        P = a.natural_posets(5)
        self.assertEqual([len(P[n]) for n in range(6)], [1, 1, 2, 7, 40, 357])

    def test_log_coeffs_witt_control(self):
        # (1-x)/(1-2x): b_n = 2^n - 1 (necklace / Witt control)
        N = 10
        A = [1] + [2 ** (n - 1) for n in range(1, N + 1)]
        self.assertEqual(a.log_coeffs(A, N)[1:], [2 ** n - 1 for n in range(1, N + 1)])

    def test_euler_product_partitions(self):
        p = a.euler_product({n: 1 for n in range(1, 11)}, 10)
        self.assertEqual(p, [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42])


class TestQuotientFormula(unittest.TestCase):
    def test_bowtie_swap(self):
        rel = [(0, 2), (0, 3), (1, 2), (1, 3)]
        g = [1, 0, 2, 3]
        self.assertEqual(a.ppartitions_fixed(4, rel, g, 12),
                         a.quotient_formula(4, rel, g, 12)[0])

    def test_wrong_weights_fail(self):
        # negative control: forgetting orbit sizes (weight 1 per orbit) fails
        rel = [(0, 1), (2, 3)]
        g = [2, 3, 0, 1]
        bf = a.ppartitions_fixed(4, rel, g, 12)
        unweighted = a.ppartitions_fixed(2, [(0, 1)], [0, 1], 12)
        self.assertNotEqual(bf, unweighted)

    def test_leading_pole(self):
        _, lin, lead = a.quotient_formula(3, [], [0, 1, 2], 4)
        self.assertEqual((lin, lead), (6, Fraction(1)))


class TestFrame(unittest.TestCase):
    def test_wilson(self):
        for p in (3, 5, 7):
            r = a.frame_shape(lambda e: a.lie_char(p, a.power_type((p,), e)), p)
            self.assertEqual(r, {1: -1, p: (a.math.factorial(p - 1) + 1) // p})

    def test_lie_restricted_regular(self):
        self.assertEqual(a.lie_char(6, (2, 2, 1, 1)), 0)
        self.assertEqual(a.lie_char(6, (2, 2, 2)), -8)

    def test_non_rational_character_rejected(self):
        # negative control: chi(g) = 1, chi(1) = 3 on C_3 is not the character
        # of a rational representation (3 r_3 = 2), and the inversion refuses it
        with self.assertRaises(AssertionError):
            a.frame_shape(lambda e: 3 if e % 3 == 0 else 1, 3)


if __name__ == "__main__":
    unittest.main()
