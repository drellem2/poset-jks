"""Unit tests for audit_cyclic_sieving_gcd.py.
Run (from compute/): python3 -m unittest test_audit_cyclic_sieving_gcd"""

import unittest
from fractions import Fraction as Fr

import audit_cyclic_sieving_gcd as a


class TestAuditCyclicSievingGcd(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_chain_dp_matches_brute(self):
        for lens in ([2, 2], [1, 1, 1], [1, 2], [3, 1, 1], [2, 2, 1], [3, 2]):
            n, less, _ = a.build([((m, tuple((i, i + 1) for i in range(m - 1))), 1)
                                  for m in lens])
            self.assertEqual(a.eC_chains(lens), len(a.cyc_classes(n, less)))

    def test_cyclotomic_zero_detection(self):
        self.assertTrue(a.vanishes_at([1, 0, 0, 1], 6))    # 1 + q^3 at zeta_6
        self.assertTrue(a.vanishes_at([1, 0, 0, 1], 2))
        self.assertFalse(a.vanishes_at([1, 0, 0, 1], 4))

    def test_enclosures(self):
        enc = a.s_enclosures(6)
        self.assertTrue(enc[1][0] <= 1 <= enc[1][1])
        self.assertTrue(enc[3][0] <= 2 <= enc[3][1])
        enc8 = a.s_enclosures(8)
        lo, hi = enc8[1]
        self.assertTrue(lo ** 2 <= 2 - Fr(14142135623730950, 10 ** 16) + Fr(1, 10 ** 15))
        self.assertTrue(hi ** 2 >= 2 - Fr(14142135623730951, 10 ** 16) - Fr(1, 10 ** 15))

    def test_dminus(self):
        self.assertEqual(a.Dminus(3, 3), [3])
        self.assertEqual(a.Dminus(8, 4), [4])
        self.assertEqual(a.Dminus(12, 6), [2, 6])
        self.assertEqual(a.Dminus(5, 5), [])

    def test_lemma5_exception_and_control(self):
        lo, hi = a.lemma5_sum(6, 3, 3)
        self.assertTrue(lo <= 1 <= hi)          # attained exactly
        self.assertTrue(a.lemma5_sum(9, 6, 3)[1] < 1)
        self.assertTrue(a.lemma5_sum(6, 5, 5, alld=True)[0] > 3)   # control fires

    def test_A3_closed_form(self):
        X = a.closed_form_X([3], [1], 1)
        self.assertEqual([int(x) for x in X], [1, 0, 0, 1])

    def test_sections_small(self):
        a.sec_lemma6(log=lambda s: None)
        a.sec_yroot(log=lambda s: None)
        self.assertEqual(a.FAIL, [])


if __name__ == "__main__":
    unittest.main()
