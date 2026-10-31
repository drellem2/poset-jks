"""Unit tests for h_double_prime.py (run from compute/: python3 -m unittest test_h_double_prime)."""

import contextlib
import io
import unittest

import h_double_prime as H


class TestHDoublePrime(unittest.TestCase):
    def test_worked_example(self):
        # 0<1, 3<4, 2 isolated: one all-ascent class, 3041|2, with d = 2, s = 2.
        rel = frozenset({(0, 1), (3, 4)})
        cd, _, _ = H.class_data(rel, 5)
        aa = [c for c in cd if c[3]]
        self.assertEqual(len(aa), 1)
        self.assertEqual((aa[0][1], aa[0][2]), (2, 2))
        self.assertIn((3, 0, 4, 1, 2), aa[0][4])
        hC = H.hC_moebius(rel, 5)
        self.assertEqual(hC, [1, 9, 9, 1])
        self.assertEqual(H.formula(cd), hC)
        mind = H.trim(H.Counter_to_list(H.Counter(c[0] for c in cd)))
        self.assertEqual(mind, [1, 9, 8, 2])

    def test_aa_term(self):
        # x^{d-1}(1-(1-x)^s) with d = 2, s = 2 is 2x^2 - x^3.
        self.assertEqual(H.aa_term(2, 2), [0, 0, 2, -1])
        self.assertEqual(H.aa_term(1, 3), [0, 3, -3, 1])

    def test_controls_fire_on_example(self):
        rel = frozenset({(0, 1), (3, 4)})
        cd, _, _ = H.class_data(rel, 5)
        hC = [1, 9, 9, 1]
        self.assertNotEqual(H.formula(cd, sexp_off=1), hC)
        self.assertNotEqual(H.formula(cd, dshift=0), hC)

    def test_small_run(self):
        with contextlib.redirect_stdout(io.StringIO()):
            rc = H.main(["--lmax", "5", "--mobmax", "5", "--pcmax", "5"])
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
