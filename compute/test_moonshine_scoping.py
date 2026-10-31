"""Tests for moonshine_scoping.py, with positive and negative controls
(run from compute/)."""

import io
import unittest
from contextlib import redirect_stdout

import moonshine_scoping as ms
from poset_jks_check import transitive_closure


class Detector(unittest.TestCase):
    def test_theta3_positive(self):
        th = [0] * 50
        for n in range(-7, 8):
            if n * n < 50:
                th[n * n] += 1
        d = ms.detect_eta_quotient(th)
        self.assertTrue(d["ok"])
        self.assertEqual(d["r"], {1: -2, 2: 5, 4: -2})

    def test_rejects_rational_and_macmahon(self):
        self.assertFalse(ms.detect_eta_quotient([1] + [2 ** (n - 1) for n in range(1, 40)])["ok"])
        mac = ms.euler_product({n: -n for n in range(1, 40)}, 40)
        self.assertFalse(ms.detect_eta_quotient(mac)["ok"])

    def test_witt_necklace(self):
        _, _, e = ms.product_exponents([1] + [2 ** (n - 1) for n in range(1, 30)])
        l = ms.witt_one_per_degree(30)
        self.assertEqual([-x for x in e[1:]], l[1:])

    def test_eta_form_data_ramanujan(self):
        fd = ms.eta_form_data({1: -1, 5: 5})
        self.assertEqual((fd["weight"], fd["level"], fd["holomorphic"]), (2, 5, True))
        # 1^5 5^-1 is the companion Eisenstein series, also holomorphic;
        # negative control: 1/Delta has a pole at infinity
        self.assertTrue(ms.eta_form_data({1: 5, 5: -1})["holomorphic"])
        self.assertFalse(ms.eta_form_data({1: -24})["holomorphic"])


class PPartitions(unittest.TestCase):
    def test_quotient_formula_matches_brute_force(self):
        rel, n = ms.chains([2, 2])
        rel = transitive_closure(rel, n)
        g = (2, 3, 0, 1)
        bf = ms.brute_fixed_ppartitions(rel, n, g, 20)
        qf, _, _ = ms.quotient_formula(rel, n, g, 20)
        self.assertEqual(bf, qf)
        # negative control: the identity's series differs from the swap's
        qid, _, _ = ms.quotient_formula(rel, n, (0, 1, 2, 3), 20)
        self.assertNotEqual(qid, qf)


class FrameShapes(unittest.TestCase):
    def test_lie5_five_cycle(self):
        rel, n = ms.antichain(5)
        g = (1, 2, 3, 4, 0)
        chis = {e: ms.closed_formula(rel, n, ms.power(g, e)) for e in range(1, 6)}
        self.assertEqual(ms.frame_shape(chis, 5), {1: -1, 5: 5})
        T = ms.fock_trace(chis, 5, 30)
        self.assertEqual(T, ms.eta_quotient({1: 1, 5: -5}, 30))


class FullRun(unittest.TestCase):
    def test_all_sections_pass(self):
        with redirect_stdout(io.StringIO()) as out:
            status = ms.main([])
        self.assertEqual(status, 0, out.getvalue()[-2000:])


if __name__ == "__main__":
    unittest.main()
