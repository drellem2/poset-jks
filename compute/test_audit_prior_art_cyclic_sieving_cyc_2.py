"""Unit tests for audit_prior_art_cyclic_sieving_cyc_2.py.
Run (from compute/): python3 -m unittest test_audit_prior_art_cyclic_sieving_cyc_2"""

import unittest
from fractions import Fraction

import audit_prior_art_cyclic_sieving_cyc_2 as a


class TestAudit(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_group_orders_and_degrees(self):
        for (m, p, n), order in [((3, 1, 2), 18), ((4, 2, 2), 16), ((2, 2, 4), 192)]:
            els, degs = a.G_mpn(m, p, n)
            self.assertEqual(len(els), order)
            prod = 1
            for d in degs:
                prod *= d
            self.assertEqual(prod, order)          # |G| = prod d_i

    def test_eigen_angles_match_matrices(self):
        els, _ = a.G_mpn(3, 1, 2)
        self.assertEqual(a.eig_check(els, [g.matrix() for g in els]), 0)

    def test_propE_one_case_and_control(self):
        els, degs = a.G_mpn(3, 1, 2)
        mats = [g.matrix() for g in els]
        cls, nc = a.conj_classes(els)
        chi = [complex(1 + c, 2 - c) for c in cls]
        lhs, ok = a.f_at_zeta_numeric(els, mats, degs, chi, 3)
        self.assertTrue(ok)
        self.assertAlmostEqual(abs(lhs - a.rhs_propE(els, degs, chi, 3)), 0, places=7)
        self.assertGreater(abs(lhs - a.rhs_propE(els, degs, chi, 3, flip=True)), 1e-3)

    def test_fake_degree_trivial(self):
        # F = 1: X = 1 for S_3 (one orbit, trivial module)
        F = {(lam,): 1 for lam in a.partitions(3)}
        self.assertEqual(a.fake_poly_W([3], F)[0], 1)
        self.assertTrue(all(c == 0 for c in a.fake_poly_W([3], F)[1:]))

    def test_typeA_formula_k5_e3(self):
        F = {lam: i + 1 for i, lam in enumerate(a.partitions(5))}
        X = a.fake_poly_W([5], {(lam,): v for lam, v in F.items()})
        z = a.root(Fraction(1, 3))
        self.assertAlmostEqual(abs(a.peval(X, z) - a.typeA_formula(5, 3, F, z)), 0, places=8)


if __name__ == "__main__":
    unittest.main()
