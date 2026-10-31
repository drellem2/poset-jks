"""Unit tests for audit_cyclic_sieving_cyc.py: positive and negative controls."""

import itertools
import unittest
from fractions import Fraction

import audit_cyclic_sieving_cyc as a


class TestControls(unittest.TestCase):
    def test_rsw_necklaces(self):
        # [RSW] Thm 1.1: words of content (2,2) under rotation, X = [4; 2]_q
        words = sorted(set(itertools.permutations((0, 0, 1, 1))))
        idx = {w: i for i, w in enumerate(words)}
        rot = [idx[w[1:] + w[:1]] for w in words]
        X = a.qmultinomial((2, 2))
        self.assertEqual(X, [1, 1, 2, 1, 1])
        self.assertTrue(a.sieves(X, rot, 4))
        self.assertFalse(a.sieves([2, 0, 2, 1, 1], rot, 4))   # negative control

    def test_qbinomial_fake_degree(self):
        X = a.fake_degree_Sk(4, lambda lam: {(4,): 0, (3, 1): 0, (2, 2): 2, (2, 1, 1): 2, (1, 1, 1, 1): 6}[lam])
        self.assertEqual([int(x) for x in X], a.qmultinomial((2, 2)))

    def test_poset_counts(self):
        P = a.all_posets(5)
        self.assertEqual([len(P[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])

    def test_eC_chains(self):
        self.assertEqual(a.eC_chains({2: 2}), 5)
        self.assertEqual(a.eC_chains({1: 4}), 6)
        self.assertEqual(a.eC_chains({2: 3}), 74)


class TestNote(unittest.TestCase):
    def test_A4(self):
        r = a.analyse(a.make_poset(4, []))
        self.assertEqual(r["XW"], [1, 0, 1, 1, 2, 1])
        byg = {tuple(sorted(len(c) for c in a.cycles(c["g"]))): c for c in r["classes"]}
        self.assertEqual(byg[(1, 1, 2)]["Fs"], [6, 0])
        self.assertEqual(byg[(2, 2)]["Fs"], [6, 2])
        self.assertFalse(byg[(1, 1, 2)]["XW_sieves"])     # obstruction
        self.assertTrue(byg[(4,)]["XW_sieves"])

    def test_sigma_C2_cubed(self):
        T = a.make_poset(2, [(0, 1)])
        r = a.analyse(a.disjoint_union(T, T, T))
        self.assertEqual(r["eC"], 74)
        self.assertEqual(r["XW"], [13, 24, 24, 13])

    def test_thmC_criterion(self):
        self.assertEqual(a.thmC_criterion([8], [[6, 2]]), (True, True))
        self.assertEqual(a.thmC_criterion([5], [[2, 3]]), (False, True))
        self.assertEqual(a.thmC_criterion([4], [[2, 1, 1]]), (True, False))

    def test_regular(self):
        # S_4: the 4-cycle and the 3-cycle are regular, a transposition is not
        self.assertTrue(a.is_regular([(1, [(4, 0)])], 4))
        self.assertTrue(a.is_regular([(1, [(3, 0), (1, 0)])], 3))
        self.assertFalse(a.is_regular([(1, [(2, 0), (1, 0), (1, 0)])], 2))
        # G(2,1,1) = {+-1}: -1 is regular; G(2,1,2): a 2-cycle with cycle product c is regular
        self.assertTrue(a.is_regular([(2, [(1, 1)])], 2))
        self.assertTrue(a.is_regular([(2, [(2, 1)])], 4))

    def test_neca_gcd_one(self):
        # two types, k = (3, 2): only the identity term, X(zeta_6) != 0
        self.assertEqual(a.bad_es([3, 2]), [6])

    def test_sturm(self):
        self.assertEqual(a.positive_roots([-2, 0, 1]), 1)
        self.assertEqual(a.positive_roots([6, -5, 1], 1), 2)
        self.assertEqual(a.positive_roots([0, -12, 50, 0, 1048410], 1), 0)


if __name__ == "__main__":
    unittest.main()
