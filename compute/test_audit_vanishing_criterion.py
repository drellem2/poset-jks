"""Unit tests for audit_vanishing_criterion.py: positive and negative controls."""

import io
import unittest
from fractions import Fraction as Fr

import audit_vanishing_criterion as a


def run_one(name):
    log = a.Log(io.StringIO())
    neg = {}
    a.run_arrangement(name, a.examples(True)[name], log, neg)
    return log, neg


class TestPrimitives(unittest.TestCase):
    def test_counts(self):
        # chambers and top-cones of A2, A3, B2, B3
        for name, ch, cones in (("A2", 6, 19), ("A3", 24, 219), ("B2", 8, 33), ("B3", 48, 941)):
            N, d, _ = a.examples(True)[name]
            A = a.Arr(N, d)
            self.assertEqual(A.nch, ch, name)
            self.assertEqual(len(a.all_cones(A)), cones, name)

    def test_lie4_character(self):
        N, d, _, pm = a.braid(4)
        A = a.Arr(N, d)
        for ct, val in (([1, 1, 1, 1], 6), ([2, 1, 1], 0), ([2, 2], -2), ([3, 1], 0), ([4], 0)):
            g = pm(a.perm_of_type(ct))
            self.assertEqual(a.chi_def(A, a.Sym(A, g), {}), val, ct)

    def test_order_of_minus_w(self):
        self.assertEqual(a.ord_on_sum_zero([3], -1), 6)
        self.assertEqual(a.ord_on_sum_zero([2, 1], -1), 2)
        # negative control: at n = 2, -(12) is the identity of R^2_0
        self.assertEqual(a.ord_on_sum_zero([2], -1), 1)


class TestTheorems(unittest.TestCase):
    def test_small_arrangements(self):
        for name in ("A2", "B2", "rank1", "coord2", "tri2"):
            log, neg = run_one(name)
            self.assertEqual(log.fails, {}, (name, log.examples))
            self.assertGreater(log.counts["[Z]"], 0)

    def test_formula_Z_negative_controls(self):
        log, neg = run_one("A3")
        self.assertEqual(log.fails, {})
        for var in ("m_one", "no_meet", "no_transverse", "nonminimal_witness"):
            self.assertGreater(neg[var][1], 0, var)

    def test_tri2_cancellation(self):
        # a reflection whose mirror is not a hyperplane of A: not sign-coherent,
        # and the half-plane y >= 0 cancels (Cor. PC(c) needs the mirror hypothesis)
        N, d, _ = a.examples(True)["tri2"]
        A = a.Arr(N, d)
        s = a.as_mat(((-1, 0), (0, 1)))
        gs = a.Sym(A, s)
        gd = a.GData(A, gs)
        cons = {0: 1}
        self.assertEqual(a.chi_def(A, gs, cons), 0)
        terms = sorted((A.dim(S), gd.mu[S], gd.m_X(S, cons)) for S in gd.zstar)
        self.assertEqual(terms, [(0, 1, 1), (1, -1, 1)])

    def test_coord2_reflection(self):
        # S3's "iff R alpha is a flat" fails without the mirror hypothesis
        log, neg = run_one("coord2")
        self.assertGreater(neg["S3_without_mirror_hyp"][1], 0)

    def test_type_A_partitions(self):
        log = a.Log(io.StringIO())
        neg = {}
        a.run_typeA_partitions(log, 5, neg)
        self.assertEqual(log.fails, {}, log.examples)
        self.assertGreater(neg["A-_drop_parity_condition"][1], 0)
        self.assertGreater(neg["ord_n2"][1], 0)

    def test_stated_rule_examples(self):
        for ct, val in (([3, 3], True), ([6], True), ([2, 2, 1, 1], True),
                        ([4], False), ([3, 1], False), ([3, 3, 1], False),
                        ([6, 3], True), ([9], False)):
            self.assertEqual(a.stated_rule(ct, -1), val, ct)

    def test_b3_coxeter(self):
        N, d, _ = a.typeB(3)
        A = a.Arr(N, d, faces=False)
        c = a.as_mat(((0, 0, -1), (1, 0, 0), (0, 1, 0)))
        gd = a.GData(A, a.Sym(A, c))
        self.assertEqual(sorted(A.dim(S) for S in gd.fixed), [0, 1, 3])
        self.assertEqual(gd.mu[frozenset()], 0)


if __name__ == "__main__":
    unittest.main()
