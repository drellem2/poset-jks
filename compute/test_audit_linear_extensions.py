"""Unit tests for audit_linear_extensions.py: positive and negative controls."""

import unittest

import audit_linear_extensions as a


def V():
    return a.Poset.from_relations(3, [(0, 1), (0, 2)])


class TestPromotion(unittest.TestCase):
    def test_stanley_figure_1(self):
        # Stanley, Promotion and evacuation, Fig. 1: on a chain promotion is
        # the identity, on an antichain it is rotation.
        C = a.chain(4)
        self.assertEqual(a.promote_jdt(C, (0, 1, 2, 3)), (0, 1, 2, 3))
        A = a.antichain(4)
        self.assertEqual(a.promote_jdt(A, (2, 0, 3, 1)), (0, 3, 1, 2))

    def test_jdt_equals_toggles(self):
        for P in a.all_posets(5)[5]:
            self.assertTrue(a.check_jdt(P, a.lin_ext(P)))

    def test_rectangle_order(self):
        # Schuetzenberger/Haiman: promotion on SYT of a rectangle has order n
        P = a.shape_poset(a.young((3, 3)))
        self.assertEqual(a.promotion_order(P, a.lin_ext(P)), 6)

    def test_toggle_negative_control(self):
        # toggling in the wrong order (tau_1 last) is not promotion
        P = a.disjoint_union(a.chain(2), a.chain(1))
        w = (0, 1, 2)
        x = list(w)
        for i in reversed(range(2)):
            if not P.comparable(x[i], x[i + 1]):
                x[i], x[i + 1] = x[i + 1], x[i]
        self.assertNotEqual(tuple(x), a.promote_jdt(P, w))


class TestGeneration(unittest.TestCase):
    def test_counts(self):
        ps = a.all_posets(5)
        self.assertEqual([len(ps[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])


class TestLemmaP(unittest.TestCase):
    def test_VV(self):
        P = a.disjoint_union(V(), V())
        ok, n = a.check_lemma_P(P, a.lin_ext(P))
        self.assertTrue(ok)
        self.assertGreater(n, 0)
        self.assertTrue(a.check_P1(P, a.lin_ext(P)))
        self.assertTrue(a.check_P2(P, a.lin_ext(P)))


class TestTheoremR(unittest.TestCase):
    def test_hypothesis_needed(self):
        P = a.disjoint_union(V(), V())
        self.assertFalse(a.hypothesis_R(P))
        self.assertFalse(a.refinement(P, a.lin_ext(P)))

    def test_holds(self):
        P = a.disjoint_union(a.chain(2), a.chain(2), a.chain(2))
        self.assertTrue(a.hypothesis_R(P))
        self.assertTrue(a.refinement(P, a.lin_ext(P)))


class TestPropositions(unittest.TestCase):
    def test_O(self):
        P = a.disjoint_union(V(), V())
        self.assertTrue(a.check_O(P, a.lin_ext(P)))

    def test_E(self):
        self.assertTrue(a.orbits_equal_classes(a.antichain(4), a.lin_ext(a.antichain(4))))
        P = a.disjoint_union(a.chain(2), a.chain(1))
        self.assertFalse(a.orbits_equal_classes(P, a.lin_ext(P)))

    def test_D(self):
        A = a.antichain(3)
        self.assertTrue(a.promotion_preserves_kernel(A, a.lin_ext(A)))
        P = a.disjoint_union(a.chain(2), a.chain(1))
        self.assertFalse(a.promotion_preserves_kernel(P, a.lin_ext(P)))

    def test_F(self):
        P = a.disjoint_union(a.chain(2), a.chain(2), a.chain(2))
        self.assertEqual(a.eC(P), 74)
        self.assertEqual(a.cumulant(P), 74)
        self.assertTrue(a.check_F(a.disjoint_union(V(), V()), a.lin_ext(a.disjoint_union(V(), V()))))


class TestCSP(unittest.TestCase):
    def test_qmultinomial(self):
        self.assertEqual(a.qmultinomial([2, 2]), [1, 1, 2, 1, 1])

    def test_rsw(self):
        ok, n = a.check_rsw(6)
        self.assertTrue(ok)

    def test_negative_control(self):
        P = a.disjoint_union(a.chain(2), a.chain(2))
        lin = a.lin_ext(P)
        X = a.qmultinomial([2, 2])
        self.assertTrue(a.csp_holds(P, lin, X))
        self.assertFalse(a.csp_holds(P, lin, [0] + X))

    def test_theorem_U(self):
        P = a.disjoint_union(a.shape_poset(a.young((2, 2))), a.chain(1))
        self.assertEqual(a.theorem_U(P, a.lin_ext(P)), (True, True))


class TestTheoremM(unittest.TestCase):
    def test_C2C2(self):
        P = a.disjoint_union(a.chain(2), a.chain(2))
        lin = a.lin_ext(P)
        sp, gens, index = a.RP_span(P, lin)
        self.assertEqual(sp.dim(), len(lin) - a.eC(P, lin))
        self.assertTrue(a.homogeneous(sp, gens, index, lambda w: a.restrictions(P, w)))
        lab = a.natural_labelling(P)
        self.assertFalse(a.homogeneous(sp, gens, index, lambda w: a.des(w, lab)))

    def test_span(self):
        s = a.Span()
        self.assertTrue(s.add({0: 1, 1: 2}))
        self.assertFalse(s.add({0: 2, 1: 4}))
        self.assertTrue(s.contains({0: 3, 1: 6}))
        self.assertFalse(s.contains({0: 1}))


if __name__ == "__main__":
    unittest.main()
