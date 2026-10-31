"""Unit tests for audit_per_cone_vanishing.py: positive and negative controls."""

import unittest
from fractions import Fraction as Fr

import audit_per_cone_vanishing as a


def antichain(n):
    return a.Poset(n, [])


class TestPal(unittest.TestCase):
    def test_swap_and_cycle(self):
        P = antichain(4)
        self.assertEqual(a.pal_count(P, (1, 0, 3, 2)), a.pal_brute(P, (1, 0, 3, 2)))
        self.assertGreater(a.pal_count(P, (1, 0, 3, 2)), 0)
        # a 4-cycle is an anti-automorphism of the antichain but not an
        # involution: no palindromic extension (this caught a search bug)
        self.assertEqual(a.pal_count(P, (1, 2, 3, 0)), 0)
        self.assertEqual(a.pal_brute(P, (1, 2, 3, 0)), 0)

    def test_two_fixed_points(self):
        P = antichain(3)
        self.assertEqual(a.pal_count(P, (0, 1, 2)), 0)
        self.assertEqual(a.pal_count(antichain(1), (0,)), 1)

    def test_chain(self):
        P = a.Poset(3, [(0, 1), (1, 2)])
        self.assertEqual(a.anti_automorphisms(P), [(2, 1, 0)])
        self.assertEqual(a.pal_count(P, (2, 1, 0)), 1)

    def test_poset_counts(self):
        lv = a.all_posets(5)
        self.assertEqual([len(lv[n]) for n in range(6)], [1, 1, 2, 5, 16, 63])


class TestTypeA(unittest.TestCase):
    def test_A2_cancelling_pair(self):
        P = antichain(3)
        t = (1, 0, 2)
        self.assertEqual(a.chi_face_poset(P, t), 0)
        res, m = a.ta_conditions(P, t)
        self.assertTrue(res["TA1"] and res["TA2"] and res["TA3"])
        self.assertFalse(res["TA4"])
        # negative control: (TA1)-(TA3) alone predict nonzero here (n = 3)
        self.assertTrue(a.zstar_nonzero_mu(P, t))

    def test_minus_identity(self):
        # -id on all chambers of A_{n-1}: chi = mu(Pi_n) = (-1)^{n-1}(n-1)!
        for n, val in ((3, 2), (4, -6)):
            self.assertEqual(a.chi_face_poset(antichain(n), tuple(range(n))), val)
            self.assertEqual(a.closed_formula(antichain(n), tuple(range(n))), val)

    def test_note_revival_example(self):
        P = a.Poset(5, [(0, 1), (1, 2)])
        t = (2, 1, 0, 3, 4)
        self.assertEqual(a.chi_face_poset(P, t), 2)
        self.assertEqual(a.closed_formula(P, t), 2)

    def test_two_face_models_agree(self):
        P = a.Poset(4, [(0, 1), (2, 3)])
        for t in a.anti_automorphisms(P):
            self.assertEqual(a.chi_face_poset(P, t), a.chi_stable_spans(P, t))

    def test_not_stable_rejected(self):
        # +id is not -tau-stable data for a chain: g V != V must be detected
        P = a.Poset(3, [(0, 1), (1, 2)])
        with self.assertRaises(AssertionError):
            a.chi_face_poset(P, (0, 1, 2))

    def test_case_IIb_needs_S2m(self):
        # antichain on 4 points, tau = (0 1)(2 3): Case IIb
        P = antichain(4)
        t = (1, 0, 3, 2)
        val, det = a.closed_formula(P, t, detail=True)
        self.assertEqual(det["case"], "IIb")
        self.assertNotEqual(det["S2m"], 0)
        self.assertEqual(val, a.chi_face_poset(P, t))
        self.assertNotEqual(val - det["S2m"], a.chi_face_poset(P, t))

    def test_crapo_element(self):
        P = a.Poset(4, [(0, 1)])
        t = (1, 0, 2, 3)
        n = 4
        fixed = [p for p in a.tau_stable_partitions(n, t) if a.has_face_with_span(P, p)]
        A0 = frozenset([frozenset([0, 1]), frozenset([2]), frozenset([3])])
        bottom = frozenset([frozenset(range(n))])
        top = frozenset(frozenset([i]) for i in range(n))
        self.assertEqual(a.lattice_complements(fixed, a.partition_leq_flat, A0,
                                               bottom, top), [])
        # positive control: the singleton-split {0,1},{2,3} ... has complements
        b = frozenset([frozenset([0]), frozenset([1]), frozenset([2, 3])])
        self.assertIn(b, fixed)
        self.assertNotEqual(a.lattice_complements(fixed, a.partition_leq_flat, b,
                                                  bottom, top), [])
        self.assertEqual(a.chi_face_poset(P, t), 0)

    def test_lambda_not_intersection_closed(self):
        P = a.Poset(4, [(0, 2), (1, 3)])
        lam = {frozenset(f) for f in a.faces_of_cone(P)}
        p = frozenset([frozenset([0, 3]), frozenset([1]), frozenset([2])])
        q = frozenset([frozenset([1, 2]), frozenset([0]), frozenset([3])])
        self.assertIn(p, lam)
        self.assertIn(q, lam)
        self.assertNotIn(a.join_part(p, q, 4), lam)   # X_p cap X_q
        self.assertIn(a.meet_part(p, q), lam)         # flat closure of X_p + X_q


class TestLemmaE(unittest.TestCase):
    def test_connected(self):
        self.assertEqual(a.connected_count((1, 1)), 1)        # one 2-cycle
        self.assertEqual(a.connected_brute((2, 1)), a.connected_count((2, 1)))
        self.assertEqual(a.connected_count((0, 1)), 0)
        self.assertEqual(a.connected_count((0,)), 1)


class TestLemmaM(unittest.TestCase):
    def setUp(self):
        self.arr = a.Arrangement("A_2", [(1, 0), (0, 1), (1, 1)])

    def test_all_pass(self):
        st = a.check_lemma_M(self.arr)
        self.assertEqual(st["elements"], 12)

    def test_negative_controls(self):
        """dropping the sign (-1)^{dim U}, or the condition Z cap U = 0,
        breaks Lemma M on A_2 for -id (U = 0 is excluded) and reflections."""
        arr = self.arr
        broke_sign = broke_cond = False
        for G, sigma in arr.symmetries():
            d = arr.d
            M = [S for S in arr.flats if a.flat_image(sigma, S) == S]
            Ub = a.nullspace([[G[i][j] - (i == j) for j in range(d)]
                              for i in range(d)], d)
            if len(Ub) != 1:
                continue
            mutop = {Z: a.mu_bottom_top(M, a.Arrangement.leq, Z, arr.top) for Z in M}

            def zero(S):
                Xb = arr.basis(S)
                return a.rank(Xb + Ub) == len(Xb) + len(Ub)
            X = arr.bottom      # the flat 0 is in Z*(g) iff U in no line
            if any(all(sum(x * y for x, y in zip(arr.normals[h], u)) == 0 for u in Ub)
                   for h in range(arr.nh)):
                continue
            m = 1 if len(Ub) == 1 else None   # A_X|_U: points in a line, mu = -1
            good = -sum(mutop[Z] for Z in M if zero(Z))
            self.assertEqual(good, m)
            broke_sign |= sum(mutop[Z] for Z in M if zero(Z)) != m
            broke_cond |= -sum(mutop[Z] for Z in M) != m
        self.assertTrue(broke_sign)
        self.assertTrue(broke_cond)


if __name__ == "__main__":
    unittest.main()
