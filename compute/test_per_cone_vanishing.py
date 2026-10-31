"""Tests for per_cone_vanishing.py, with positive and negative controls
(run from compute/)."""

import itertools
import unittest

import per_cone_vanishing as pc


def chain(n):
    return frozenset((i, j) for i in range(n) for j in range(i + 1, n))


def chi(n, rel, t):
    return pc.sgn_perm(t) * pc.mu_OP(n, rel, t)


class Lattices(unittest.TestCase):
    def test_complement_instrument(self):
        # chain 0 < a < 1: a has no complement, mu = 0
        el = [0, 1, 2]
        mu, unc = pc.lattice_info(el, lambda a, b: a <= b)
        self.assertEqual((mu, unc), (0, True))
        # Boolean lattice B_2: complemented, mu = 1
        el = [frozenset(s) for s in [(), (1,), (2,), (1, 2)]]
        mu, unc = pc.lattice_info(el, lambda a, b: a <= b)
        self.assertEqual((mu, unc), (1, False))

    def test_tau_stable_partitions(self):
        t = (1, 0, 3, 2, 4)
        a = set(pc.tau_stable_partitions(5, t))
        b = set()
        for p in pc.setparts(list(range(5))):
            fs = frozenset(frozenset(B) for B in p)
            if frozenset(frozenset(t[x] for x in B) for B in fs) == fs:
                b.add(fs)
        self.assertEqual(a, b)

    def test_pal_count(self):
        # chain 0<1<2 reversed: one palindromic extension; antichain {0,1} swapped: 2
        self.assertEqual(pc.pal_count(range(3), chain(3), (2, 1, 0)), 1)
        self.assertEqual(pc.pal_count(range(2), frozenset(), (1, 0)), 2)
        # one fixed point: 0 in the middle, 1 2 / 2 1 outside; three fixed points: none (Lemma Pal)
        self.assertEqual(pc.pal_count(range(3), frozenset(), (0, 2, 1)), 2)
        self.assertEqual(pc.pal_count(range(3), frozenset(), (0, 1, 2)), 0)

    def test_conn_perm(self):
        self.assertEqual(pc.conn_perm([2]), 2)
        self.assertEqual(pc.conn_perm([1, 1]), 1)          # the 2-cycle only
        self.assertEqual(pc.conn_perm([1, 0]), 0)          # an empty group is never joined
        self.assertEqual(pc.conn_perm([1, 1, 1]), 2)       # 3!-3*1-... = the two 3-cycles


class TypeA(unittest.TestCase):
    def test_smallest_cancellation(self):
        # A_2, all chambers, g = -(1 2): chi = 0, cancelled by the isolated fixed point
        rel, t = frozenset(), (1, 0, 2)
        self.assertEqual(chi(3, rel, t), 0)
        self.assertEqual(pc.chi_closed(3, rel, t), 0)
        self.assertFalse(pc.rule(3, rel, t))

    def test_non_isolated_fixed_point_revives(self):
        # chain 0<1<2 plus two isolated points, tau = (0 2): nonzero although 3, 4 are fixed
        rel, t = chain(3), (2, 1, 0, 3, 4)
        self.assertEqual(chi(5, rel, t), 2)
        self.assertEqual(pc.chi_closed(5, rel, t), 2)

    def test_exhaustive_n5(self):
        for rel in pc.iso_classes(5):
            for t in pc.antiauts(5, rel):
                c = chi(5, rel, t)
                self.assertEqual(c, pc.chi_closed(5, rel, t))
                self.assertEqual(c != 0, pc.rule(5, rel, t))

    def test_negative_control_drop_TA4(self):
        """Without (TA4) the criterion misclassifies the isolated-fixed-point zeros."""
        bad = 0
        for rel in pc.iso_classes(4):
            for t in pc.antiauts(4, rel):
                cs = pc.cycles(t)
                O = {x for c in cs if len(c) % 2 for x in c}
                iso = {x for K in pc.comps(4, rel) if len(K) == 1 for x in K}
                weak = pc.rule(4, rel, t) or (
                    O and O <= iso and any(len(c) % 2 == 0 for c in cs)
                    and all(len(c) in (1, 2) for c in cs)
                    and all(len(K & O) <= 1 for K in pc.comps(4, rel)))
                bad += bool(weak) != (chi(4, rel, t) != 0)
        self.assertGreater(bad, 0)

    def test_negative_control_case_IIb_needs_correction(self):
        """In case IIb the l = 2m term of CF is needed: without it the value is wrong."""
        rel, t = frozenset(), (1, 0, 3, 2)          # -(12)(34) on all chambers of A_3
        self.assertEqual(pc.case_of(4, rel, t), 'IIb')
        self.assertEqual(chi(4, rel, t), pc.chi_closed(4, rel, t))
        hs = [1, 1]
        naive = 1 * 1 * pc.conn_perm(hs) * 2 * 2      # the l = m part alone
        self.assertNotEqual(naive, chi(4, rel, t))

    def test_sign_rule(self):
        for rel in pc.iso_classes(5):
            for t in pc.antiauts(5, rel):
                c = chi(5, rel, t)
                if c:
                    self.assertEqual(c > 0, pc.sign_rule(t) > 0)

    def test_crapo_obstruction_element(self):
        """P = Q + antichain of fixed points, tau fixed-point-free on Q: the partition
        {Q} + singletons has no complement in OP(P)^tau."""
        rel = frozenset({(0, 1)})                  # Q = {0 < 1}, A = {2, 3}
        t = (1, 0, 2, 3)
        parts = pc.fixed_OP(4, rel, t)
        a = frozenset([frozenset({0, 1}), frozenset({2}), frozenset({3})])
        self.assertIn(a, parts)
        bot = frozenset(frozenset([x]) for x in range(4))
        top = frozenset([frozenset(range(4))])

        def meet(p, q):
            cands = [r for r in parts if pc.refines(r, p) and pc.refines(r, q)]
            return [r for r in cands if all(pc.refines(s, r) for s in cands)][0]

        def join(p, q):
            cands = [r for r in parts if pc.refines(p, r) and pc.refines(q, r)]
            return [r for r in cands if all(pc.refines(r, s) for s in cands)][0]
        self.assertFalse(any(meet(a, x) == bot and join(a, x) == top for x in parts))


class Arrangement(unittest.TestCase):
    def test_typeA_arrangement_link(self):
        self.assertTrue(pc.part_TAarr(True))


if __name__ == '__main__':
    unittest.main()
