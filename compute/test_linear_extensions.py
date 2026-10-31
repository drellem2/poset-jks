import io
import unittest

import linear_extensions as m
import n7_sweep


def small_posets(nmax):
    allp = n7_sweep.unlabeled_posets(nmax)
    return {n: allp[n] for n in range(1, nmax + 1)}


class TestLinearExtensions(unittest.TestCase):
    def setUp(self):
        m.FAILS.clear()

    def test_promotion_antichain_is_rotation(self):
        lt = m.less_matrix(frozenset(), 4)
        self.assertEqual(m.promote((2, 0, 3, 1), lt), (0, 3, 1, 2))

    def test_promotion_two_chains_rotates_pattern(self):
        rel, n = m.disjoint_union(m.chain(2), m.chain(1))   # a1 < a2, c = 2
        lt = m.less_matrix(rel, n)
        self.assertEqual(m.promote((0, 1, 2), lt), (0, 2, 1))
        self.assertEqual(m.promote((0, 2, 1), lt), (2, 0, 1))
        self.assertEqual(m.promote((2, 0, 1), lt), (0, 1, 2))

    def test_q_hook_and_rhoades_2x3(self):
        rel, n = m.rectangle(2, 3)
        lin = m.linexts(rel, n)
        lt = m.less_matrix(rel, n)
        pm = {w: m.promote(w, lt) for w in lin}
        X = m.q_hook([3, 3])
        self.assertEqual(sum(X), 5)
        self.assertTrue(m.csp_holds(m.fixed_counts(pm, n), X, n))
        self.assertFalse(m.csp_holds(m.fixed_counts(pm, n), [0] + X, n))

    def test_e_C_examples(self):
        self.assertEqual(m.e_C(frozenset(), 4), 6)          # (n-1)!
        rel, n = m.disjoint_union(m.chain(2), m.chain(2))
        self.assertEqual(m.e_C(rel, n), 5)
        rel, n = m.disjoint_union(m.chain(2), m.chain(2), m.chain(2))
        self.assertEqual(m.e_C(rel, n), 74)

    def test_sections_small(self):
        P = small_posets(5)
        out = io.StringIO()
        m.section_csp(P, out)
        dK, dR = m.section_promo(P, out, 5)
        m.section_count(P, out, 5)
        m.section_burnside(P, out)
        m.section_struct(P, out, 5)
        self.assertEqual(m.FAILS, [])
        # promotion descends to PLie(P) only for antichains
        self.assertTrue(all(covers == [] for _, covers in dK))
        self.assertEqual(len(dK), 4)


if __name__ == "__main__":
    unittest.main()
