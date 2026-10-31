import io
import unittest

import cyclic_sieving_cyc as m
import n7_sweep


def copies(rel, size, k):
    return m.Poset(*m.disjoint_copies(rel, size, k))


class TestCyclicSievingCyc(unittest.TestCase):
    def setUp(self):
        m.FAILS.clear()

    def test_controls(self):
        m.section_ctl(io.StringIO())
        self.assertEqual(m.FAILS, [])

    def test_antichain_4(self):
        P = m.Poset(frozenset(), 4)
        X = m.fake_degree(P)
        self.assertEqual(X, [1, 0, 1, 1, 2, 1])
        self.assertEqual(sum(X), P.eC)
        sigma = (1, 2, 3, 0)
        self.assertEqual(P.fix_data(sigma), [6, 2, 2, 2])
        self.assertTrue(m.sieves(X, P.fix_data(sigma)))
        # double transposition: semiregular, sieves; transposition: does not
        self.assertTrue(m.sieves(X, P.fix_data((1, 0, 3, 2))))
        self.assertFalse(m.sieves(X, P.fix_data((1, 0, 2, 3))))
        self.assertFalse(m.criterion_W(P, (1, 0, 2, 3)))
        self.assertTrue(m.criterion_W(P, (1, 0, 3, 2)))

    def test_closed_form_two_chains(self):
        rel, n = n7_sweep.chain(2)
        cs = {0: 1}
        for k in range(1, 4):
            cs[k] = copies(rel, n, k).eC
        self.assertEqual(cs, {0: 1, 1: 1, 2: 5, 3: 74})
        P = copies(rel, n, 3)
        self.assertEqual(m.fake_degree(P), m.closed_form_tk(cs, 3))
        self.assertEqual(m.fake_degree(P), [13, 24, 24, 13])

    def test_regularity(self):
        # S_4: 4-cycle and (3,1) regular, (2,1,1) not
        self.assertEqual(m.is_regular([1], [[(4, 0)]]), 4)
        self.assertEqual(m.is_regular([1], [[(3, 0), (1, 0)]]), 3)
        self.assertIsNone(m.is_regular([1], [[(2, 0), (1, 0), (1, 0)]]))
        # G(2,1,2) = B_2: (a, 1; swap) has order 4 and is regular
        self.assertEqual(m.is_regular([2], [[(2, 1)]]), 4)

    def test_negative_control_perturbed(self):
        P = m.Poset(frozenset(), 3)
        X = m.fake_degree(P)
        self.assertTrue(m.sieves(X, P.fix_data((1, 2, 0))))
        self.assertFalse(m.sieves(m.perturb(X), P.fix_data((1, 2, 0))))

    def test_obstruction_is_antichain_4(self):
        out = io.StringIO()
        n, rel, bad = m.section_obst(out, 4)
        self.assertEqual((n, rel), (4, []))
        self.assertEqual(sorted(bad[2]), [(6, 0), (6, 2)])


if __name__ == "__main__":
    unittest.main()
