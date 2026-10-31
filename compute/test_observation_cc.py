"""Unit tests for observation_cc.py (notes/observation_cc.md).  ~5 s.

Positive controls: CC on known lattices, Prop. A on W+1/W+2/W-1, Prop. B on a
W-4 pair, every check on all pairs with n <= 5.
Negative controls: CC fails on Pi_4 and on the CR_V counterexample's 8-element
model lattice; Prop. A's predicate with c replaced by 0 misses zeros; on a W-4
pair the predicate c ^ D != 0 is false (so the atom side is needed).
"""
import unittest

import cr_v_type_a as C
import observation_cc as O


def pair(P, eps, t):
    return O.analyse_pair(P, eps, t, None, C.pair_index(P.n))


class TestCC(unittest.TestCase):
    def test_chain_and_partition_lattice(self):
        r = pair(C.antichain(4), 1, (1, 2, 3, 0))
        self.assertEqual((r['mu'], r['cc']), (0, True))
        r = pair(C.antichain(4), 1, (0, 1, 2, 3))
        self.assertEqual((r['mu'], r['cc']), (-6, False))

    def test_two_element_lattice_is_not_cc(self):
        r = pair(C.antichain(3), 1, (1, 2, 0))       # Pi_3^{(012)} = {0, 1}
        self.assertEqual((r['size'], r['mu'], r['cc']), (2, -1, False))

    def test_D_partition(self):
        # antichain 4, w = (01)(23): components are points, lambda = 2, r = 2, D = 0
        D, r = O.D_partition(4, (0, 1, 2, 3), (1, 0, 3, 2))
        self.assertEqual((D, r), ((0, 1, 2, 3), 2))
        # antichain 4, w = (0123): lambda = 4, r = 2, D = {02, 13}
        D, r = O.D_partition(4, (0, 1, 2, 3), (1, 2, 3, 0))
        self.assertEqual((D, r), ((0, 1, 0, 1), 2))

    def test_prop_A_W1_two_cycle_lengths(self):
        # antichain 3, +(01): not free, c ^ D = 01|2 != 0
        r = pair(C.antichain(3), 1, (1, 0, 2))
        self.assertTrue(r['pred'] and r['low'] and r['mu'] == 0 and r['row'] == 'W+1')

    def test_prop_B_W4(self):
        # 2-chain 0 < 1 plus isolated 2; t = (01)(2) anti-automorphism: odd point 2 isolated
        P = C.Poset(3, [(0, 1)])
        r = pair(P, -1, (1, 0, 2))
        self.assertEqual(r['row'], 'W-4')
        self.assertFalse(r['w4_fail'])
        self.assertTrue(r['high'])

    def test_W4_needs_atom_side(self):
        found = False
        levels = C.posets_up_to_iso(5)
        for rel in levels[5]:
            P = C.Poset(5, rel)
            auts, antis = C.symmetries(P)
            for t in C.conj_classes(antis, auts):
                r = pair(P, -1, t)
                if r['row'] == 'W-4' and not r['low']:
                    found = True
                    self.assertTrue(r['high'] and not r['pred'])
        self.assertTrue(found)

    def test_sweep_n5_no_failures(self):
        levels = C.posets_up_to_iso(5)
        for n in range(3, 6):
            O._init(n)
            for rel in levels[n]:
                for r in O._work(rel):
                    self.assertEqual(r['cc'], r['mu'] == 0)
                    for k in ('cd_fail', 'ck_fail', 'a_fail', 'u_fail', 'zl_fail', 'w4_fail'):
                        self.assertFalse(r[k], (k, r))

    def test_fault_injection_fires(self):
        hits = 0
        levels = C.posets_up_to_iso(4)
        for n in range(3, 5):
            for rel in levels[n]:
                P = C.Poset(n, rel)
                auts, antis = C.symmetries(P)
                for eps, elems in ((1, auts), (-1, antis)):
                    for t in C.conj_classes(elems, auts):
                        hits += O.analyse_pair(P, eps, t, None, C.pair_index(n), fault=True)['zl_fail']
        self.assertGreater(hits, 0)

    def test_extra(self):
        self.assertTrue(O.part_EXTRA())


if __name__ == '__main__':
    unittest.main()
