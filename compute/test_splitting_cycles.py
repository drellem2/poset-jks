#!/usr/bin/env python3
"""Tests for splitting_cycles.py.  Run: python3 -m unittest test_splitting_cycles"""

import itertools
import math
import unittest

import poset_jks_check as pj
import splitting_cycles as sc


def chain(n):
    return frozenset((i, j) for i in range(n) for j in range(i + 1, n))


class SplittingCycles(unittest.TestCase):
    def test_rho_is_cycle_and_normalized(self):
        for n in (4, 5):
            w = (2, 0, 3, 1, 4)[:n] if n == 5 else (2, 0, 3, 1)
            r = sc.rho(w)
            self.assertEqual(sc.boundary(r), {})
            m_w = tuple(sc.split_partition(w, set(range(1, k + 1))) for k in range(1, n - 1))
            self.assertEqual(r[m_w], 1)
            self.assertEqual(len(r), math.factorial(n - 1))  # one chain per order of cuts

    def test_signed_shuffles_vanish_unsigned_do_not(self):
        n = 4
        rhos = {w: sc.rho(w) for w in itertools.permutations(range(n))}
        s = dict.fromkeys(sc.shuffles((0, 2), (1, 3)), 1)
        signed, unsigned = {}, {}
        for w, c in s.items():
            sc.add_scaled(signed, rhos[w], c * pj.sign(w))
            sc.add_scaled(unsigned, rhos[w], c)
        self.assertFalse({k: v for k, v in signed.items() if v})
        # positive control: dropping the sign twist must break the relation
        self.assertTrue({k: v for k, v in unsigned.items() if v})

    def test_rank_mod_p_control(self):
        self.assertEqual(sc.rank_mod_p([{0: 1, 1: 2}, {0: 2, 1: 4}, {1: 1}]), 2)

    def test_chain_and_dual_share_OP_but_not_W_e_zeta(self):
        for n in (3, 4, 5):
            c, cop = chain(n), sc.opposite(chain(n))
            self.assertEqual(set(pj.order_preserving_partitions(c, n)),
                             set(pj.order_preserving_partitions(cop, n)))
            p = sc.prime_1_mod(60)
            ez = sc.e_zeta(n, sc.root_of_unity(n, p), p)
            ident, w0 = tuple(range(n)), tuple(reversed(range(n)))
            self.assertEqual(pj.linear_extensions(cop, n), [w0])
            self.assertFalse(sc.proportional(sc.mul({ident: 1}, ez, p), sc.mul({w0: 1}, ez, p), p))

    def test_linear_extension_splitting_cycles_span_n4(self):
        out = []
        self.assertTrue(sc.check_posets(4, out))

    def test_comb_coordinates_kill_shuffles_n5(self):
        coords = sc.comb_coordinates(5)
        for s in sc.proper_shuffle_elements(5)[:60]:
            acc = {}
            for w, c in s.items():
                for j, v in coords.get(w, {}).items():
                    acc[j] = acc.get(j, 0) + c * v
            self.assertFalse(any(acc.values()))


if __name__ == "__main__":
    unittest.main()
