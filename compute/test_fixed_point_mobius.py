#!/usr/bin/env python3
"""Tests for fixed_point_mobius.py.  Run: python3 -m unittest test_fixed_point_mobius"""

import unittest
from collections import Counter

import fixed_point_mobius as fm
import poset_jks_check as pj


def chains(m, length):
    rel = set()
    for c in range(m):
        base = c * length
        rel |= {(base + i, base + j) for i in range(length) for j in range(i + 1, length)}
    return frozenset(rel), m * length


class Helpers(unittest.TestCase):
    def test_num_moebius(self):
        self.assertEqual([fm.num_moebius(d) for d in range(1, 13)],
                         [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0])

    def test_transversals_two_chains(self):
        rel, n = chains(2, 2)          # {0<1}, {2<3}; g swaps the chains
        g = (2, 3, 0, 1)
        Ts = fm.transversals(rel, n, g, 0)
        self.assertEqual([T for T, _ in Ts], [frozenset({0, 1})])

    def test_transversals_antichain(self):
        g = (1, 0, 3, 2)               # type 2^2 on the 4-antichain
        Ts = fm.transversals(frozenset(), 4, g, 0)
        self.assertEqual(sorted(sorted(T) for T, _ in Ts), [[0, 2], [0, 3]])


class Checks(unittest.TestCase):
    def run_one(self, rel, n):
        stats, fails = Counter(), []
        fm.analyse(rel, n, stats, fails, "t")
        return stats, fails

    def test_three_two_chains(self):
        """The seed note's n = 6 example: the 3-cycle on components has
        mu(OP(P)^g) = mu(3) * mu(OP(2-chain)) = (-1)(-1) = 1."""
        rel, n = chains(3, 2)
        g = (2, 3, 4, 5, 0, 1)
        L = [pi for pi in pj.order_preserving_partitions(rel, n)
             if pj.act_partition(g, pi) == pi]
        self.assertEqual(pj.moebius_bottom_top(L, n), 1)
        stats, fails = self.run_one(rel, n)
        self.assertEqual(fails, [])
        self.assertGreater(stats["L3"], 0)

    def test_connected_vanishing(self):
        # crown / K_{3,3}: connected, large automorphism group
        k33 = frozenset((a, b) for a in range(3) for b in range(3, 6))
        stats, fails = self.run_one(k33, 6)
        self.assertEqual(fails, [])
        self.assertGreater(stats["L5"], 0)

    def test_all_n_le_5(self):
        stats, fails = Counter(), []
        posets = pj.unlabeled_posets_by_extension(5)
        for n in range(3, 6):
            for rel in posets[n]:
                fm.analyse(rel, n, stats, fails, "t")
        self.assertEqual(fails, [])

    def test_control_wrong_recursion_detected(self):
        """Positive control: without the mu(d) factor the recursion is wrong
        for the swapped pair of 2-chains (d = 2)."""
        rel, n = chains(2, 2)
        g = (2, 3, 0, 1)
        L = [pi for pi in pj.order_preserving_partitions(rel, n)
             if pj.act_partition(g, pi) == pi]
        mu = pj.moebius_bottom_top(L, n)
        s = sum(fm.mu_of_OP(*fm.induced(rel, T)) for T, _ in fm.transversals(rel, n, g, 0))
        self.assertEqual(mu, fm.num_moebius(2) * s)
        self.assertNotEqual(mu, s)


if __name__ == "__main__":
    unittest.main()
