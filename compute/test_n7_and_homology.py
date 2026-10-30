#!/usr/bin/env python3
"""Tests for n7_sweep.py and equivariant_homology.py.
Run: python3 -m unittest test_n7_and_homology"""

import itertools
import math
import unittest

import equivariant_homology as eh
import n7_sweep as sw
import poset_jks_check as pj


def lie_character(g):
    """Character of Lie_n at g (CITED closed form): mu(d) (n/d-1)! d^(n/d-1)
    if g has cycle type d^(n/d), else 0."""
    ct = pj.cycle_type(g)
    d = ct[0]
    if any(c != d for c in ct):
        return 0
    k = len(ct)
    return eh.mobius(d) * math.factorial(k - 1) * d ** (k - 1)


class Enumeration(unittest.TestCase):
    def test_counts_A000112_through_7(self):
        P = sw.unlabeled_posets(7)
        self.assertEqual([len(P[n]) for n in range(1, 8)], [1, 2, 5, 16, 63, 318, 2045])

    def test_fast_canonical_and_aut_agree_with_bruteforce(self):
        P = sw.unlabeled_posets(5)
        Q = pj.unlabeled_posets_by_extension(5)
        for n in range(1, 6):
            perms = list(itertools.permutations(range(n)))
            self.assertEqual(sorted(pj.canonical(r, n, perms) for r in P[n]),
                             sorted(pj.canonical(r, n, perms) for r in Q[n]))
            for r in P[n]:
                self.assertEqual(sw.automorphisms_fast(r, n), pj.automorphisms(r, n))

    def test_families_are_posets(self):
        for nm, (rel, m) in sw.families(7):
            self.assertTrue(pj.is_poset(rel, m), nm)


class Homology(unittest.TestCase):
    def test_op_matches_checker(self):
        rel = frozenset([(0, 1), (2, 3), (4, 5)])
        self.assertEqual(eh.Complex(rel, 6).opsize, 174)
        self.assertEqual(eh.Complex(frozenset(), 6).opsize, 203)

    def test_jks_positive_control(self):
        """Antichain: trace on H~_{n-3}(Pi_n bar) = sgn(g) chi_Lie_n(g)."""
        for n in (3, 4, 5, 6):
            cx = eh.Complex(frozenset(), n)
            G = list(itertools.permutations(range(n)))
            for cl in pj.conjugacy_classes(G):
                g = cl[0]
                h = eh.homology_trace(frozenset(), n, g, cx=cx)
                self.assertEqual(h["trace"], pj.sign(g) * lie_character(g), (n, g))

    def test_dimension_is_jenca_sarkoci(self):
        rel = frozenset([(0, 1), (2, 3), (4, 5)])
        h = eh.homology_trace(rel, 6, tuple(range(6)))
        self.assertEqual(h["dim"], 74)

    def test_three_two_chains_phase(self):
        rel = frozenset([(0, 1), (2, 3), (4, 5)])
        g = eh.parse_cycles("(1 3 5)(2 4 6)", 6)
        self.assertEqual(eh.homology_trace(rel, 6, g)["trace"], -1)

    def test_negative_control_corrupted_boundary(self):
        """Dropping one face map must change the answer (n=5 antichain and
        the three 2-chains with the phase-discriminating g)."""
        eh.CORRUPT = True
        try:
            h = eh.homology_trace(frozenset(), 5, tuple(range(5)))
            rel = frozenset([(0, 1), (2, 3), (4, 5)])
            k = eh.homology_trace(rel, 6, eh.parse_cycles("(1 3 5)(2 4 6)", 6))
        finally:
            eh.CORRUPT = False
        self.assertNotEqual(h["dim"], 24)
        self.assertNotEqual(k["trace"], -1)

    def test_two_distinct_primes(self):
        for m in (1, 2, 3, 4, 6, 7, 12):
            p = eh.prime_1_mod(m, 1_000_003)
            q = eh.prime_1_mod(m, p + 1)
            self.assertTrue(p % m == 1 % m and q % m == 1 % m and q > p >= 1_000_003)
        h = eh.homology_trace(frozenset(), 4, eh.parse_cycles("(1 2 3 4)", 4))
        self.assertEqual(len({r["p"] for r in h["runs"]}), 2)

    def test_parse_roundtrip(self):
        g = eh.parse_cycles("(1 3 5)(2 4 6)", 6)
        self.assertEqual(pj.cycle_str(g), "(1 3 5)(2 4 6)")


if __name__ == "__main__":
    unittest.main()
