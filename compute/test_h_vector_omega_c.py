#!/usr/bin/env python3
"""Unit tests for h_vector_omega_c.py.  Run from compute/:

    python3 -m unittest test_h_vector_omega_c
"""

import unittest
from math import comb

import h_vector_omega_c as H


def hC(rel, n):
    a, ok = H.omega_c_coeffs(frozenset(rel), n)
    assert ok
    return H.h_of_poly(a, n)


def cdes_dist(rel, n):
    rel = frozenset(rel)
    comp = H.components(rel, n)
    cls = H.classes(H.linexts(rel, n), comp)
    return H.trim(H.dist([H.cdes(c[0]) - 1 for c in cls]))


def eulerian(k):
    """Eulerian numbers A(k, j), j = 0..k-1 (des on S_k)."""
    import itertools
    if k == 0:
        return [1]
    c = [0] * k
    for w in itertools.permutations(range(k)):
        c[H.des(w)] += 1
    return c


class SmallValues(unittest.TestCase):
    def test_table(self):
        # survey table: A_3, C2+C1, C2+C2, A_4, C3+C1
        self.assertEqual(hC([], 3), [1, 1])
        self.assertEqual(hC([(0, 1)], 3), [1, 1])
        self.assertEqual(hC([(0, 1), (2, 3)], 4), [1, 3, 1])
        self.assertEqual(hC([], 4), [1, 4, 1])
        self.assertEqual(hC([(0, 1), (1, 2), (0, 2)], 4), [1, 2])

    def test_antichain_is_eulerian(self):
        for n in range(1, 6):
            self.assertEqual(hC([], n), eulerian(n - 1))

    def test_connected_is_des(self):
        rel = [(0, 1), (0, 3), (2, 3)]          # zigzag, connected
        lin = H.linexts(frozenset(rel), 4)
        self.assertEqual(hC(rel, 4), H.trim(H.dist([H.des(w) for w in lin])))


class MainTheorem(unittest.TestCase):
    def test_separated_examples(self):
        for rel, n in [([(0, 2), (1, 3)], 4),     # C2+C2, separated
                       ([(0, 2), (1, 3), (0, 4), (1, 4)], 6),
                       ([(0, 3), (1, 4)], 5)]:
            self.assertTrue(H.is_separated(frozenset(rel), n))
            self.assertEqual(cdes_dist(rel, n), hC(rel, n))

    def test_nonseparated_cdes_fails(self):
        # C2+C2 labelled 0<1, 2<3: not separated (2 > 1); cdes-1 gives 1,4
        rel = [(0, 1), (2, 3)]
        self.assertFalse(H.is_separated(frozenset(rel), 4))
        self.assertEqual(cdes_dist(rel, 4), [1, 4])
        self.assertEqual(hC(rel, 4), [1, 3, 1])

    def test_all_ascent_class_breaks_mindes(self):
        # 0<1, 3<4, 2 isolated: the class of 3041|2 is all-ascent
        rel = frozenset([(0, 1), (3, 4)])
        comp = H.components(rel, 5)
        self.assertTrue(H.all_ascent((3, 0, 4, 1, 2), comp))
        cls = H.classes(H.linexts(rel, 5), comp)
        md = H.trim(H.dist([min(H.des(w) for w in c) for c in cls]))
        self.assertNotEqual(md, hC(rel, 5))

    def test_per_class_lemma(self):
        rel = frozenset([(0, 2), (1, 3)])
        comp = H.components(rel, 5)          # 4 is isolated
        for c in H.classes(H.linexts(rel, 5), comp):
            md = min(H.des(w) for w in c)
            for T in range(max(comp) + 1):
                for m in range(7):
                    self.assertEqual(H.omegaC_des_class(c, comp, T, 5, m),
                                     comb(m + 4 - md, 5))

    def test_all_posets_n_le_5(self):
        by_n = H.unlabeled_posets(5)
        self.assertEqual([len(by_n[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])
        for n in range(2, 6):
            for rel0 in by_n[n]:
                rel = H.relabel(rel0, H.separated_extension(rel0, n))
                self.assertEqual(cdes_dist(rel, n), hC(rel0, n))


if __name__ == "__main__":
    unittest.main()
