#!/usr/bin/env python3
"""Tests for conjecture_s.py.  Run: python3 -m unittest test_conjecture_s"""

import itertools
import unittest

import poset_jks_check as pj
import conjecture_s as cs


def chain(n):
    return frozenset((i, j) for i in range(n) for j in range(i + 1, n))


def antichain(n):
    return frozenset()


class ConjectureS(unittest.TestCase):
    def test_E_lemma_small(self):
        out = []
        self.assertTrue(cs.check_E(4, out))

    def test_E_lemma_control(self):
        # positive control: flipping the sign of the "ax" case must break it
        u, v = (0, 1, 2), (3,)
        vec = cs.shuffle_vec(u, v)
        wrong = {k: -c for k, c in cs.predicted_E(u, v, 1, 0).items()}
        self.assertNotEqual(cs.E(vec, 1, 0), wrong)
        self.assertNotEqual(cs.E(vec, 1, 0), {})

    def test_E_is_adjoint_of_substitution(self):
        # <E(w), w'> = <w, w'[a -> xa] - w'[a -> ax]>
        n, a, x = 4, 1, 3
        for w in itertools.permutations(range(n)):
            ew = cs.E({w: 1}, a, x)
            for wp in itertools.permutations([0, 1, 2]):
                i = wp.index(a)
                sub = {wp[:i] + (x, a) + wp[i + 1:]: 1, wp[:i] + (a, x) + wp[i + 1:]: -1}
                self.assertEqual(ew.get(wp, 0), sub.get(w, 0))

    def test_La_kernel(self):
        self.assertTrue(cs.check_La_kernel(4, []))

    def test_connected_independent_disconnected_not(self):
        n = 4
        lin = pj.linear_extensions(chain(2) | {(2, 3)}, n)  # 0<1 and 2<3
        self.assertEqual(len(cs.components(chain(2) | {(2, 3)}, n)), 2)
        # positive control: a disconnected poset has K_P != 0
        self.assertLess(cs.rank_mod_sh(lin, range(n)), len(lin))
        # connected "N" poset: 0<2, 1<2, 1<3
        rel = frozenset({(0, 2), (1, 2), (1, 3)})
        lin = pj.linear_extensions(rel, n)
        self.assertEqual(cs.rank_mod_sh(lin, range(n)), len(lin))

    def test_first_block_basis_counts(self):
        n = 3
        lin = pj.linear_extensions(antichain(n), n)
        comps = cs.components(antichain(n), n)
        B = [w for w in lin if cs.first_block_rep(w, comps)]
        # antichain: B = words starting with 0, (n-1)! of them (Lyndon words)
        self.assertEqual(sorted(B), [(0, 1, 2), (0, 2, 1)])
        self.assertEqual(cs.rank_mod_sh(B, range(n)), 2)
        # control: all of Lin P is dependent modulo Sh
        self.assertEqual(cs.rank_mod_sh(lin, range(n)), 2)

    def test_first_block_not_first_letter(self):
        # 0<1, 2<3: the word 2 0 3 1 is good (its first block is everything)
        comps = cs.components(frozenset({(0, 1), (2, 3)}), 4)
        self.assertTrue(cs.first_block_rep((2, 0, 3, 1), comps))
        self.assertFalse(cs.first_block_rep((2, 3, 0, 1), comps))

    def test_posets_small(self):
        self.assertTrue(cs.check_posets(5, []))
        self.assertTrue(cs.check_rho_B(4, []))


if __name__ == "__main__":
    unittest.main()
