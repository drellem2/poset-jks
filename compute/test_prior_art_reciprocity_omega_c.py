"""Unit tests for prior_art_reciprocity_omega_c.py (run from compute/)."""
import unittest
from math import comb

import prior_art_reciprocity_omega_c as M


class TestPriorArtReciprocity(unittest.TestCase):

    def test_small_hC(self):
        self.assertEqual(M.h_c(*M.antichain(4)), [1, 4, 1])
        self.assertEqual(M.h_c(*M.disjoint_union(*M.chain(2), *M.chain(2))),
                         [1, 3, 1])
        self.assertEqual(M.h_c(*M.disjoint_union(*M.chain(3), *M.chain(3))),
                         [1, 8, 9, 1])
        self.assertEqual(M.h_c(*M.chain(5)), [1])

    def test_connected_is_W(self):
        # the "N" poset 0<2, 1<2, 1<3 has W = 1 + 3t + t^2 (5 extensions)
        n, P = 4, M.transitive_closure(4, [(0, 2), (1, 2), (1, 3)])
        self.assertEqual(M.W_poly(n, P), M.h_c(n, P))
        self.assertEqual(sum(M.W_poly(n, P)), 5)

    def test_two_component_identity(self):
        nQ, Q = 3, M.transitive_closure(3, [(0, 1), (0, 2)])
        nT, T = M.chain(2)
        n, P = M.disjoint_union(nQ, Q, nT, T)
        pred = M.p_sub(M.W_poly(n, P),
                       [0] + M.p_mul(M.W_poly(nQ, Q), M.W_poly(nT, T)))
        self.assertEqual(M.h_c(n, P), pred)

    def test_chain_family(self):
        n, P = M.disjoint_union(*M.chain(4), *M.chain(3))
        pred = [comb(4, k) * comb(3, k) for k in range(4)]
        pred[1] -= 1
        self.assertEqual(M.h_c(n, P), pred)

    def test_real_rooted_controls(self):
        self.assertTrue(M.real_rooted([1, 26, 66, 26, 1]))
        self.assertTrue(M.real_rooted([1, 2, 1]))          # double root
        self.assertFalse(M.real_rooted([1, 0, 1]))
        self.assertFalse(M.real_rooted([1, 1, 1]))
        br = [comb(36, k) * comb(6, k) for k in range(7)]
        br[0] -= 1
        self.assertFalse(M.real_rooted(br))                # Branden P_{36,6}

    def test_stembridge(self):
        found = [M.W_poly(17, M.naturalize(17, d))
                 for _, d in M.stembridge_candidates()]
        self.assertIn(M.STANLEY_AP[1:], found)

    def test_reciprocity_bruteforce_small(self):
        # P = C_2 + C_1, T = the chain: (-1)^n Omega_C(-m) = strict D_T count
        n, P = M.disjoint_union(*M.chain(2), *M.chain(1))
        T = 0b011
        vals = M.omega_c_values(n, P, T, n + 1)
        for m in range(1, 6):
            self.assertEqual((-1) ** n * M.interp_at(vals, -m),
                             M.strict_DT_count(n, P, T, m))


if __name__ == "__main__":
    unittest.main()
