"""Unit tests for prior_art_linext_statistics.py (run from compute/):

    python3 -m unittest test_prior_art_linext_statistics
"""
import unittest

import prior_art_linext_statistics as M


class Tests(unittest.TestCase):
    def test_poset_counts(self):
        by_n = M.all_posets(5)
        self.assertEqual([len(by_n[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])

    def test_antichain_omegaC_is_power_sum(self):
        # Omega_C(A_n, m) = sum_{j<=m} j^{n-1} (antichain case of Theorem Omega)
        for n in range(1, 6):
            P = (0,) * n
            comps = M.components(n, P)
            c = M.anchored_chain_data(n, P, comps, comps[0])
            for m in range(0, 7):
                self.assertEqual(M.omega_values(c, [m])[0],
                                 sum(j ** (n - 1) for j in range(1, m + 1)))

    def test_h_vectors(self):
        # h_C(A_4) = Eulerian (1,4,1); C_2 + C_2 has h_C = (1,3,1)
        P = (0, 0, 0, 0)
        comps = M.components(4, P)
        h = M.h_vector(4, M.anchored_chain_data(4, P, comps, comps[0]))
        self.assertEqual(h, [0, 1, 4, 1, 0])
        P = (0, 1, 0, 4)  # 0<1, 2<3
        comps = M.components(4, P)
        h = M.h_vector(4, M.anchored_chain_data(4, P, comps, comps[0]))
        self.assertEqual(h, [0, 1, 3, 1, 0])

    def test_e_C_two_chains(self):
        # C_3 + C_3: 20 shuffles, only aaabbb ~ bbbaaa merge -> e_C = 19
        P = (0, 1, 3, 0, 8, 24)
        comps = M.components(6, P)
        lin = M.linear_extensions(6, P)
        self.assertEqual(len(lin), 20)
        self.assertEqual(len(M.cut_classes(6, P, comps, lin)), 19)

    def test_g_formula_matches_bruteforce(self):
        # toric order polynomial of a total cyclic order [w] is g_{cdes w}
        for w in [(0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 2, 1)]:
            arcs = [(w[i], w[i + 1]) for i in range(3)] + [(w[0], w[3]),
                                                            (w[0], w[2]),
                                                            (w[1], w[3])]
            cd = sum(1 for i in range(4) if w[i] > w[(i + 1) % 4])
            for m in range(1, 5):
                self.assertEqual(M.toric_count_bruteforce(4, arcs, m),
                                 M.g_poly_values(4, cd, [m])[0])

    def test_m_to_f(self):
        # M_{(1,1)} = F_{(1,1)};  M_{(2)} = F_{(2)} - F_{(1,1)}
        self.assertEqual(M.m_to_f(2, {frozenset({1}): 1}), {frozenset({1}): 1})
        self.assertEqual(M.m_to_f(2, {frozenset(): 1}),
                         {frozenset(): 1, frozenset({1}): -1})

    def test_antichain_lift_not_cyclic(self):
        P = (0, 0, 0)
        comps = M.components(3, P)
        mc = M.anchored_chain_data(3, P, comps, comps[0], want_comp=True)
        self.assertEqual(mc[(1, 2)], 2)
        self.assertEqual(mc[(2, 1)], 1)
        self.assertFalse(M.is_cyclic_qsym(mc))


if __name__ == "__main__":
    unittest.main()
