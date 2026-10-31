#!/usr/bin/env python3
"""Unit tests for qsym_refinement_omega_c.py.  Run from compute/:

    python3 -m unittest test_qsym_refinement_omega_c
"""

import itertools
import unittest
from collections import Counter

import qsym_refinement_omega_c as Q

F = lambda *Js: Counter(frozenset(J) for J in Js)


def K(rel, n, T):
    rel = frozenset(rel)
    return Q.m_to_f(n, Q.KCT_M(rel, n, Q.components(rel, n), T))


def K_brute(rel, n, T, m):
    """Coefficients of K_{C,T} truncated to m variables, by listing maps."""
    rel = frozenset(rel)
    comps = Q.components(rel, n)
    out = Counter()
    for f in itertools.product(range(1, m + 1), repeat=n):
        if all(f[a] <= f[b] for a, b in rel) and Q.anchored(f, n, comps, T):
            out[tuple(sorted(Counter(f).items()))] += 1
    return out


def F_expand(n, fc, m):
    """Same truncation of sum c_J F_J."""
    out = Counter()
    for J, c in fc.items():
        for seq in itertools.combinations_with_replacement(range(1, m + 1), n):
            if all(seq[i - 1] < seq[i] for i in J):
                out[tuple(sorted(Counter(seq).items()))] += c
    return Counter({k: v for k, v in out.items() if v})


class Definition(unittest.TestCase):
    def test_chain_count_matches_brute_force(self):
        # K_{C,T} from chains of ideals = brute-force sum of x^f, 3 variables
        cases = [([], 3, 0b001), ([(1, 2)], 3, 0b001), ([(1, 2)], 3, 0b110),
                 ([(0, 1), (2, 3)], 4, 0b0011), ([(0, 2)], 4, 0b1000),
                 ([(0, 1), (0, 2)], 4, 0b1000)]
        for rel, n, T in cases:
            self.assertEqual(F_expand(n, K(rel, n, T), 3),
                             Counter({k: v for k, v in
                                      K_brute(rel, n, T, 3).items()}),
                             (rel, n, T))

    def test_T_dependence_C2_plus_C1(self):
        # 0 isolated, 1 < 2
        self.assertEqual(K([(1, 2)], 3, 0b001), F([], [2]))
        self.assertEqual(K([(1, 2)], 3, 0b110), F([], [1]))

    def test_no_rotation_rule_under_fixed_separated_labelling(self):
        # 0 isolated, 1 < 2 is separated.  Classes {012, 120} and {102}.
        # K_{C,{0}} = F_{} + F_{2}, but the singleton class {102} can only
        # give F_{1}: no choice of one rotation per class works.
        rel = frozenset([(1, 2)])
        self.assertTrue(Q.is_separated(rel, 3))
        cls = Q.classes(Q.linexts(rel, 3), Q.components(rel, 3))
        self.assertIn([(1, 0, 2)], cls)
        self.assertNotIn(frozenset([1]), K(rel, 3, 0b001))

    def test_antichain_is_ordinal_sum(self):
        # K_{C,{t}}(A_n) = sum_{u in S_{n-1}} F_{Des u}  (t labelled n-1)
        for n in range(2, 6):
            want = Counter(Q.Des(u) for u in itertools.permutations(range(n - 1)))
            self.assertEqual(K([], n, 1 << (n - 1)), want)


class TheoremQ(unittest.TestCase):
    def test_C2_plus_C2(self):
        rel = frozenset([(0, 2), (1, 3)])   # 0<2, 1<3: labels separated, E_T
        comps = Q.components(rel, 4)
        T = 0b0101
        self.assertTrue(Q.satisfies_Estar(rel, 4, comps, T))
        lin = Q.linexts(rel, 4)
        reps = [w for w in lin if Q.last_piece_has_T(w, comps, T)]
        self.assertEqual(Counter(Q.Des(w) for w in reps), K(rel, 4, T))
        self.assertEqual(len(reps), 5)          # e_C(C2 + C2) = 5

    def test_violating_labelling_fails(self):
        # 0<1, 2<3, T = {0,1}: max 1 < min 2 of the other component
        rel = frozenset([(0, 1), (2, 3)])
        comps = Q.components(rel, 4)
        T = 0b0011
        self.assertFalse(Q.satisfies_Estar(rel, 4, comps, T))
        lin = Q.linexts(rel, 4)
        reps = [w for w in lin if Q.last_piece_has_T(w, comps, T)]
        self.assertNotEqual(Counter(Q.Des(w) for w in reps), K(rel, 4, T))

    def test_inclusion_exclusion_word(self):
        # G_T(w) for w = 012 with pieces 0 | 12, T = {0}: f0 = f1 <= f2
        rel = frozenset([(1, 2)])
        comps = Q.components(rel, 3)
        self.assertEqual(Q.G_T((0, 1, 2), comps, 0b001),
                         Counter({frozenset(): 1, frozenset([1]): -1}))

    def test_per_class_negative(self):
        # antichain 0,1,2 with T = {1}: class {012,120,201} gives
        # F_{} + F_{1} - F_{2}, not F-positive (labelling violates E*)
        comps = Q.components(frozenset(), 3)
        g = Counter()
        for w in [(0, 1, 2), (1, 2, 0), (2, 0, 1)]:
            g = Q.add(g, Q.G_T(w, comps, 0b010))
        self.assertEqual(g, Counter({frozenset(): 1, frozenset([1]): 1,
                                     frozenset([2]): -1}))

    def test_m_to_f_control(self):
        self.assertEqual(Q.m_to_f(2, Counter({frozenset(): 1})),
                         Counter({frozenset(): 1, frozenset([1]): -1}))

    def test_small_run(self):
        self.assertEqual(Q.main(["--nmax", "4", "--lmax", "4",
                                 "--specmax", "4", "--bijmax", "4"]), 0)


if __name__ == "__main__":
    unittest.main()
