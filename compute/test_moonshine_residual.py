"""Unit tests for moonshine_residual.py: positive and negative controls."""

import unittest
from fractions import Fraction

import moonshine_residual as m


class TestSeries(unittest.TestCase):
    def test_euler_roundtrip(self):
        u = [0, 3, 1, 4, 1, 5, 9, 2, 6]
        a = m.euler_transform(u, 8)
        self.assertEqual(m.product_exponents(a, 8), u)

    def test_partitions(self):
        self.assertEqual(m.euler_transform([0] + [1] * 10, 10),
                         [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42])

    def test_alpha_log_type(self):
        # necklaces: log singularity, alpha = -1; Catalan: square root, -3/2
        N = 120
        lyn = [0] + [sum(m.mobius(d) * 2 ** (n // d) for d in m.divisors(n)) // n
                     for n in range(1, N + 1)]
        cat = [1]
        for n in range(1, N + 1):
            cat.append(cat[-1] * 2 * (2 * n - 1) // (n + 1))
        self.assertAlmostEqual(m.alpha_estimates(lyn, [120])[120], -1.0, places=2)
        self.assertAlmostEqual(m.alpha_estimates(cat, [120])[120], -1.5, places=1)


class TestClasses(unittest.TestCase):
    def test_rooted_and_oriented(self):
        self.assertEqual(m.rooted_trees(8)[1:], [1, 1, 2, 4, 9, 20, 48, 115])
        self.assertEqual(m.rooted_trees(6, 2)[1:], [1, 2, 7, 26, 107, 458])

    def test_sp(self):
        self.assertEqual(m.sp_connected(7)[1:], [1, 1, 3, 9, 30, 103, 375])

    def test_cycle_hasse(self):
        # 4: diamond and bowtie; 5: two; 6: seven
        self.assertEqual([m.cycle_hasse_burnside(n) for n in (4, 5, 6)], [2, 2, 7])

    def test_features_negative(self):
        # the 4-chain is a tree, rooted, N-free, not a cycle
        rel = m.transitive_closure({(0, 1), (1, 2), (2, 3)}, 4)
        f = m.poset_features(rel, 4)
        self.assertTrue(f["tree"] and f["rooted"] and f["nfree"])
        self.assertFalse(f["cycle"])
        # N itself is not N-free
        f = m.poset_features(frozenset({(0, 2), (1, 2), (1, 3)}), 4)
        self.assertFalse(f["nfree"])


class TestInfinite(unittest.TestCase):
    def test_shifted(self):
        W = 10
        self.assertEqual(m.shifted_quadrant(W),
                         m.euler_transform([0] + [(n + 1) // 2 for n in range(1, W + 1)], W))
        self.assertNotEqual(m.shifted_quadrant(W),
                            m.euler_transform([0] + [n // 2 for n in range(1, W + 1)], W))

    def test_binary_tree(self):
        self.assertEqual(m.binary_tree_series(7), m.binary_tree_brute(7))


class TestTwisted(unittest.TestCase):
    def setUp(self):
        self.rel = m.transitive_closure(frozenset(), 4)
        self.g = m.from_cycles(4, [[0, 1, 2, 3]])
        self.h = m.from_cycles(4, [[0, 2], [1, 3]])
        self.taus = [complex(0.11, 0.93), complex(-0.23, 1.17)]

    def test_spectrum(self):
        spec = m.joint_spectrum(self.rel, 4, self.g, self.h)
        self.assertEqual(sum(spec.values()), 6)
        for (s, r), k in spec.items():
            self.assertEqual(spec[(-s) % 1, (-r) % 1], k)

    def test_S_law_and_control(self):
        spec = m.joint_spectrum(self.rel, 4, self.g, self.h)
        d0 = spec.get((Fraction(0), Fraction(0)), 0)
        hinv = m.ppow(self.h, m.porder(self.h) - 1)
        good = m.joint_spectrum(self.rel, 4, hinv, self.g)
        rat = [m.Z(spec, -1 / t) / ((-1j * t) ** (-d0 / 2) * m.Z(good, t)) for t in self.taus]
        self.assertTrue(m.is_constant(rat))
        lone = {(Fraction(1, 3), Fraction(1, 4)): 1}
        lone_S = {(Fraction(3, 4), Fraction(1, 3)): 1}
        bad = [m.Z(lone, -1 / t) / m.Z(lone_S, t) for t in self.taus]
        self.assertFalse(m.is_constant(bad))


if __name__ == "__main__":
    unittest.main()
