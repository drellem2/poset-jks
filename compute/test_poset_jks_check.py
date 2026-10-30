#!/usr/bin/env python3
"""Tests for poset_jks_check.py.  Run: python3 -m unittest test_poset_jks_check"""

import math
import unittest

import poset_jks_check as pj


def antichain(n):
    return frozenset()


def by_rep(res):
    return {c["rep"]: c for c in res["classes"]}


class Counts(unittest.TestCase):
    def test_unlabeled_counts_oeis_A000112(self):
        posets = pj.unlabeled_posets_by_extension(6)
        self.assertEqual([len(posets[n]) for n in range(1, 7)], [1, 2, 5, 16, 63, 318])

    def test_bruteforce_counts_A006455_A001035_A000112(self):
        got = [pj.poset_counts_bruteforce(n) for n in range(1, 6)]
        self.assertEqual(got, [(1, 1, 1), (2, 3, 2), (7, 19, 5), (40, 219, 16), (357, 4231, 63)])


class Arithmetic(unittest.TestCase):
    def test_cyclotomic(self):
        self.assertEqual(pj.cyclotomic(6), [1, -1, 1])
        self.assertEqual(pj.cyclotomic(4), [1, 0, 1])
        self.assertEqual(pj.cyclotomic(5), [1, 1, 1, 1, 1])

    def test_zeta_sums(self):
        self.assertTrue(pj.zeta_sum_equals_int([0, 1, 1], -1, 3))      # z + z^2 = -1
        self.assertTrue(pj.zeta_sum_equals_int([0, 1, 0, 1], 0, 4))    # i + (-i) = 0
        self.assertTrue(pj.zeta_sum_equals_int([0, 1, 0, 0, 0, 1], 1, 6))
        self.assertFalse(pj.zeta_sum_equals_int([0, 1, 1], 2, 3))
        self.assertIsNone(pj.as_int_if_rational([0, 1, 0], 3))         # z alone is irrational


class Identity(unittest.TestCase):
    def test_partition_lattice_moebius(self):
        # antichain: OP(P) = Pi_n, mu = (-1)^(n-1) (n-1)!
        for n in range(1, 6):
            res = pj.analyse(antichain(n), n)
            self.assertEqual(by_rep(res)["id"]["mu"], (-1) ** (n - 1) * math.factorial(n - 1))

    def test_chain_three_excludes_13_2(self):
        chain = frozenset([(0, 1), (1, 2), (0, 2)])
        self.assertEqual(len(pj.order_preserving_partitions(chain, 3)), 4)

    def test_antichain3_phase(self):
        g = by_rep(pj.analyse(antichain(3), 3))["(1 2 3)"]
        self.assertEqual((g["lhs"], g["rhs"], g["num_fixed_classes"]), (-1, -1, 2))
        self.assertTrue(g["ok"]["F0_note"])
        self.assertFalse(g["ok"]["F3_count"])   # positive control: phase matters

    def test_sign_twist_discriminated_at_n6(self):
        g = by_rep(pj.analyse(antichain(6), 6, explicit=False))["(1 2)(3 4)(5 6)"]
        self.assertTrue(g["ok"]["F0_note"])
        self.assertFalse(g["ok"]["F2_nosgn"])   # positive control: sign matters

    def test_three_two_chains_value_minus_one(self):
        rel = frozenset([(0, 1), (2, 3), (4, 5)])
        g = by_rep(pj.analyse(rel, 6))["(1 3 5)(2 4 6)"]
        self.assertEqual((g["lhs"], g["rhs"], g["rotations"]), (-1, -1, {"2": 1, "4": 1}))

    def test_rotation_convention(self):
        # g*w = w*gamma^r with (w*gamma^r)[i] = w[i+r]
        self.assertEqual(pj.rotation_amount((1, 2, 0), (0, 1, 2)), 1)
        self.assertEqual(pj.rotation_amount((1, 2, 0), (0, 2, 1)), 2)

    def test_explicit_trace_matches_zeta_r(self):
        cyc = pj.cyclic_classes(pj.linear_extensions(antichain(4), 4))
        tr, _ = pj.lie_trace_explicit((1, 0, 3, 2), cyc, 4)
        self.assertAlmostEqual(tr, -2)

    def test_explicit_scalar_is_zeta_not_conjugate(self):
        # discriminates zeta^r from zeta^-r on a single class (the trace cannot)
        _, scal = pj.lie_trace_explicit((1, 2, 0), [(0, 1, 2), (0, 2, 1)], 3)
        z = pj.cmath.exp(2j * pj.cmath.pi / 3)
        self.assertAlmostEqual(scal[(0, 1, 2)], z)
        self.assertAlmostEqual(scal[(0, 2, 1)], z ** 2)


if __name__ == "__main__":
    unittest.main()
