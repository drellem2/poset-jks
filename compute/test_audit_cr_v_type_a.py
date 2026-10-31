"""Unit tests for audit_cr_v_type_a.py (positive and negative controls)."""

import math
import unittest

import audit_cr_v_type_a as A


class Controls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reps = A.posets_upto_iso(5)

    def test_poset_counts(self):
        self.assertEqual([len(self.reps[n]) for n in range(6)], [1, 1, 2, 5, 16, 63])

    def test_partition_lattice_mu(self):
        for n in range(1, 6):
            L = A.Lat(n, [0] * n, A.set_partitions(n))
            self.assertEqual(L.mu(), (-1) ** (n - 1) * math.factorial(n - 1))

    def test_uncomplemented_detected(self):
        # Pi_4^(1234): chain 0 < 13|24 < 1
        L = A.Lat(4, [0] * 4, A.stable_parts(A.set_partitions(4), (1, 2, 3, 0)))
        self.assertEqual(L.mu(), 0)
        self.assertEqual(len(L.uncomplemented()), 1)

    def test_f6_acyclic_join(self):
        up = [0b0100, 0b1000, 0, 0]
        x = tuple(sorted([0b1001, 0b0010, 0b0100]))
        y = tuple(sorted([0b0110, 0b0001, 0b1000]))
        self.assertEqual(A.join_M(x, y, up), (0b1111,))
        self.assertNotEqual(A.partition_join(x, y), (0b1111,))

    def test_clfix_minus_formula(self):
        for lam in [(1, 3), (2, 2), (3, 6), (1, 2, 4), (5,)]:
            t = A.perm_from_cycle_type(lam)
            self.assertEqual(A.clfix(-1, t, sum(lam)), A.clfix_formula_minus(t))


class Sweep(unittest.TestCase):
    def test_sweep_n5_no_failures(self):
        reps = A.posets_upto_iso(5)
        per_n, fails, unrun = A.sweep(3, 5, reps, 1e9, 5, verbose=False)
        self.assertEqual(fails, [])
        self.assertFalse(unrun)
        # the author's per-n counts (conjugacy-reduced) for n = 3, 4, 5
        got = [(per_n[n][0]["pairs+"], per_n[n][0]["pairs-"],
                per_n[n][0]["zeros+"], per_n[n][0]["zeros-"]) for n in (3, 4, 5)]
        self.assertEqual(got, [(9, 5, 3, 2), (34, 16, 16, 6), (144, 30, 80, 19)])

    def test_negative_controls_fire(self):
        reps = A.posets_upto_iso(5)
        for kw in (dict(variant="clfix"), dict(crit_no_ta4=True), dict(joinf_name="plain")):
            _, fails, _ = A.sweep(3, 5, reps, 1e9, 0, verbose=False, **kw)
            self.assertTrue(fails, kw)


class LemmaC(unittest.TestCase):
    def test_bruteforce_n5(self):
        checks, agree, pos = A.lemma_c_bruteforce(5)
        self.assertEqual(checks, agree)
        self.assertTrue(0 < pos < checks)


class BigBranch(unittest.TestCase):
    def test_9_18_k6_uncomplemented(self):
        st, found, stable, W = A.complement_search_antichain((9, 18), 6)
        self.assertTrue(stable)
        self.assertEqual(found, 0)
        self.assertEqual(len(W), 9)
        self.assertEqual(A.ta_status(27, [0] * 27, A.perm_from_cycle_type((9, 18))), "TA1")

    def test_9_18_k2_complemented_positive_control(self):
        st, found, stable, W = A.complement_search_antichain((9, 18), 2)
        self.assertGreater(found, 0)

    def test_9_cycle_k2_fails_k6_works(self):
        self.assertGreater(A.complement_search_antichain((9,), 2)[1], 0)
        self.assertEqual(A.complement_search_antichain((9,), 6)[1], 0)


if __name__ == "__main__":
    unittest.main()
