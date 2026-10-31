"""Unit tests for audit_complementation_axiom.py (controls and small cases)."""

import io
import unittest

import audit_complementation_axiom as A


class Controls(unittest.TestCase):
    def test_controls_fire(self):
        self.assertTrue(A.controls(io.StringIO()))

    def test_purity_counterexample(self):
        A.FAILS.clear()
        A.section_pure(io.StringIO())
        self.assertEqual(A.FAILS, [])


class Small(unittest.TestCase):
    def test_partition_lattice_homology(self):
        P = A.partition_lattice(4)
        self.assertEqual(P.n, 15)
        self.assertEqual(A.interval_betti(P, P.bot, P.top, 3), {1: 6})

    def test_bw_on_pi4_every_antichain_z(self):
        P = A.partition_lattice(4)
        actual = A.interval_betti(P, P.bot, P.top, 2)
        n = 0
        for z in P.open_interval(P.bot, P.top):
            pred = A.bw_prediction(P, z, P.bot, P.top, 2)
            if pred is not None:
                n += 1
                self.assertEqual(pred, actual)
        self.assertGreater(n, 0)

    def test_a4(self):
        name, gens, deg, _ = [g for g in A.groups() if g[0] == "A4"][0]
        L = A.subgroup_lattice(gens, deg, "L(A4)")
        self.assertEqual(L.n, 10)
        self.assertEqual(A.interval_betti(L, L.bot, L.top, 2), {0: 4})
        ok, sph = A.cert(L, L.bot, L.top)
        self.assertTrue(ok)
        self.assertEqual(sph, {0: 4})

    def test_length_cache_is_per_lattice(self):
        # regression: an id()-keyed global cache returned stale lengths across lattices
        for _ in range(3):
            P3 = A.partition_lattice(3)
            self.assertEqual(P3.length(P3.bot, P3.top), 2)
            P5 = A.partition_lattice(5)
            self.assertEqual(P5.length(P5.bot, P5.top), 4)


if __name__ == "__main__":
    unittest.main()
