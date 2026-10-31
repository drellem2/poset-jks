"""Tests for vanishing_criterion.py, with positive and negative controls
(run from compute/)."""

import contextlib
import io
import unittest

import vanishing_criterion as vc


def classes(A):
    return [(rep, vc.GCtx(A, rep)) for rep, _ in vc.classes_in(A.G)]


def full_cone(A):
    return vc.ConeCtx(A, (1 << A.nch) - 1)


class Runs(unittest.TestCase):
    def test_quick_run_passes(self):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            code = vc.main(["--quick"])
        out = buf.getvalue()
        self.assertEqual(code, 0, out[-2000:])
        self.assertIn("top-cones=219, W-orbits=16", out)    # A3: posets on 4 points
        self.assertIn("top-cones=941, W-orbits=35", out)    # B3, as in [GT]
        self.assertIn("ALL CHECKS PASSED", out)


class Field(unittest.TestCase):
    def test_q5_sign(self):
        tau = vc.Q5(vc.Fraction(1, 2), vc.Fraction(1, 2))     # golden ratio
        self.assertEqual(vc.sgn(tau * tau - tau - 1), 0)
        self.assertEqual(vc.sgn(vc.Q5(-2, 1)), 1)             # sqrt5 > 2
        self.assertEqual(vc.sgn(vc.Q5(3, -1)), 1)             # 3 > sqrt5
        self.assertEqual(vc.sgn(vc.Q5(2, -1)), -1)


class PositiveControls(unittest.TestCase):
    def test_lie4_character(self):
        # all chambers of A3: chi is the Lie_4 character 6, -2, 0, 0, 0
        A = vc.Arrangement("A3")
        C = full_cone(A)
        vals = {}
        for rep, G in classes(A):
            if A.inW[rep]:
                vals[vc.cycle_type_A(A, rep)] = vc.chi_direct(C, rep, G.gd)
        self.assertEqual(vals, {"(1,1,1,1)": 6, "(2,2)": -2, "(2,1,1)": 0,
                                "(3,1)": 0, "(4)": 0})

    def test_b2_every_class_nonvanishing(self):
        A = vc.Arrangement("B2")
        self.assertTrue(all(G.crit for _, G in classes(A)))

    def test_braid_rule(self):
        buf = io.StringIO()
        self.assertTrue(vc.braid_control(buf), buf.getvalue())

    def test_type_a_partitions(self):
        buf = io.StringIO()
        self.assertTrue(vc.typeA_partition_check(buf, 6), buf.getvalue())

    def test_type_a_rule_examples(self):
        self.assertTrue(vc.type_A_rule((5,), False))
        self.assertFalse(vc.type_A_rule((4,), False))          # mu(4) = 0
        self.assertFalse(vc.type_A_rule((2, 1), False))
        self.assertTrue(vc.type_A_rule((2, 1, 1), True))        # -w, w an involution
        self.assertTrue(vc.type_A_rule((6, 3), True))           # lcm(2, k) = 6 for both
        self.assertFalse(vc.type_A_rule((3, 3, 1), True))
        self.assertFalse(vc.type_A_rule((9,), True))            # mu(18) = 0

    def test_elliptic_vanishes_on_proper_cones(self):
        # Fix(g) = 0: only the cone of all chambers can carry chi != 0
        A = vc.Arrangement("B3")
        cones = vc.orbit_reps(A, vc.all_cones(A), A.W)
        full = (1 << A.nch) - 1
        for rep, G in classes(A):
            if G.gd["dimU"]:
                continue
            for V in cones:
                P, N = vc.cone_constraints(A, V)
                if V != full and rep in vc.stabilizer(A, P, N):
                    self.assertEqual(vc.chi_direct(vc.ConeCtx(A, V), rep, G.gd), 0)

    def test_springer_regular_b3(self):
        # regular classes of B3: 1, -1, the Coxeter class [3-] and [3+]
        A = vc.Arrangement("B3")
        reg = {vc.signed_cycle_type_B(A, rep) for rep, _ in classes(A)
               if vc.springer_regular(A, rep)}
        self.assertEqual(reg, {"[1+ 1+ 1+]", "[1- 1- 1-]", "[3-]", "[3+]"})


class NegativeControls(unittest.TestCase):
    def _z_variant(self, A, keep, use_m=True):
        """Formula Z with a modified index set; returns the number of pairs
        (V, g) where it disagrees with chi."""
        cones = vc.orbit_reps(A, vc.all_cones(A), A.W)
        bad = 0
        for V in cones:
            C = vc.ConeCtx(A, V)
            P, N = C.P, C.N
            for g, _ in vc.classes_in(vc.stabilizer(A, P, N)):
                G = vc.GCtx(A, g)
                chi = vc.chi_direct(C, g, G.gd)
                tot = 0
                for X, mu in G.mu.items():
                    if (X & C.Lhyp) == C.Lhyp and keep(A, G, X) and mu:
                        # hyperplanes containing Fix g are dropped, so that m is
                        # defined (and >= 1) also when X + Fix g lies in one
                        Xr = X & ~G.gd["hypU"]
                        tot += mu * (vc.m_restricted(C, g, G.gd, Xr) if use_m else 1)
                bad += tot != chi
        return bad

    def test_z_correct(self):
        A = vc.Arrangement("B3")
        keep = lambda A, G, X: X in G.zmu
        self.assertEqual(self._z_variant(A, keep), 0)

    def test_z_needs_hyperplane_condition(self):
        A = vc.Arrangement("B3")
        keep = lambda A, G, X: A.meets_U_trivially(X, G.gd)
        self.assertGreater(self._z_variant(A, keep), 0)

    def test_z_needs_trivial_intersection(self):
        A = vc.Arrangement("B3")
        keep = lambda A, G, X: A.sum_in_no_hyperplane(X, G.gd)
        self.assertGreater(self._z_variant(A, keep), 0)

    def test_z_needs_multiplicity(self):
        A = vc.Arrangement("A3")
        keep = lambda A, G, X: X in G.zmu
        self.assertGreater(self._z_variant(A, keep, use_m=False), 0)

    def test_witness_must_be_minimal(self):
        # H3, rotation by pi: Z* = four lines (mu = -1) inside a plane (mu = 5).
        # The witness cone of the plane has chi = 5 - 4 = 1, not 5.
        A = vc.Arrangement("H3")
        found = False
        for rep, G in classes(A):
            vals = sorted(G.zmu.values())
            if vals == [-1, -1, -1, -1, 5]:
                X = next(X for X, mu in G.zmu.items() if mu == 5)
                C = vc.ConeCtx(A, vc.witness_cone(A, G, X))
                self.assertEqual(vc.chi_direct(C, rep, G.gd), 1)
                found = True
        self.assertTrue(found)

    def test_cancellation_exists(self):
        # all chambers of A2, g = -(12): Z* = {0, H_12}, mu = 1, -1, chi = 0
        A = vc.Arrangement("A2")
        C = full_cone(A)
        for rep, G in classes(A):
            if vc.cycle_type_A(A, rep) == "-(2,1)":
                self.assertEqual(sorted(G.zmu.values()), [-1, 1])
                self.assertEqual(vc.chi_direct(C, rep, G.gd), 0)


if __name__ == "__main__":
    unittest.main()
