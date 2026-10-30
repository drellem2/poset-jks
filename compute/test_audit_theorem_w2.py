"""Unit tests for audit_theorem_w2.py: positive and negative controls."""

import io
import unittest
from collections import defaultdict
from fractions import Fraction as Fr

import audit_theorem_w2 as w


class TestPrimitives(unittest.TestCase):
    def test_fm_feasible(self):
        self.assertTrue(w.strictly_feasible([(1, 0), (0, 1), (1, -1)]))
        # x > 0 and -x > 0: infeasible (negative control for the instrument)
        self.assertFalse(w.strictly_feasible([(1, 0), (-1, 0)]))
        # x > 0, y > 0, -x - y > 0: infeasible
        self.assertFalse(w.strictly_feasible([(1, 0), (0, 1), (-1, -1)]))

    def test_chamber_counts(self):
        ex = w.examples()
        for name, c in w.EXPECT_CHAMBERS.items():
            self.assertEqual(len(w.get_arr(ex[name][0]).chambers), c, name)

    def test_betti_sphere_and_point(self):
        arr = w.get_arr(w.examples()["coord3"][0])
        # boundary of one chamber (octant): circle -> reduced H_1 = 1
        C = arr.chambers[0]
        cone = w.Cone(arr, [C])
        bar = [Z for Z in cone.lam if Z not in (arr.top, arr.bottom)]
        b = w.reduced_betti(bar, lambda a, c: a != c and w.leq(a, c))
        self.assertEqual(b, {1: 1})
        # a single point is contractible
        self.assertEqual(w.reduced_betti([arr.top], lambda a, c: False), {})


class TestTheorem(unittest.TestCase):
    def run_small(self, name):
        T, NC, total = w.run([name], io.StringIO())
        return T, NC, total

    def test_coordsum3_all_pass(self):
        T, NC, total = self.run_small("coordsum3")
        self.assertFalse(dict(T.bad), T.examples)
        self.assertGreater(total["W2b"] - total["g=1"], 0)
        for tag in ("nosign", "noclose", "rho+1", "nohyp"):
            self.assertGreater(NC[tag], 0, tag)

    def test_negative_wrong_sign_detected(self):
        # S(g) = m(V^U) without the sign (-1)^k must fail on some pair.
        T, NC, _ = self.run_small("coord3")
        self.assertGreater(NC["nosign"], 0)

    def test_g_identity_is_m(self):
        arr = w.get_arr(w.examples()["coordsum3"][0])
        for V in w.all_top_cones(arr):
            T = w.Tally()
            NC = defaultdict(int)
            st = defaultdict(int)
            I = w.ident(arr.d)
            w.analyse_pair(arr, V, I, arr.act(I), T, NC, st)
            self.assertFalse(dict(T.bad), T.examples)

    def test_quotient_chi_identity_at_bottom(self):
        # chi_{V_0}(g) for X = 0 is chi_V(g) = (-1)^d det g mu(Lambda(V)^g)
        arr = w.get_arr(w.examples()["cyc3"][0])
        V = w.Cone(arr, arr.chambers)
        g = w.neg(3)
        perm = arr.act(g)
        M = [Z for Z in V.lam if arr.act_flat(perm, Z) == Z]
        direct = (-1) ** 3 * w.det(g) * w.mu_bottom_top(M, arr)
        self.assertEqual(w.quotient_chi(arr, V, arr.bottom, g), direct)


if __name__ == "__main__":
    unittest.main()
