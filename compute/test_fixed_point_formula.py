"""Tests for fixed_point_formula.py, with positive and negative controls
(run from compute/)."""

import io
import unittest

import fixed_point_formula as fp


def chi_and_parts(arr, V, e):
    """chi_V(g), #V^g, and the per-flat data used by [EZ] and [CF]."""
    ch, smax, lam = fp.cone_data(arr, V)
    lamg = [Z for Z in lam if arr.pmask(e, Z) == Z]
    mut = fp.mu_to_top(lamg)
    chi = e["det"] * (-1) ** arr.d * mut[arr.full]
    LL = [Z for Z in lamg if Z & smax == smax]
    return ch, smax, LL, mut, chi


def stab(arr, V):
    return [e for e in arr.W if fp.image(e["chperm"], V) == V]


class Runs(unittest.TestCase):
    def test_small_types_pass(self):
        out = io.StringIO()
        self.assertTrue(fp.run(["A2", "B2", "A3"], out))
        self.assertIn("top-cones=219", out.getvalue())  # A001035 / OEIS count
        self.assertIn("top-cones=33", out.getvalue())


class PositiveControls(unittest.TestCase):
    def test_lie4_character(self):
        # V = all chambers of A3: chi is the character of Lie_4:
        # 6 at 1, -2 at (12)(34), 0 at (12), (123), (1234).
        arr, _ = fp.build("A3")
        V = (1 << len(arr.chambers)) - 1
        vals = {}
        for e in arr.W:
            *_, chi = chi_and_parts(arr, V, e)
            vals[fp.class_key(arr, e)] = chi
        self.assertEqual(vals[(3,)], 6)            # identity
        self.assertEqual(vals[(1, 3)], -2)         # (12)(34): Fix dim 1
        self.assertEqual(vals[(2, 3)], 0)          # transposition
        self.assertEqual(vals[(1, 1, 3)], 0)       # 3-cycle
        self.assertEqual(vals[(0, 1, 0, 3)], 0)    # 4-cycle

    def test_pointed_cone_is_free(self):
        # A chamber is a pointed cone; Stab_W is trivial, chi(1) = 1.
        arr, _ = fp.build("B3")
        V = 1
        self.assertEqual(len(stab(arr, V)), 1)
        *_, chi = chi_and_parts(arr, V, stab(arr, V)[0])
        self.assertEqual(chi, 1)


class NegativeControls(unittest.TestCase):
    def setUp(self):
        self.arr, _ = fp.build("B3")
        self.reps = fp.orbit_reps(self.arr, fp.all_cones(self.arr))

    def test_cf_needs_fixed_chambers(self):
        # Replacing c(Y, g) by the number of all chambers of A_Y in |V|
        # must break [CF] on some (V, g).
        arr = self.arr
        broken = 0
        for V, _ in self.reps:
            for e in stab(arr, V):
                ch, smax, LL, mut, chi = chi_and_parts(arr, V, e)
                mub = fp.mu_from_bottom(LL, arr.full)
                wrong = sum(mub[Z] * len({c & Z for c in ch}) for Z in LL)
                broken += wrong != chi
        self.assertGreater(broken, 0)

    def test_ez_needs_det_twist(self):
        # Dropping det(g | R^d/Y) from chi_{V_Y} must break [EZ] somewhere.
        arr = self.arr
        broken = 0
        for V, _ in self.reps:
            for e in stab(arr, V):
                ch, smax, LL, mut, chi = chi_and_parts(arr, V, e)
                nfix = sum(1 for c in ch if arr.act_mask(e, c) == c)
                wrong = sum((-1) ** arr.rk[Z] * mut[Z] for Z in LL)
                broken += wrong != nfix
        self.assertGreater(broken, 0)

    def test_weisner_needs_flat_fixed_space(self):
        # [WR] is asserted only when Fix(g) is a flat; for -w in Aut(A3)
        # it fails on some cone, so the hypothesis is not decorative.
        out = io.StringIO()
        fp.run(["A3"], out)
        line = [l for l in out.getvalue().splitlines() if "not a flat" in l][0]
        self.assertIn("holds on 9/20", line)


if __name__ == "__main__":
    unittest.main()
