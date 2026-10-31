"""Tests for lean_js_route.py, with positive controls (run from compute/)."""

import io
import unittest

import lean_js_route as r
import mu_op_elementary as m


class Runs(unittest.TestCase):
    def test_up_to_four_passes(self):
        out = io.StringIO()
        self.assertTrue(r.run(4, out, 1))
        self.assertIn("total posets checked: 24", out.getvalue())
        self.assertIn("ALL CHECKS PASS", out.getvalue())


class Betti(unittest.TestCase):
    def test_antichain_top_betti_is_factorial(self):
        # Delta(proper part of Pi_n) is a wedge of (n-1)! spheres S^{n-3}
        for n, f in [(3, 2), (4, 6)]:
            L = m.op_lattice(n, frozenset())
            Lbar = [x for x in L if x != tuple(range(n)) and x != tuple([0] * n)]
            b = r.betti(r.chains(Lbar, m.leq))
            self.assertEqual(b[n - 3], f)
            self.assertTrue(all(v == 0 for d, v in b.items() if d != n - 3))

    def test_two_point_antichain_is_not_acyclic(self):
        # control: S^0 has reduced b_0 = 1
        b = r.betti(r.chains([0, 1], lambda x, y: x == y))
        self.assertEqual(b[0], 1)

    def test_cone_is_acyclic(self):
        b = r.betti(r.chains([0, 1, 2], lambda x, y: x == y or y == 2))
        self.assertTrue(all(v == 0 for v in b.values()))


class Controls(unittest.TestCase):
    def test_controls_fire_on_antichain_4(self):
        _, res = r.analyse((4, frozenset(), True))
        for k in ("M", "Pz", "inv", "N", "Qac", "rel", "JS"):
            self.assertTrue(res[k], k)
        for k in ("C1", "C2", "C3", "C4"):
            self.assertTrue(res[k], k)


if __name__ == "__main__":
    unittest.main()
