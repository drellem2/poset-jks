"""Unit tests for audit_oriented_matroid_cones.py.
Run (from compute/): python3 -m unittest test_audit_oriented_matroid_cones"""

import random
import unittest

import audit_oriented_matroid_cones as a


def setup_cones(om):
    om.prepare()
    auts = om.automorphisms()
    tperm = [[om.tidx[om.act(g, T)] for T in om.topes] for g in auts]
    dets = []
    for g in auts:
        imap = [om.idx[om.act(g, X)] for X in om.L]
        s, c = next(iter(om.omega.items()))
        dets.append(om.omega[tuple(imap[i] for i in s)] * c)
    sets = a.tconvex_sets(om)
    a.G.clear()
    a.G.update(om=om, auts=auts, sets=sets, tperm=tperm, dets=dets, deep=True,
               integral=set(sets))
    return auts, dets, sets


class TestAudit(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_controls_fire(self):
        self.assertTrue(a.controls(log=lambda s: None))
        self.assertEqual(a.FAIL, [])

    def test_linear_algebra(self):
        self.assertEqual(a.rank_mod([{0: 1, 1: 1}, {0: 2, 1: 2}, {1: 5}]), 2)
        self.assertEqual(a.smith_check([{0: 2, 1: 0}, {1: 2}]), (2, [2, 2]))
        self.assertEqual(a.smith_check([{0: 1, 1: 1}, {0: 1, 1: -1}]), (2, [2]))
        piv = a.rref_mod([{0: 1, 1: 1}, {1: 1, 2: 1}])
        self.assertEqual(piv, {0: {0: 1, 2: a.P - 1}, 1: {1: 1, 2: 1}})

    def test_lifting_is_non_realizable_rank4(self):
        M, d, ext, N, seq = a.lifting_N()
        self.assertTrue(a.chirotope_axioms(N)[0])
        self.assertEqual(N.r, 4)
        con = N.contract(9)
        self.assertTrue(a.non_realizability_certificate(con))
        om = a.OM("N", N)
        self.assertTrue(om.simple())
        self.assertEqual((len(om.L), len(om.topes), len(om.flats)), (1737, 244, 153))
        self.assertEqual(om.rk(om.full & ~(1 << 9)), 4)     # p is not a coloop

    def test_N_cones_sample(self):
        _, _, _, N, _ = a.lifting_N()
        om = a.OM("N", N)
        auts, dets, sets = setup_cones(om)
        self.assertEqual(len(sets), 12965)
        self.assertEqual(abs(om.mu_L), 76)
        keys = random.Random(5).sample(sorted(sets), 25) + [(0, 0)]
        nonpointed = [k for k in sorted(sets) if om.rk(k[0] | k[1]) < 3][:10]
        for k in keys + nonpointed:
            _, r = a.check_cone(k)
            for name in ("flatL", "zas", "wedge", "brown", "lunL", "rho", "q=m", "G1", "eq",
                         "Z_rho", "pi1"):
                self.assertTrue(r[name], (k, name))
            self.assertEqual(r["Z_tors"], [])

    def test_coloop_sum_has_det_minus_one(self):
        NC = a.with_coloop(a.non_pappus(1)[1])
        om = a.OM("NC", NC)
        auts, dets, sets = setup_cones(om)
        self.assertEqual(om.r, 4)
        self.assertIn(-1, dets)
        for g, d in zip(auts, dets):
            self.assertEqual(a.chirotope_factor(om, g), d)
        _, r = a.check_cone((0, 0))
        self.assertTrue(r["eq"])
        self.assertFalse(r["eq_untwisted"])     # the twist is visible at V = all topes

    def test_lemma02_and_negative_control(self):
        om = a.OM("B3", a.Chirotope.from_vectors(a.vectors_B3()))
        om.prepare()
        a.prepare_lem02(om)
        T = om.topes[3]
        e = 2
        sp = T[0] & (1 << e)
        sm = T[1] & (1 << e)
        kind, b = a.classify_K(om, a.K_mask(om, sp, sm))
        self.assertTrue(kind == "point" or b == {})
        kind, b = a.classify_K(om, a.K_mask(om, 0, 0))
        self.assertEqual(b, {2: 1})
        a.negative_cone_control(om, log=lambda s: None)
        self.assertEqual(a.FAIL, [])

    def test_known_counts(self):
        om = a.OM("A3", a.Chirotope.from_vectors(a.vectors_A(4)))
        self.assertEqual(len(a.tconvex_sets(om)), 219)


if __name__ == "__main__":
    unittest.main()
