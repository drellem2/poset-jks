"""Tests for general_theory.py, with positive controls (run from compute/)."""

import io
import unittest

import cone_lie as cl
import general_theory as gt
import poset_jks_check as pj


class Cones(unittest.TestCase):
    def test_small_arrangements_pass(self):
        out = io.StringIO()
        self.assertTrue(gt.run_cones("A2", cl.braid(3), "all", 0, True, True, out))
        self.assertTrue(gt.run_cones("B2", cl.type_b(2), "all", 0, True, True, out))

    def test_twist_control_B2(self):
        out = io.StringIO()
        gt.run_cones("B2", cl.type_b(2), "all", 0, False, True, out)
        line = [l for l in out.getvalue().splitlines() if "control" in l][0]
        self.assertIn("holds on 24/33", line)  # untwisted fails on 9 cones

    def test_lineality_restriction_matters(self):
        # Control for [zas]: summing m(V_Z) over every Z in Lambda(V), not
        # only over Z >= S_max, gives the wrong count on some cone of A3.
        vecs = cl.braid(4)
        covs, _ = cl.covectors(vecs)
        topes = [x for x in covs if all(x)]
        less = lambda a, b: a > b
        bad = 0
        for V in cl.all_top_cones(topes, len(vecs)):
            Vt = [topes[i] for i in V]
            Smax = {e: Vt[0][e] for e in range(len(vecs))
                    if len({t[e] for t in Vt}) == 1}
            faces = [x for x in covs if all(x[e] in (0, s) for e, s in Smax.items())]
            sup = sorted({cl.zeros(x) for x in faces}, key=lambda Z: -len(Z))
            tot = 0
            for Z in sup:
                r = cl.rank_q([vecs[e] for e in Z]) if Z else 0
                tot += (-1) ** r * gt.mobius_up(sup, Z, less)[frozenset()]
            bad += tot != len(V)
        self.assertGreater(bad, 0)

    def test_trace_identity_is_q(self):
        vecs = cl.type_b(2)
        covs, cc = cl.covectors(vecs)
        topes = [x for x in covs if all(x)]
        flats_max = sorted({cl.zeros(c) for c in cc}, key=sorted)
        piv, res = cl.lune_quotient(topes, flats_max, len(topes) - 3)
        V = list(range(len(topes)))
        self.assertEqual(gt.trace_mod_lune(V, res, lambda i: i), 3)


class Posets(unittest.TestCase):
    def test_posets_n4(self):
        self.assertTrue(gt.run_posets(4, io.StringIO()))

    def test_foata_needs_cycles(self):
        # Control: with |Lin| in place of e_C on blocks the identity fails
        # for the 2-antichain (2 vs 1 + 1*1 ... = 3).
        rel, n = frozenset(), 2
        comps = gt.comps_of(rel, n)
        lin = len(pj.linear_extensions(rel, n))
        wrong = 0
        for sig in gt.partitions_of(comps):
            p = 1
            for blk in sig:
                B = frozenset().union(*blk)
                r, _ = gt.restrict(rel, B)
                p *= len(pj.linear_extensions(r, len(B)))
            wrong += p
        self.assertNotEqual(wrong, lin)

    def test_foata_injective(self):
        seqs = [((0,), (1,), (2,)), ((1,), (0,), (2,)), ((2,), (0,), (1,))]
        self.assertEqual(len({gt.foata(s) for s in seqs}), 3)


if __name__ == "__main__":
    unittest.main()
