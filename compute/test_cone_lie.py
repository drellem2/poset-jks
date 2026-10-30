#!/usr/bin/env python3
"""Tests for cone_lie.py.  Run: python3 -m unittest test_cone_lie"""

import io
import itertools
import unittest

import cone_lie as cl
import poset_jks_check as pj


def setup(vecs):
    covs, cc = cl.covectors(vecs)
    m = len(vecs)
    topes = [x for x in covs if all(x)]
    flats = sorted({cl.zeros(x) for x in covs}, key=lambda Z: -len(Z))
    E = frozenset(range(m))
    fp = [Z for Z in flats if Z != E]
    fm = sorted({cl.zeros(c) for c in cc}, key=sorted)
    mu = cl.moebius_from_bottom(flats, lambda a, b: a > b)[frozenset()]
    piv, res = cl.lune_quotient(topes, fm, len(topes) - abs(mu))
    return covs, topes, fp, mu, res


def braid_pairs(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


class ConeLie(unittest.TestCase):
    def test_top_cones_of_braid_are_labeled_posets(self):
        # OEIS A001035: labeled posets 1, 3, 19, 219
        for n, count in [(2, 3), (3, 19), (4, 219)]:
            covs, topes, fp, mu, res = setup(cl.braid(n))
            self.assertEqual(len(cl.all_top_cones(topes, len(topes[0]))), count)

    def test_braid_q_equals_e_C(self):
        # independent cross-check against poset_jks_check (cyclic classes)
        n = 4
        pairs = braid_pairs(n)
        covs, topes, fp, mu, res = setup(cl.braid(n))
        for V in cl.all_top_cones(topes, len(pairs)):
            rel = set()
            for e, (i, j) in enumerate(pairs):
                s = {topes[k][e] for k in V}
                if s == {-1}:      # sign(x_i - x_j) = -1: i before j
                    rel.add((i, j))
                elif s == {1}:
                    rel.add((j, i))
            lin = pj.linear_extensions(rel, n)
            self.assertEqual(len(lin), len(V))
            r = cl.analyse_cone(V, topes, covs, len(pairs), res, fp, False)
            self.assertEqual(r["q"], len(pj.cyclic_classes(lin)))

    def test_lin_predicate_control(self):
        # positive control: dropping "S_max in Z" from the predicate must fail
        covs, topes, fp, mu, res = setup(cl.braid(3))
        V = frozenset(i for i, t in enumerate(topes) if t[0] == 1)
        bad = False
        for Z in fp:
            for cls in cl.lune_classes(topes, Z):
                inside = all(i in V for i in cls)
                if any(i in V for i in cls) and not inside:
                    bad = True  # "D in V" alone does not put the lune in V
        self.assertTrue(bad)

    def test_restriction_control(self):
        covs, topes, fp, mu, res = setup(cl.type_b(2))
        self.assertTrue(cl.check_restriction(topes, covs, fp, 4))
        # flip one tope's sign data: lunes then no longer map correctly
        broken = [topes[0]] + [tuple(-x for x in topes[0])] + topes[2:]
        self.assertFalse(cl.check_restriction(broken, covs, fp, 4))

    def test_brown_multiplicity(self):
        # m_bottom = |mu| for the whole arrangement, 0 for a single chamber
        covs, topes, fp, mu, res = setup(cl.type_b(2))
        full = cl.analyse_cone(frozenset(range(len(topes))), topes, covs, 4,
                               res, fp, False)
        self.assertEqual(full["brown"], abs(mu))
        one = cl.analyse_cone(frozenset([0]), topes, covs, 4, res, fp, False)
        self.assertEqual(one["brown"], 0)
        self.assertEqual(one["q"], 1)

    def test_kernel(self):
        # boundary of a 4-cycle graph: one-dimensional cycle space
        eqs = [{0: 1, 1: -1}, {1: 1, 2: -1}, {2: 1, 3: -1}, {3: 1, 0: -1}]
        self.assertEqual(len(cl.kernel_mod_p(eqs, 4)), 1)

    def test_quick_run(self):
        out = io.StringIO()
        ok, st = cl.run_arrangement("B2", cl.type_b(2), "all", out=out)
        self.assertTrue(ok, out.getvalue())


if __name__ == "__main__":
    unittest.main()
