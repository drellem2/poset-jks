"""Tests for oriented_matroid_cones.py, with positive controls (run from compute/)."""

import io
import itertools
import unittest

import oriented_matroid_cones as om


def lt(a, b):
    return a != b and om.leq(a, b)


class Instruments(unittest.TestCase):
    def test_reduced_betti_sphere_and_ball(self):
        # Proper faces of a triangle (boundary): a circle.  All faces: a cone.
        verts = [frozenset([i]) for i in range(3)]
        edges = [frozenset(e) for e in itertools.combinations(range(3), 2)]
        sub = lambda a, b: a < b
        self.assertEqual(om.reduced_betti(verts + edges, sub), {1: 1})
        self.assertEqual(om.reduced_betti(verts + edges + [frozenset(range(3))], sub), {})
        self.assertEqual(om.reduced_betti([], sub), {-1: 1})
        self.assertEqual(om.reduced_betti(verts, sub), {0: 2})

    def test_chirotope_check_rejects_a_perturbation(self):
        # Control for [chi]: flipping one basis sign of A3 is not a chirotope.
        chi = om.chirotope_from_vectors(om.braid_vectors(4))
        self.assertTrue(om.check_chirotope(chi, 6, 3)[0])
        bad = 0
        for B, v in chi.items():
            if v:
                c2 = dict(chi)
                c2[B] = -v
                bad += not om.check_chirotope(c2, 6, 3)[0]
        self.assertGreater(bad, 0)

    def test_nonpappus_certificate_and_control(self):
        chi, pz, xyz = om.non_pappus(1)
        f = om.nonpappus_extra(pz, xyz)
        self.assertEqual(f(chi)[0], 1)
        # Control: the realizable Pappus chirotope fails the certificate.
        vecs, _ = om.pappus_points()
        self.assertEqual(f(om.chirotope_from_vectors(vecs))[0], 0)
        self.assertEqual(len(pz), 9)


class Runs(unittest.TestCase):
    def test_A3_reproduces_known_values(self):
        out = io.StringIO()
        ok, info = om.run("A3", om.chirotope_from_vectors(om.braid_vectors(4)), 6, 3, out)
        self.assertTrue(ok, out.getvalue())
        self.assertEqual(info["cones"], 219)   # A001035(4); general_theory.txt [A3]
        self.assertEqual(info["mu"], 6)
        self.assertEqual(info["topes"], 24)

    def test_nonpappus_quick(self):
        out = io.StringIO()
        chi, pz, xyz = om.non_pappus(-1)
        ok, info = om.run("np", chi, 9, 3, out, quick=True,
                          extra=om.nonpappus_extra(pz, xyz))
        self.assertTrue(ok, out.getvalue())
        self.assertEqual(info["mu"], 20)
        self.assertEqual(info["cones"], 1295)
        # the det twist is detected at V = all topes (g = -1, det = -1)
        self.assertEqual(info["ctrl"], info["cones"] - 1)

    def test_lineality_restriction_matters(self):
        # Control for [zas]: summing over all of Lambda(V) instead of the
        # flats containing S_max fails on some cone of non-Pappus.
        chi, _, _ = om.non_pappus(1)
        n, r = 9, 3
        L = om.covectors_from_cocircuits(om.cocircuits(chi, n, r), n)
        topes = [x for x in L if all(x)]
        less = lambda A, B: A != B and A > B
        dimx = {}
        for x in sorted(L, key=lambda x: -len(om.zeros(x))):
            dimx[x] = 0 if not any(x) else 1 + max(dimx[y] for y in dimx if lt(y, x))
        rkZ = {om.zeros(x): r - dimx[x] for x in L}
        bad = 0
        seen = set()
        for s in itertools.islice(itertools.product((1, 0, -1), repeat=n), 0, None, 5):
            V = frozenset(t for t in topes if all(c == 0 or t[e] == c for e, c in enumerate(s)))
            if not V or V in seen:
                continue
            seen.add(V)
            Smax = {e: next(iter(V))[e] for e in range(n) if len({t[e] for t in V}) == 1}
            FV = [x for x in L if all(x[e] in (0, c) for e, c in Smax.items())]
            Lam = sorted({om.zeros(x) for x in FV}, key=lambda Z: -len(Z))
            mu = om.mobius_to_top(Lam, less, frozenset())
            wrong = sum((-1) ** rkZ[Z] * mu[Z] for Z in Lam)
            right = sum((-1) ** rkZ[Z] * mu[Z] for Z in Lam if Z >= frozenset(Smax))
            self.assertEqual(right, len(V))
            bad += wrong != len(V)
        self.assertGreater(bad, 0)


if __name__ == "__main__":
    unittest.main()
