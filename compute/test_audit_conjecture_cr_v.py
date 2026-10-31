"""Unit tests for audit_conjecture_cr_v.py (positive and negative controls)."""

import unittest
from fractions import Fraction as F

import audit_conjecture_cr_v as M


def poset_lattice(elems, rel):
    """Lattice from a cover list rel (pairs x < y), closed transitively."""
    up = {x: {x} for x in elems}
    changed = True
    for a, b in rel:
        up[a].add(b)
    while changed:
        changed = False
        for x in elems:
            new = set().union(*(up[y] for y in up[x]))
            if new != up[x]:
                up[x] = new
                changed = True
    rk = {}
    for x in elems:
        rk[x] = len([y for y in elems if x in up[y]])
    return M.Lattice(elems, lambda x, y: y in up[x], lambda x: rk[x])


class LatticeControls(unittest.TestCase):
    def test_eight_element_complemented_mu_zero(self):
        # the 8-element lattice: a<y,z; b<x,y; c<x
        E = ["0", "a", "b", "c", "x", "y", "z", "1"]
        rel = [("0", t) for t in "abc"] + [("a", "y"), ("a", "z"), ("b", "x"), ("b", "y"),
                                           ("c", "x")] + [(t, "1") for t in "xyz"]
        L = poset_lattice(E, rel)
        self.assertTrue(L.is_lattice)
        self.assertEqual(L.mu(), 0)
        self.assertEqual(L.uncomplemented(), [])
        self.assertFalse(L.is_modular())

    def test_M3_N5_chain(self):
        E = ["0", "a", "b", "c", "1"]
        M3 = poset_lattice(E, [("0", t) for t in "abc"] + [(t, "1") for t in "abc"])
        self.assertTrue(M3.is_modular())
        self.assertEqual(M3.mu(), 2)
        N5 = poset_lattice(E, [("0", "a"), ("a", "b"), ("b", "1"), ("0", "c"), ("c", "1")])
        self.assertFalse(N5.is_modular())
        self.assertEqual(N5.mu(), 1)
        self.assertEqual(N5.uncomplemented(), [])
        chain = poset_lattice(["0", "a", "1"], [("0", "a"), ("a", "1")])
        self.assertEqual(chain.mu(), 0)
        self.assertEqual(len(chain.uncomplemented()), 1)

    def test_non_lattice_refused(self):
        E = ["0", "a", "b", "c", "d", "1"]
        rel = [("0", "a"), ("0", "b"), ("a", "c"), ("a", "d"), ("b", "c"), ("b", "d"),
               ("c", "1"), ("d", "1")]
        self.assertFalse(poset_lattice(E, rel).is_lattice)


class ArrangementControls(unittest.TestCase):
    def test_lie3_and_cancellation(self):
        normals, _ = M.braid(3)
        A = M.Arrangement(normals)
        allc = frozenset(range(len(A.chambers)))
        self.assertEqual(len(A.chambers), 6)
        self.assertEqual(len(A.top_cones()), 19)
        s = [[F(0), F(1)], [F(1), F(0)]]          # x1 <-> x2 in coordinates (x1-x3, x2-x3)
        P = M.Pair(A, allc, M.Sym(A, s))
        self.assertEqual(P.chi, 0)
        minus_s = [[-x for x in r] for r in s]
        P = M.Pair(A, allc, M.Sym(A, minus_s))
        z, terms = M.formula_Z(P)
        self.assertEqual((P.chi, z, sorted(terms)), (0, 0, [(0, 1, 1), (1, -1, 1)]))
        self.assertEqual(M.formula_CF(P), 0)

    def test_multiplicity_matters(self):
        # negative control: Formula Z with every m_X replaced by 1 is wrong (A2, g = 1)
        normals, _ = M.braid(3)
        A = M.Arrangement(normals)
        allc = frozenset(range(len(A.chambers)))
        P = M.Pair(A, allc, M.Sym(A, [[F(1), F(0)], [F(0), F(1)]]))
        z, terms = M.formula_Z(P)
        self.assertEqual((P.chi, z, terms), (2, 2, [(0, 1, 2)]))
        self.assertNotEqual(sum(mu for _, mu, _ in terms), P.chi)


class Counterexample(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        normals, gens = M.c6c4()
        cls.A = M.Arrangement(normals)
        cls.normals = normals
        g = [[F(-1), 0, 0, 0], [0, F(-1), 0, 0], [0, 0, F(1), 0], [0, 0, 0, F(1)]]
        cls.sym = M.Sym(cls.A, g)
        e1 = normals.index([1, 3, 0, -1])
        e2 = normals.index([1, 3, 0, 1])
        cls.V = frozenset(i for i, c in enumerate(cls.A.chambers) if c[e1] > 0 and c[e2] < 0)
        cls.P = M.Pair(cls.A, cls.V, cls.sym)

    def test_lattice(self):
        P = self.P
        self.assertEqual(len(P.M), 9)
        self.assertTrue(P.lat.is_lattice)
        self.assertEqual(P.unc, [])
        self.assertFalse(P.lat.is_modular())
        self.assertEqual(sorted(self.A.flats[z] for z in P.M), [0, 1, 1, 1, 2, 2, 2, 2, 4])

    def test_chi_zero_three_ways(self):
        P = self.P
        self.assertEqual(P.chi, 0)
        z, terms = M.formula_Z(P)
        self.assertEqual((z, sorted(terms)), (0, [(0, 1, 1), (1, -1, 1)]))
        self.assertEqual(M.formula_CF(P), 0)
        self.assertEqual(P.fixed_chambers(), 2)

    def test_other_cone_same_g_nonzero(self):
        # negative control: the same g on all chambers is nonzero (1 - 3 = -2)
        allc = frozenset(range(len(self.A.chambers)))
        Q = M.Pair(self.A, allc, self.sym)
        self.assertEqual(Q.chi, -2)


if __name__ == "__main__":
    unittest.main()
