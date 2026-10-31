"""Unit tests for audit_theorem_e.py (positive and negative controls)."""

import unittest

import audit_theorem_e as A


class Controls(unittest.TestCase):
    def test_subgroup_counts(self):
        S3 = A.gen_group([A.perm_sp((1, 0, 2)), A.perm_sp((1, 2, 0))], 3)
        S4 = A.gen_group([A.perm_sp((1, 0, 2, 3)), A.perm_sp((1, 2, 3, 0))], 4)
        self.assertEqual(len(A.subgroups(S3, 3)), 6)
        self.assertEqual(len(A.subgroups(S4, 4)), 30)

    def test_orthant_S3_nonfree(self):
        Ar = A.boolean(3)
        V = A.Cone(Ar, [(1, 1, 1)])
        S3 = A.gen_group([A.perm_sp((1, 0, 2)), A.perm_sp((1, 2, 0))], 3)
        r = A.analyse(V, S3, 3, check_E=True)
        self.assertEqual(r["S_fail"], 0)      # Theorem S holds
        self.assertEqual(r["E_fail"], 5)      # Theorem E prediction fails on every H != 1
        self.assertEqual(r["empty"], 2)       # T^H empty for A_3 and S_3

    def test_pi4_transposition_acyclic_double_transposition_not(self):
        A4, _ = A.braid(4)
        V = A.Cone(A4, [f for f in A4.faces if 0 not in f])
        self.assertFalse(V.pointed)
        out = {}
        for name, g in (("t", (1, 0, 2, 3)), ("tt", (1, 0, 3, 2))):
            hp = A4.hperm(A.perm_sp(g))
            el = [z for z in V.flats if A.act_zset(hp, z) == z]
            out[name] = A.poset_betti_all(el, A.flat_lt)[0]
        self.assertEqual(out, {"t": {}, "tt": {0: 2}})

    def test_free_poset_V(self):
        # P: 0 < 1, 0 < 2 (n = 3), Aut = swap: free, d = 2
        A3, pairs = A.braid(3)
        V = A.poset_cone(A3, pairs, frozenset({(0, 1), (0, 2)}))
        G = A.gen_group([A.perm_sp((0, 2, 1))], 3)
        r = A.analyse(V, G, 3, check_E=True)
        self.assertEqual((r["E_fail"], r["S_fail"]), (0, 0))
        self.assertTrue(all(x[5] for x in r["free"]))

    def test_two_chains_not_free(self):
        A4, pairs = A.braid(4)
        V = A.poset_cone(A4, pairs, frozenset({(0, 1), (2, 3)}))
        G = A.gen_group([A.perm_sp((2, 3, 0, 1))], 4)
        r = A.analyse(V, G, 4, check_E=True)
        self.assertGreater(r["E_fail"], 0)
        self.assertFalse(any(x[5] for x in r["free"]))


if __name__ == "__main__":
    unittest.main()
