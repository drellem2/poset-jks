"""Unit tests for conjecture_cr_v.py: positive and negative controls (run: python3 -m unittest test_conjecture_cr_v)."""
import unittest

import conjecture_cr_v as C


class Lattices(unittest.TestCase):
    def test_eight_element_lattice_is_complemented_with_mu_zero(self):
        covers = [(0, 1), (0, 2), (0, 3), (1, 5), (1, 6), (2, 4), (2, 5), (3, 4), (4, 7), (5, 7), (6, 7)]
        E, leq = C.poset_from_covers(8, covers)
        L = C.lattice(E, leq)
        self.assertEqual(L['mu'], 0)
        self.assertEqual(L['unc'], [])
        self.assertFalse(L['modular'])

    def test_chain_has_uncomplemented_elements(self):
        E, leq = C.poset_from_covers(3, [(0, 1), (1, 2)])
        L = C.lattice(E, leq)
        self.assertEqual((L['mu'], L['unc']), (0, [1]))

    def test_not_a_lattice_is_refused(self):
        # 0 < a, b < c, d < 1: a, b have two minimal upper bounds
        E, leq = C.poset_from_covers(6, [(0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 5), (4, 5)])
        with self.assertRaises(AssertionError):
            C.lattice(E, leq)


def pairs(arr, G):
    for g in C.class_reps(G):
        for cone in arr.cones():
            a = C.analyse(arr, g, cone)
            if a is not None:
                yield g, cone, a


class Theorems(unittest.TestCase):
    def test_theorem_P_pointed(self):
        arr, G = C.typeB(2)
        seen_zero = seen_nonzero = False
        for g, cone, a in pairs(arr, G):
            if a['Lz'] != arr.full:
                continue
            idx = {z: i for i, z in enumerate(a['lam'])}
            if a['clU'] != 0:   # Fix g in a hyperplane: cl(U) is uncomplemented and mu = 0
                seen_zero = True
                self.assertIn(idx[a['clU']], a['L']['unc'])
                self.assertEqual(a['L']['mu'], 0)
            else:               # negative control: then cl(U) = R^d and mu != 0
                seen_nonzero = True
                self.assertNotEqual(a['L']['mu'], 0)
        self.assertTrue(seen_zero and seen_nonzero)

    def test_lemma_K_needs_U_inside_W(self):
        """Negative control for Lemma K: an element not containing U can have a complement outside L."""
        arr, G = C.typeA(4)
        found = False
        for g, cone, a in pairs(arr, G):
            lam, Lt = a['lam'], a['L']
            for i, W in enumerate(lam):
                if (W & ~a['clU']) != 0 and W != 0:   # zero(W) not inside zero(cl U): U not inside W
                    for x in Lt['comps'][i]:
                        if (lam[x] & a['Lz']) != a['Lz']:
                            found = True
            if found:
                break
        self.assertTrue(found)

    def test_sweeps_small(self):
        for b in (lambda: C.typeA(3), C.deleted_a3, lambda: C.generic(3)):
            arr, G = b()
            st = C.sweep(arr, G, arr.name)
            self.assertFalse(st['crv_fail'])
            self.assertTrue(st['P_ok'] and st['Q_ok'] and st['K_ok'] and st['line_ok'])
            self.assertEqual(st['crvp_fail'], 0)

    def test_line_formula_needs_the_subtraction(self):
        """Prop. Ln: chi = c_0 - c_L; c_0 alone is wrong on some line pair (generic 4 in R^3)."""
        arr, G = C.generic(3)
        wrong = 0
        for g, cone, a in pairs(arr, G):
            BL = arr.basis(a['Lz'])
            if len(BL) == 1 and a['clU'] == 0 and C.rank(BL + a['U'], arr.d) == 1 + len(a['U']):
                c0 = sum(1 for i in cone if g.act_cov(arr.topes[i]) == arr.topes[i])
                chi = (-1) ** arr.d * g.det * a['L']['mu']
                wrong += chi != c0
        self.assertGreater(wrong, 0)

    def test_strict_form_of_CR_V_prime_fails(self):
        """'An element inside L has no complement' alone is not enough: generic 5 in R^4 has 4 zeros
        (L + U in no hyperplane) where only cl(U) is uncomplemented."""
        arr, G = C.generic(4)
        st = C.sweep(arr, G, arr.name)
        self.assertEqual((st['strict_fail'], st['crvp_fail'], len(st['crv_fail'])), (4, 0, 0))

    def test_counterexample(self):
        self.assertTrue(C.part_counterexample())

    def test_counterexample_lattice_is_8_element_pattern_plus_one_coatom(self):
        """The 9-element lattice minus the coatom D = span{(-2,3,0,0), e_4} is the 8-element lattice
        of the prior-art note: still complemented with mu = 0."""
        names = ["0", "a", "b", "c", "L", "B", "C", "1"]
        covers = [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (1, 5), (3, 5), (3, 6), (4, 7), (5, 7), (6, 7)]
        E, leq = C.poset_from_covers(8, covers)
        Lt = C.lattice(E, leq)
        self.assertEqual((Lt['mu'], Lt['unc']), (0, []))
        E, leq = C.poset_from_covers(9, covers[:-3] + [(3, 7), (4, 8), (5, 8), (6, 8), (7, 8)])
        Lt = C.lattice(E, leq)
        self.assertEqual((Lt['mu'], Lt['unc']), (0, []))


if __name__ == "__main__":
    unittest.main()
