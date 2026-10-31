"""Unit tests for audit_qsym_refinement_omega_c.py (hand-checked small cases)."""
import unittest
import audit_qsym_refinement_omega_c as A

fs = frozenset

# C_2 + C_1: 0 isolated, 1 < 2.
C2C1 = (0, 0, 0b010)
# antichain on {0,1,2}
A3 = (0, 0, 0)


class T(unittest.TestCase):
    def test_poset_counts(self):
        L = A.all_posets(5)
        self.assertEqual([len(L[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])

    def test_M_F_roundtrip(self):
        Fc = {fs(): 1, fs({2}): 3, fs({1, 3}): -2}
        self.assertEqual(A.M_to_F(A.F_to_M(Fc, 4), 4), Fc)

    def test_chain_example_depends_on_T(self):
        comps = A.components(C2C1)
        K0 = A.K_chain(C2C1, comps, 0b001)
        K12 = A.K_chain(C2C1, comps, 0b110)
        self.assertEqual(K0, {fs(): 1, fs({2}): 1})
        self.assertEqual(K12, {fs(): 1, fs({1}): 1})
        lit = A.K_literal(C2C1, comps, [0b001, 0b110])
        self.assertEqual(lit[0b001], K0)
        self.assertEqual(lit[0b110], K12)

    def test_no_rotation_rule_identity_labelling(self):
        # identity labelling, T = {0}: (E*_T) fails (t = 0 < minimal 1), and the
        # class {102} would force F_{1}, absent from K_{C,{0}}.
        comps = A.components(C2C1); lab = [0, 1, 2]
        self.assertFalse(A.E_star(C2C1, comps, 0b001, lab))
        self.assertTrue(A.E_star(C2C1, comps, 0b110, lab))
        self.assertEqual(A.Des((1, 0, 2), lab), fs({1}))

    def test_rotation_choice_matching(self):
        comps = A.components(C2C1); L = A.linexts(C2C1)
        classes = list({A.cls(w, comps) for w in L})
        K0 = A.K_chain(C2C1, comps, 0b001); K12 = A.K_chain(C2C1, comps, 0b110)
        ident = [0, 1, 2]                 # isolated point labelled 0: fails for T = {0}
        self.assertFalse(A.choice_exists(classes, ident, K0))
        self.assertTrue(A.choice_exists(classes, ident, K12))
        mid = [1, 0, 2]                   # isolated point labelled 1: works for both T
        self.assertTrue(A.choice_exists(classes, mid, K0))
        self.assertTrue(A.choice_exists(classes, mid, K12))
        self.assertTrue(all(A.E_star(C2C1, comps, T, mid) for T in comps))

    def test_antichain_class_not_F_positive(self):
        comps = A.components(A3); lab = [0, 1, 2]; T = 0b010
        k = A.cls((0, 1, 2), comps)
        self.assertEqual(k, {(0, 1, 2), (1, 2, 0), (2, 0, 1)})
        c = A.Fsum((J, d) for w in k for J, d in A.G_T(w, comps, T, lab).items())
        self.assertEqual(c, {fs(): 1, fs({1}): 1, fs({2}): -1})

    def test_lambda_T_and_theorem_Q_small(self):
        P = (0, 0, 0b001, 0b001)  # 0 < 2, 0 < 3, 1 isolated
        comps = A.components(P); T = 0b1101
        lab = A.lambda_T(P, comps, T)
        self.assertTrue(A.natural(P, lab) and A.separated(P, comps, lab)
                        and A.E_star(P, comps, T, lab))
        L = A.linexts(P)
        Q = A.Fsum((A.Des(w, lab), 1) for w in L if A.last_piece_has(w, comps, T))
        self.assertEqual(Q, A.K_chain(P, comps, T))


if __name__ == '__main__':
    unittest.main()
