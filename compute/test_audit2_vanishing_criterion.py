"""Positive and negative controls for audit2_vanishing_criterion.py."""
import unittest

import audit2_vanishing_criterion as V


def quiet(*a, **k):
    pass


class TestEngine(unittest.TestCase):
    def test_counts_A3_B3(self):
        a, _, _ = V.typeA(4)
        self.assertEqual((len(a.flats), len(a.covectors), len(a.chambers), len(a.top_cones())),
                         (15, 75, 24, 219))
        b, _, _ = V.typeB(3)
        self.assertEqual((len(b.chambers), len(b.top_cones())), (48, 941))

    def test_lie4_character(self):
        # Lie_4 on all chambers of A3: 6, -2, 0, 0, 0 at 1, (12), (12)(34), (123), (1234)
        a, G, W = V.typeA(4)
        vals = sorted(V.chi_def(a, {}, cl[0]) for cl in V.conj_classes(W))
        self.assertEqual(vals, [-2, 0, 0, 0, 6])

    def test_non_symmetry_rejected(self):
        a, _, _ = V.generic(3)
        with self.assertRaises(ValueError):
            V.Sym(a, ((1, 1, 0), (0, 1, 0), (0, 0, 1)))


class TestFormulaZ(unittest.TestCase):
    def _pairs(self, arr, G):
        for m in arr.top_cones():
            S = arr.cone_constraints(m)
            for g in G:
                if g.act_mask(m) == m:
                    yield S, g

    def test_Z_all_elements_generic3(self):
        arr, G, _ = V.generic(3)
        n = 0
        for S, g in self._pairs(arr, G):
            gd = V.GData(arr, g)
            terms = gd.Z_terms(S)
            self.assertEqual(V.chi_def(arr, S, g), sum(mu * m for _, mu, m in terms))
            self.assertTrue(all(m >= 1 for _, _, m in terms))
            n += 1
        self.assertGreater(n, 200)

    def test_Z_needs_transversality_and_multiplicity(self):
        # dropping "X + U in no hyperplane", or replacing m_X by 1, breaks (Z)
        arr, G, _ = V.typeA(4)
        drop_fail = mult_fail = False
        for S, g in self._pairs(arr, G):
            gd = V.GData(arr, g)
            chi = V.chi_def(arr, S, g)
            terms = gd.Z_terms(S)
            if sum(mu for _, mu, _ in terms) != chi:
                mult_fail = True
            L = arr.lin(S)
            k = len(g.fix)
            loose = 0
            for X in gd.stable:
                BX = arr.basis(X)
                if not arr.leq(X, L):
                    continue
                if BX and g.fix and V.rank(BX + g.fix) != len(BX) + k:
                    continue
                if X in gd.Zstar:
                    loose += gd.mu0[X] * gd.m_X(X, S)
                else:
                    loose += gd.mu0[X]
            if loose != chi:
                drop_fail = True
            if drop_fail and mult_fail:
                break
        self.assertTrue(drop_fail)
        self.assertTrue(mult_fail)

    def test_audit_runs_on_probes(self):
        for b in (V.b3_minus_one, V.deleted_a3, lambda: V.generic(3), lambda: V.typeA(3)):
            arr, G, W = b()
            st = V.audit_arrangement(arr, G, W, out=quiet)
            self.assertEqual(st['Z_ok'], st['pairs'])
            self.assertEqual(st['S_ok'], st['classes'])

    def test_cancellation_A2(self):
        # -s12 on A2: Z* = {0, H12}, terms +1 and -1, chi = 0 on all chambers
        arr, G, W = V.typeA(3)
        st = V.audit_arrangement(arr, G, W, out=quiet)
        self.assertEqual(st['cancel'], 2)


class TestTopLune(unittest.TestCase):
    def test_nonminimal_witness_can_fail(self):
        # for some g and some non-minimal X in Z*(g) with mu != 0, the top-lune
        # of X has chi != mu(0, X): minimality is needed
        found = False
        for b in (V.b3_minus_one, lambda: V.typeA(4)):
            arr, G, _ = b()
            for cl in V.conj_classes(G):
                g = cl[0]
                gd = V.GData(arr, g)
                good = [X for X in gd.Zstar if gd.mu0[X] != 0]
                for X in good:
                    if not any(Y != X and arr.leq(Y, X) for Y in gd.Zstar if gd.mu0[Y] != 0):
                        continue
                    for C in arr.chambers:
                        r = tuple(C[e] if e in X else 0 for e in range(arr.n))
                        if g.act(r) == r:
                            S = {e: r[e] for e in X}
                            if V.chi_def(arr, S, g) != gd.mu0[X]:
                                found = True
                            break
            if found:
                break
        self.assertTrue(found)


class TestTheoremA(unittest.TestCase):
    def test_rule_n_le_6(self):
        for n in range(3, 7):
            rows = V.theorem_A_check(n)
            self.assertTrue(all(c == r for _, _, c, r, _, _ in rows))

    def test_examples(self):
        rows = {(e, l): c for e, l, c, _, _, _ in V.theorem_A_check(6)}
        for lam in [(3, 3), (6,), (2, 2, 1, 1)]:
            self.assertTrue(rows[(-1, lam)])
        rows5 = {(e, l): c for e, l, c, _, _, _ in V.theorem_A_check(4)}
        self.assertFalse(rows5[(-1, (4,))])
        self.assertFalse(rows5[(-1, (3, 1))])

    def test_even_m_is_wrong(self):
        # allowing even m (lengths in {m, 2m}) would wrongly call -(4,2) nonzero
        rows = {(e, l): c for e, l, c, _, _, _ in V.theorem_A_check(6)}
        self.assertFalse(rows[(-1, (4, 2))])

    def test_hanlon_vs_recursion(self):
        for b in range(1, 7):
            for lam in V.partitions_of_int(b):
                s = V.perm_of_type(lam)
                self.assertEqual(V.mu_fixed_lattice(b, s), V.hanlon(b, s))


if __name__ == '__main__':
    unittest.main()
