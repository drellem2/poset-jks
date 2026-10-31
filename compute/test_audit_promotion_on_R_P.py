import unittest

import audit_promotion_on_R_P as A


def poset(*comps):
    """comps: list of (size, list of relations) for each component."""
    out = []
    for s, rel in comps:
        out.append((s, A.canon(s, A.closure(s, rel))))
    return A.Poset(out)


class TestAudit(unittest.TestCase):
    def test_rho_triangular(self):
        f = A.rho((1, 2, 0))
        self.assertEqual(f, {(1, 2, 0): 1, (1, 0, 2): -1, (2, 0, 1): -1, (0, 2, 1): 1})

    def test_A3_example(self):
        P = poset((1, []), (1, []), (1, []))
        case, ann, val = A.cert_check(P, 0, (0,), (1, 2))
        self.assertEqual((case, ann, val), ('B', True, 1))
        self.assertFalse(A.def_preserves(P))

    def test_V_plus_point(self):
        # V = {0 < 1, 0 < 2}
        P = poset((3, [(0, 1), (0, 2)]), (1, []))
        ci = [i for i in range(2) if not P.chain[i]][0]
        T = P.comps[ci]
        s = P.lin(T)[0]
        B = tuple(x for x in range(4) if x not in T)
        case, ann, val = A.cert_check(P, ci, s, B)
        self.assertEqual((case, ann, val), ('A', True, 1))
        self.assertFalse(A.def_preserves(P))

    def test_two_chains_preserve(self):
        P = poset((2, [(0, 1)]), (3, [(0, 1), (1, 2)]))
        self.assertTrue(A.def_preserves(P))

    def test_negative_control(self):
        P = poset((1, []), (1, []), (1, []))
        self.assertFalse(A.annihilates_RP(P, {(0, 1, 2): 1}))

    def test_counts(self):
        allp = A.all_posets(5)
        self.assertEqual([len(allp[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])


if __name__ == '__main__':
    unittest.main()
