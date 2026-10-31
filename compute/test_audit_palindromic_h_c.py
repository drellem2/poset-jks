import unittest

import audit_palindromic_h_c as A


def h_of(n, rel):
    a, ok = A.omega_c_coeffs(n, frozenset(rel))
    assert ok
    return A.h_from_omega(n, [A.omega_c(a, m) for m in range(n + 2)])


class TestAudit(unittest.TestCase):
    def test_poset_counts(self):
        P = A.all_posets(6)
        self.assertEqual([len(P[n]) for n in range(1, 7)], [1, 2, 5, 16, 63, 318])

    def test_small_h(self):
        self.assertEqual(h_of(2, set()), [1])
        self.assertEqual(h_of(4, {(0, 1), (2, 3)}), [1, 3, 1])
        self.assertEqual(h_of(4, {(0, 1), (1, 2), (0, 2)}), [1, 2])
        self.assertEqual(h_of(4, set()), [1, 4, 1])
        c3c3 = {(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)}
        self.assertEqual(h_of(6, c3c3), [1, 8, 9, 1])

    def test_three_C3_gap(self):
        rel = set()
        for b in (0, 3, 6):
            rel |= {(b, b + 1), (b + 1, b + 2), (b, b + 2)}
        n, L, r = 9, 3, 3
        # literal end coefficients (Moebius at n = 9 is too slow)
        comps = A.components(n, frozenset(rel))
        T = comps[0]
        cl = A.clusters(comps, T)
        hd = A.omegabar_literal(n, frozenset(rel), comps, T, L)
        hd1 = A.omegabar_literal(n, frozenset(rel), comps, T, L + 1) - (n + 1) * hd
        anch2 = sum(1 for f in A.weak_maps(n, frozenset(rel), 2) if A.anchored(f, n, cl))
        h1 = anch2 - (n + 1)
        self.assertEqual(hd, 1)
        self.assertEqual(hd1 - h1, 2 ** (r - 1) - 1)

    def test_strict_count_against_all_maps(self):
        P = A.all_posets(5)
        for n in range(1, 6):
            for rel in P[n]:
                for m in range(1, 5):
                    self.assertEqual(A.count_strict(n, rel, m), A.count_strict_allmaps(n, rel, m))

    def test_graded(self):
        self.assertTrue(A.is_graded(3, frozenset({(0, 1), (1, 2), (0, 2)})))
        # 0<2, 1<2, 2<3 graded? chains 0<2<3 and 1<2<3: yes; add 4<3: chain 4<3 has 2 elements: no
        self.assertFalse(A.is_graded(5, frozenset({(0, 2), (1, 2), (2, 3), (0, 3), (1, 3), (4, 3)})))


if __name__ == "__main__":
    unittest.main()
