"""Unit tests for audit_s4_eh3.py (controls and small cases)."""

import io
import unittest

import audit_s4_eh3 as S


class Controls(unittest.TestCase):
    def test_controls_fire(self):
        self.assertTrue(S.controls(io.StringIO()))

    def test_chain6_reversal(self):
        # P = 6-chain, H = <-rev>: fixes the unique chamber, e_H = 3, m_H = 1.
        n = 6
        Ar = S.braid(n)
        less = frozenset((a, b) for a in range(n) for b in range(a + 1, n))
        V = S.poset_cone(Ar, n, less)
        g = tuple(tuple(-1 if i == n - 1 - j else 0 for j in range(n)) for i in range(n))
        H = [S.ident(n), g]
        self.assertEqual(S.fix_dim(H, n, quotient_by_ones=True), 3)
        r = S.analyse_pair(V, H)
        self.assertEqual(r["m"], 1)
        self.assertEqual(r["hQ"], 2)          # X^H is a graph
        self.assertTrue(r["ok"])               # T^H ~ S^1

    def test_transposition_m0_is_2dim_contractible(self):
        # P = 5-antichain-free example: the claw 0 < 1,2,3,4; H = <(1 2)>, e_H = 3, m_H = 0.
        n = 5
        Ar = S.braid(n)
        V = S.poset_cone(Ar, n, frozenset({(0, 1), (0, 2), (0, 3), (0, 4)}))
        g = [[0] * n for _ in range(n)]
        p = [0, 2, 1, 3, 4]
        for i in range(n):
            g[p[i]][i] = 1
        H = [S.ident(n), tuple(map(tuple, g))]
        self.assertEqual(S.fix_dim(H, n, quotient_by_ones=True), 3)
        r = S.analyse_pair(V, H)
        self.assertEqual(r["m"], 0)
        self.assertEqual(r["hQ"], 3)          # X^H is 2-dimensional here
        self.assertTrue(r["ok"])               # and contractible

    def test_poset_counts(self):
        self.assertEqual([len(S.connected_posets(n)) for n in (3, 4, 5)], [3, 10, 44])


if __name__ == "__main__":
    unittest.main()
