"""Unit tests for audit_prop_w_prime.py.
Run (from compute/): python3 -m unittest test_audit_prop_w_prime"""

import unittest

import audit_prop_w_prime as a


def quiet(*_):
    pass


class TestAuditPropWPrime(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_counts(self):
        # positive controls: f-vector and top-cone count of A3 (75 faces, 219 cones)
        A, G, W = a.arr_A3()
        self.assertEqual(len(A.cov), 75)
        self.assertEqual(len(a.all_cones(A)), 219)
        self.assertEqual(len(W), 24)
        # every element of G preserves A
        self.assertTrue(all(A.perm_of(g) is not None for g in G))

    def test_hex_is_not_orthogonal(self):
        A, G, _ = a.arr_hex()
        self.assertEqual(len(G), 12)
        h = [[0, -1, 0], [1, 1, 0], [0, 0, 1]]
        ht = [list(r) for r in zip(*h)]
        self.assertNotEqual(a.matmul(h, ht), [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        # Fix(h) = z-axis lies in no hyperplane
        self.assertTrue(all(n[2] != 0 for n in A.n))

    def _run(self, bld):
        A, G, W = bld()
        st = a.Stats()
        a.run_arr(A, G, W, a.all_cones(A), st, quiet)
        return st

    def test_tetra7_hex7_checks_and_controls(self):
        for bld in (a.arr_tetra7, a.arr_hex):
            st = self._run(bld)
            self.assertEqual(a.FAIL, [])
            for k in ("G*", "Wex", "m>=1", "q=m", "rho", "sgn"):
                self.assertEqual(st.c[k][0], 0, k)
                self.assertGreater(st.c[k][1], 0, k)
            for k in ("neg:G*-no-det", "neg:G*-perm", "neg:rho-nosign"):
                self.assertGreater(st.c[k][0], 0, k)

    def test_A3_weisner_split(self):
        # Fix(g) not a flat: 9 pairs with Fix(g) in a hyperplane (S = 0) and
        # 11 with Fix(g) in no hyperplane (S != 0), as in the earlier audit.
        st = self._run(a.arr_A3)
        self.assertEqual(a.FAIL, [])
        self.assertEqual(st.tab[("A3", "W", "nonflat-inhyp", True)], 9)
        self.assertEqual(st.tab[("A3", "W", "nohyp", False)], 11)
        self.assertEqual(st.c["Wp"][0], 0)
        self.assertEqual(st.c["Wex"], [0, 11])
        self.assertGreater(st.c["neg:Wex-count"][0] + st.c["neg:Wex-nosign"][0], 0)


if __name__ == "__main__":
    unittest.main()
