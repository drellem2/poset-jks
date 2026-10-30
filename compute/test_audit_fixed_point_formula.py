"""Unit tests for audit_fixed_point_formula.py.
Run (from compute/): python3 -m unittest test_audit_fixed_point_formula"""

import unittest

import audit_fixed_point_formula as a


def quiet(*_):
    pass


class TestAuditFixedPointFormula(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_face_counts(self):
        # positive controls: f-vectors of A3 and B3 (75 and 147 faces incl. 0)
        self.assertEqual(len(a.braid_arr(4).cov), 75)
        B3 = a.Arr("B3", a.forms_B(3), a.signed_perm_gens(3))
        self.assertEqual(len(B3.cov), 147)
        self.assertEqual(len(B3.G), 48)

    def test_det_on_subspace(self):
        h = [[a.F(x) for x in r] for r in ([0, -1, 0], [1, 1, 0], [0, 0, 1])]
        self.assertEqual(a.det_on_subspace(h, [[1, 0, 0], [0, 1, 0]]), 1)
        m = [[a.F(-1), 0, 0], [0, a.F(1), 0], [0, 0, a.F(1)]]
        self.assertEqual(a.det_on_subspace(m, [[1, 0, 0]]), -1)

    def test_tetra7_all_checks_and_controls(self):
        T7 = a.tetra7()
        st = a.run_arr(T7, a.all_cones(T7), quiet, "tetra7")
        self.assertEqual(a.FAIL, [])
        for k in ("EZ", "CF", "2.1", "F", "W", "Wcl", "V", "P"):
            self.assertEqual(st.c[k][0], 0, k)
            self.assertGreater(st.c[k][1], 0, k)
        # negative controls fire
        for k in ("neg:2.1-no-orientation", "neg:EZ-no-detbar",
                  "neg:CF-all-chambers", "W-nonflat"):
            self.assertGreater(st.c[k][0], 0, k)

    def test_weak_weisner_a3(self):
        # Prop. W's sum vanishes exactly when Fix(g) lies in a hyperplane
        A3 = a.braid_arr(4)
        W = [e for e in A3.G if e["inW"]]
        st = a.run_arr(A3, a.all_cones(A3), quiet, "A3", reps_by=W)
        self.assertEqual(a.FAIL, [])
        xt = {k[1]: v for k, v in st.cnt.items() if isinstance(k, tuple) and k[0] == "xtab"}
        self.assertEqual(xt, {(False, False): 11, (True, True): 9})
        self.assertEqual(st.c["Wweak"][0], 0)
        self.assertGreater(st.c["Wweak"][1], st.c["W"][1])

    def test_braid_small(self):
        st = a.braid_check(4, quiet)
        self.assertEqual(a.FAIL, [])
        self.assertEqual(sum(st.c["braid:eq-closed"]), 12 + 59)

    def test_poset_counts(self):
        self.assertEqual([len(a.all_posets(n)) for n in (3, 4, 5)], [5, 16, 63])


if __name__ == "__main__":
    unittest.main()
