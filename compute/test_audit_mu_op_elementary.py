"""Unit tests for audit_mu_op_elementary.py.
Run (from compute/): python3 -m unittest test_audit_mu_op_elementary"""

import unittest
from math import factorial

import audit_mu_op_elementary as a


class TestAuditMuOpElementary(unittest.TestCase):
    def setUp(self):
        a.FAIL.clear()

    def test_generator_counts(self):
        # positive control: A000112
        self.assertEqual([len(a.all_posets(n)) for n in range(1, 6)], [1, 2, 5, 16, 63])

    def test_mobius_positive_controls(self):
        for n in range(1, 6):
            anti = tuple([0] * n)
            chain = tuple(sum(1 << y for y in range(x + 1, n)) for x in range(n))
            self.assertEqual(a.mu_OP(anti), (-1) ** (n - 1) * factorial(n - 1))
            self.assertEqual(a.mu_OP(chain), (-1) ** (n - 1))

    def test_small_values(self):
        # 1 + 2 with 1 < 2 and an isolated point: e = 3, e_C = 2, mu = 2
        up = (0, 4, 0)
        self.assertEqual(len(a.lin_exts(up)), 3)
        self.assertEqual(a.e_C(up), 2)
        self.assertEqual(a.mu_OP(up), 2)

    def _run(self, nmax):
        st, ctx = a.Stats(), a.Ctx()
        for n in range(1, nmax + 1):
            for up in a.all_posets(n):
                a.check_poset(up, st, ctx, True)
        return st

    def test_all_checks_and_controls_n_le_4(self):
        st = self._run(4)
        self.assertEqual(a.FAIL, [])
        for k in ("A", "C", "Cbij", "D", "F", "Mb", "Mclose", "U", "W", "W(J)",
                  "Wdual", "Z", "prod", "comp", "pab"):
            self.assertEqual(st.c[k][0], 0, k)
            self.assertGreater(st.c[k][1], 0, k)
        for k in ("neg:A-e", "neg:C-e", "neg:C-mid", "neg:D-mid", "neg:F-nokappa",
                  "neg:W-strict", "neg:Wdual-top"):
            self.assertGreater(st.c[k][0], 0, k)

    def test_mutated_eC_is_detected(self):
        # negative control on the harness: count words, not necklaces
        orig = a.necklace
        try:
            a.necklace = lambda w: w
            st = self._run(3)
        finally:
            a.necklace = orig
        self.assertGreater(st.c["A"][0], 0)
        self.assertGreater(st.c["C"][0], 0)


if __name__ == "__main__":
    unittest.main()
