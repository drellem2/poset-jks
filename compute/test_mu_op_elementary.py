"""Tests for mu_op_elementary.py, with positive and negative controls
(run from compute/)."""

import io
import unittest

import mu_op_elementary as m


def chain(n):
    return m.transitive_closure(n, {(i, i + 1) for i in range(n - 1)})


class Runs(unittest.TestCase):
    def test_up_to_five_passes(self):
        out = io.StringIO()
        self.assertTrue(m.run(5, out))
        self.assertIn("total posets checked: 87", out.getvalue())

    def test_poset_counts(self):
        # A000112: unlabeled posets on 1..5 points
        self.assertEqual([len(m.all_posets(n)) for n in range(1, 6)],
                         [1, 2, 5, 16, 63])


class PositiveControls(unittest.TestCase):
    def test_antichain(self):
        # OP(antichain) = Pi_n, mu = (-1)^(n-1) (n-1)!, e_C = (n-1)!
        for n, f in [(3, 2), (4, 6), (5, 24)]:
            self.assertEqual(m.mu_op(n, frozenset()), (-1) ** (n - 1) * f)
            self.assertEqual(m.e_C(n, frozenset()), f)

    def test_chain(self):
        # OP(chain) is Boolean of rank n-1, e_C = 1
        for n in range(1, 6):
            self.assertEqual(m.mu_op(n, chain(n)), (-1) ** (n - 1))
            self.assertEqual(m.e_C(n, chain(n)), 1)

    def test_lemma_w_values(self):
        # Fubini numbers with signs: sum_k (-1)^k k! S(3,k) = -1
        self.assertEqual(sum((-1) ** k for k in m.compositions(3, frozenset())), -1)
        self.assertEqual(sum((-1) ** k for k in m.compositions(3, chain(3))), 0)

    def test_weisner_complement_set(self):
        # V shape a < b, a < c: x meet pi_a = 0 iff x in {0, pi_ab, pi_ac}
        rel = frozenset({(0, 1), (0, 2)})
        L = m.op_lattice(3, rel)
        pa = m.normalize([0, 1, 1])
        comp = {x for x in L if m.meet(x, pa) == (0, 1, 2)}
        self.assertEqual(comp, {(0, 1, 2), (0, 0, 1), (0, 1, 0)})


class NegativeControls(unittest.TestCase):
    def test_lin_instead_of_eC_fails(self):
        # 2-antichain: mu = -1 but |Lin| = 2
        lin = len(m.lin_exts(2, frozenset()))
        self.assertEqual(lin, 2)
        self.assertNotEqual(m.mu_op(2, frozenset()), -lin)
        self.assertEqual(m.mu_op(2, frozenset()), -m.e_C(2, frozenset()))

    def test_recursion_needs_minimal_a(self):
        # chain 0<1<2 with a = 1 (neither minimal nor maximal):
        # only pi_{1,0}, pi_{1,2} are OP; each quotient is a 2-chain (e_C = 1),
        # so the sum is 2 != e_C = 1.
        rel = chain(3)
        tot = sum(m.e_C(*m.quotient_poset(rel, m.pi_ab(3, 1, b)))
                  for b in (0, 2) if m.is_op(rel, m.pi_ab(3, 1, b)))
        self.assertEqual(tot, 2)
        self.assertEqual(m.e_C(3, rel), 1)

    def test_broken_checker_is_caught(self):
        # mutate e_C: the main check must then report failures
        orig = m.e_C
        try:
            m.e_C = lambda n, rel: len(m.lin_exts(n, rel))
            self.assertFalse(m.run(3, io.StringIO()))
        finally:
            m.e_C = orig


if __name__ == "__main__":
    unittest.main()
