"""Fast tests for audit_jks_maps.py (n <= 4).  Run: python3 -m unittest test_audit_jks_maps"""
import unittest

import audit_jks_maps as A


class TestAudit(unittest.TestCase):
    def test_poset_counts(self):
        self.assertEqual([len(A.natural_posets(n)) for n in range(1, 6)], [1, 2, 7, 40, 357])
        self.assertEqual([len(A.unlabeled_posets(n)) for n in range(1, 6)], [1, 2, 5, 16, 63])

    def test_splitting_cycle_is_cycle(self):
        for w in A.perms(4):
            self.assertFalse(A.boundary(A.splitting_cycle(w)))

    def test_signed_shuffle_relation_and_control(self):
        rho = {w: A.splitting_cycle(w) for w in A.perms(4)}
        for s in A.proper_shuffles(4):
            acc, acc_u = {}, {}
            for w in s:
                A.add_into(acc, rho[w], A.sign(w))
                A.add_into(acc_u, rho[w], 1)
            self.assertFalse(any(acc.values()))
            self.assertTrue(any(acc_u.values()))

    def test_chain_and_dual_same_lattice(self):
        chain = frozenset((i, j) for i in range(1, 5) for j in range(i + 1, 5))
        dual = frozenset((j, i) for i, j in chain)
        self.assertEqual(set(A.op_lattice(chain, 4)), set(A.op_lattice(dual, 4)))
        self.assertEqual(len(A.op_lattice(chain, 4)), 8)  # Boolean B_3

    def test_conjecture_S_n4(self):
        for rel in A.unlabeled_posets(4):
            lin = A.linear_extensions(rel, 4)
            self.assertEqual(A.rank_mod_p(A.splitting_cycle(w) for w in lin), A.cyclic_classes(lin))


if __name__ == "__main__":
    unittest.main()
