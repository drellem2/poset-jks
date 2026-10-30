import unittest

import audit_general_theory_hopf as a


class TestAudit(unittest.TestCase):
    def test_counts(self):
        p = a.enumerate_posets(4)
        self.assertEqual([len(p[n]) for n in range(1, 5)], [1, 2, 5, 16])

    def test_small_run(self):
        self.assertEqual(a.main(["--nmax", "4", "--nax", "3", "--nree", "5",
                                 "--nbr", "5", "--nlune", "4"]), 0)

    def test_axiom_controls_fail(self):
        # down-set coproduct is not cocommutative; ordinal-sum product is
        # not compatible with the union-of-components coproduct
        self.assertFalse(a.check_axioms(3, 'down', 'sum')['cocomm'])
        self.assertFalse(a.check_axioms(3, 'Qp', 'ordinal')['compat'])
        self.assertTrue(all(a.check_axioms(3, 'Qp', 'sum').values()))

    def test_prim_dims_and_glob_nonhomogeneity(self):
        basis = a.species_basis(range(2))
        rows = a.primitive_system(range(2), basis, 'Qp')
        self.assertEqual(len(a.kernel_basis(rows, len(basis))), 3)
        rowsQ = a.primitive_system(range(2), basis, 'Q')
        byP = {}
        for i, b in enumerate(basis):
            byP.setdefault(b[0], []).append(i)
        hom = sum(len(a.kernel_basis(rowsQ, len(basis), c)) for c in byP.values())
        self.assertEqual(hom, 1)   # only the antichain bracket is homogeneous

    def test_two_antichain_prim_is_lie2(self):
        R, ints = a.prim_space(frozenset({0, 1}), frozenset())
        self.assertEqual(R.rank(), 1)
        self.assertEqual(ints[0], {(0, 1): 1, (1, 0): -1})


if __name__ == '__main__':
    unittest.main()
