import unittest

import poset_lie_structure as m


class TestPosetLieStructure(unittest.TestCase):
    def test_mobius(self):
        self.assertEqual([m.mobius(k) for k in range(1, 11)],
                         [1, -1, -1, 0, -1, 1, -1, 0, 0, 1])

    def test_closed_formula_examples(self):
        # three 2-chains, g = (1 3 5)(2 4 6): mu(3) * e_C(2-chain) = -1
        rel = frozenset([(0, 1), (2, 3), (4, 5)])
        self.assertEqual(m.closed_formula(rel, 6, (2, 3, 4, 5, 0, 1)), -1)
        # antichain on 4, g = (1 2)(3 4): Lie_4 character on (2,2) is -2
        self.assertEqual(m.closed_formula(frozenset(), 4, (1, 0, 3, 2)), -2)
        # connected poset, g != 1: 0
        V = frozenset([(0, 1), (0, 2)])
        self.assertEqual(m.closed_formula(V, 3, (0, 2, 1)), 0)

    def test_ec_component_formula(self):
        rel = frozenset([(0, 1), (2, 3), (4, 5)])
        self.assertEqual(m.ec_component_formula(rel, 6), 74)

    def test_theorem_small(self):
        self.assertTrue(m.section_theorem(4))

    def test_homology_small(self):
        self.assertTrue(m.section_homology_real(4))

    def test_hopf_small(self):
        self.assertTrue(m.section_hopf(3))


if __name__ == "__main__":
    unittest.main()
