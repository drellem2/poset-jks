import unittest
import audit_quotient_categories as A


class T(unittest.TestCase):
    def test_rp2_torsion_detected(self):
        self.assertEqual(A.reduced_betti_complex(A.RP2, 2), {1: 1, 2: 1})
        self.assertEqual(A.reduced_betti_complex(A.RP2, 3), {})

    def test_torus(self):
        self.assertEqual(A.reduced_betti_complex(A.torus7(), 3), {1: 2, 2: 1})

    def test_beta(self):
        self.assertEqual(A.beta_desc(5, [2, 4]), 16)
        self.assertEqual(A.beta_desc(6, [2, 4]), 61)

    def test_val_count(self):
        # 2-block decompositions sharing restriction labels
        self.assertEqual(sum(1 for up in __import__('itertools').product((0, 1, 2), repeat=2)
                             if not (1 in up and 2 in up)), 7)

    def test_mixed_nonpointed(self):
        lam, desc, nch, pointed, cG = A.mixed_case(3, [(0, 1), (1, 2), (0, 2)], [(0, 1)])
        self.assertEqual(lam, desc)
        self.assertFalse(pointed)
        self.assertEqual(nch, 3)


if __name__ == "__main__":
    unittest.main()
