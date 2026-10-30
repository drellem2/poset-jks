import unittest

import audit_conjecture_s as a


class TestAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.posets = a.unlabeled_posets(4)

    def test_counts(self):
        self.assertEqual([len(self.posets[n]) for n in range(1, 5)], [1, 2, 5, 16])

    def test_controls(self):
        self.assertTrue(a.check_CTL(self.posets))

    def test_lemma1(self):
        self.assertTrue(a.check_L1(4))

    def test_small_range(self):
        self.assertTrue(a.check_LEM(self.posets, 4))
        self.assertTrue(a.check_AB(self.posets, 4))
        self.assertTrue(a.check_CHN(self.posets, 4))
        self.assertTrue(a.check_REE(self.posets, 4))

    def test_sign_flipped_E_fails(self):
        X = a.vec_of(a.shuffle_set((0,), (1, 2)))  # x = 0 in u, a = 1 in v
        self.assertEqual(a.E(X, 1, 0), {})
        self.assertNotEqual(a.E(X, 1, 0, sign=-1), {})


if __name__ == "__main__":
    unittest.main()
