import unittest

import audit_natural_isomorphism as a


class TestAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.posets = a.enumerate_posets(4)
        cls.p = a.PRIMES[0]

    def test_counts(self):
        self.assertEqual([len(self.posets[n]) for n in range(1, 5)],
                         [1, 2, 5, 16])

    def test_full_small_run(self):
        self.assertEqual(a.main(["--nmax", "4", "--nsh", "4", "--ncon", "4",
                                 "--nsum", "4"]), 0)

    def test_lambda_one_drops_on_every_disconnected_poset(self):
        # sum of all class sums at lam == 1 is sum Lin P = Lin P_1 sh Lin P'
        for n in range(2, 5):
            for rel in self.posets[n]:
                if len(a.components(rel, n)) > 1:
                    r, e = a.psi_rank(rel, n, [1] * n, self.p)
                    self.assertLess(r, e)

    def test_single_word_not_in_sh_but_shuffle_is(self):
        self.assertFalse(a.in_sh({(0, 1, 2): 1}, 3, self.p))
        v = {}
        for z in a.shuffle((0,), (1, 2)):
            a.add(v, z, 1, self.p)
        self.assertTrue(a.in_sh(v, 3, self.p))

    def test_n2_antichain(self):
        # (01 + 10) e_zeta = 0 for zeta = -1
        z = self.p - 1
        y = {}
        for w in [(0, 1), (1, 0)]:
            for u, c in a.we_zeta(w, z, self.p).items():
                a.add(y, u, c, self.p)
        self.assertFalse(any(y.values()))


if __name__ == "__main__":
    unittest.main()
