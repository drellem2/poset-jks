"""Unit tests for audit_lean_js_route.py: positive and negative controls."""

import unittest

import audit_lean_js_route as a


def antichain(n):
    return a.Poset.from_relations(n, [])


def chain(n):
    return a.Poset.from_relations(n, [(i, i + 1) for i in range(n - 1)])


class TestRank(unittest.TestCase):
    def test_controls(self):
        self.assertTrue(a.run_controls())

    def test_rank_Q_vs_F2(self):
        # [[2]] has rank 1 over Q and rank 0 mod 2
        self.assertEqual(a.rank_Q([{0: 2}]), 1)
        self.assertEqual(a.rank_F2([{0: 2}]), 0)

    def test_empty_poset(self):
        # Delta(empty) = {empty face}: beta_{-1} = 1
        self.assertEqual(a.reduced_betti([], lambda x, y: False), {-1: 1})


class TestPosets(unittest.TestCase):
    def test_counts(self):
        ps = a.all_posets(5)
        self.assertEqual([len(ps[n]) for n in range(1, 6)], [1, 2, 5, 16, 63])

    def test_eC(self):
        self.assertEqual(a.e_C(antichain(4)), 6)   # (n-1)!
        self.assertEqual(a.e_C(chain(4)), 1)


class TestRouteC(unittest.TestCase):
    def test_antichain4(self):
        # Lbar = proper part of Pi_4: beta_1 = 3! = 6
        r = a.check_poset(antichain(4))
        self.assertEqual({d: v for d, v in r["beta"].items() if v}, {1: 6})
        for k in ["JS", "M", "Pz", "K", "Qac", "U", "rel"]:
            self.assertTrue(r[k], k)
        self.assertTrue(r["ctl_sign"])
        self.assertTrue(r["ctl_Q"])

    def test_all_n4(self):
        for P in a.all_posets(4)[4]:
            r = a.check_poset(P)
            for k in ["JS", "M", "Pz", "K", "Qac", "U", "rel"]:
                self.assertTrue(r[k], k)

    def test_lemma_k_needs_retraction(self):
        # two-point antichain: no t with a retraction; with t = 0 and
        # p = id the identity fails (the other point is high and p(h) = h)
        less = lambda x, y: False
        ok, _ = a.lemma_k_check([0, 1], less, 0, lambda x: x)
        self.assertFalse(ok)


if __name__ == "__main__":
    unittest.main()
