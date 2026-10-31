import io
import unittest
from contextlib import redirect_stdout

import promotion_on_R_P as m


class TestPromotionOnRP(unittest.TestCase):
    def setUp(self):
        m.FAILS.clear()

    def test_promotion_antichain_is_rotation(self):
        self.assertEqual(m.promote((2, 0, 3, 1), frozenset()), (0, 3, 1, 2))

    def test_rho_last_letter(self):
        # the only word of rho(c) ending in c_m is c itself
        vec = m.rho((2, 0, 1, 3))
        self.assertEqual({w: x for w, x in vec.items() if w[-1] == 3}, {(2, 0, 1, 3): 1})

    def test_pi_kills_shuffles_not_words(self):
        self.assertEqual(m.pi(m.shuffle_vec((0, 3), (2, 1)), 3), {})
        self.assertTrue(m.pi({(0, 1, 2, 3): 1}, 3))

    def test_two_chains_preserve(self):
        rel = frozenset({(0, 1), (0, 2), (1, 2), (3, 4)})   # C_3 + C_2
        comps = m.components(rel, 5)
        holds, cert, cnt = m.preserves(rel, 5, comps)
        self.assertTrue(holds)
        self.assertEqual(cnt, 2)

    def test_three_points_fail(self):
        holds, cert, _ = m.preserves(frozenset(), 3, m.components(frozenset(), 3))
        self.assertFalse(holds)
        self.assertEqual(m.proof_certificate(frozenset(), 3, m.components(frozenset(), 3)),
                         ("B", True))

    def test_nonchain_component_fails(self):
        rel = frozenset({(0, 1), (0, 2), (3, 4)})          # V + C_2
        comps = m.components(rel, 5)
        self.assertFalse(m.preserves(rel, 5, comps)[0])
        self.assertEqual(m.proof_certificate(rel, 5, comps), ("A", True))

    def test_main_n6_positive_control(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = m.main(["--nmax", "6"])
        self.assertEqual(code, 0, buf.getvalue())
        self.assertIn("9 of 108 (linear_extensions.md: 9 of 108): PASS", buf.getvalue())


if __name__ == "__main__":
    unittest.main()
