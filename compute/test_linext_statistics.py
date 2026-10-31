import io
import unittest
from contextlib import redirect_stdout

import linext_statistics as m
import linear_extensions as LE


class TestLinextStatistics(unittest.TestCase):
    def setUp(self):
        m.FAILS.clear()

    def test_full_run_small(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = m.main(["--nmax", "5", "--lmax", "4", "--fmax", "5"])
        self.assertEqual(rc, 0, buf.getvalue())

    def test_antichain_power_sums(self):
        # Omega_C(antichain_n, m) = sum_{j<=m} j^(n-1)
        n = 4
        rel = frozenset()
        L, mu = m.op_data(rel, n)
        for M in range(6):
            oc = sum(abs(mu[p]) * m.comb(M, m.ME.nblocks(p)) for p in L)
            self.assertEqual(oc, sum(j ** (n - 1) for j in range(1, M + 1)))

    def test_two_chains_plus_point_example(self):
        # P = {0<2} + {1<4} + {3}: the labelling on which the naive
        # last-block descent sum fails, but the corrected expansion holds.
        rel = frozenset({(0, 2), (1, 4)})
        n = 5
        L, mu = m.op_data(rel, n)
        lin = LE.linexts(rel, n)
        comps, lab = LE.components(rel, n)
        T = set(comps[lab[4]])
        for M in range(7):
            oc = sum(abs(mu[p]) * m.comb(M, m.ME.nblocks(p)) for p in L)
            self.assertEqual(m.omegaC_des(lin, n, M, T, lab, comps), oc)
        naive = [w for w in lin if T <= m.last_block(w, lab, comps)]
        self.assertNotEqual(
            [m.omega(naive, n, M) for M in range(7)],
            [sum(abs(mu[p]) * m.comb(M, m.ME.nblocks(p)) for p in L) for M in range(7)])

    def test_control_fails_detected(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            m.control(0, "dummy")
        self.assertIn("CONTROL dummy", m.FAILS)


if __name__ == "__main__":
    unittest.main()
