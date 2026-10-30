import subprocess
import sys
import unittest

import audit_character_identity as A


def run(*args):
    return subprocess.run([sys.executable, "audit_character_identity.py", *args],
                          capture_output=True, text=True).returncode


class TestAudit(unittest.TestCase):
    def test_poset_counts(self):
        self.assertEqual([len(A.all_posets(n)) for n in range(1, 5)], [1, 2, 5, 16])

    def test_antichain_mu(self):
        # mu(Pi_4^g) for g of type 2^2: (-1)^{k-1} mu(d) d^{k-1} (k-1)! = 2
        n, lt = A.disjoint_union(*[(1, [])] * 4)
        self.assertEqual(A.mu_bounded(A.op_labs(n, lt, (1, 0, 3, 2))), 2)

    def test_checks_pass_small(self):
        self.assertEqual(run("--nmax", "5", "--large", "--homology", "4"), 0)

    def test_controls_fail(self):
        for c in ["no_mu_o", "no_sgn", "trace_sign", "no_mu_X", "crapo_drop", "lin_not_ec"]:
            self.assertEqual(run("--nmax", "5", "--large", "--homology", "5", "--control", c), 1, c)


if __name__ == "__main__":
    unittest.main()
