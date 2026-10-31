"""Unit tests for audit_observation_cc.py (positive and negative controls)."""

import unittest

import audit_observation_cc as A


def poset(n, rels):
    down = [0] * n
    for (i, j) in rels:
        down[j] |= 1 << i
    # transitive closure
    changed = True
    while changed:
        changed = False
        for j in range(n):
            new = down[j]
            for i in A.bits(down[j]):
                new |= down[i]
            if new != down[j]:
                down[j], changed = new, True
    return down


def run(n, down, eps, t):
    PI, data = A.all_partition_data(n)
    rels = [(i, j) for j in range(n) for i in A.bits(down[j])]
    OP = [m for (m, lab) in data if A.acyclic(lab, rels)]
    return A.analyse_pair(n, down, eps, t, OP, PI)


class Controls(unittest.TestCase):
    def test_counts(self):
        reps = A.posets_upto_iso(6)
        self.assertEqual([len(reps[n]) for n in range(7)], [1, 1, 2, 5, 16, 63, 318])

    def test_antichain_identity_is_not_cc(self):
        rec = run(4, [0] * 4, 1, (0, 1, 2, 3))
        self.assertEqual((rec["mu"], rec["low"], rec["high"]), (-6, False, False))
        self.assertEqual(rec["fails"], {})

    def test_w4_pair_needs_high(self):
        # odd point 4 isolated and fixed; 0<1, 2<3, tau = (0 3)(1 2)(4)
        down = poset(5, [(0, 1), (2, 3)])
        t = (3, 2, 1, 0, 4)
        self.assertEqual(len(A.morphisms(5, down, True)) > 0, True)
        rec = run(5, down, -1, t)
        self.assertEqual(rec["row"], "W-4")
        self.assertTrue(rec["zero"] and rec["high"])
        self.assertFalse(rec["cD"])
        self.assertEqual(rec["fails"], {})

    def test_failure_path_fires(self):
        # a broken lattice routine (HIGH always false) must be reported as a CC
        # failure on a HIGH-only W-4 zero
        reps = A.posets_upto_iso(5)
        orig = A.Lattice.high
        try:
            A.Lattice.high = lambda self, at: False
            nfail = 0
            for down in reps[5]:
                for rec in A.work_poset((5, down)):
                    nfail += rec["fails"].get("CC", 0)
        finally:
            A.Lattice.high = orig
        self.assertEqual(nfail, 3)   # the three HIGH-only zeros at n = 5

    def test_complemented_mu0_lattice_found(self):
        reps = A.posets_upto_iso(6)
        k, down, comp = A.find_complemented_mu0(reps)
        self.assertTrue(comp)


if __name__ == "__main__":
    unittest.main()
