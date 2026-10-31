"""Unit tests for cr_v_type_a.py (notes/cr_v_type_a.md).  ~2 s.

Positive controls: each witness case on a small pair; known lattices.
Negative controls: the witnesses are not interchangeable (a wrong choice is
complemented), and the complement test does return 'complemented'.
"""
import unittest

import cr_v_type_a as C


def lattice(P, t):
    return C.Lattice(P, t, None, C.pair_index(P.n))


def first_pair_of_case(case, nmax=6):
    levels = C.posets_up_to_iso(nmax)
    for n in range(3, nmax + 1):
        for rel in levels[n]:
            P = C.Poset(n, rel)
            auts, antis = C.symmetries(P)
            for eps, elems in ((1, auts), (-1, antis)):
                for t in C.conj_classes(elems, auts):
                    name, w = C.witness(P, eps, t)
                    if name and name.split()[0] == case:
                        return P, eps, t, w
    return None


class TestControls(unittest.TestCase):
    def test_poset_counts(self):
        L = C.posets_up_to_iso(6)
        self.assertEqual([len(L[k]) for k in range(7)], [1, 1, 2, 5, 16, 63, 318])

    def test_chain_lattice(self):
        M = lattice(C.antichain(4), (1, 2, 3, 0))
        self.assertEqual(M.mu(), 0)
        self.assertEqual([M.elems[a] for a in M.uncomplemented()], [(0, 1, 0, 1)])

    def test_partition_lattice_complemented(self):
        M = lattice(C.antichain(4), (0, 1, 2, 3))
        self.assertEqual(M.mu(), -6)
        self.assertEqual(M.uncomplemented(), [])

    def test_hanlon(self):
        for t in [(1, 0, 3, 2), (1, 2, 0, 4, 5, 3), (1, 0, 2), (1, 2, 3, 0, 4)]:
            self.assertEqual(lattice(C.antichain(len(t)), t).mu(), C.hanlon_mu(t))

    def test_stable_partitions_match_filter(self):
        for t in [(1, 0, 3, 2, 4), (1, 2, 0, 4, 5, 3), (0, 1, 2, 3, 4, 5)]:
            n = len(t)
            a = sorted(p for p in C.rgs_all(n) if C.image(p, t) == p)
            self.assertEqual(a, sorted(C.stable_partitions(n, t)))


class TestWitnesses(unittest.TestCase):
    def check_case(self, case):
        found = first_pair_of_case(case)
        self.assertIsNotNone(found, case)
        P, eps, t, w = found
        M = lattice(P, t)
        self.assertEqual(M.mu(), 0)
        self.assertTrue(M.contains(w))
        self.assertFalse(M.has_complement(M.index[w]))

    def test_W_plus_1(self):
        self.check_case('W+1')

    def test_W_plus_2(self):
        self.check_case('W+2')

    def test_W_minus_1(self):
        self.check_case('W-1')

    def test_W_minus_2(self):
        self.check_case('W-2')

    def test_W_minus_3(self):
        self.check_case('W-3')

    def test_W_minus_4(self):
        self.check_case('W-4')

    def test_TA4_example_of_PCV(self):
        # {0 < 1} + {2} + {3}, t = (0 1): witness 01 | 2 | 3 ... Q = {0, 1}
        P = C.Poset(4, [(0, 1)])
        t = (1, 0, 2, 3)
        name, w = C.witness(P, -1, t)
        self.assertEqual(name.split()[0], 'W-4')
        self.assertEqual(C.blocks_of(w), [[0, 1], [2], [3]])
        M = lattice(P, t)
        self.assertFalse(M.has_complement(M.index[w]))
        # negative control: cl(Fix g) is complemented here
        c = C.cl_fix(4, -1, t)
        self.assertTrue(M.has_complement(M.index[c]))

    def test_odd_nonsquarefree_needs_k_2m_over_p(self):
        # antichain 9, -(9): k = 2 gives cyc(t^2) = one block (complemented: the
        # top); the rule picks k = 6 and cyc(t^6) is uncomplemented
        P, t = C.antichain(9), tuple((i + 1) % 9 for i in range(9))
        self.assertEqual(C.choose_k(t), 6)
        M = lattice(P, t)
        w2 = C.cl_fix(9, 1, C.power(t, 2))
        self.assertTrue(M.has_complement(M.index[w2]))
        w6 = C.cl_fix(9, 1, C.power(t, 6))
        self.assertFalse(M.has_complement(M.index[w6]))

    def test_nonzero_pair_is_complemented(self):
        # Case IIa of [PCV]: {0<1} + {2<3}, t swapping the chains reversed
        P = C.Poset(4, [(0, 1), (2, 3)])
        t = (3, 2, 1, 0)
        self.assertTrue(P.is_anti(t))
        M = lattice(P, t)
        self.assertNotEqual(M.mu(), 0)
        self.assertEqual(M.uncomplemented(), [])


class TestLemmaC(unittest.TestCase):
    def test_free_squarefree_complemented(self):
        # antichain 6, w = (012)(345): s = 3, h = 1 -> complemented
        t = (1, 2, 0, 4, 5, 3)
        self.assertTrue(C.lemma_C_predicts_complement(tuple(range(6)), t, 1))

    def test_mixed_lengths(self):
        t = (1, 0, 2)
        self.assertFalse(C.lemma_C_predicts_complement(tuple(range(3)), t, 1))

    def test_square(self):
        t = (1, 2, 3, 0)
        self.assertFalse(C.lemma_C_predicts_complement(tuple(range(4)), t, 2))
        self.assertTrue(C.lemma_C_predicts_complement(tuple(range(4)), t, 1))


if __name__ == '__main__':
    unittest.main()
