#!/usr/bin/env python3
"""Check for notes/prior_art_cr_v_type_a.md: which zeros of mu(OP(P)^t) are
already explained by EC1 Cor. 3.9.5 (0 not a meet of coatoms, or dually 1 not
a join of atoms), the mechanism of Stanley 1982, Remark after Lemma 7.1.

For every pair (P, g = eps*t) with 3 <= n <= nmax, up to isomorphism (the
enumeration of cr_v_type_a.py, imported):
  - CC  = "0 is not the meet of the coatoms of M, or 1 is not the join of the
          atoms of M";
  - check that CC implies mu(M) = 0 (EC1 Cor. 3.9.5);
  - check that CC implies an uncomplemented element: the meet of all coatoms
    (resp. the join of all atoms) has no complement (the one-line argument of
    the note, Section 2.2);
  - count the zeros that are NOT of type CC (these need the work of
    cr_v_type_a.md beyond Cor. 3.9.5);
  - count which side of CC fires (coatom meet, atom join, or both);
  - on antichains with g = +w (the all-chambers lattice Pi_n^w) check that
    mu = 0 iff CC (Stanley 1982, Remark after Lemma 7.1).

Controls: Pi_4^{(1234)} (a 3-element chain: CC holds, mu = 0) and Pi_4
(CC fails, mu = -6).

Run:  python3 prior_art_cr_v_type_a.py [--nmax 6]
Plain Python 3, single process.
"""
import sys
import time

import cr_v_type_a as C


def coatoms_atoms(M):
    E = range(len(M.elems))
    mk = M.mask
    sub = lambda i, j: i != j and (mk[i] | mk[j]) == mk[j]   # elems[i] < elems[j]
    proper = [i for i in E if i not in (M.bot, M.top)]
    coatoms = [i for i in proper if not any(sub(i, j) for j in proper)]
    atoms = [i for i in proper if not any(sub(j, i) for j in proper)]
    if not proper:                       # M = {0, 1}: the coatom is 0, the atom is 1
        coatoms, atoms = [M.bot], [M.top]
    return coatoms, atoms


def meet_all(M, idx):
    m = (1 << 62) - 1 if idx else 0
    for i in idx:
        m &= M.mask[i]
    return m


def join_all(M, idx):
    r = M.bot
    for i in idx:
        r = M.join(r, i)
    return r


def element_with_mask(M, m):
    for i, mm in enumerate(M.mask):
        if mm == m:
            return i
    return None


def analyse(M):
    mu = M.mu()
    co, at = coatoms_atoms(M)
    mco = meet_all(M, co)
    jat = join_all(M, at)
    low = mco != 0                 # 0 is not the meet of the coatoms
    high = jat != M.top            # 1 is not the join of the atoms
    cc = low or high
    witness_ok = True
    if low:
        x = element_with_mask(M, mco)   # meet in M = common refinement, so it is in M
        witness_ok &= x is not None and not M.has_complement(x)
    if high:
        witness_ok &= not M.has_complement(jat)
    analyse.side = (low, high)
    return mu, cc, witness_ok


def main(argv):
    nmax = int(argv[argv.index('--nmax') + 1]) if '--nmax' in argv else 6
    t0 = time.time()
    ok = True
    # controls
    for t, n, want_cc, want_mu in (((1, 2, 3, 0), 4, True, 0), ((0, 1, 2, 3), 4, False, -6)):
        P = C.antichain(n)
        M = C.Lattice(P, t, C.rgs_all(n), C.pair_index(n))
        mu, cc, wok = analyse(M)
        good = (cc == want_cc and mu == want_mu and wok)
        ok &= good
        print(f"[CTL] Pi_{n}^{t}: |M| = {len(M.elems)}, mu = {mu}, CC = {cc}  {'ok' if good else 'FAIL'}")
    levels = C.posets_up_to_iso(nmax)
    tot = {'pairs': 0, 'zeros': 0, 'cc': 0, 'cc_nonzero': 0, 'cc_wit_fail': 0, 'zeros_not_cc': 0,
           'anti_pairs': 0, 'anti_mismatch': 0, 'low_only': 0, 'high_only': 0, 'both': 0}
    for n in range(3, nmax + 1):
        allparts, PI = C.rgs_all(n), C.pair_index(n)
        row = {k: 0 for k in tot}
        notcc_by_sign = {1: 0, -1: 0}
        for rel in levels[n]:
            P = C.Poset(n, rel)
            is_antichain = not rel
            auts, antis = C.symmetries(P)
            for eps, elems in ((1, auts), (-1, antis)):
                for t in C.conj_classes(elems, auts):
                    M = C.Lattice(P, t, allparts, PI)
                    mu, cc, wok = analyse(M)
                    row['pairs'] += 1
                    row['zeros'] += (mu == 0)
                    row['cc'] += cc
                    row['cc_nonzero'] += (cc and mu != 0)
                    row['cc_wit_fail'] += (cc and not wok)
                    low, high = analyse.side
                    row['low_only'] += (low and not high)
                    row['high_only'] += (high and not low)
                    row['both'] += (low and high)
                    if mu == 0 and not cc:
                        row['zeros_not_cc'] += 1
                        notcc_by_sign[eps] += 1
                    if is_antichain and eps == 1:
                        row['anti_pairs'] += 1
                        row['anti_mismatch'] += ((mu == 0) != cc)
        for k in tot:
            tot[k] += row[k]
        print(f"n={n}: pairs {row['pairs']}, zeros {row['zeros']}, CC {row['cc']} "
              f"(CC with mu != 0: {row['cc_nonzero']}; CC witness failures: {row['cc_wit_fail']}), "
              f"zeros not CC {row['zeros_not_cc']} (+w {notcc_by_sign[1]}, -t {notcc_by_sign[-1]}); "
              f"antichain +w pairs {row['anti_pairs']}, mismatches {row['anti_mismatch']}; "
              f"CC sides: coatom-meet only {row['low_only']}, atom-join only {row['high_only']}, both {row['both']}")
    print(f"total: {tot}")
    ok &= tot['cc_nonzero'] == 0 and tot['cc_wit_fail'] == 0 and tot['anti_mismatch'] == 0
    print(f"total {time.time() - t0:.1f}s")
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
