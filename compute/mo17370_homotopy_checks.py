#!/usr/bin/env python3
"""Checks for notes/mo17370_wedges_of_spheres.md (homotopy vs homology of fixed lattices).

For a finite bounded lattice M with proper part Mbar, this script computes
  - the reduced Betti numbers of the order complex Delta(Mbar), as ranks mod p = 2^31 - 1
    (a mod-p Betti number bounds the rational one from above, so a 0 here is 0 over Q);
  - the Stong core of Mbar: repeatedly delete beat points (x is a beat point if the
    elements strictly below x have a maximum, or the elements strictly above x have a
    minimum). Deleting a beat point does not change the homotopy type of the order
    complex (Stong 1966; Barmak, "Algebraic topology of finite topological spaces and
    applications", LNM 2032, ch. 1 -- cited, not re-read), so a core
    with one point (or none, for empty Mbar handled separately) certifies contractibility.

Parts:
  [CTL] controls: Boolean lattice B_3 (proper part = S^1: Betti in degree 1 only, no beat
        point, core = all 6 points); a chain (contractible, core one point); the 8-element
        complemented lattice with mu = 0 of notes/prior_art_per_cone_vanishing.md section 3.2
        (contractible); a crown (S^1, no beat point: the core routine must not shrink it).
  [R4]  the CR_V counterexample family of notes/conjecture_cr_v.md: the C6 x C4 orbit
        arrangement in R^4, every class representative g and every g-stable top-cone V;
        on the pairs with mu(Lambda(V)^g) = 0 and every element complemented, report the
        Betti numbers and the Stong core of the proper part.
  [TA]  type A: every poset P on n points (3 <= n <= NMAX, up to isomorphism), every
        automorphism and anti-automorphism tau up to conjugacy, M = OP(P)^tau.
        On the zeros (mu(M) = 0): Delta(Mbar) acyclic? Stong core a point?
        On the nonzeros: is the reduced homology concentrated in one degree?
        For tau = id: Betti numbers are e_C(P) in degree n - 3 (Jenca-Sarkoci; control).

Run:  python3 mo17370_homotopy_checks.py [--nmax N]      (default N = 6)
"""
import itertools
import sys

import conjecture_cr_v as CR
import cr_v_type_a as TA

P_MOD = 2 ** 31 - 1


# ---------------------------------------------------------------- finite posets


def order_complex_betti(elems, lt):
    """Reduced Betti numbers (mod P_MOD) of the order complex of the poset (elems, lt).
    lt(a, b) means a < b. Returns a list indexed by degree -1, 0, 1, ...; index 0 is
    degree -1."""
    E = list(elems)
    up = {a: [b for b in E if lt(a, b)] for a in E}
    chains = [[()]]                      # chains[k] = chains with k elements, sorted upward
    k = 0
    while chains[k]:
        nxt = []
        for c in chains[k]:
            cands = E if not c else up[c[-1]]
            for b in cands:
                nxt.append(c + (b,))
        chains.append(nxt)
        k += 1
    chains.pop()                         # last is empty
    idx = [{c: i for i, c in enumerate(ch)} for ch in chains]
    # boundary d_k : C(k elements) -> C(k-1 elements)
    ranks = [0] * (len(chains) + 1)
    for k in range(1, len(chains)):
        rows = []
        for c in chains[k]:
            row = {}
            for i in range(len(c)):
                f = c[:i] + c[i + 1:]
                row[idx[k - 1][f]] = (row.get(idx[k - 1][f], 0) + (-1) ** i) % P_MOD
            rows.append(row)
        ranks[k] = rank_mod(rows)
    betti = []
    for k in range(len(chains)):
        dimC = len(chains[k])
        betti.append(dimC - ranks[k] - ranks[k + 1])
    return betti                         # betti[k] = reduced Betti in degree k - 1


def rank_mod(rows):
    """Rank mod P_MOD of a sparse matrix given as a list of {col: value} dicts."""
    pivots = {}
    r = 0
    for row in rows:
        row = {c: v % P_MOD for c, v in row.items() if v % P_MOD}
        while row:
            c = min(row)
            if c in pivots:
                prow = pivots[c]
                f = row[c] * pow(prow[c], P_MOD - 2, P_MOD) % P_MOD
                for cc, vv in prow.items():
                    nv = (row.get(cc, 0) - f * vv) % P_MOD
                    if nv:
                        row[cc] = nv
                    else:
                        row.pop(cc, None)
            else:
                pivots[c] = row
                r += 1
                break
    return r


def stong_core(elems, lt):
    """Delete beat points until none is left. Returns the remaining elements."""
    S = set(elems)
    changed = True
    while changed:
        changed = False
        for x in sorted(S, key=repr):
            below = [y for y in S if lt(y, x)]
            above = [y for y in S if lt(x, y)]
            down_beat = below and any(all(y == m or lt(y, m) for y in below) for m in below)
            up_beat = above and any(all(y == m or lt(m, y) for y in above) for m in above)
            if down_beat or up_beat:
                S.discard(x)
                changed = True
                break
    return S


def describe(betti):
    nz = [(k - 1, b) for k, b in enumerate(betti) if b]
    return nz


# ---------------------------------------------------------------- controls


def part_CTL():
    ok = True
    # B_3: subsets of {0,1,2}; proper part is the face poset of a triangle's boundary = S^1
    E = [frozenset(s) for r in (1, 2) for s in itertools.combinations(range(3), r)]
    lt = lambda a, b: a < b
    b = describe(order_complex_betti(E, lt))
    core = stong_core(E, lt)
    c1 = b == [(1, 1)] and len(core) == 6
    print(f"  [CTL] B_3 proper part: Betti {b} (want [(1, 1)]), core size {len(core)} (want 6) {'ok' if c1 else 'FAIL'}")
    ok &= c1
    # a chain 0 < 1 < 2 < 3: proper part {1, 2}, contractible, core one point
    E = [1, 2]
    lt = lambda a, b: a < b
    b = describe(order_complex_betti(E, lt))
    core = stong_core(E, lt)
    c2 = b == [] and len(core) == 1
    print(f"  [CTL] chain proper part: Betti {b} (want []), core size {len(core)} (want 1) {'ok' if c2 else 'FAIL'}")
    ok &= c2
    # the 8-element complemented lattice with mu = 0 ([PAP] section 3.2, as described in
    # notes/conjecture_cr_v.md section 0.2 after deleting D): atoms a, b, c; coatoms L, B, C;
    # a < L, B; b < L; c < B, C
    cov = {('a', 'L'), ('a', 'B'), ('b', 'L'), ('c', 'B'), ('c', 'C')}
    E = ['a', 'b', 'c', 'L', 'B', 'C']
    lt = lambda x, y: (x, y) in cov
    b = describe(order_complex_betti(E, lt))
    core = stong_core(E, lt)
    c3 = b == [] and len(core) == 1
    print(f"  [CTL] 8-element complemented lattice, mu = 0: Betti {b}, core size {len(core)} {'ok' if c3 else 'FAIL'}")
    ok &= c3
    # negative control for the core routine: a crown (4-cycle a<C,D; b<C,D) is S^1, no beat point
    cov = {('a', 'C'), ('a', 'D'), ('b', 'C'), ('b', 'D')}
    E = ['a', 'b', 'C', 'D']
    lt = lambda x, y: (x, y) in cov
    b = describe(order_complex_betti(E, lt))
    core = stong_core(E, lt)
    c4 = b == [(1, 1)] and len(core) == 4
    print(f"  [CTL] crown (S^1, no beat points): Betti {b}, core size {len(core)} {'ok' if c4 else 'FAIL'}")
    ok &= c4
    return ok


# ---------------------------------------------------------------- R^4 counterexamples


def part_R4():
    ok = True
    R, I2, Q = CR.rot_hex(), [[1, 0], [0, 1]], [[0, -1], [1, 0]]
    arr, G = CR.orbit_arrangement(4, [CR.block(R, I2), CR.block(I2, Q)], [[2, -1, 0, -1]], "R^4 C6 x C4")
    cones = arr.cones()
    reps = CR.class_reps(G)
    fails, pairs, zeros = [], 0, 0
    zero_unc_contractible = zero_unc_total = 0
    for g in reps:
        for cone in cones:
            a = CR.analyse(arr, g, cone)
            if a is None:
                continue
            pairs += 1
            Lt = a['L']
            if Lt['mu'] != 0:
                continue
            zeros += 1
            n = len(a['lam'])
            prop = [i for i in range(n) if i not in (Lt['bot'], Lt['top'])]
            lt = lambda x, y, up=Lt['up']: x != y and y in up[x]
            betti = describe(order_complex_betti(prop, lt))
            core = stong_core(prop, lt)
            if Lt['unc']:
                zero_unc_total += 1
                zero_unc_contractible += (betti == [] and len(core) == 1)
            else:
                fails.append((n, tuple(betti), len(core)))
    print(f"  [R4] {arr.name}: {arr.n} hyperplanes, {pairs} pairs (class reps), {zeros} zeros")
    from collections import Counter
    cnt = Counter(fails)
    print(f"  [R4] CR_V counterexample pairs (mu = 0, all complemented): {len(fails)}")
    for (n, betti, c), v in sorted(cnt.items()):
        print(f"       |Lambda(V)^g| = {n}: {v} pairs, reduced Betti {betti}, Stong core size {c}")
    print(f"  [R4] zeros with an uncomplemented element: {zero_unc_total}, of which certified "
          f"contractible by the Stong core: {zero_unc_contractible}")
    ok &= len(fails) == 36
    ok &= all(b == () for (_, b, _) in fails)
    return ok, fails


# ---------------------------------------------------------------- type A


def part_TA(nmax):
    ok = True
    levels = TA.posets_up_to_iso(nmax)
    stats = dict(pairs=0, zeros=0, zero_acyclic=0, zero_core1=0, nonzero=0, nonzero_conc=0,
                 id_ok=0, id_total=0, nonconc=[])
    for n in range(3, nmax + 1):
        allparts, PI = TA.rgs_all(n), TA.pair_index(n)
        for rel in levels[n]:
            P = TA.Poset(n, rel)
            auts, antis = TA.symmetries(P)
            group = auts + antis
            for sym in (auts, antis):
                for t in TA.conj_classes(sym, auts):
                    M = TA.Lattice(P, t, allparts, PI)
                    mu = M.mu()
                    E = [i for i in range(len(M.elems)) if i not in (M.bot, M.top)]
                    mask = M.mask
                    lt = lambda x, y, mask=mask: x != y and (mask[x] | mask[y]) == mask[y]
                    betti = describe(order_complex_betti(E, lt))
                    stats['pairs'] += 1
                    if t == tuple(range(n)):
                        stats['id_total'] += 1
                        ec = abs(mu)          # |mu(OP(P))| = e_C(P)
                        stats['id_ok'] += betti == [(n - 3, ec)]
                    if mu == 0:
                        stats['zeros'] += 1
                        if betti == []:
                            stats['zero_acyclic'] += 1
                        core = stong_core(E, lt)
                        stats['zero_core1'] += len(core) == 1
                    else:
                        stats['nonzero'] += 1
                        if len(betti) == 1:
                            stats['nonzero_conc'] += 1
                        else:
                            stats['nonconc'].append((n, sorted(rel), t, betti))
        print(f"  [TA] n = {n}: cumulative pairs {stats['pairs']}, zeros {stats['zeros']} "
              f"(acyclic {stats['zero_acyclic']}, Stong core a point {stats['zero_core1']}), "
              f"nonzeros {stats['nonzero']} (homology in one degree: {stats['nonzero_conc']}); "
              f"tau = id: {stats['id_ok']}/{stats['id_total']} have Betti e_C(P) in degree n - 3", flush=True)
    for x in stats['nonconc'][:10]:
        print(f"       not concentrated: n = {x[0]}, P = {x[1]}, tau = {x[2]}, Betti {x[3]}")
    ok &= stats['id_ok'] == stats['id_total']
    ok &= stats['zero_acyclic'] == stats['zeros']
    return ok, stats


def main(argv):
    nmax = 6
    if '--nmax' in argv:
        nmax = int(argv[argv.index('--nmax') + 1])
    ok = part_CTL()
    ok3, _ = part_TA(nmax)
    ok2, _ = part_R4()
    ok = ok and ok2 and ok3
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
