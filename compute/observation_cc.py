#!/usr/bin/env python3
"""Checks for notes/observation_cc.md: Observation CC on the cones of the braid
arrangement, and the steps of its proof.

Observation CC.  For a poset P on [n] (n >= 3) and g = eps*t preserving C_P,
put M = OP(P)^t (cr_v_type_a.py: refinement order, 0 = discrete, 1 = one block).
Then mu(M) = 0 iff
    LOW : the meet of the coatoms of M is not 0, or
    HIGH: the join of the atoms of M is not 1.
(For M = {0, 1} the coatom is 0 and the atom is 1, so CC fails there.)

[TA]  every pair (P, +-t) with 3 <= n <= nmax, up to isomorphism (enumeration
      and lattice code of cr_v_type_a.py, imported).  On every pair:
  CC     CC <=> mu = 0                                     (Observation CC)
  CD     every coatom x of M has x >= kappa or x >= c      (Lemma CD; c = cl(Fix g),
                                                            kappa = comp(P))
  CK     every coatom x >= kappa has x >= D               (Lemma CK; D = blocks
         U_a t^{a r} K, r = rad gcd_K lambda_K)
  A      if c ^ D != 0 then LOW holds and meet(coatoms) >= c ^ D   (Prop. A)
  U      if c ^ D != 0 then c ^ D has no complement in M; on row W-4,
         O|Q has no complement in M                        (Cor. U)
  ZL     on every zero of rows W+1, W+2, W-1, W-2, W-3: c ^ D != 0  (Prop. Z)
  W4     on every zero of row W-4: every atom is <= a or <= b, and
         join(atoms) <= O|Q (two blocks), so HIGH holds    (Prop. B)
  plus counts of which side of CC fires, per row of table W.

[GEN] beyond type A (COMPUTED only): CC against mu = 0 on the cone lattices of
      conjecture_cr_v.py (imported): the rank-4 counterexample to CR_V, the rank
      <= 3 families of its [REP] and [CRV] parts, and (with --gen-r4) its rank-4
      families.

Controls: Pi_4^{(1234)} (chain, CC holds, mu = 0), Pi_4 (CC fails, mu = -6),
a 4-element chain (CC holds), B_3 (CC fails), the 8-element complemented
lattice with mu = 0 (CC fails), and an injected-fault control: replacing c by 0
in Prop. A's predicate must make check ZL fail on some zero.

--budget bounds the wall time of [TA]; posets not reached are reported UNRUN and
the script exits 1 without "ALL CHECKS PASSED".  --jobs sets the worker count
(default 1; pass $POGO_WORKER_CORES).

[EXTRA] the 13 targeted pairs (n = 8, 9, 18) of cr_v_type_a.py: CC and Prop. A/Z there.

Run:  python3 observation_cc.py [--nmax 8] [--budget S] [--jobs J] [--no-extra] [--no-gen] [--gen-r4]
"""
import signal
import sys
import time
from math import gcd
from multiprocessing import Pool

import cr_v_type_a as C


# ------------------------------------------------------------- lattice helpers (M)

def coatoms_atoms(M):
    mk = M.mask
    proper = [i for i in range(len(M.elems)) if i not in (M.bot, M.top)]
    if not proper:
        return [M.bot], [M.top]
    co = [i for i in proper if not any(mk[i] != mk[j] and (mk[i] | mk[j]) == mk[j] for j in proper)]
    at = [i for i in proper if not any(mk[i] != mk[j] and (mk[i] | mk[j]) == mk[i] for j in proper)]
    return co, at


def le(m1, m2):           # partition with pair-mask m1 refines the one with m2
    return (m1 | m2) == m2


def rad(x):
    r, p = 1, 2
    while x > 1:
        if x % p == 0:
            r *= p
            while x % p == 0:
                x //= p
        p += 1
    return r


def D_partition(n, comp, t):
    """D: blocks U_a t^{a r} K over components K, r = rad(gcd of the orbit lengths)."""
    orbs = C.component_orbits(comp, t)
    g = 0
    for _, s in orbs:
        g = gcd(g, s)
    r = rad(g)
    tr = C.power(t, r)
    seen, blocks = set(), []
    for K, _ in orbs:
        if K in seen:
            continue
        B, cur = set(), K
        while cur not in seen:
            seen.add(cur)
            B |= cur
            cur = frozenset(tr[x] for x in cur)
        blocks.append(sorted(B))
    return C.from_blocks(n, blocks), r


def row_of(P, eps, t, mu):
    if mu != 0:
        return 'nonzero'
    name, _ = C.witness(P, eps, t)
    return name.split()[0] if name else 'NONE'


def analyse_pair(P, eps, t, allparts, PI, fault=False):
    n = P.n
    M = C.Lattice(P, t, allparts, PI)
    mu = M.mu()
    co, at = coatoms_atoms(M)
    mco = M.mask[M.top]           # all pairs (n(n-1)/2 bits; not a fixed width)
    for i in co:
        mco &= M.mask[i]
    jat = M.bot
    for i in at:
        jat = M.join(jat, i)
    low, high = mco != 0, jat != M.top
    cc = low or high
    comp = P.components()
    kap = C.pmask(comp, PI)
    c = C.cl_fix(n, eps, t)
    cm = C.pmask(c, PI) if not fault else 0
    D, r = D_partition(n, comp, t)
    Dm = C.pmask(D, PI)
    proper = len(M.elems) > 2
    res = dict(mu=mu, low=low, high=high, cc=cc, size=len(M.elems))
    res['cd_fail'] = proper and any(not (le(kap, M.mask[x]) or le(cm, M.mask[x])) for x in co)
    res['ck_fail'] = proper and any(le(kap, M.mask[x]) and not le(Dm, M.mask[x]) for x in co)
    pred = (cm & Dm) != 0
    res['pred'] = pred
    res['a_fail'] = pred and not (proper and low and le(cm & Dm, mco))
    # Cor. U: c ^ D (when != 0) is itself an uncomplemented element of M
    res['u_fail'] = False
    if pred and not fault:
        cd = C.common_refinement(c, D)
        res['u_fail'] = not (M.contains(cd) and not M.has_complement(M.index[cd]))
    row = row_of(P, eps, t, mu)
    res['row'] = row
    res['zl_fail'] = row in ('W+1', 'W+2', 'W-1', 'W-2', 'W-3') and not pred
    res['w4_fail'] = False
    res['wrel'] = None
    if mu == 0:          # how the TA-CR witness W sits relative to meet(coatoms) and join(atoms)
        _, W = C.witness(P, eps, t)
        if W is not None:
            Wm = C.pmask(W, PI)
            res['wrel'] = (le(mco, Wm), le(Wm, M.mask[jat]))
    if row == 'W-4':
        O = sorted(x for cyc in C.cycles(t) if len(cyc) % 2 for x in cyc)
        Q = [x for x in range(n) if x not in O]
        am = C.pmask(C.from_blocks(n, [Q] + [[x] for x in O]), PI)
        bm = C.pmask(C.from_blocks(n, [O] + [[x] for x in Q]), PI)
        OQ = C.pmask(C.from_blocks(n, [O, Q]), PI)
        ok = proper and all(le(M.mask[x], am) or le(M.mask[x], bm) for x in at)
        ok = ok and le(M.mask[jat], OQ) and high
        oq = C.from_blocks(n, [O, Q])
        ok = ok and M.contains(oq) and not M.has_complement(M.index[oq])   # Cor. U: O|Q uncomplemented
        res['w4_fail'] = not ok
    return res


# ------------------------------------------------------------- [TA] sweep

_G = {}


def _init(n):
    _G['n'] = n
    _G['allparts'] = C.rgs_all(n)
    _G['PI'] = C.pair_index(n)


def _work(rel):
    n = _G['n']
    P = C.Poset(n, rel)
    auts, antis = C.symmetries(P)
    out = []
    for eps, elems in ((1, auts), (-1, antis)):
        for t in C.conj_classes(elems, auts):
            r = analyse_pair(P, eps, t, _G['allparts'], _G['PI'])
            r['eps'], r['t'], r['rel'] = eps, t, sorted(rel)
            out.append(r)
    return out


KEYS = ('pairs', 'zeros', 'cc_mismatch', 'cd_fail', 'ck_fail', 'a_fail', 'u_fail', 'zl_fail', 'w4_fail',
        'low_only', 'high_only', 'both', 'pred_true', 'pred_zero_W4')


def tally(row, results, sides):
    for r in results:
        row['pairs'] += 1
        row['zeros'] += r['mu'] == 0
        bad = (r['cc'] != (r['mu'] == 0))
        row['cc_mismatch'] += bad
        for k in ('cd_fail', 'ck_fail', 'a_fail', 'u_fail', 'zl_fail', 'w4_fail'):
            row[k] += r[k]
        if bad or r['cd_fail'] or r['ck_fail'] or r['a_fail'] or r['u_fail'] or r['zl_fail'] or r['w4_fail']:
            print(f"    FAIL: P={r['rel']} eps={r['eps']} t={r['t']} mu={r['mu']} "
                  f"low={r['low']} high={r['high']} row={r['row']} {[k for k in KEYS if r.get(k) is True]}")
        row['low_only'] += r['low'] and not r['high']
        row['high_only'] += r['high'] and not r['low']
        row['both'] += r['low'] and r['high']
        row['pred_true'] += r['pred']
        row['pred_zero_W4'] += r['pred'] and r['row'] == 'W-4'
        if r['mu'] == 0:
            key = (r['row'], r['low'], r['high']) + tuple(r['wrel'] or ())
            sides[key] = sides.get(key, 0) + 1


def part_TA(levels, nmax, budget, jobs):
    ok = True
    t0 = time.time()
    tot = {k: 0 for k in KEYS}
    sides_tot = {}
    print("[TA] Observation CC and its proof steps on every pair (P, +-t), up to isomorphism")
    for n in range(3, nmax + 1):
        tn = time.time()
        row = {k: 0 for k in KEYS}
        sides = {}
        posets = levels[n]
        done = 0
        if jobs > 1 and len(posets) > 50:
            pool = Pool(jobs, initializer=_init, initargs=(n,))
            try:
                for res in pool.imap_unordered(_work, posets, chunksize=8):
                    tally(row, res, sides)
                    done += 1
                    if done % 2000 == 0:
                        print(f"    n={n}: {done}/{len(posets)} posets, {time.time() - tn:.0f}s", flush=True)
                    if time.time() - t0 > budget:
                        break
            finally:
                pool.terminate()
                pool.join()
        else:
            _init(n)
            for rel in posets:
                if time.time() - t0 > budget:
                    break
                tally(row, _work(rel), sides)
                done += 1
        complete = done == len(posets)
        fails = sum(row[k] for k in ('cc_mismatch', 'cd_fail', 'ck_fail', 'a_fail', 'u_fail', 'zl_fail', 'w4_fail'))
        ok &= fails == 0 and complete
        for k in KEYS:
            tot[k] += row[k]
        for k, v in sides.items():
            sides_tot[k] = sides_tot.get(k, 0) + v
        print(f"  n={n}: posets {done}/{len(posets)}{'' if complete else ' -- remaining posets UNRUN (budget)'}; "
              f"pairs {row['pairs']}, zeros {row['zeros']}; CC mismatches {row['cc_mismatch']}; "
              f"CD fails {row['cd_fail']}, CK fails {row['ck_fail']}, A fails {row['a_fail']}, U fails {row['u_fail']}, "
              f"ZL fails {row['zl_fail']}, W4 fails {row['w4_fail']}; sides low-only {row['low_only']}, "
              f"high-only {row['high_only']}, both {row['both']}; c^D != 0 on {row['pred_true']} pairs "
              f"({row['pred_zero_W4']} of them W-4)  [{time.time() - tn:.1f}s]", flush=True)
        print(f"         zeros by (row, LOW, HIGH, W >= meet coatoms, W <= join atoms): {dict(sorted(sides.items()))}")
        if not complete:
            for n2 in range(n + 1, nmax + 1):
                print(f"  n={n2}: UNRUN (budget)")
            break
    print(f"  total: {tot}")
    print(f"  zeros by (row, LOW, HIGH, W >= meet coatoms, W <= join atoms), all n: {dict(sorted(sides_tot.items()))}")
    return ok


# ------------------------------------------------------------- controls

def part_CTL():
    ok = True
    print("[CTL] controls")
    for t, n, want_cc, want_mu in (((1, 2, 3, 0), 4, True, 0), ((0, 1, 2, 3), 4, False, -6)):
        P = C.antichain(n)
        r = analyse_pair(P, 1, t, C.rgs_all(n), C.pair_index(n))
        good = r['cc'] == want_cc and r['mu'] == want_mu
        ok &= good
        print(f"  Pi_{n}^{t}: |M| = {r['size']}, mu = {r['mu']}, CC = {r['cc']}  {'ok' if good else 'FAIL'}")
    # injected fault: with c replaced by 0, check ZL must fail on some zero (n <= 5)
    levels = C.posets_up_to_iso(5)
    hits = 0
    for n in range(3, 6):
        ap, PI = C.rgs_all(n), C.pair_index(n)
        for rel in levels[n]:
            P = C.Poset(n, rel)
            auts, antis = C.symmetries(P)
            for eps, elems in ((1, auts), (-1, antis)):
                for t in C.conj_classes(elems, auts):
                    hits += analyse_pair(P, eps, t, ap, PI, fault=True)['zl_fail']
    print(f"  injected fault (c := 0 in Prop. A's predicate), n <= 5: ZL fails on {hits} zeros "
          f"(must be > 0)  {'ok' if hits else 'FAIL'}")
    ok &= hits > 0
    return ok


def part_EXTRA():
    """The 13 targeted pairs of cr_v_type_a.py (n = 8, 9, 18): rows W+2 and the
    'm odd, not squarefree' branch of W-1, plus nonzero controls."""
    ok = True
    print("[EXTRA] targeted pairs of cr_v_type_a.py (n = 8, 9, 18)")
    for label, P, eps, t, expect_zero in C.extra_cases():
        r = analyse_pair(P, eps, t, None, C.pair_index(P.n))
        good = ((r['mu'] == 0) == expect_zero and r['cc'] == expect_zero and not
                (r['cd_fail'] or r['ck_fail'] or r['a_fail'] or r['u_fail'] or r['zl_fail'] or r['w4_fail']))
        if expect_zero and r['row'] in ('W+1', 'W+2', 'W-1', 'W-2', 'W-3'):
            good &= r['pred'] and r['low']
        print(f"  {label}: |M| = {r['size']}, mu = {r['mu']}, row {r['row']}, LOW = {r['low']}, "
              f"HIGH = {r['high']}, c^D != 0: {r['pred']}  {'ok' if good else 'FAIL'}")
        ok &= good
    return ok


# ------------------------------------------------------------- [GEN] beyond type A

def cc_generic(L):
    """CC on a lattice dict of conjecture_cr_v.lattice()."""
    n, bot, top = L['size'], L['bot'], L['top']
    up, down = L['up'], L['down']
    proper = [i for i in range(n) if i not in (bot, top)]
    if not proper:
        return False, False
    co = [i for i in proper if all(j == i or j == top for j in up[i])]
    at = [i for i in proper if all(j == i or j == bot for j in down[i])]
    m = co[0]
    for x in co[1:]:
        m = L['meet'][m][x]
    j = at[0]
    for x in at[1:]:
        j = L['join'][j][x]
    return m != bot, j != top


def gen_controls(CR):
    ok = True
    E, leq = CR.poset_from_covers(8, [(0, 1), (0, 2), (0, 3), (1, 5), (1, 6), (2, 4), (2, 5), (3, 4),
                                      (4, 7), (5, 7), (6, 7)])
    L8 = CR.lattice(E, leq)
    lo, hi = cc_generic(L8)
    g1 = L8['mu'] == 0 and not (lo or hi)
    E, leq = CR.poset_from_covers(4, [(0, 1), (1, 2), (2, 3)])
    C4 = CR.lattice(E, leq)
    lo4, hi4 = cc_generic(C4)
    g2 = lo4 and hi4
    B3 = CR.lattice(list(range(8)), lambda a, b: a & b == a)
    lob, hib = cc_generic(B3)
    g3 = not (lob or hib)
    print(f"  controls: 8-element complemented lattice mu = 0, CC = {lo or hi} ({'ok' if g1 else 'FAIL'}); "
          f"4-chain CC = {lo4 or hi4} ({'ok' if g2 else 'FAIL'}); B_3 CC = {lob or hib} ({'ok' if g3 else 'FAIL'})")
    return ok and g1 and g2 and g3


def gen_sweep(CR, arr, G):
    st = dict(pairs=0, zeros=0, cc=0, zeros_not_cc=0, cc_nonzero=0, unc_zero=0, zeros_not_cc_unc=0,
              zeros_compl=0)
    for g in CR.class_reps(G):
        for cone in arr.cones():
            a = CR.analyse(arr, g, cone)
            if a is None:
                continue
            L = a['L']
            lo, hi = cc_generic(L)
            cc = lo or hi
            st['pairs'] += 1
            z = L['mu'] == 0
            st['zeros'] += z
            st['cc'] += cc
            st['cc_nonzero'] += cc and not z
            if z:
                st['unc_zero'] += bool(L['unc'])
                st['zeros_compl'] += not L['unc']
                if not cc:
                    st['zeros_not_cc'] += 1
                    st['zeros_not_cc_unc'] += bool(L['unc'])
    return st


def part_GEN(r4):
    import conjecture_cr_v as CR
    ok = True
    print("[GEN] CC beyond type A (cone lattices Lambda(V)^g of conjecture_cr_v.py; COMPUTED only)")
    ok &= gen_controls(CR)
    # the rank-4 counterexample
    N = [list(u) + list(w) for u in ((1, 3), (2, -1), (3, 2)) for w in ((1, 0), (0, 1), (-1, 0), (0, -1))]
    arr = CR.Arr(4, N, "C6 x C4 orbit arrangement")
    g = CR.Sym(arr, [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    i1, i2 = arr.normals.index((1, 3, 0, -1)), arr.normals.index((1, 3, 0, 1))
    cone = frozenset(i for i, t in enumerate(arr.topes) if t[i1] == 1 and t[i2] == -1)
    a = CR.analyse(arr, g, cone)
    lo, hi = cc_generic(a['L'])
    good = len(a['lam']) == 9 and a['L']['mu'] == 0 and not a['L']['unc'] and not (lo or hi)
    print(f"  CR_V counterexample: |Lambda(V)^g| = {len(a['lam'])}, mu = {a['L']['mu']}, uncomplemented "
          f"{len(a['L']['unc'])}, LOW = {lo}, HIGH = {hi}: CC fails on a zero (expected)  {'ok' if good else 'FAIL'}")
    ok &= good
    fams = [("A2", lambda: CR.typeA(3)), ("A3", lambda: CR.typeA(4)), ("B2", lambda: CR.typeB(2)),
            ("B3", lambda: CR.typeB(3)), ("generic 4 in R^3", lambda: CR.generic(3)),
            ("B3 minus {z=0}", CR.b3_minus_one), ("A3 minus a plane", CR.deleted_a3),
            ("hexagon 12", lambda: CR.hexagon(False)), ("hexagon 13", lambda: CR.hexagon(True))]
    for name, d, gens, seeds in CR.new_families(True):
        if d == 3:
            fams.append((name, lambda d=d, gens=gens, seeds=seeds, name=name: CR.orbit_arrangement(d, gens, seeds, name)))
    if r4:
        fams += [("A4", lambda: CR.typeA(5)), ("generic 5 in R^4", lambda: CR.generic(4))]
        for name, d, gens, seeds in CR.new_families(False):
            if d == 4:
                fams.append((name, lambda d=d, gens=gens, seeds=seeds, name=name: CR.orbit_arrangement(d, gens, seeds, name)))
    tot = {}
    for name, b in fams:
        t0 = time.time()
        arr, G = b()
        st = gen_sweep(CR, arr, G)
        for k, v in st.items():
            tot[k] = tot.get(k, 0) + v
        ok &= st['cc_nonzero'] == 0      # Cor. 3.9.5 on the data
        print(f"  {name} (d = {arr.d}, {arr.n} hyperplanes): pairs {st['pairs']}, zeros {st['zeros']}, "
              f"CC {st['cc']}, CC with mu != 0 {st['cc_nonzero']}, zeros without CC {st['zeros_not_cc']} "
              f"(of which with an uncomplemented element {st['zeros_not_cc_unc']}), complemented zeros "
              f"{st['zeros_compl']}  [{time.time() - t0:.1f}s]", flush=True)
    print(f"  total: {tot}")
    return ok


def main(argv):
    nmax = int(argv[argv.index('--nmax') + 1]) if '--nmax' in argv else 7
    budget = float(argv[argv.index('--budget') + 1]) if '--budget' in argv else 3000.0
    jobs = int(argv[argv.index('--jobs') + 1]) if '--jobs' in argv else 1
    signal.signal(signal.SIGTERM, lambda *a: sys.exit(143))   # so the pool's finally runs
    t0 = time.time()
    levels = C.posets_up_to_iso(nmax)
    print(f"observation_cc.py: n = 3..{nmax}, budget {budget:.0f}s, jobs {jobs}; "
          f"posets {[len(levels[n]) for n in range(nmax + 1)]}")
    ok = part_CTL()
    if '--no-extra' not in argv:
        ok &= part_EXTRA()
    ok &= part_TA(levels, nmax, budget, jobs)
    if '--no-gen' not in argv:
        ok &= part_GEN('--gen-r4' in argv)
    print(f"total {time.time() - t0:.1f}s")
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED OR UNRUN")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
