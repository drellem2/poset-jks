"""Checks for the complementation route to jencaSarkoci_homology
(notes/lean_js_route.md, Section 3).

For every unlabeled poset P with 1 <= n <= NMAX and every minimal element a,
with L = OP(P), Lbar = L minus {0,1}, z = pi_a and Q = Lbar minus the atoms
pi_ab:

  [M]    {x in Lbar : x meet z = 0} = {pi_ab in OP(P) : b != a}
         (the partition meet; Lemma M(b)).
  [Pz]   for x in Q, p(x) = x meet z lies in Q, p(x) <= x, p(x) <= z,
         and p(x) = x for x <= z.
  [inv]  tau (Section 3.2) is a fixed-point-free involution on all chains of
         Q, the empty chain included: every chain is matched.
  [N]    with s(c) = (-1)^j (c + tau(c)) (j = position of tau(c)) when
         tau(c) is not in c, and s(c) = 0 otherwise, the operator
         N = id - bd s - s bd sends a chain with k high elements into the span
         of chains with fewer than k high elements, and kills chains with
         k = 0.  (High = not <= z.)
  [Qac]  the augmented chain complex of Delta(Q) is exact (all reduced Betti
         numbers 0).
  [rel]  rank H~_d(Lbar) = sum_b rank H~_{d-1}(Delta((pi_ab, 1))) for d >= 1,
         and (pi_ab, 1) is isomorphic to the proper part of OP(P/pi_ab)
         (Lemma U).
  [JS]   H~_d(Lbar) = 0 for d != n - 3 and rank H~_{n-3} = e_C(P), n >= 3.

Positive controls (each must FAIL on at least one poset):
  C1  s with the sign (-1)^(j+1): [N] fails.
  C2  z any element of Lbar instead of pi_a: the formula of [rel], summed over
      the meet-complements y of z (y meet z = 0), fails for some (P, z) with
      n <= 5 (complements need not be atoms, and then the lower intervals
      (0, y) contribute).
  C3  Q = Lbar (atoms kept): [Qac] fails whenever e_C(P) > 0 and n >= 3.
  C4  tau(c) = p(max c) instead of p(min of the high part): [inv] fails.

Ranks are computed modulo a large prime; a rank mod p is <= the rank over Q,
and exactness is concluded only from rank equalities that force it over Q
(see `betti`).
"""

import argparse
import sys
from multiprocessing import Pool

import mu_op_elementary as m

PRIME = 2_147_483_647


# ---------------------------------------------------------------------------
# Order complex

def chains(elems, le):
    """All chains (tuples, increasing) of the poset (elems, le), empty included."""
    lt = {x: [y for y in elems if y != x and le(x, y)] for x in elems}
    out = [()]

    def ext(c):
        for y in lt[c[-1]]:
            d = c + (y,)
            out.append(d)
            ext(d)
    for x in elems:
        out.append((x,))
        ext((x,))
    return out


def bd(c):
    """Boundary of a chain as a dict chain -> coefficient."""
    out = {}
    for i in range(len(c)):
        f = c[:i] + c[i + 1:]
        out[f] = out.get(f, 0) + (-1) ** i
    return out


def rank_mod_p(rows):
    """Rank of a list of sparse rows (dict col -> int) mod PRIME."""
    pivots = {}
    r = 0
    for row in rows:
        row = {k: v % PRIME for k, v in row.items() if v % PRIME}
        while row:
            col = min(row)
            if col in pivots:
                prow = pivots[col]
                f = row[col]
                for k, v in prow.items():
                    nv = (row.get(k, 0) - f * v) % PRIME
                    if nv:
                        row[k] = nv
                    else:
                        row.pop(k, None)
            else:
                inv = pow(row[col], PRIME - 2, PRIME)
                pivots[col] = {k: v * inv % PRIME for k, v in row.items()}
                r += 1
                break
    return r


def betti(ch):
    """Reduced Betti numbers b_d, d = -1, 0, 1, ... of the augmented complex
    on the chain list `ch`, as dict d -> b_d, from mod-p ranks.  A rank mod p
    is <= the rank over Q, so b_d(mod p) >= b_d(Q) >= 0: a mod-p value 0 gives
    b_d(Q) = 0.  If all b_d(mod p) vanish except one, equal to e, then
    b_d(Q) = e there too, since the Euler characteristic does not depend on
    the field."""
    by_len = {}
    for c in ch:
        by_len.setdefault(len(c), []).append(c)
    top = max(by_len)
    index = {k: {c: i for i, c in enumerate(v)} for k, v in by_len.items()}
    rk = {}
    for k in range(1, top + 1):
        rows = []
        for c in by_len[k]:
            rows.append({index[k - 1][f]: v for f, v in bd(c).items()})
        rk[k] = rank_mod_p(rows)
    rk[0] = 0
    rk[top + 1] = 0
    b = {}
    for k in range(0, top + 1):
        b[k - 1] = len(by_len[k]) - rk[k] - rk[k + 1]
    return b


# ---------------------------------------------------------------------------
# The route

def analyse(args):
    n, rel, controls = args
    res = {"M": True, "Pz": True, "inv": True, "N": True, "Qac": True,
           "rel": True, "JS": True, "C1": False, "C2": False, "C3": False,
           "C4": False, "minimals": 0}
    L = m.op_lattice(n, rel)
    bot, top = tuple(range(n)), tuple([0] * n)
    Lbar = [x for x in L if x != bot and x != top]
    Lset = set(L)
    le = m.leq
    ec = m.e_C(n, rel)

    # [JS]
    if n >= 3:
        bl = betti(chains(Lbar, le))
        for d, v in bl.items():
            want = ec if d == n - 3 else 0
            if v != want:
                res["JS"] = False
    full_betti = betti(chains(Lbar, le)) if n >= 3 else None

    for a in m.minimal_elements(n, rel):
        res["minimals"] += 1
        if n < 2:
            continue
        z = m.normalize([0 if x == a else 1 for x in range(n)])
        atoms = [m.pi_ab(n, a, b) for b in range(n) if b != a]
        atoms = [p for p in atoms if p in Lset and p != top]
        # [M]
        comp = [x for x in Lbar if m.meet(x, z) == bot]
        if sorted(comp) != sorted(atoms) or any(m.meet(x, z) not in Lset for x in L):
            res["M"] = False
        if n < 3:
            continue
        aset = set(atoms)
        Q = [x for x in Lbar if x not in aset]
        Qset = set(Q)
        p = {x: m.meet(x, z) for x in Q}
        for x in Q:
            if not (p[x] in Qset and le(p[x], x) and le(p[x], z)
                    and (p[x] == x or not le(x, z))):
                res["Pz"] = False
        chQ = chains(Q, le)
        chQset = set(chQ)

        def high(c):
            return [x for x in c if not le(x, z)]

        def tau(c, variant=0):
            h = high(c)
            if variant == 4:
                return p[c[-1]] if c else z
            return p[h[0]] if h else z

        def insert(c, t):
            j = sum(1 for x in c if le(x, t) and x != t)
            return c[:j] + (t,) + c[j:], j

        # [inv] and C4
        for variant, key in ((0, "inv"), (4, "C4")):
            ok = True
            for c in chQ:
                t = tau(c, variant)
                if t in c:
                    d = tuple(x for x in c if x != t)
                else:
                    d, _ = insert(c, t)
                    if any(not (le(d[i], d[i + 1])) for i in range(len(d) - 1)):
                        ok = False
                        break
                if d not in chQset or tau(d, variant) != t or d == c:
                    ok = False
                    break
            if variant == 0:
                res["inv"] = res["inv"] and ok
            elif not ok:
                res["C4"] = True

        # [N] and C1
        for sgn, key in ((0, "N"), (1, "C1")):
            def s(c):
                t = tau(c)
                if t in c:
                    return {}
                d, j = insert(c, t)
                return {d: (-1) ** (j + sgn)}
            ok = True
            for c in chQ:
                acc = {c: 1}
                for d, v in s(c).items():
                    for f, w in bd(d).items():
                        acc[f] = acc.get(f, 0) - v * w
                for f, w in bd(c).items():
                    for d, v in s(f).items():
                        acc[d] = acc.get(d, 0) - v * w
                k = len(high(c))
                for d, v in acc.items():
                    if v and len(high(d)) >= k:
                        ok = False
                if not ok:
                    break
            if sgn == 0:
                res["N"] = res["N"] and ok
            elif not ok:
                res["C1"] = True

        # [Qac]
        bQ = betti(chQ)
        if any(v != 0 for v in bQ.values()):
            res["Qac"] = False

        # [rel]: sum over b of the Betti numbers of (pi_ab, 1), and Lemma U
        rel_sum = {}
        for at in atoms:
            up = [x for x in Lbar if x != at and le(at, x)]
            # Lemma U: sigma -> sigma / pi_ab onto proper part of OP(P/pi_ab)
            qn, qrel = m.quotient_poset(rel, at)
            Lq = m.op_lattice(qn, qrel)
            img = {m.normalize([x[at.index(blk)] for blk in range(qn)]) for x in up}
            if img != {y for y in Lq if y != tuple(range(qn)) and y != tuple([0] * qn)}:
                res["rel"] = False
            bu = betti(chains(up, le)) if up else {-1: 1}
            for d, v in bu.items():
                rel_sum[d + 1] = rel_sum.get(d + 1, 0) + v
        for d, v in full_betti.items():
            if d >= 1 and v != rel_sum.get(d, 0):
                res["rel"] = False

        if controls:
            # C2: z any element of Lbar, complements = {y : y meet z = 0}
            if n <= 5:
                for zz in Lbar:
                    comps = [y for y in Lbar if m.meet(y, zz) == bot]
                    rs = {}
                    for y in comps:
                        up = [x for x in Lbar if x != y and le(y, x)]
                        bu = betti(chains(up, le)) if up else {-1: 1}
                        for d, v in bu.items():
                            rs[d + 1] = rs.get(d + 1, 0) + v
                    if any(d >= 1 and v != rs.get(d, 0) for d, v in full_betti.items()):
                        res["C2"] = True
            # C3: Q = Lbar
            if any(v != 0 for v in full_betti.values()):
                res["C3"] = True
    return n, res


def run(nmax, out, procs, controls=True):
    tasks = [(n, rel, controls) for n in range(1, nmax + 1) for rel in m.all_posets(n)]
    keys = ["M", "Pz", "inv", "N", "Qac", "rel", "JS"]
    tot = {k: 0 for k in keys}
    ctl = {k: 0 for k in ("C1", "C2", "C3", "C4")}
    per_n = {}
    nmin = 0
    with Pool(procs) as pool:
        for n, res in pool.imap_unordered(analyse, tasks, chunksize=4):
            per_n[n] = per_n.get(n, 0) + 1
            nmin += res["minimals"]
            for k in keys:
                tot[k] += res[k]
            for k in ctl:
                ctl[k] += res[k]
    ok = all(tot[k] == len(tasks) for k in keys)
    print(f"posets per n: {dict(sorted(per_n.items()))}", file=out)
    print(f"total posets checked: {len(tasks)}; (P, a minimal) pairs: {nmin}", file=out)
    for k in keys:
        print(f"[{k}] holds on {tot[k]}/{len(tasks)}", file=out)
    if controls:
        for k, v in ctl.items():
            print(f"control {k} fails (as it must) on {v} posets", file=out)
        ok = ok and all(v > 0 for v in ctl.values())
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED", file=out)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=5)
    ap.add_argument("--procs", type=int, default=1)
    ap.add_argument("--no-controls", action="store_true")
    args = ap.parse_args()
    sys.exit(0 if run(args.nmax, sys.stdout, args.procs, not args.no_controls) else 1)


if __name__ == "__main__":
    main()
