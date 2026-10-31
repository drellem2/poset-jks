#!/usr/bin/env python3
"""H'': a natural labelling with an all-ascent cyclic class makes min-des fail.

Companion to ../notes/h_double_prime.md.  Self-contained: it does not import
any other module of this repository.

Fix a natural labelling of P (n >= 2).  For a cyclic class kappa with pieces
c_1 .. c_s put d = sum_k des(c_k).  The class is all-ascent if s >= 2 and every
junction last(c_k) -> first(c_{k+1}) (indices mod s) is an ascent.  Write
h_C(x) = sum_j h_j x^j.  The note proves

  (F)  h_C(x) = sum_{kappa not all-ascent} x^{mindes kappa}
              + sum_{kappa all-ascent} x^{d-1} (1 - (1 - x)^s),

and hence (M) sum_kappa mindes(kappa) - sum_j j h_j = A, the number of
all-ascent classes, so min-des realises h_C iff A = 0 (H' and H'').

Claims checked (PASS/FAIL lines with bracketed tags):

  [formula]   (F) on every natural labelling, n <= LMAX;
  [moment]    (M) on every natural labelling, n <= LMAX;
  [iff]       min-des distribution = h_C  <=>  no all-ascent class;
  [aa-class]  an all-ascent class contributes C(m+n-d, n) - C(m+n-d-s, n-s)
              to the descent expansion (Prop. D of h_vector_omega_c.md), for
              every component T and m <= n + 1 (n <= PCMAX, default 7);
  [aa-d]      1 <= d <= n - s on every all-ascent class;
  [hC-indep]  h_C from the Moebius definition (n <= MOBMAX) agrees with the
              cdes - 1 distribution under a separated labelling; for
              MOBMAX < n <= LMAX h_C is taken from the latter (Theorem H).

CONTROLS (must be refuted somewhere; each is a false variant):
  [ctl-mindes-all]  min-des realises h_C on every natural labelling;
  [ctl-formula-s1]  (F) with (1 - x)^(s-1) in place of (1 - x)^s;
  [ctl-formula-d]   (F) with x^d in place of x^(d-1);
  [ctl-moment-0]    (M) with right-hand side 0.

Run from compute/:

    timeout 1500 python3 h_double_prime.py --lmax 7 --mobmax 7 > output/h_double_prime.txt

Plain Python 3, no dependencies, one core.  Exit status 0 iff every claim
holds and every control is refuted somewhere.
"""

import argparse
import itertools
import sys
import time
from collections import Counter
from math import comb as _comb

FAILS = []


def comb(a, b):
    return _comb(a, b) if a >= 0 and b >= 0 else 0


def check(ok, label):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        FAILS.append(label)


def control(failures, total, label):
    ok = failures > 0
    print(("PASS " if ok else "FAIL ") + "CONTROL " + label
          + f" (refuted on {failures} of {total})")
    if not ok:
        FAILS.append("CONTROL " + label)


# ---------------------------------------------------------------------------
# Posets up to isomorphism (add a maximal element above an order ideal).


def cells(rel, n):
    down = [[a for a in range(n) if (a, x) in rel] for x in range(n)]
    up = [[b for b in range(n) if (x, b) in rel] for x in range(n)]
    col = [(len(down[x]), len(up[x])) for x in range(n)]
    while True:
        new = [(col[x], tuple(sorted(col[a] for a in down[x])),
                tuple(sorted(col[b] for b in up[x]))) for x in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    out = {}
    for x in range(n):
        out.setdefault(col[x], []).append(x)
    return [out[k] for k in sorted(out)]


def canonical(rel, n):
    best = None
    for parts in itertools.product(*[itertools.permutations(c) for c in cells(rel, n)]):
        pos = {x: i for i, x in enumerate(x for p in parts for x in p)}
        code = tuple(sorted((pos[a], pos[b]) for a, b in rel))
        if best is None or code < best:
            best = code
    return frozenset(best)


def ideals(rel, n):
    out = []
    for mask in range(1 << n):
        if all(mask >> a & 1 for (a, b) in rel if mask >> b & 1):
            out.append([x for x in range(n) if mask >> x & 1])
    return out


def unlabeled_posets(nmax):
    by_n = {1: [frozenset()]}
    for n in range(2, nmax + 1):
        seen = set()
        for rel in by_n[n - 1]:
            for I in ideals(rel, n - 1):
                seen.add(canonical(frozenset(set(rel) | {(a, n - 1) for a in I}), n))
        by_n[n] = sorted(seen, key=lambda r: sorted(r))
    return by_n


def linexts(rel, n):
    below = [0] * n
    for a, b in rel:
        below[b] |= 1 << a
    out = []

    def rec(word, used):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not used >> x & 1 and below[x] & ~used == 0:
                word.append(x)
                rec(word, used | 1 << x)
                word.pop()
    rec([], 0)
    return out


def components(rel, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for a, b in rel:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    roots = [find(x) for x in range(n)]
    idx = {}
    for x in range(n):
        idx.setdefault(roots[x], len(idx))
    return [idx[r] for r in roots]


def relabel(rel, w):
    lab = {x: i for i, x in enumerate(w)}
    return frozenset((lab[a], lab[b]) for a, b in rel)


def separated_extension(rel, n):
    hasdown = [False] * n
    hasup = [False] * n
    for a, b in rel:
        hasup[a] = True
        hasdown[b] = True
    mins = [x for x in range(n) if not hasdown[x] and hasup[x]]
    maxs = [x for x in range(n) if hasdown[x] and not hasup[x]]
    iso = [x for x in range(n) if not hasdown[x] and not hasup[x]]
    mid = [x for x in range(n) if hasdown[x] and hasup[x]]
    dsz = [sum(1 for y in range(n) if (y, x) in rel) for x in range(n)]
    mid.sort(key=lambda x: dsz[x])
    return mins + mid + iso + maxs


# ---------------------------------------------------------------------------
# Omega_C from the Moebius definition on OP(P).


RGS = {}


def rgs(k):
    if k not in RGS:
        out = []

        def rec(s, mx):
            if len(s) == k:
                out.append(tuple(s))
                return
            for v in range(mx + 2):
                s.append(v)
                rec(s, max(mx, v))
                s.pop()
        rec([], -1)
        RGS[k] = out
    return RGS[k]


def acyclic_quotient(blk, rel, nb):
    edges = {(blk[a], blk[b]) for a, b in rel if blk[a] != blk[b]}
    indeg = [0] * nb
    adj = [[] for _ in range(nb)]
    for u, v in edges:
        adj[u].append(v)
        indeg[v] += 1
    stack = [u for u in range(nb) if indeg[u] == 0]
    seen = 0
    while stack:
        u = stack.pop()
        seen += 1
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                stack.append(v)
    return seen == nb


def normalise(blk):
    m = {}
    return tuple(m.setdefault(b, len(m)) for b in blk)


def hC_moebius(rel, n):
    OP = [p for p in rgs(n) if acyclic_quotient(p, rel, max(p) + 1)]
    OPset = set(OP)
    mu = {}
    for p in sorted(OP, key=lambda p: max(p)):
        k = max(p) + 1
        if k == 1:
            mu[p] = 1
            continue
        s = 0
        for q in rgs(k):
            if max(q) + 1 == k:
                continue
            sig = normalise(tuple(q[b] for b in p))
            if sig in OPset:
                s += mu[sig]
        mu[p] = -s
    a = [0] * (n + 1)
    for p in OP:
        k = max(p) + 1
        a[k] += (-1) ** (k - 1) * mu[p]
    vals = [sum(a[k] * comb(m, k) for k in range(n + 1)) for m in range(n + 1)]
    # sum_m F(m) x^m = sum_j h_j x^{j+1} / (1-x)^{n+1}
    prod = [0] * (n + 1)
    for i in range(n + 2):
        c = comb(n + 1, i) * (-1) ** i
        for j, v in enumerate(vals):
            if i + j <= n:
                prod[i + j] += c * v
    assert prod[0] == 0
    return trim(prod[1:])


def trim(h):
    h = list(h)
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


# ---------------------------------------------------------------------------
# Classes and their statistics.


def des(w):
    return sum(1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def cuts(w, comp, size):
    seen = Counter()
    out = []
    open_ = 0
    for p in range(1, len(w)):
        c = comp[w[p - 1]]
        if seen[c] == 0:
            open_ += 1
        seen[c] += 1
        if seen[c] == size[c]:
            open_ -= 1
        if open_ == 0:
            out.append(p)
    return out


def class_data(rel, n):
    """List of (mindes, d, s, all_ascent, members) for the classes of Lin P."""
    comp = components(rel, n)
    size = Counter(comp)
    seen = set()
    out = []
    for w in linexts(rel, n):
        if w in seen:
            continue
        cs = cuts(w, comp, size)
        cl = [w] + [w[p:] + w[:p] for p in cs]
        seen.update(cl)
        bounds = [0] + cs + [n]
        ps = [w[bounds[i]:bounds[i + 1]] for i in range(len(bounds) - 1)]
        s = len(ps)
        d = sum(des(c) for c in ps)
        aa = s >= 2 and all(ps[k][-1] < ps[(k + 1) % s][0] for k in range(s))
        out.append((min(des(u) for u in cl), d, s, aa, cl))
    return out, comp, size


def poly_add(p, q, sign=1):
    r = [0] * max(len(p), len(q))
    for i, c in enumerate(p):
        r[i] += c
    for i, c in enumerate(q):
        r[i] += sign * c
    return r


def aa_term(d, s, dshift=1, sexp=None):
    """Coefficients of x^{d-dshift} (1 - (1-x)^sexp)."""
    if sexp is None:
        sexp = s
    one_minus = [comb(sexp, t) * (-1) ** t for t in range(sexp + 1)]
    q = [-c for c in one_minus]
    q[0] += 1
    e = d - dshift
    assert e >= 0
    return [0] * e + q


def formula(cd, dshift=1, sexp_off=0):
    h = [0]
    for mind, d, s, aa, _ in cd:
        if aa:
            h = poly_add(h, aa_term(d, s, dshift, s - sexp_off))
        else:
            h = poly_add(h, [0] * mind + [1])
    return trim(h)


def NT_sum(cl, comp, size, T, n, m):
    tot = 0
    for w in cl:
        pos = {x: i for i, x in enumerate(w)}
        lastT = max(pos[x] for x in range(n) if comp[x] == T)
        CT = [p for p in cuts(w, comp, size) if lastT < p]
        D = {i + 1 for i in range(n - 1) if w[i] > w[i + 1]}
        if any(p in D for p in CT):
            continue
        c = len(CT)
        tot += comb(m + n - 1 - len(D) - c, n - c)
    return tot


# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--lmax", type=int, default=7,
                    help="largest n at which every natural labelling is tested")
    ap.add_argument("--mobmax", type=int, default=7,
                    help="largest n at which h_C is computed from the Moebius definition")
    ap.add_argument("--pcmax", type=int, default=7,
                    help="largest n for the per-class check [aa-class]")
    args = ap.parse_args(argv)
    t0 = time.time()

    by_n = unlabeled_posets(args.lmax)
    print("posets: " + ", ".join(f"n={n}: {len(by_n[n])}" for n in by_n))

    ok_formula = ok_moment = ok_iff = ok_aa = ok_d = ok_indep = True
    ctl_mindes = ctl_s1 = ctl_d = ctl_m0 = 0
    nlab = nasc = nmob = 0
    aa_cases = 0
    per_n = {}
    maxA = 0
    example = None

    for n in range(2, args.lmax + 1):
        tn = time.time()
        lab_n = asc_n = 0
        for rel0 in by_n[n]:
            sep = relabel(rel0, separated_extension(rel0, n))
            cd_sep, _, _ = class_data(sep, n)
            hsep = trim(Counter_to_list(Counter(cd[0] for cd in cd_sep)))
            if n <= args.mobmax:
                hC = hC_moebius(rel0, n)
                nmob += 1
                if hC != hsep:
                    ok_indep = False
                    print("  hC-indep FAILS", sorted(rel0), hC, hsep)
            else:
                hC = hsep
            labs = {relabel(rel0, w) for w in linexts(rel0, n)}
            for rl in labs:
                nlab += 1
                lab_n += 1
                cd, comp, size = class_data(rl, n)
                A = sum(1 for c in cd if c[3])
                mind = trim(Counter_to_list(Counter(c[0] for c in cd)))
                if A:
                    nasc += 1
                    asc_n += 1
                    maxA = max(maxA, A)
                if formula(cd) != hC:
                    ok_formula = False
                    print("  formula FAILS", sorted(rl), hC, formula(cd))
                mom = sum(c[0] for c in cd) - sum(j * h for j, h in enumerate(hC))
                if mom != A:
                    ok_moment = False
                    print("  moment FAILS", sorted(rl), mom, A)
                if (mind == hC) != (A == 0):
                    ok_iff = False
                    print("  iff FAILS", sorted(rl))
                if A and example is None:
                    example = (n, sorted(rl), hC, mind, A)
                # controls
                if mind != hC:
                    ctl_mindes += 1
                if A:
                    if formula(cd, sexp_off=1) != hC:
                        ctl_s1 += 1
                    if formula(cd, dshift=0) != hC:
                        ctl_d += 1
                if mom != 0:
                    ctl_m0 += 1
                # all-ascent class data
                for mn, d, s, aa, cl in cd:
                    if not aa:
                        continue
                    if not (1 <= d <= n - s and mn == d):
                        ok_d = False
                        print("  aa-d FAILS", sorted(rl), cl[0], d, s, mn)
                    if n <= args.pcmax:
                        for T in range(max(comp) + 1):
                            for m in range(n + 2):
                                aa_cases += 1
                                want = comb(m + n - d, n) - comb(m + n - d - s, n - s)
                                if NT_sum(cl, comp, size, T, n, m) != want:
                                    ok_aa = False
        per_n[n] = (lab_n, asc_n)
        print(f"INFO n={n}: {lab_n} labelled posets, {asc_n} with an all-ascent class, "
              f"{time.time() - tn:.1f}s", flush=True)

    rng = f"n <= {args.lmax}"
    check(ok_indep, f"[hC-indep] Moebius h_C = cdes-1 distribution (separated labelling), {nmob} posets n <= {min(args.mobmax, args.lmax)}")
    check(ok_formula, f"[formula] h_C(x) = sum_non-aa x^mindes + sum_aa x^(d-1)(1-(1-x)^s), every natural labelling, {nlab} labelled posets {rng}")
    check(ok_moment, f"[moment] sum mindes - sum j h_j = #all-ascent classes, {nlab} labelled posets {rng}")
    check(ok_iff and nasc > 0, f"[iff] min-des = h_C iff no all-ascent class, {nlab} labelled posets ({nasc} with an all-ascent class) {rng}")
    check(ok_d and nasc > 0, f"[aa-d] 1 <= d <= n - s and mindes = d on every all-ascent class, {rng}")
    check(ok_aa and aa_cases > 0, f"[aa-class] all-ascent class contributes C(m+n-d,n) - C(m+n-d-s,n-s), every T, m <= n+1, {aa_cases} cases n <= {args.pcmax}")
    print("INFO per n (labelled posets, with all-ascent class): "
          + ", ".join(f"n={k}: {v[0]}, {v[1]}" for k, v in per_n.items()))
    print(f"INFO largest number of all-ascent classes in one labelling: {maxA}")
    control(ctl_mindes, nlab, f"[ctl-mindes-all] min-des realises h_C on every natural labelling, {rng}")
    control(ctl_s1, nasc, f"[ctl-formula-s1] (F) with (1-x)^(s-1), labellings with an all-ascent class, {rng}")
    control(ctl_d, nasc, f"[ctl-formula-d] (F) with x^d in place of x^(d-1), labellings with an all-ascent class, {rng}")
    control(ctl_m0, nlab, f"[ctl-moment-0] sum mindes = sum j h_j, {rng}")
    if example:
        print(f"EXAMPLE first all-ascent labelling: n={example[0]} rel={example[1]} h_C={example[2]} min-des={example[3]} A={example[4]}")
    print(f"INFO total time {time.time() - t0:.1f}s")
    print("ALL PASS" if not FAILS else "FAILURES: " + "; ".join(FAILS))
    return 0 if not FAILS else 1


def Counter_to_list(c):
    if not c:
        return [0]
    return [c.get(j, 0) for j in range(max(c) + 1)]


if __name__ == "__main__":
    sys.exit(main())
