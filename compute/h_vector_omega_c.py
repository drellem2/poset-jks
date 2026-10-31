#!/usr/bin/env python3
"""The h-vector of the cyclic order polynomial is the cdes-distribution on
cyclic classes.

Companion to ../notes/h_vector_omega_c.md.  Self-contained: it does not
import any other module of this repository.

Omega_C(P, m) is computed from its DEFINITION,

    Omega_C(P, m) = sum_{pi in OP(P)} (-1)^{|pi|-1} mu_{OP(P)}(pi, 1) C(m, |pi|),

with OP(P) the order-preserving set partitions of P under refinement and mu
its Moebius function, computed here by the defining recursion.  Its h-vector
h_C(P) is defined by Omega_C(P, m) = sum_j h_j C(m + n - 1 - j, n).

Claims checked (each line prints PASS/FAIL with a bracketed tag):

  [sep-cdes]   for a separated natural labelling (every minimal element of a
               non-singleton component is labelled below every maximal element
               of a non-singleton component), h_C(P)_j is the number of cyclic
               classes of Lin P with cdes = j + 1 (n >= 2);
  [sep-mindes] the same with the statistic "min des over the class";
  [mindes-all] for an arbitrary natural labelling, min-des realises h_C
               whenever no class is all-ascent (pieces >= 2 and every junction
               an ascent), on all natural labellings, n <= LMAX;
  [perclass]   the per-class telescoping lemma, checked numerically on every
               class (n <= LMAX labellings), every component T, m <= n + 1;
  [mu-sign]    (-1)^{|pi|-1} mu(pi, 1) >= 0 (consistency with Theorem A);
  [sumh]       sum_j h_j = number of cyclic classes.

CONTROLS (must be refuted somewhere):
  [ctl-cdes-any]  cdes - 1 on classes for an ARBITRARY natural labelling;
  [ctl-mindes-asc] min-des for natural labellings that HAVE an all-ascent class;
  [ctl-BP-last]   des on B_P (rotation with T in the last piece; T the
                  component of the largest label), separated labelling;
  [ctl-BP-first]  des of the rotation with the piece of label 0 first,
                  separated labelling;
  [ctl-lin]       des on all of Lin P (no quotient by rotation).

Run from compute/:

    python3 h_vector_omega_c.py --nmax 7 --lmax 6 > output/h_vector_omega_c.txt

Plain Python 3, no dependencies, one core.  Exit status 0 iff every claim
holds and every control is refuted somewhere.
"""

import argparse
import itertools
import sys
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
# Posets: relation = frozenset of pairs (a, b) meaning a < b (transitively
# closed, strict).  Enumeration up to isomorphism by adding a maximal element
# above an order ideal, with a canonical form by refined cells.


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
    cs = cells(rel, n)
    best = None
    # positions assigned cell by cell
    for parts in itertools.product(*[itertools.permutations(c) for c in cs]):
        order = [x for p in parts for x in p]
        pos = {x: i for i, x in enumerate(order)}
        code = tuple(sorted((pos[a], pos[b]) for a, b in rel))
        if best is None or code < best:
            best = code
    return frozenset(best)


def ideals(rel, n):
    """All down-closed subsets of the poset on range(n)."""
    out = []
    for mask in range(1 << n):
        s = [x for x in range(n) if mask >> x & 1]
        ok = all((mask >> a & 1) for (a, b) in rel if mask >> b & 1)
        if ok:
            out.append(s)
    return out


def unlabeled_posets(nmax):
    by_n = {1: [frozenset()]}
    for n in range(2, nmax + 1):
        seen = set()
        for rel in by_n[n - 1]:
            for I in ideals(rel, n - 1):
                new = set(rel) | {(a, n - 1) for a in I}
                c = canonical(frozenset(new), n)
                seen.add(c)
        by_n[n] = sorted(seen, key=lambda r: sorted(r))
    return by_n


def less(rel, n):
    L = [[False] * n for _ in range(n)]
    for a, b in rel:
        L[a][b] = True
    return L


def linexts(rel, n):
    L = less(rel, n)
    out = []

    def rec(word, used):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not used >> x & 1 and all(used >> y & 1 for y in range(n) if L[y][x]):
                word.append(x)
                rec(word, used | 1 << x)
                word.pop()
    rec([], 0)
    return out


def components(rel, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in rel:
        parent[find(a)] = find(b)
    comp = [find(x) for x in range(n)]
    keys = sorted(set(comp), key=lambda r: min(x for x in range(n) if comp[x] == r))
    idx = {k: i for i, k in enumerate(keys)}
    return [idx[c] for c in comp]          # comp index of each element


def relabel(rel, w):
    """Natural labelling from the linear extension w: w_i gets label i."""
    lab = {x: i for i, x in enumerate(w)}
    return frozenset((lab[a], lab[b]) for a, b in rel)


def separated_extension(rel, n):
    """A linear extension listing every non-isolated minimal element first and
    every non-isolated maximal element last."""
    hasdown = [False] * n
    hasup = [False] * n
    for a, b in rel:
        hasup[a] = True
        hasdown[b] = True
    mins = [x for x in range(n) if not hasdown[x] and hasup[x]]
    maxs = [x for x in range(n) if hasdown[x] and not hasup[x]]
    iso = [x for x in range(n) if not hasdown[x] and not hasup[x]]
    mid = [x for x in range(n) if hasdown[x] and hasup[x]]
    # middle in a topological order (sort by size of down-set works: a<b
    # implies down(a) strictly inside down(b))
    dsz = [sum(1 for y in range(n) if (y, x) in rel) for x in range(n)]
    mid.sort(key=lambda x: dsz[x])
    return mins + mid + iso + maxs


def is_separated(rel, n):
    hasdown = [False] * n
    hasup = [False] * n
    for a, b in rel:
        hasup[a] = True
        hasdown[b] = True
    mins = [x for x in range(n) if not hasdown[x] and hasup[x]]
    maxs = [x for x in range(n) if hasdown[x] and not hasup[x]]
    return all(a < b for a in mins for b in maxs)


# ---------------------------------------------------------------------------
# Omega_C from the Moebius definition


def set_partitions_rgs(k):
    """Restricted growth strings of length k."""
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
    return out


RGS = {}


def rgs(k):
    if k not in RGS:
        RGS[k] = set_partitions_rgs(k)
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


def omega_c_coeffs(rel, n):
    """Return (a, signs_ok) with a[k] = sum_{|pi|=k} (-1)^{k-1} mu(pi,1)."""
    OP = [p for p in rgs(n) if acyclic_quotient(p, rel, max(p) + 1)]
    OPset = set(OP)
    nblocks = {p: max(p) + 1 for p in OP}
    order = sorted(OP, key=lambda p: nblocks[p])
    mu = {}
    signs_ok = True
    for p in order:
        k = nblocks[p]
        if k == 1:
            mu[p] = 1
            continue
        s = 0
        for q in rgs(k):
            if max(q) + 1 == k:           # q = discrete on blocks: sigma = pi
                continue
            sigma = normalise(tuple(q[b] for b in p))
            if sigma in OPset:
                s += mu[sigma]
        mu[p] = -s
    a = [0] * (n + 1)
    for p in OP:
        k = nblocks[p]
        v = (-1) ** (k - 1) * mu[p]
        if v < 0:
            signs_ok = False
        a[k] += v
    return a, signs_ok


def h_from_values(vals, n):
    """vals[m] = F(m) for m = 0..n; F(m) = sum_j h_j C(m+n-1-j, n)."""
    # sum_m F(m) x^m = sum_j h_j x^{j+1} / (1-x)^{n+1}
    series = vals[:n + 1]
    one_minus = [comb(n + 1, i) * (-1) ** i for i in range(n + 2)]
    prod = [0] * (n + 1)
    for i, c in enumerate(one_minus):
        for j, v in enumerate(series):
            if i + j <= n:
                prod[i + j] += c * v
    assert prod[0] == 0, prod
    h = prod[1:]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def h_of_poly(a, n):
    vals = [sum(a[k] * comb(m, k) for k in range(n + 1)) for m in range(n + 1)]
    return h_from_values(vals, n)


def dist(stats):
    c = Counter(stats)
    if not c:
        return [0]
    h = [c.get(j, 0) for j in range(max(c) + 1)]
    return h


def trim(h):
    h = list(h)
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


# ---------------------------------------------------------------------------
# Words, cuts, pieces, classes


def des(w):
    return sum(1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def cdes(w):
    return des(w) + (1 if w[-1] > w[0] else 0)


def cuts(w, comp):
    """Cut positions p in 1..n-1: prefix of length p is a union of components."""
    n = len(w)
    size = Counter(comp)
    seen = Counter()
    out = []
    for p in range(1, n):
        seen[comp[w[p - 1]]] += 1
        if all(seen[c] in (0, size[c]) for c in seen):
            out.append(p)
    return out


def pieces(w, comp):
    c = [0] + cuts(w, comp) + [len(w)]
    return [w[c[i]:c[i + 1]] for i in range(len(c) - 1)]


def classes(lin, comp):
    seen = set()
    out = []
    for w in lin:
        if w in seen:
            continue
        cl = [w] + [w[p:] + w[:p] for p in cuts(w, comp)]
        for u in cl:
            seen.add(u)
        out.append(cl)
    return out


def all_ascent(w, comp):
    ps = pieces(w, comp)
    if len(ps) < 2:
        return False
    s = len(ps)
    return all(ps[k][-1] < ps[(k + 1) % s][0] for k in range(s))


def omegaC_des_class(cl, comp, T, n, m):
    """Contribution of one class to Corollary Omega-des with component T."""
    tot = 0
    for w in cl:
        pos = {x: i for i, x in enumerate(w)}
        CT = [p for p in cuts(w, comp)
              if all(pos[x] < p for x in range(n) if comp[x] == T)]
        D = {i + 1 for i in range(n - 1) if w[i] > w[i + 1]}
        if any(p in D for p in CT):
            continue
        c = len(CT)
        tot += comb(m + n - 1 - len(D) - c, n - c)
    return tot


# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--lmax", type=int, default=6,
                    help="largest n at which all natural labellings are tested")
    args = ap.parse_args(argv)

    by_n = unlabeled_posets(args.nmax)
    total_posets = sum(len(v) for v in by_n.values())
    print(f"posets: " + ", ".join(f"n={n}: {len(by_n[n])}" for n in by_n)
          + f"; total {total_posets}")

    ok_sep = ok_sepmin = ok_sum = ok_sign = True
    nsep = 0
    ctl_BPlast = ctl_BPfirst = ctl_lin = 0
    ctl_cdes_any = ctl_mindes_asc = 0
    n_any = n_asc = 0
    ok_mindes_noasc = True
    noasc_checked = 0
    asc_but_ok = 0
    ok_perclass = True
    ok_seplab = ok_l0BP = True
    n_seplab = 0
    perclass_checked = 0
    examples = {}
    table = []

    for n in sorted(by_n):
        for rel0 in by_n[n]:
            a, sgn_ok = omega_c_coeffs(rel0, n)
            ok_sign &= sgn_ok
            hC = h_of_poly(a, n)
            # separated labelling
            rel = relabel(rel0, separated_extension(rel0, n))
            assert is_separated(rel, n)
            assert all(x < y for x, y in rel)
            comp = components(rel, n)
            lin = linexts(rel, n)
            cls = classes(lin, comp)
            ok_sum &= (sum(hC) == len(cls))
            if n == 1:
                st = [0]
                st_min = [0]
            else:
                st = [cdes(cl[0]) - 1 for cl in cls]
                st_min = [min(des(w) for w in cl) for cl in cls]
                # cdes is constant on a class
                assert all(len({cdes(w) for w in cl}) == 1 for cl in cls)
            nsep += 1
            if trim(dist(st)) != hC:
                ok_sep = False
                print("  sep-cdes FAILS on", sorted(rel), hC, dist(st))
            if trim(dist(st_min)) != hC:
                ok_sepmin = False
            # controls on the separated labelling
            if n >= 2:
                big = comp[n - 1]
                bp_last = [des(w) for w in lin if all(comp[x] != big or x in pieces(w, comp)[-1] for x in range(n))]
                bp_first = [des(w) for w in lin if 0 in pieces(w, comp)[0]]
                if trim(dist(bp_last)) != hC or trim(dist(bp_first)) != hC:
                    ok_l0BP = False
                    print("  lambda0-BP FAILS", sorted(rel))
                if trim(dist([des(w) for w in lin])) != hC:
                    ctl_lin += 1
            ncomp = max(comp) + 1
            if ncomp >= 2:
                table.append((n, sorted(rel0), hC, len(cls)))

            # all natural labellings
            if 2 <= n <= args.lmax:
                labs = set()
                for w in linexts(rel0, n):
                    labs.add(relabel(rel0, w))
                for rl in labs:
                    cp = components(rl, n)
                    ln = linexts(rl, n)
                    cl2 = classes(ln, cp)
                    n_any += 1
                    if trim(dist([cdes(c[0]) - 1 for c in cl2])) != hC:
                        ctl_cdes_any += 1
                        examples.setdefault("cdes-any", (sorted(rl), hC, dist([cdes(c[0]) - 1 for c in cl2])))
                    if is_separated(rl, n):
                        n_seplab += 1
                        if trim(dist([cdes(c[0]) - 1 for c in cl2])) != hC:
                            ok_seplab = False
                            print("  sep-all FAILS", sorted(rl))
                        big = cp[n - 1]
                        bl = [des(w) for w in ln if all(cp[x] != big or x in pieces(w, cp)[-1] for x in range(n))]
                        bf = [des(w) for w in ln if 0 in pieces(w, cp)[0]]
                        if trim(dist(bl)) != hC:
                            ctl_BPlast += 1
                            examples.setdefault("BP-last", (sorted(rl), hC, dist(bl)))
                        if trim(dist(bf)) != hC:
                            ctl_BPfirst += 1
                            examples.setdefault("BP-first", (sorted(rl), hC, dist(bf)))
                    has_asc = any(all_ascent(c[0], cp) for c in cl2)
                    good = trim(dist([min(des(w) for w in c) for c in cl2])) == hC
                    if has_asc:
                        n_asc += 1
                        if not good:
                            ctl_mindes_asc += 1
                            examples.setdefault("mindes-asc", (sorted(rl), hC, dist([min(des(w) for w in c) for c in cl2])))
                        else:
                            asc_but_ok += 1
                    else:
                        noasc_checked += 1
                        if not good:
                            ok_mindes_noasc = False
                            print("  mindes FAILS without all-ascent class", sorted(rl))
                    # per-class lemma: every class, every T, m <= n+1
                    if n <= min(args.lmax, 5) or cp.count(cp[0]) < n:
                        for c in cl2:
                            mind = min(des(w) for w in c)
                            if all_ascent(c[0], cp):
                                continue
                            for T in range(max(cp) + 1):
                                for m in range(n + 2):
                                    perclass_checked += 1
                                    if omegaC_des_class(c, cp, T, n, m) != comb(m + n - 1 - mind, n):
                                        ok_perclass = False

    check(ok_sign, "[mu-sign] (-1)^{|pi|-1} mu(pi,1) >= 0 on every pi, every poset")
    check(ok_sum, f"[sumh] sum h_C = #cyclic classes, {total_posets} posets")
    check(ok_sep, f"[sep-cdes] h_C = distribution of cdes-1 on Cyc(P), separated labelling, {nsep} posets n <= {args.nmax}")
    check(ok_sepmin, f"[sep-mindes] h_C = distribution of min-des on Cyc(P), separated labelling, {nsep} posets")
    check(ok_mindes_noasc, f"[mindes-all] min-des realises h_C on every natural labelling with no all-ascent class, n <= {args.lmax} ({noasc_checked} labelled posets)")
    check(ok_perclass and perclass_checked > 0, f"[perclass] per-class lemma: sum over rotations (Cor. Omega-des, every T) = C(m+n-1-mindes, n), {perclass_checked} (class, T, m) cases")
    check(ok_seplab and n_seplab > 0, f"[sep-all] h_C = cdes-1 distribution on EVERY separated natural labelling, n <= {args.lmax} ({n_seplab} labelled posets)")
    check(ok_l0BP, f"[lambda0-BP] labelling lambda_0 (mins < middle < isolated < maxs): des on B_P (T = component of label n-1, last piece) and des on rotations with 0 in the first piece both realise h_C, {nsep} posets")
    print(f"INFO labelled posets with an all-ascent class: {n_asc}; of these min-des still gives h_C on {asc_but_ok}")
    control(ctl_cdes_any, n_any, f"[ctl-cdes-any] cdes-1 on Cyc(P), arbitrary natural labelling, n <= {args.lmax}")
    control(ctl_mindes_asc, n_asc, "[ctl-mindes-asc] min-des on labellings that have an all-ascent class")
    control(ctl_BPlast, n_seplab, f"[ctl-BP-last] des on B_P (T = component of largest label in last piece), separated labellings, n <= {args.lmax}")
    control(ctl_BPfirst, n_seplab, f"[ctl-BP-first] des on rotations with label 0 in the first piece, separated labellings, n <= {args.lmax}")
    control(ctl_lin, nsep, "[ctl-lin] des on all of Lin P")
    for k, v in examples.items():
        print(f"EXAMPLE {k}: rel={v[0]} h_C={v[1]} candidate={v[2]}")

    print("TABLE disconnected posets n <= 5: n, relations (canonical), h_C, e_C")
    for n, r, h, e in table:
        if n <= 5:
            print(f"  {n} {r} {h} {e}")

    print("ALL PASS" if not FAILS else "FAILURES: " + "; ".join(FAILS))
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
