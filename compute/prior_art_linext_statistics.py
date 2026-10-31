#!/usr/bin/env python3
"""Checks for notes/prior_art_linext_statistics.md.

Independent of the rest of compute/: this file imports nothing from the repo.
It regenerates the posets with n <= NMAX up to isomorphism, recomputes the
cyclic order polynomial Omega_C(P, m) from its counting description
(Theorem Omega, right-hand side), and tests it against the candidate prior
art:

  [gen]      poset counts 1, 2, 5, 16, 63, 318, 2045 (OEIS A000112), control.
  [eC]       e_C(P) (orbits of Lin P under rotation at cuts) equals the
             number of T-anchored linear extensions, for every component T,
             and Omega_C has leading coefficient e_C/n!.
  [toric]    is Omega_C(P, .) (or n * Omega_C(P, .)) a toric order
             polynomial in the sense of Adin-Gessel-Reiner-Roichman, i.e. a
             nonnegative integer combination of the polynomials
               g_d(m) = d C(m+n-d, n) + (n-d) C(m+n-1-d, n),  1 <= d <= n-1,
             one per total cyclic order with d cyclic descents?
  [toric-bf] brute-force control for n <= 4: the toric order polynomial of
             every DAG on [n] (computed by enumerating its flip class) lies in
             that cone, and no Omega_C(P, .) with n | e_C is among them.
  [cdes]     h_C(P) versus Cellini's cdes on the cut-rotation classes, for
             every natural labelling.
  [anchor]   h_C(P) versus des of the T-anchored representative of each class
             (Petersen's representative for the antichain), every natural
             labelling and every T.
  [arr]      h_C(P) versus the cdes distribution that Adin-Reiner-Roichman
             Lemma 2.4 forces on Lin P from the des distribution.
  [qsym]     the quasisymmetric lift K_C(P) = sum over T-anchored P-partitions
             f of x^f: its expansion in Gessel's fundamental basis
             (positivity), and whether it is cyclically quasisymmetric.

Each line prints PASS/FAIL; the script exits 0 iff every claim line passes
and every CONTROL line is refuted at least once.

Run from compute/:
    python3 prior_art_linext_statistics.py --nmax 7 > output/prior_art_linext_statistics.txt

Plain Python 3, no third-party packages, one core.
"""

import argparse
import itertools
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from math import comb as _comb, factorial

FAILS = []


def comb(a, b):
    return _comb(a, b) if a >= 0 and b >= 0 else 0


def check(ok, label):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        FAILS.append(label)


def control(refutations, label):
    ok = refutations > 0
    print(("PASS " if ok else "FAIL ") + "CONTROL " + label
          + f" (refuted on {refutations} cases)")
    if not ok:
        FAILS.append("CONTROL " + label)


# ---------------------------------------------------------------- posets
# A poset on {0..n-1} is a tuple `down` of bitmasks: down[x] = strict
# down-set of x.  All posets produced here are naturally labelled
# (down[x] only contains labels < x).

def ideals(n, down):
    """All order ideals (down-closed sets) as bitmasks."""
    out = []

    def rec(x, mask):
        if x == n:
            out.append(mask)
            return
        rec(x + 1, mask)
        if down[x] & ~mask == 0:  # natural labelling: down[x] already decided
            rec(x + 1, mask | (1 << x))
    rec(0, 0)
    return out


def up_sets(n, down):
    up = [0] * n
    for x in range(n):
        for y in range(n):
            if down[x] >> y & 1:
                up[y] |= 1 << x
    return up


def canon(n, down):
    """Canonical key of the isomorphism class (min over invariant-respecting
    relabellings of the sorted relation list)."""
    up = up_sets(n, down)
    inv = [(bin(down[x]).count("1"), bin(up[x]).count("1")) for x in range(n)]
    classes = defaultdict(list)
    for x in range(n):
        classes[inv[x]].append(x)
    keys = sorted(classes)
    best = None
    for perms in itertools.product(*(itertools.permutations(classes[k])
                                     for k in keys)):
        order = [x for p in perms for x in p]
        pos = {x: i for i, x in enumerate(order)}
        rel = tuple(sorted((pos[y], pos[x]) for x in range(n)
                           for y in range(n) if down[x] >> y & 1))
        if best is None or rel < best:
            best = rel
    return best


def natural_relabel(n, down):
    """Relabel along one linear extension so the labelling is natural."""
    order = []
    placed = 0
    while len(order) < n:
        for x in range(n):
            if not placed >> x & 1 and down[x] & ~placed == 0:
                order.append(x)
                placed |= 1 << x
                break
    pos = {x: i for i, x in enumerate(order)}
    new = [0] * n
    for x in range(n):
        for y in range(n):
            if down[x] >> y & 1:
                new[pos[x]] |= 1 << pos[y]
    return tuple(new)


def all_posets(nmax):
    """by_n[n] = list of naturally labelled representatives, one per
    isomorphism class.  Every poset arises from one on n-1 points by adding
    a maximal element whose strict down-set is an order ideal."""
    by_n = {0: [()]}
    for n in range(1, nmax + 1):
        seen = {}
        for P in by_n[n - 1]:
            for I in ideals(n - 1, P):
                Q = P + (I,)
                key = canon(n, Q)
                if key not in seen:
                    seen[key] = Q
        by_n[n] = [natural_relabel(n, Q) for Q in seen.values()]
    return by_n


def components(n, down):
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for x in range(n):
        for y in range(n):
            if down[x] >> y & 1:
                parent[find(x)] = find(y)
    comp = defaultdict(int)
    for x in range(n):
        comp[find(x)] |= 1 << x
    return sorted(comp.values())


def is_union_of_components(mask, comps):
    return all((mask & c) in (0, c) for c in comps)


def linear_extensions(n, down):
    out = []

    def rec(word, placed):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not placed >> x & 1 and down[x] & ~placed == 0:
                word.append(x)
                rec(word, placed | (1 << x))
                word.pop()
    rec([], 0)
    return out


def cut_positions(w, comps):
    cuts, mask = [], 0
    for j in range(1, len(w)):
        mask |= 1 << w[j - 1]
        if is_union_of_components(mask, comps):
            cuts.append(j)
    return cuts


def cut_classes(n, down, comps, lin):
    """Orbits of Lin P under rotation at cuts."""
    index = {w: i for i, w in enumerate(lin)}
    parent = list(range(len(lin)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for w in lin:
        for j in cut_positions(w, comps):
            u = w[j:] + w[:j]
            parent[find(index[w])] = find(index[u])
    cls = defaultdict(list)
    for w in lin:
        cls[find(index[w])].append(w)
    return list(cls.values())


# ------------------------------------------- Omega_C from its counting form

def anchored_chain_data(n, down, comps, T, want_comp=False):
    """Chains of ideals 0 = I_0 < I_1 < ... < I_k = P (an order-preserving
    surjection onto [k], I_j = f^{-1}[1, j]) such that every I_j, j < k, that
    is a union of components is disjoint from T.  (Equivalently: every
    nonempty upper level set that is a union of components contains T.)
    Returns c[k] = number of such chains, and optionally the multiset of
    block-size compositions."""
    full = (1 << n) - 1
    ids = ideals(n, down)
    ok = {I: (I == full or not is_union_of_components(I, comps)
              or (I & T) == 0) for I in ids}
    ids_sorted = sorted(ids, key=lambda m: bin(m).count("1"))
    # dp[I] = Counter(composition -> count) of chains from 0 to I
    dp = {0: Counter({(): 1} if want_comp else {0: 1})}
    for I in ids_sorted:
        if I not in dp or not ok[I] or I == full:
            continue
        for J in ids_sorted:
            if J != I and (J & I) == I:
                add = bin(J ^ I).count("1")
                tgt = dp.setdefault(J, Counter())
                for comp, c in dp[I].items():
                    tgt[comp + (add,) if want_comp else comp + 1] += c
    res = dp.get(full, Counter())
    if want_comp:
        return res
    c = [0] * (n + 1)
    for k, v in res.items():
        c[k] += v
    return c


def h_vector(n, c):
    """sum_m Omega(m) t^m = sum_k c_k t^k / (1-t)^{k+1}
                         = (sum_k c_k t^k (1-t)^{n-k}) / (1-t)^{n+1}."""
    h = [0] * (n + 1)
    for k in range(n + 1):
        for i in range(n - k + 1):
            h[k + i] += c[k] * comb(n - k, i) * (-1) ** i
    return h


def omega_values(c, ms):
    return [sum(ck * comb(m, k) for k, ck in enumerate(c)) for m in ms]


# --------------------------------------------------------------- toric cone

def g_poly_values(n, d, ms):
    return [d * comb(m + n - d, n) + (n - d) * comb(m + n - 1 - d, n)
            for m in ms]


def solve_exact(A, b):
    """Solve A x = b over Q (A: rows x cols).  Returns x or None if
    inconsistent; raises if underdetermined."""
    rows, cols = len(A), len(A[0])
    M = [[Fraction(v) for v in A[i]] + [Fraction(b[i])] for i in range(rows)]
    piv_cols, r = [], 0
    for col in range(cols):
        p = next((i for i in range(r, rows) if M[i][col] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][col]
        M[r] = [v * inv for v in M[r]]
        for i in range(rows):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * bb for a, bb in zip(M[i], M[r])]
        piv_cols.append(col)
        r += 1
    if len(piv_cols) < cols:
        raise ValueError("underdetermined")
    for i in range(r, rows):
        if M[i][cols] != 0:
            return None
    x = [Fraction(0)] * cols
    for i, col in enumerate(piv_cols):
        x[col] = M[i][cols]
    return x


def toric_cone_coords(n, values):
    """values = polynomial at m = 1..n (degree <= n, zero constant term).
    Returns coordinates in {g_1..g_{n-1}} or None."""
    ms = list(range(1, n + 1))
    cols = [g_poly_values(n, d, ms) for d in range(1, n)]
    A = [[cols[d][i] for d in range(n - 1)] for i in range(n)]
    return solve_exact(A, values)


def in_N_cone(x):
    return x is not None and all(v >= 0 and v.denominator == 1 for v in x)


def acyclic(n, arcs):
    indeg = [0] * n
    for a, b in arcs:
        indeg[b] += 1
    stack = [v for v in range(n) if indeg[v] == 0]
    seen = 0
    adj = defaultdict(list)
    for a, b in arcs:
        adj[a].append(b)
    while stack:
        v = stack.pop()
        seen += 1
        for b in adj[v]:
            indeg[b] -= 1
            if indeg[b] == 0:
                stack.append(b)
    return seen == n


def flip_class(n, arcs):
    start = frozenset(arcs)
    seen = {start}
    todo = [start]
    while todo:
        D = todo.pop()
        for v in range(n):
            ins = [a for a in D if a[1] == v]
            outs = [a for a in D if a[0] == v]
            if ins and outs:
                continue
            E = frozenset((b, a) if v in (a, b) else (a, b) for a, b in D)
            if E not in seen:
                seen.add(E)
                todo.append(E)
    return seen


def toric_count_bruteforce(n, arcs, m):
    """# toric [D]-partitions with values in [m] (AGRR Def. 3.14): f is a
    D'-partition for some D' in the flip class of D."""
    cls = flip_class(n, arcs)
    cnt = 0
    for f in itertools.product(range(1, m + 1), repeat=n):
        for D in cls:
            if all((f[a] <= f[b]) if a < b else (f[a] < f[b]) for a, b in D):
                cnt += 1
                break
    return cnt


# -------------------------------------------------------------- statistics

def natural_labellings(lin):
    """A natural labelling lambda: element -> label is the inverse of a
    linear extension."""
    for w in lin:
        lam = [0] * len(w)
        for i, x in enumerate(w):
            lam[x] = i
        yield lam


def des_lab(w, lam):
    return sum(1 for i in range(len(w) - 1) if lam[w[i]] > lam[w[i + 1]])


def cdes_lab(w, lam):
    return des_lab(w, lam) + (1 if lam[w[-1]] > lam[w[0]] else 0)


def dist(vals, n):
    d = [0] * (n + 1)
    for v in vals:
        d[v] += 1
    return d


def arr_cdes_from_des(n, des_dist):
    """ARR Lemma 2.4: n D(t)/(1-t)^{n+1} = d/dt [C(t)/(1-t)^n], C(0) = 0.
    Returns the coefficient list of C, or None if not a polynomial of
    degree <= n."""
    N = 3 * n + 5
    inv = [comb(n + k, n) for k in range(N)]  # 1/(1-t)^{n+1}
    a = [Fraction(0)] * N
    for i, di in enumerate(des_dist):
        for k in range(N - i):
            a[i + k] += n * di * inv[k]
    integ = [Fraction(0)] + [a[k] / (k + 1) for k in range(N - 1)]
    C = [Fraction(0)] * N
    for i in range(n + 1):
        coef = comb(n, i) * (-1) ** i
        for k in range(N - i):
            C[i + k] += coef * integ[k]
    if any(v != 0 for v in C[n + 1:2 * n + 2]):
        return None
    return C[:n + 1]


# ---------------------------------------------------------- quasisymmetric

def comp_to_set(comp):
    s, out = 0, []
    for part in comp[:-1]:
        s += part
        out.append(s)
    return frozenset(out)


def m_to_f(n, mcoef):
    """mcoef: {descent set J subset [n-1]: coefficient of M_J}.
    M_J = sum_{K >= J} (-1)^{|K-J|} F_K."""
    f = Counter()
    rest = list(range(1, n))
    for J, c in mcoef.items():
        free = [i for i in rest if i not in J]
        for r in range(len(free) + 1):
            for add in itertools.combinations(free, r):
                f[J | frozenset(add)] += c * (-1) ** r
    return {K: v for K, v in f.items() if v != 0}


def is_cyclic_qsym(mcomp):
    """Coefficient of M_alpha invariant under cyclic shifts of alpha."""
    for comp, c in mcomp.items():
        for j in range(1, len(comp)):
            if mcomp.get(comp[j:] + comp[:j], 0) != c:
                return False
    return True


# -------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--lab-nmax", type=int, default=7,
                    help="largest n at which every natural labelling is tried")
    ap.add_argument("--bf-nmax", type=int, default=4,
                    help="largest n for the brute-force toric control")
    args = ap.parse_args()
    nmax = args.nmax

    by_n = all_posets(nmax)
    counts = [len(by_n[n]) for n in range(1, nmax + 1)]
    expected = [1, 2, 5, 16, 63, 318, 2045, 16999][:nmax]
    check(counts == expected, f"[gen] posets per n = {counts} (A000112)")

    stats = Counter()
    hc_table = {}
    cone_cases = []
    omegaC_by_n = defaultdict(list)  # n -> list of (values, e_C)
    first = {}

    def note(key, example):
        stats[key] += 1
        first.setdefault(key, example)

    for n in range(1, nmax + 1):
        for P in by_n[n]:
            comps = components(n, P)
            lin = linear_extensions(n, P)
            e = len(lin)
            classes = cut_classes(n, P, comps, lin)
            eC = len(classes)
            name = (n, P)
            # Omega_C for every choice of T
            cs = [anchored_chain_data(n, P, comps, T) for T in comps]
            c = cs[0]
            stats["posets"] += 1
            if any(ci != c for ci in cs):
                note("eC-Tdep", name)
            if c[n] != eC:
                note("eC-lead", name)
            # T-anchored linear extensions: last piece contains T
            for T in comps:
                cnt = 0
                for w in lin:
                    cuts = cut_positions(w, comps)
                    last = w[cuts[-1]:] if cuts else w
                    lastmask = sum(1 << x for x in last)
                    if lastmask & T == T:
                        cnt += 1
                if cnt != eC:
                    note("eC-anchor", name)
            # ordinary order polynomial (control: no anchoring)
            c_plain = anchored_chain_data(n, P, [(1 << n) - 1], (1 << n) - 1)
            if len(comps) > 1 and c_plain != c:
                note("ctl-plain", name)
            if len(comps) == 1 and c_plain != c:
                note("conn-mismatch", name)
            h = h_vector(n, c)
            hC = h[1:]  # h_0 = 0 always for n >= 1
            if h[0] != 0 or any(v < 0 for v in hC):
                note("h-neg", name)
            if sum(hC) != eC:
                note("h-sum", name)
            if n <= 4:
                hc_table[name] = (hC, eC, e, len(comps))

            # ---- toric cone
            vals = omega_values(c, range(1, n + 1))
            omegaC_by_n[n].append((vals, eC, P))
            if n >= 2:
                x = toric_cone_coords(n, vals)
                if in_N_cone(x):
                    note("toric-in-cone", name)
                    cone_cases.append((name, x))
                    if n <= 5:
                        note("toric-in-cone-n<=5", name)
                if eC % n == 0:
                    note("toric-n-divides", name)
                xn = toric_cone_coords(n, [n * v for v in vals])
                if in_N_cone(xn):
                    note("toricN-in-cone", name)
                if xn is None:
                    note("toricN-not-in-span", name)

            # ---- cdes on classes, anchored des, every natural labelling
            if n >= 2:
                labs = list(natural_labellings(lin)) if n <= args.lab_nmax \
                    else [list(range(n))]
                cd_all, cd_some = True, False
                an_all, an_some = True, False
                reps_by_T = []
                for T in comps:
                    reps = []
                    for cl in classes:
                        for w in cl:
                            cuts = cut_positions(w, comps)
                            last = w[cuts[-1]:] if cuts else w
                            if sum(1 << x for x in last) & T == T:
                                reps.append(w)
                                break
                    reps_by_T.append(reps)
                for lam in labs:
                    d = dist([cdes_lab(cl[0], lam) - 1 for cl in classes], n)
                    ok = d[:n] == hC[:n] and d[n] == 0
                    cd_all &= ok
                    cd_some |= ok
                    for reps in reps_by_T:
                        d2 = dist([des_lab(w, lam) for w in reps], n)
                        ok2 = d2[:n] == hC[:n]
                        an_all &= ok2
                        an_some |= ok2
                # Theorem H (notes/h_vector_omega_c.md): separated labellings
                up = up_sets(n, P)
                big = [cc for cc in comps if bin(cc).count("1") > 1]
                mins = [x for cc in big for x in range(n)
                        if cc >> x & 1 and P[x] == 0]
                maxs = [x for cc in big for x in range(n)
                        if cc >> x & 1 and up[x] == 0]

                def separated(lam):
                    return all(lam[a] < lam[b] for a in mins for b in maxs)
                sep_labs = [lam for lam in labs if separated(lam)]
                if not sep_labs:  # n above lab-nmax: find one separated
                    sep_labs = [lam for lam in natural_labellings(lin)
                                if separated(lam)][:1]
                if not sep_labs:
                    note("sep-missing", name)
                for lam in sep_labs:
                    stats["sep-labelled"] += 1
                    d = dist([cdes_lab(cl[0], lam) - 1 for cl in classes], n)
                    if not (d[:n] == hC[:n] and d[n] == 0):
                        note("sep-fail", name)
                stats["lab-posets"] += 1
                if cd_all:
                    note("cdes-all", name)
                elif cd_some:
                    note("cdes-some", name)
                else:
                    note("cdes-none", name)
                if an_all:
                    note("anchor-all", name)
                elif an_some:
                    note("anchor-some", name)
                else:
                    note("anchor-none", name)

                # ---- ARR Lemma 2.4 from des on Lin P (canonical labelling)
                lam0 = list(range(n))
                dd = dist([des_lab(w, lam0) for w in lin], n)
                C = arr_cdes_from_des(n, dd)
                if C is None:
                    note("arr-nonpoly", name)
                else:
                    target = [0] + [Fraction(n * v) for v in hC[:n]]
                    if [Fraction(v) for v in C] == target:
                        note("arr-match", name)
                    else:
                        note("arr-nomatch", name)
                    # internal control: C(1) must equal e(P)
                    if sum(C) != e:
                        note("arr-total-bad", name)

            # ---- quasisymmetric lift
            mcomp = anchored_chain_data(n, P, comps, comps[0], want_comp=True)
            mset = Counter()
            for comp, v in mcomp.items():
                mset[comp_to_set(comp)] += v
            fexp = m_to_f(n, mset)
            if any(v < 0 for v in fexp.values()):
                note("qsym-Fneg", name)
            else:
                note("qsym-Fpos", name)
                hF = [0] * (n + 1)
                for K, v in fexp.items():
                    hF[len(K) + 1] += v
                if hF[1:] != hC:
                    note("qsym-h-mismatch", name)
            if n >= 2:
                if is_cyclic_qsym(mcomp):
                    note("qsym-cyclic", name)
                else:
                    note("qsym-notcyclic", name)
            if len(comps) == 1:
                gessel = Counter()
                for w in lin:
                    gessel[frozenset(i + 1 for i in range(n - 1)
                                     if w[i] > w[i + 1])] += 1
                if dict(gessel) != fexp:
                    note("qsym-gessel-bad", name)

    P_ = stats["posets"]
    print(f"# posets with 1 <= n <= {nmax}: {P_}")
    check(stats["eC-Tdep"] == 0, "[eC] Omega_C does not depend on T")
    check(stats["eC-lead"] == 0,
          "[eC] leading coefficient of Omega_C is e_C/n! (c_n = e_C)")
    check(stats["eC-anchor"] == 0,
          "[eC] e_C = #{w in Lin P : last piece contains T}, every T")
    check(stats["conn-mismatch"] == 0, "[eC] Omega_C = Omega for connected P")
    control(stats["ctl-plain"], "[eC] Omega_C = Omega for every P")
    check(stats["h-neg"] == 0, "[eC] h_C(P) >= 0 (recomputed)")
    check(stats["h-sum"] == 0, "[eC] sum of h_C = e_C")

    print("# small values: (n, down-sets) -> h_C, e_C, e, #components")
    for k, v in sorted(hc_table.items())[:12]:
        print("#  ", k, "->", v)

    # ---- toric
    tor_pos = stats["toric-in-cone"]
    check(stats["toric-in-cone-n<=5"] == 0,
          "[toric] for n <= 5, Omega_C(P,.) is in the N-cone of the g_d "
          "(a necessary condition for being a toric order polynomial) for "
          "no P")
    print(f"#  N-cone membership for all n: {tor_pos} of {P_ - 1} posets "
          f"(n >= 2); undecided cases:")
    for nm, x in cone_cases:
        print(f"#    n={nm[0]} down={nm[1]} coords={[str(v) for v in x]}")
    print(f"#  n | e_C(P) (necessary for the unnormalised match) on "
          f"{stats['toric-n-divides']} posets")
    print(f"#  n*Omega_C in Q-span of the g_d: "
          f"{P_ - 1 - stats['toricN-not-in-span']}; in N-cone: "
          f"{stats['toricN-in-cone']}")
    if "toricN-in-cone" in first:
        print("#  first n*Omega_C in N-cone:", first["toricN-in-cone"])

    # brute-force control: real toric order polynomials of DAGs, n <= bf
    bf_bad = 0
    bf_total = 0
    bf_hits = 0
    bf_hits_norm = 0
    for n in range(2, args.bf_nmax + 1):
        pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
        polys = set()
        for edges in itertools.chain.from_iterable(
                itertools.combinations(pairs, r)
                for r in range(len(pairs) + 1)):
            for signs in itertools.product((0, 1), repeat=len(edges)):
                arcs = [(a, b) if s == 0 else (b, a)
                        for (a, b), s in zip(edges, signs)]
                if not acyclic(n, arcs):
                    continue
                vals = tuple(toric_count_bruteforce(n, arcs, m)
                             for m in range(1, n + 1))
                polys.add(vals)
        for vals in polys:
            bf_total += 1
            if not in_N_cone(toric_cone_coords(n, list(vals))):
                bf_bad += 1
        for vals, eC, P in omegaC_by_n[n]:
            if tuple(vals) in polys:
                bf_hits += 1
            if tuple(n * v for v in vals) in polys:
                bf_hits_norm += 1
    check(bf_bad == 0,
          f"[toric-bf] all {bf_total} distinct toric order polynomials of "
          f"DAGs on n <= {args.bf_nmax} lie in the N-cone of the g_d")
    check(bf_hits == 0,
          f"[toric-bf] no Omega_C(P,.) with n <= {args.bf_nmax} equals a "
          f"toric order polynomial (matches: {bf_hits})")
    check(bf_hits_norm == 0,
          f"[toric-bf] no n*Omega_C(P,.) with n <= {args.bf_nmax} equals a "
          f"toric order polynomial (matches: {bf_hits_norm})")
    # a cone case realised: connected P on 6 points (Omega_C = Omega) and the
    # toric poset with toric chains [01234], [01235] (L^tor = {[012345],
    # [012354]}, cdes 1 and 2) have the same polynomial
    if nmax >= 6:
        Pc = (0, 0, 0, 4, 15, 31)
        cc = anchored_chain_data(6, Pc, components(6, Pc), 63)
        D = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (3, 5), (0, 5)]
        tor = [toric_count_bruteforce(6, D, m) for m in range(1, 7)]
        check(tor == omega_values(cc, range(1, 7)),
              f"[toric] coincidence: Omega of connected {Pc} equals the "
              f"toric order polynomial of [D], D = {D}: values {tor}")
    # positive control for the cone test: g_d themselves are found
    n = 5
    hit = in_N_cone(toric_cone_coords(n, g_poly_values(n, 2, range(1, n + 1))))
    check(hit, "[toric] cone test recognises g_2 at n = 5 (positive control)")

    # ---- cyclic descents
    L = stats["lab-posets"]
    print(f"# cdes-1 on cut-rotation classes = h_C: every natural labelling "
          f"{stats['cdes-all']}, some {stats['cdes-some']}, none "
          f"{stats['cdes-none']} (of {L} posets, n >= 2)")
    control(stats["cdes-some"] + stats["cdes-none"],
            "[cdes] cdes-1 on classes realises h_C for every labelling")
    check(stats["cdes-none"] == 0,
          "[cdes] for every P some natural labelling makes cdes-1 on the "
          "cut-rotation classes distributed as h_C (computed observation)")
    if "cdes-none" in first:
        print("#  first poset with no labelling:", first["cdes-none"])
    check(stats["sep-missing"] == 0 and stats["sep-fail"] == 0,
          f"[sep] Theorem H: cdes-1 on classes realises h_C under every "
          f"separated labelling tried ({stats['sep-labelled']} labelled "
          f"posets; all separated labellings for "
          f"n <= {min(args.lab_nmax, nmax)})")
    print(f"# des of T-anchored representative = h_C: every labelling and T "
          f"{stats['anchor-all']}, some {stats['anchor-some']}, none "
          f"{stats['anchor-none']}")
    control(stats["anchor-some"] + stats["anchor-none"],
            "[anchor] des of T-anchored representative realises h_C always")
    check(stats["arr-total-bad"] == 0,
          "[arr] Lemma 2.4 cdes polynomial has C(1) = e(P) (internal check)")
    print(f"# ARR Lemma 2.4: n t h_C(t) = forced cdes generating function on "
          f"Lin P: {stats['arr-match']} match, {stats['arr-nomatch']} not, "
          f"{stats['arr-nonpoly']} non-polynomial")
    control(stats["arr-nomatch"] + stats["arr-nonpoly"],
            "[arr] n t h_C(t) = ARR cdes generating function on Lin P")

    # ---- quasisymmetric
    check(stats["qsym-gessel-bad"] == 0,
          "[qsym] connected P: K_C(P) = Gessel's sum of F_Des(w) "
          "(check of the M -> F conversion)")
    m2 = m_to_f(2, {frozenset(): 1})
    check(any(v < 0 for v in m2.values()),
          "[qsym] M_(2) = F_0 - F_{1} is flagged non-F-positive "
          "(positive control)")
    check(stats["qsym-Fneg"] == 0,
          f"[qsym] K_C(P) is F-positive for every P "
          f"({stats['qsym-Fpos']} of {P_})")
    check(stats["qsym-h-mismatch"] == 0,
          "[qsym] principal specialisation of the F-expansion gives h_C")
    print(f"# K_C(P) cyclically quasisymmetric: {stats['qsym-cyclic']}, "
          f"not: {stats['qsym-notcyclic']} (n >= 2)")
    control(stats["qsym-notcyclic"],
            "[qsym] K_C(P) lies in cQSym for every P")
    if "qsym-cyclic" in first:
        print("#  first cyclic one:", first["qsym-cyclic"])

    print("FAILS:", FAILS if FAILS else "none")
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
