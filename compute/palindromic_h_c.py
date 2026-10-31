#!/usr/bin/env python3
"""Palindromicity of h_C(P): the classification S'.

Companion to ../notes/palindromic_h_c.md.

S' (n >= 2): h_C(P) is palindromic iff (P connected and graded) or (every
component of P has height <= 2, i.e. no 3-element chain).

The note proves the "only if" for disconnected P from the two end pairs
(h_0, h_d) and (h_1, h_{d-1}) of h_C, d = deg h_C.  This script checks the
classification and every intermediate formula of that proof on ALL posets
with 2 <= n <= NMAX (default 8: 19 448 posets).

h_C is computed two independent ways and compared:
  [B+]  h_j = #{w in Lin P : des w = j, T inside the last piece of w} under
        the labelling lambda_T (notes/reciprocity_omega_c.md, Prop. B+),
        for EVERY component T, with lambda_T built in this file;
  [H]   h_j = #{cyclic classes kappa : cdes kappa = j + 1} under a separated
        labelling (notes/h_vector_omega_c.md, Theorem H), via the helpers of
        h_vector_omega_c.py;
  [mob] for n <= MOBMAX (default 7) also from the Moebius definition of
        Omega_C (h_vector_omega_c.omega_c_coeffs).

Claims (PASS/FAIL, bracketed tags):
  [agree]      the B+ vector (every T), the Theorem H vector and (n <= MOBMAX)
               the Moebius vector coincide
  [h0]         h_0 = 1
  [h1]         h_1 = J(P) - 2^(r-1) - n          (J = number of order ideals,
               r = number of components)
  [deg]        d = n - L for L >= 2, where L = max number of elements of a chain
  [top]        L >= 2:  h_d = (L-1)^i * prod_{K non-singleton} sbar(K, L), where
               i = number of isolated points and sbar(K, m) = number of strictly
               order-preserving maps K -> [m] (counted by backtracking here)
  [next]       L >= 3 and every component has longest chain L:
               h_{d-1} + (n+1) h_d = prod_K sbar(K, L+1)
  [inj]        sbar(K, L_K + 1) >= J(K) for every connected K (L_K its longest
               chain), equality iff K graded
  [gap]        P disconnected with a 3-chain:  h_d >= 2, or
               h_{d-1} - h_1 >= 2^(r-1) - 1 >= 1
  [pal-class]  S' itself: palindromic iff (connected and graded) or all
               components of height <= 2
CONTROLS (must be refuted somewhere; each one would pass if the instrument
were blind):
  [ctl-first]      B+ with "T inside the FIRST piece" instead of the last
                   piece agrees with Theorem H
  [ctl-h1-r]       h_1 = J(P) - 1 - n (the 2^(r-1) correction dropped)
  [ctl-next-L2]    [next] with L = 2 in place of L >= 3 (D_T is no longer
                   automatic at m = L + 1)
  [ctl-next-mixed] [next] for L >= 3 when some component has a shorter
                   longest chain
  [ctl-graded]     "palindromic iff every component is graded"

Run from compute/:

    python3 palindromic_h_c.py --nmax 8 --mobmax 7 > output/palindromic_h_c.txt

Plain Python 3, one core.  Exit status 0 iff every claim holds and every
control is refuted somewhere.
"""

import argparse
import sys
from collections import Counter

import h_vector_omega_c as H

FAILS = []


def check(ok, label):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        FAILS.append(label)


def control(failures, total, label):
    ok = failures > 0
    print(("PASS " if ok else "FAIL ") + f"CONTROL refuted {failures}/{total} {label}")
    if not ok:
        FAILS.append("control " + label)


# ---------------------------------------------------------------------------
# Small poset data, all written here.


class Poset:
    def __init__(self, rel, n):
        self.rel, self.n = rel, n
        self.L = H.less(rel, n)
        self.comp = H.components(rel, n)
        self.r = max(self.comp) + 1
        hasdown = [any(self.L[y][x] for y in range(n)) for x in range(n)]
        hasup = [any(self.L[x][y] for y in range(n)) for x in range(n)]
        self.kind = []
        for x in range(n):
            if not hasdown[x] and not hasup[x]:
                self.kind.append("iso")
            elif not hasdown[x]:
                self.kind.append("min")
            elif not hasup[x]:
                self.kind.append("max")
            else:
                self.kind.append("mid")
        self.dsz = [sum(1 for y in range(n) if self.L[y][x]) for x in range(n)]

    def component_posets(self):
        out = []
        for c in range(self.r):
            els = [x for x in range(self.n) if self.comp[x] == c]
            idx = {x: i for i, x in enumerate(els)}
            sub = frozenset((idx[a], idx[b]) for (a, b) in self.rel if self.comp[a] == c)
            out.append(Poset(sub, len(els)))
        return out

    def depth(self):
        """depth[x] = number of elements of a longest chain with top x."""
        order = sorted(range(self.n), key=lambda x: self.dsz[x])
        d = [1] * self.n
        for x in order:
            for y in range(self.n):
                if self.L[y][x]:
                    d[x] = max(d[x], d[y] + 1)
        return d

    def longest(self):
        return max(self.depth())

    def graded(self):
        """Every maximal chain has the same number of elements."""
        n, L = self.n, self.L
        cover = [[y for y in range(n) if L[x][y]
                  and not any(L[x][z] and L[z][y] for z in range(n))] for x in range(n)]
        lengths = set()

        def rec(x, k):
            if not cover[x]:
                lengths.add(k)
                return
            for y in cover[x]:
                rec(y, k + 1)
        for x in range(n):
            if not any(L[y][x] for y in range(n)):
                rec(x, 1)
        return len(lengths) == 1

    def ideals(self):
        n = self.n
        cnt = 0
        for mask in range(1 << n):
            if all(mask >> a & 1 for (a, b) in self.rel if mask >> b & 1):
                cnt += 1
        return cnt

    def strict_maps(self, m):
        """Number of strictly order-preserving maps to [m], by backtracking
        along a linear extension."""
        order = sorted(range(self.n), key=lambda x: self.dsz[x])
        below = [[y for y in range(self.n) if self.L[y][x]] for x in order]
        val = {}

        def rec(i):
            if i == len(order):
                return 1
            x = order[i]
            lo = 1 + max((val[y] for y in below[i]), default=0)
            tot = 0
            for v in range(lo, m + 1):
                val[x] = v
                tot += rec(i + 1)
            val.pop(x, None)
            return tot
        return rec(0)

    def lambda_T(self, T):
        """lambda_T of notes/reciprocity_omega_c.md section 0: non-isolated
        minima, middles (by down-set size), isolated points other than T,
        non-isolated maxima, then T's point if T is a singleton."""
        n, kind = self.n, self.kind
        mins = [x for x in range(n) if kind[x] == "min"]
        mids = sorted((x for x in range(n) if kind[x] == "mid"), key=lambda x: self.dsz[x])
        isos = [x for x in range(n) if kind[x] == "iso"]
        maxs = [x for x in range(n) if kind[x] == "max"]
        tiso = [x for x in isos if self.comp[x] == T]
        other = [x for x in isos if self.comp[x] != T]
        return mins + mids + other + maxs + tiso      # order[label] = element


def h_Bplus(P, T, first=False):
    """h_j = #{w in Lin P : des w = j, T inside the last (first) piece}."""
    order = P.lambda_T(T)
    lab = {x: i for i, x in enumerate(order)}
    rel = frozenset((lab[a], lab[b]) for a, b in P.rel)
    comp = [P.comp[order[i]] for i in range(P.n)]
    Tset = {i for i in range(P.n) if comp[i] == T}
    c = Counter()
    for w in H.linexts(rel, P.n):
        cs = H.cuts(w, comp)
        if first:
            piece = w[:cs[0]] if cs else w
        else:
            piece = w[cs[-1]:] if cs else w
        if Tset <= set(piece):
            c[H.des(w)] += 1
    return H.trim([c.get(j, 0) for j in range(max(c, default=0) + 1)])


def h_TheoremH(rel, n):
    sep = H.relabel(rel, H.separated_extension(rel, n))
    comp = H.components(sep, n)
    cls = H.classes(H.linexts(sep, n), comp)
    c = Counter(H.cdes(cl[0]) - 1 for cl in cls)
    return H.trim([c.get(j, 0) for j in range(max(c) + 1)])


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=8)
    ap.add_argument("--mobmax", type=int, default=7)
    args = ap.parse_args(argv)

    by_n = H.unlabeled_posets(args.nmax)
    bad, cases = Counter(), Counter()
    ctl, ctl_tot = Counter(), Counter()
    rows = Counter()
    gap_min = {}
    examples = {}

    for n in range(2, args.nmax + 1):
        for rel in by_n[n]:
            P = Poset(rel, n)
            comps = P.component_posets()
            hH = h_TheoremH(rel, n)
            # [agree]
            cases["agree"] += 1
            ok = True
            for T in range(P.r):
                if h_Bplus(P, T) != hH:
                    ok = False
            if n <= args.mobmax:
                a, _ = H.omega_c_coeffs(rel, n)
                if H.h_of_poly(a, n) != hH:
                    ok = False
            if not ok:
                bad["agree"] += 1
            if P.r >= 2:
                ctl_tot["first"] += 1
                if any(h_Bplus(P, T, first=True) != hH for T in range(P.r)):
                    ctl["first"] += 1

            h = hH
            d = len(h) - 1
            Lmax = P.longest()
            r = P.r
            iso = sum(1 for k in P.kind if k == "iso")
            J = P.ideals()
            h1 = h[1] if d >= 1 else 0

            cases["h0"] += 1
            bad["h0"] += h[0] != 1
            cases["h1"] += 1
            bad["h1"] += h1 != J - 2 ** (r - 1) - n
            if r >= 2:
                ctl_tot["h1-r"] += 1
                ctl["h1-r"] += h1 != J - 1 - n

            if Lmax >= 2:
                cases["deg"] += 1
                bad["deg"] += d != n - Lmax
                prod = (Lmax - 1) ** iso
                for K in comps:
                    if K.n >= 2:
                        prod *= K.strict_maps(Lmax)
                cases["top"] += 1
                bad["top"] += h[d] != prod

            lks = [K.longest() for K in comps]
            hd1 = h[d - 1] if d >= 1 else 0
            nextprod = 1
            for K in comps:
                nextprod *= K.strict_maps(Lmax + 1)
            if all(l == Lmax for l in lks) and d >= 1:
                if Lmax >= 3:
                    cases["next"] += 1
                    bad["next"] += hd1 + (n + 1) * h[d] != nextprod
                elif Lmax == 2 and r >= 2:
                    ctl_tot["next-L2"] += 1
                    ctl["next-L2"] += hd1 + (n + 1) * h[d] != nextprod
            elif Lmax >= 3 and d >= 1:
                ctl_tot["next-mixed"] += 1
                ctl["next-mixed"] += hd1 + (n + 1) * h[d] != nextprod

            if r == 1:
                cases["inj"] += 1
                s = P.strict_maps(Lmax + 1)
                if not (s >= J and ((s == J) == P.graded())):
                    bad["inj"] += 1

            if r >= 2 and Lmax >= 3:
                cases["gap"] += 1
                g = hd1 - h1
                if not (h[d] >= 2 or g >= 2 ** (r - 1) - 1 >= 1):
                    bad["gap"] += 1
                key = "top>=2" if h[d] >= 2 else "next-gap"
                rows[(n, key)] += 1
                if key == "next-gap":
                    gap_min[n] = min(gap_min.get(n, 10 ** 9), g - (2 ** (r - 1) - 1))
                examples.setdefault(key, (n, sorted(rel), h))

            pal = h == h[::-1]
            pred = (r == 1 and P.graded()) or all(l <= 2 for l in lks)
            cases["pal-class"] += 1
            bad["pal-class"] += pal != pred
            rows[(n, "conn" if r == 1 else "disc", pal)] += 1
            ctl_tot["graded"] += 1
            ctl["graded"] += pal != all(K.graded() for K in comps)

    for key in ["agree", "h0", "h1", "deg", "top", "next", "inj", "gap", "pal-class"]:
        check(bad[key] == 0, f"[{key}] {cases[key] - bad[key]}/{cases[key]} posets")
    for key in ["first", "h1-r", "next-L2", "next-mixed", "graded"]:
        control(ctl[key], ctl_tot[key], f"[ctl-{key}]")
    print("# posets per n:", {n: len(by_n[n]) for n in range(2, args.nmax + 1)})
    print("# disconnected with a 3-chain, by which end pair breaks the symmetry (n, case): count")
    for key in sorted(k for k in rows if len(k) == 2):
        print(f"#   {key}: {rows[key]}")
    print("# min over next-gap posets of (h_{d-1} - h_1) - (2^(r-1) - 1), by n:", gap_min)
    print("# first example of each case (n, relation, h_C):")
    for key, ex in sorted(examples.items()):
        print(f"#   {key}: {ex}")
    print("# palindromic counts (n, connected?, palindromic): count")
    for key in sorted(k for k in rows if len(k) == 3):
        print(f"#   {key}: {rows[key]}")
    print("ALL PASS" if not FAILS else f"{len(FAILS)} FAILURES: {FAILS}")
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
