#!/usr/bin/env python3
"""Reciprocity for the cyclic order polynomial Omega_C(P, m).

Companion to ../notes/reciprocity_omega_c.md.

Imports from h_vector_omega_c.py ONLY the poset enumerator, the Moebius
computation of Omega_C from its definition, and the word helpers (linear
extensions, components, cyclic classes, cdes).  Every count of maps below is
a literal enumeration of surjective maps P -> [k], k <= n, written here.

Notation.  P on range(n), components K_c, T a component.  For a map f put
a_c = min f(K_c), b_c = max f(K_c).

  anchored_T(f) : no nonempty union of components U with T not in U has
                  min f(U) >  max f(P \\ U)        (Theorem Omega condition)
  D_T(f)        : no nonempty union of components U with T not in U has
                  min f(U) >= max f(P \\ U)        (the dual condition)

  Omega_C(P, m)     = #{f : P -> [m] order-preserving, anchored_T(f)}
  OmegaBar_C(P, m)  = #{f : P -> [m] strictly order-preserving, D_T(f)}

Both are computed as sum_k c_k C(m, k), c_k the number of SURJECTIVE maps
onto [k] with the property (both conditions only see the relative order of
values), enumerated as chains of order ideals.

Claims (PASS/FAIL, bracketed tags):
  [omega-anchored] the anchored count equals the Moebius definition, every T
  [recip]          OmegaBar_C(P, m) = (-1)^n Omega_C(P, -m) as polynomials, every T
  [recip-cdes]     OmegaBar_C(P, m) = sum_{kappa in Cyc P} C(m + cdes kappa - 1, n)
                   (separated labelling, n >= 2)
  [lemma-weak]     under lambda_T, anchored_T(f) iff the last piece of the
                   weak Stanley word w(f) (sort by (f, label)) contains T
  [lemma-strict]   under lambda_T, D_T(f) iff the last piece of the strict
                   Stanley word (sort by (f, -label)) contains T
  [criterion]      the interval criteria used for anchored_T / D_T agree with
                   the definition by brute force over all U (n <= CMAX)
  [dual]           Omega_C(P*, m) = Omega_C(P, m)
  [shift-h2]       every component has height <= 2 and n >= 2  =>
                   OmegaBar_C(P, m) = Omega_C(P, m - 1) and h_j = h_{n-2-j}
  [pal-class]      for n >= 2: h_C palindromic iff (P connected and graded)
                   or (every component has height <= 2)        (COMPUTED only)
CONTROLS (must be refuted somewhere):
  [ctl-naive]      strict maps with the anchored_T condition
  [ctl-mixed]      order-preserving maps with the D_T condition
  [ctl-lower]      strict maps with the anchoring on LOWER level sets (no
                   T-free U with max f(U) < min f(P \\ U))
  [ctl-plain]      all strict maps (Stanley's OmegaBar(P, m)), no anchoring
  [ctl-reverse]    h_C(P*) = reverse of h_C(P)
  [ctl-lemma-iso]  lemma-strict with T isolated but labelled below the
                   non-isolated maxima (lambda_0 instead of lambda_T)
  [ctl-lemma-any]  lemma-strict for an arbitrary natural labelling (n <= LMAX)
  [ctl-pal-graded] "h_C palindromic iff every component is graded"
  [ctl-shift-any]  OmegaBar_C(P, m) = Omega_C(P, m - 1) for every P (n >= 2)

Run from compute/:

    python3 reciprocity_omega_c.py --nmax 7 > output/reciprocity_omega_c.txt

Plain Python 3, one core.  Exit status 0 iff every claim holds and every
control is refuted somewhere.
"""

import argparse
import functools
import itertools
import sys
from collections import Counter

import h_vector_omega_c as H

FAILS = []
comb = H.comb


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
# Poset data


class Poset:
    def __init__(self, rel, n):
        self.rel, self.n = rel, n
        self.L = H.less(rel, n)
        self.comp = H.components(rel, n)
        self.r = max(self.comp) + 1
        self.down = [sum(1 << y for y in range(n) if self.L[y][x]) for x in range(n)]
        self.cmask = [sum(1 << x for x in range(n) if self.comp[x] == c)
                      for c in range(self.r)]
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
        self.dsz = [bin(self.down[x]).count("1") for x in range(n)]

    def label(self, T, iso_last=True):
        """lambda_T (iso_last=True): non-isolated minima, middles (by down-set
        size), isolated points other than T, non-isolated maxima, then T if T
        is an isolated point.  iso_last=False gives lambda_0 with T's point
        first among the isolated points."""
        n, kind = self.n, self.kind
        mins = [x for x in range(n) if kind[x] == "min"]
        mids = sorted((x for x in range(n) if kind[x] == "mid"), key=lambda x: self.dsz[x])
        isos = [x for x in range(n) if kind[x] == "iso"]
        maxs = [x for x in range(n) if kind[x] == "max"]
        tiso = [x for x in isos if self.comp[x] == T]
        other = [x for x in isos if self.comp[x] != T]
        if iso_last:
            order = mins + mids + other + maxs + tiso
        else:
            order = mins + mids + tiso + other + maxs
        lab = [0] * n
        for i, x in enumerate(order):
            lab[x] = i
        return lab

    def heights(self):
        out = []
        for c in range(self.r):
            els = [x for x in range(self.n) if self.comp[x] == c]

            @functools.lru_cache(None)
            def lc(x):
                return 1 + max([lc(y) for y in els if self.L[x][y]], default=0)
            out.append(max(lc(x) for x in els))
        return out

    def graded(self):
        """Every maximal chain of P has the same number of elements."""
        n, L = self.n, self.L
        cover = [[y for y in range(n) if L[x][y]
                  and not any(L[x][z] and L[z][y] for z in range(n))] for x in range(n)]

        @functools.lru_cache(None)
        def lens(x):
            if not cover[x]:
                return frozenset([1])
            return frozenset(1 + t for y in cover[x] for t in lens(y))
        s = set()
        for x in range(n):
            if not any(L[y][x] for y in range(n)):
                s |= lens(x)
        return len(s) == 1


# ---------------------------------------------------------------------------
# Surjective maps as chains of ideals


def surjections(P, strict):
    """Yield f (list of values 1..k) for every surjective weakly (strict=False)
    or strictly (strict=True) order-preserving f : P -> [k]."""
    n, down = P.n, P.down
    full = (1 << n) - 1
    f = [0] * n

    def rec(I, k):
        if I == full:
            yield f
            return
        rest = full & ~I
        # candidates: elements of the complement all of whose lower elements
        # are in I (strict: the next block is a nonempty set of these)
        if strict:
            mins = [x for x in range(n) if rest >> x & 1 and down[x] & ~I == 0]
            for t in range(1, 1 << len(mins)):
                S = 0
                for i, x in enumerate(mins):
                    if t >> i & 1:
                        S |= 1 << x
                        f[x] = k + 1
                yield from rec(I | S, k + 1)
        else:
            els = [x for x in range(n) if rest >> x & 1]
            for t in range(1, 1 << len(els)):
                S = 0
                for i, x in enumerate(els):
                    if t >> i & 1:
                        S |= 1 << x
                J = I | S
                if any(J >> x & 1 and down[x] & ~J for x in els):
                    continue
                for x in els:
                    if S >> x & 1:
                        f[x] = k + 1
                yield from rec(J, k + 1)
    yield from rec(0, 0)


def intervals(P, f):
    a = [10 ** 9] * P.r
    b = [0] * P.r
    for x in range(P.n):
        c = P.comp[x]
        if f[x] < a[c]:
            a[c] = f[x]
        if f[x] > b[c]:
            b[c] = f[x]
    return a, b


def anchored(a, b, T, M):
    """No v in [b_T, M-1] with every component unstraddled (b_c <= v or a_c > v)."""
    r = len(a)
    for v in range(b[T], M):
        if not any(a[c] <= v < b[c] for c in range(r)):
            return False
    return True


def dual_ok(a, b, T, M):
    """D_T: no v >= b_T with no component strictly straddling v (a_c < v < b_c)
    and some component c != T with a_c >= v."""
    r = len(a)
    for v in range(b[T], M + 1):
        if any(a[c] < v < b[c] for c in range(r)):
            continue
        if any(c != T and a[c] >= v for c in range(r)):
            return False
    return True


def brute(a, b, T, weak):
    r = len(a)
    for U in range(1, 1 << r):
        if U >> T & 1:
            continue
        mU = min(a[c] for c in range(r) if U >> c & 1)
        mR = max(b[c] for c in range(r) if not U >> c & 1)
        if (mU > mR) if weak else (mU >= mR):
            return False
    return True


def last_piece_has_T(P, word, T):
    """Is T inside the last piece (suffix after the last cut) of word?"""
    n = P.n
    seen = 0
    for p in range(n - 1, 0, -1):          # suffix word[p:]
        seen |= 1 << word[p]
        if all((seen & m) in (0, m) for m in P.cmask):
            return any(P.comp[word[q]] == T for q in range(p, n))
    return True                              # no cut: one piece


def poly_from_surj(c, ms):
    return [sum(c[k] * comb(m, k) for k in range(len(c))) for m in ms]


def omega_values(a, ms):
    """Omega_C(P, m) = sum_k a_k C(m, k) at integer m (negative allowed)."""
    out = []
    for m in ms:
        s = 0
        for k, ak in enumerate(a):
            # C(m, k) for any integer m
            num = 1
            for i in range(k):
                num *= (m - i)
            den = 1
            for i in range(1, k + 1):
                den *= i
            s += ak * (num // den)
        out.append(s)
    return out


def is_unimodal(h):
    i = 0
    while i + 1 < len(h) and h[i] <= h[i + 1]:
        i += 1
    while i + 1 < len(h) and h[i] >= h[i + 1]:
        i += 1
    return i == len(h) - 1


# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--lemmax", type=int, default=7, help="largest n for the word lemmas")
    ap.add_argument("--lmax", type=int, default=5, help="largest n for all-labelling control")
    ap.add_argument("--cmax", type=int, default=5, help="largest n for brute-force criterion")
    args = ap.parse_args(argv)

    by = H.unlabeled_posets(args.nmax)
    total = {"posets": 0, "pairs": 0}
    bad = Counter()
    ctl = Counter()
    ctl_tot = Counter()
    cases = Counter()
    hdata = {}
    pal_rows = Counter()
    nonuni = Counter()

    for n in range(1, args.nmax + 1):
        canon_index = {rel: i for i, rel in enumerate(by[n])}
        hs = {}
        for rel in by[n]:
            P = Poset(rel, n)
            total["posets"] += 1
            a, ok = H.omega_c_coeffs(rel, n)
            hs[rel] = H.h_of_poly(a, n)
            ms = list(range(0, n + 2))
            target = [(-1) ** n * v for v in omega_values(a, [-m for m in ms])]
            omega = omega_values(a, ms)

            # counts c_k for every T
            cw = [[0] * (n + 1) for _ in range(P.r)]       # weak, anchored_T
            cs = [[0] * (n + 1) for _ in range(P.r)]       # strict, D_T
            c_naive = [[0] * (n + 1) for _ in range(P.r)]  # strict, anchored_T
            c_mixed = [[0] * (n + 1) for _ in range(P.r)]  # weak, D_T
            c_plain = [0] * (n + 1)
            c_lower = [[0] * (n + 1) for _ in range(P.r)]  # strict, lower anchoring
            labs = [P.label(T) for T in range(P.r)]
            labs0 = [P.label(T, iso_last=False) for T in range(P.r)]
            dolem = n <= args.lemmax
            for strict in (False, True):
                for f in surjections(P, strict):
                    k = max(f)
                    A, B = intervals(P, f)
                    if strict:
                        c_plain[k] += 1
                    for T in range(P.r):
                        an = anchored(A, B, T, k)
                        du = dual_ok(A, B, T, k)
                        if n <= args.cmax:
                            cases["criterion"] += 1
                            if an != brute(A, B, T, True) or du != brute(A, B, T, False):
                                bad["criterion"] += 1
                        if strict:
                            if du:
                                cs[T][k] += 1
                            if an:
                                c_naive[T][k] += 1
                            if anchored([k + 1 - y for y in B], [k + 1 - y for y in A], T, k):
                                c_lower[T][k] += 1
                        else:
                            if an:
                                cw[T][k] += 1
                            if du:
                                c_mixed[T][k] += 1
                        if dolem:
                            lab = labs[T]
                            if strict:
                                w = sorted(range(n), key=lambda x: (f[x], -lab[x]))
                                cases["lemma-strict"] += 1
                                if last_piece_has_T(P, w, T) != du:
                                    bad["lemma-strict"] += 1
                                if P.kind[P.cmask[T].bit_length() - 1] == "iso" and P.r < n:
                                    lab0 = labs0[T]
                                    w0 = sorted(range(n), key=lambda x: (f[x], -lab0[x]))
                                    ctl_tot["lemma-iso"] += 1
                                    if last_piece_has_T(P, w0, T) != du:
                                        ctl["lemma-iso-maps"] += 1
                            else:
                                w = sorted(range(n), key=lambda x: (f[x], lab[x]))
                                cases["lemma-weak"] += 1
                                if last_piece_has_T(P, w, T) != an:
                                    bad["lemma-weak"] += 1

            for T in range(P.r):
                total["pairs"] += 1
                if poly_from_surj(cw[T], ms) != omega:
                    bad["omega-anchored"] += 1
                if poly_from_surj(cs[T], ms) != target:
                    bad["recip"] += 1
                ctl_tot["naive"] += 1
                if poly_from_surj(c_naive[T], ms) != target:
                    ctl["naive"] += 1
                ctl_tot["lower"] += 1
                if poly_from_surj(c_lower[T], ms) != target:
                    ctl["lower"] += 1
                ctl_tot["mixed"] += 1
                if poly_from_surj(c_mixed[T], ms) != target:
                    ctl["mixed"] += 1
            ctl_tot["plain"] += 1
            if poly_from_surj(c_plain, ms) != target:
                ctl["plain"] += 1

            # cdes form of OmegaBar_C
            if n >= 2:
                sep = H.relabel(rel, H.separated_extension(rel, n))
                comp = H.components(sep, n)
                cls = H.classes(H.linexts(sep, n), comp)
                vals = [sum(comb(m + H.cdes(cl[0]) - 1, n) for cl in cls) for m in ms]
                cases["recip-cdes"] += 1
                if vals != target:
                    bad["recip-cdes"] += 1

            # height <= 2 shift
            if n >= 2:
                h2 = all(t <= 2 for t in P.heights())
                shifted = omega_values(a, [m - 1 for m in ms])
                eq = shifted == target
                h = hs[rel]
                hfull = h + [0] * (n - 1 - len(h))
                symm = all(hfull[j] == hfull[n - 2 - j] for j in range(n - 1))
                if h2:
                    cases["shift-h2"] += 1
                    if not (eq and symm):
                        bad["shift-h2"] += 1
                else:
                    ctl_tot["shift-any"] += 1
                    if not eq:
                        ctl["shift-any"] += 1
                pal = h == h[::-1]
                conn = P.r == 1
                gr = P.graded()
                predicted = (conn and gr) or h2
                cases["pal-class"] += 1
                if pal != predicted:
                    bad["pal-class"] += 1
                pal_rows[(n, conn, pal)] += 1
                # control: palindromic iff every component graded
                comps_graded = True
                for c in range(P.r):
                    els = [x for x in range(n) if P.comp[x] == c]
                    sub = frozenset((els.index(x), els.index(y)) for (x, y) in rel
                                    if P.comp[x] == c)
                    if not Poset(sub, len(els)).graded():
                        comps_graded = False
                ctl_tot["pal-graded"] += 1
                if pal != comps_graded:
                    ctl["pal-graded"] += 1
                if not is_unimodal(h):
                    nonuni[n] += 1

            # all-labelling control for the strict lemma
            if n <= args.lmax and n >= 2:
                for w in H.linexts(rel, n):
                    lab = [0] * n
                    for i, x in enumerate(w):
                        lab[x] = i
                    for T in range(P.r):
                        ctl_tot["lemma-any"] += 1
                        fail = False
                        for f in surjections(P, True):
                            k = max(f)
                            A, B = intervals(P, f)
                            ww = sorted(range(n), key=lambda x: (f[x], -lab[x]))
                            if last_piece_has_T(P, ww, T) != dual_ok(A, B, T, k):
                                fail = True
                                break
                        if fail:
                            ctl["lemma-any"] += 1

        # duality on this n
        for rel in by[n]:
            star = H.canonical(frozenset((b, a) for (a, b) in rel), n)
            cases["dual"] += 1
            if hs[star] != hs[rel]:
                bad["dual"] += 1
            ctl_tot["reverse"] += 1
            if hs[star] != hs[rel][::-1]:
                ctl["reverse"] += 1
        hdata[n] = hs
        print(f"# n={n}: {len(by[n])} posets done", flush=True)

    print(f"# {total['posets']} posets, {total['pairs']} (poset, T) pairs, n <= {args.nmax}")
    check(bad["omega-anchored"] == 0,
          f"[omega-anchored] anchored-map count = Moebius Omega_C on all {total['pairs']} (P, T)")
    check(bad["recip"] == 0,
          f"[recip] OmegaBar_C(P,m) = (-1)^n Omega_C(P,-m) on all {total['pairs']} (P, T), "
          f"m = 0..n+1 (polynomial identity)")
    check(bad["recip-cdes"] == 0,
          f"[recip-cdes] OmegaBar_C = sum_kappa C(m+cdes-1, n) on {cases['recip-cdes']} posets n>=2")
    check(bad["lemma-weak"] == 0,
          f"[lemma-weak] anchored_T iff T in last piece of w(f), lambda_T, "
          f"{cases['lemma-weak']} (surjective map, T) cases, n <= {args.lemmax}")
    check(bad["lemma-strict"] == 0,
          f"[lemma-strict] D_T iff T in last piece of strict word, lambda_T, "
          f"{cases['lemma-strict']} cases, n <= {args.lemmax}")
    check(bad["criterion"] == 0,
          f"[criterion] interval criteria = brute force over U, {cases['criterion']} cases, n <= {args.cmax}")
    check(bad["dual"] == 0, f"[dual] h_C(P*) = h_C(P) on {cases['dual']} posets")
    check(bad["shift-h2"] == 0,
          f"[shift-h2] heights <= 2: OmegaBar_C(m) = Omega_C(m-1), h_j = h_(n-2-j), "
          f"{cases['shift-h2']} posets")
    check(bad["pal-class"] == 0,
          f"[pal-class] palindromic iff (connected and graded) or all heights <= 2, "
          f"{cases['pal-class']} posets n>=2")
    for key in ["naive", "lower", "mixed", "plain", "reverse", "pal-graded", "shift-any"]:
        control(ctl[key], ctl_tot[key], f"[ctl-{key}]")
    control(ctl["lemma-iso-maps"], ctl_tot["lemma-iso"],
            "[ctl-lemma-iso] (counted over (map, T) cases)")
    control(ctl["lemma-any"], ctl_tot["lemma-any"],
            f"[ctl-lemma-any] (labelled (P, T) pairs, n <= {args.lmax})")
    print("# palindromic counts (n, connected, palindromic): count")
    for key in sorted(pal_rows):
        print(f"#   {key}: {pal_rows[key]}")
    print("# non-unimodal h_C by n:", dict(nonuni) if nonuni else "none")
    print("# small values: h_C and OmegaBar_C(P, m) for m = 1..5")
    small = {
        "A_2": (frozenset(), 2),
        "C_2+C_1": (frozenset({(0, 1)}), 3),
        "C_2+C_2": (frozenset({(0, 1), (2, 3)}), 4),
        "C_3+C_1": (frozenset({(0, 1), (1, 2), (0, 2)}), 4),
        "A_4": (frozenset(), 4),
        "C_3+C_3": (frozenset({(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)}), 6),
    }
    for name, (rel, n) in small.items():
        a, _ = H.omega_c_coeffs(rel, n)
        ob = [(-1) ** n * v for v in omega_values(a, [-m for m in range(1, 6)])]
        print(f"#   {name}: h_C = {H.h_of_poly(a, n)}, OmegaBar_C = {ob}")
    print("ALL PASS" if not FAILS else "FAILURES: " + ", ".join(FAILS))
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
