#!/usr/bin/env python3
"""Independent audit of notes/reciprocity_omega_c.md (mg-b2b04).

Written from the definitions only; imports nothing from the repo.

  Omega_C(P,m) := sum_{pi in OP(P)} (-1)^{|pi|-1} mu(pi,1hat) C(m,|pi|)
  (OP(P) = set partitions with acyclic quotient digraph, refinement order.)

  OmegaBar_C(P,m) := #{f : P -> [m] strictly order-preserving with D_T},
  D_T: no nonempty T-free union of components U has min f(U) >= max f(P\\U).

Checks (labels in brackets are printed in the output):
  [iso]      poset counts 1,2,5,16,63,318,2045 (A000112), positive control of
             the enumerator
  [omega]    Theorem Omega (literal anchored maps) vs the Moebius definition
  [R-all]    Theorem R with OmegaBar from ALL maps P -> [m], m <= n+1, n <= NALL
  [R-surj]   Theorem R with OmegaBar from surjective maps, n <= NMAX
  [R1],[R2]  the word lemmas under lambda_T, every surjective map, every T
  [B+]       h_C = des distribution on B_T under lambda_T
  [R']       OmegaBar = sum_kappa C(m+cdes-1,n), lambda_0 (separated)
  [dual]     Omega_C(P*) = Omega_C(P) from the Moebius sums of both
  [S]        height <= 2 => OmegaBar(m) = Omega_C(m-1), h palindromic;
             the explicit bijection g of Prop. S checked map by map
  [S']       palindromic iff (connected & graded) or all heights <= 2
  [E]        non-convexity example, interior description sampled
  CONTROLS (each must FAIL somewhere): naive, lower, lower-weak, mixed, plain,
             reverse, shift-any, pal-graded, lemma with lambda_0 for isolated T,
             lemma under arbitrary natural labellings, planted sign bug.
"""
import argparse
import itertools
import random
import sys
from math import comb, factorial
from fractions import Fraction


# ---------------------------------------------------------------- posets
def closure_ok(downs, D):
    for i in range(len(downs)):
        if D >> i & 1 and downs[i] & ~D:
            return False
    return True


def canon(n, downs):
    """Canonical form: min over relabellings within signature classes."""
    up = [0] * n
    for j in range(n):
        for i in range(n):
            if downs[j] >> i & 1:
                up[i] |= 1 << j
    sig = [(bin(downs[i]).count('1'), bin(up[i]).count('1')) for i in range(n)]
    for _ in range(2):
        sig = [(sig[i],
                tuple(sorted(sig[k] for k in range(n) if downs[i] >> k & 1)),
                tuple(sorted(sig[k] for k in range(n) if up[i] >> k & 1)))
               for i in range(n)]
    keys = sorted(set(sig))
    classes = [[i for i in range(n) if sig[i] == k] for k in keys]
    best = None
    for parts in itertools.product(*[itertools.permutations(c) for c in classes]):
        order = [x for p in parts for x in p]          # new position -> old
        pos = {old: new for new, old in enumerate(order)}
        enc = tuple(sum(1 << pos[i] for i in range(n) if downs[old] >> i & 1)
                    for old in order)
        if best is None or enc < best:
            best = enc
    return best


def posets_upto(nmax):
    """Iso classes, by adding a new maximal element over every order ideal."""
    levels = {1: [(0,)]}
    for n in range(2, nmax + 1):
        seen = set()
        out = []
        for Q in levels[n - 1]:
            m = n - 1
            for D in range(1 << m):
                if not closure_ok(Q, D):
                    continue
                downs = list(Q) + [D]
                c = canon(n, downs)
                if c not in seen:
                    seen.add(c)
                    out.append(c)
        levels[n] = out
    return levels


class Poset:
    def __init__(self, downs):
        self.n = n = len(downs)
        self.down = list(downs)
        self.up = [0] * n
        for j in range(n):
            for i in range(n):
                if downs[j] >> i & 1:
                    self.up[i] |= 1 << j
        # components
        comp = list(range(n))

        def find(x):
            while comp[x] != x:
                comp[x] = comp[comp[x]]
                x = comp[x]
            return x
        for j in range(n):
            for i in range(n):
                if downs[j] >> i & 1:
                    comp[find(i)] = find(j)
        roots = sorted(set(find(i) for i in range(n)))
        self.comps = [sum(1 << i for i in range(n) if find(i) == r) for r in roots]
        self.r = len(self.comps)
        self.compof = [0] * n
        for c, mask in enumerate(self.comps):
            for i in range(n):
                if mask >> i & 1:
                    self.compof[i] = c
        self.relations = [(i, j) for j in range(n) for i in range(n) if downs[j] >> i & 1]
        # T-free clusters for each T, as element masks
        full = (1 << self.r) - 1
        self.cl_by_cmask = {}
        for cm in range(1, full):
            self.cl_by_cmask[cm] = sum(self.comps[c] for c in range(self.r) if cm >> c & 1)

    def dual(self):
        return Poset(self.up)

    def kind(self, x):
        if self.down[x] == 0 and self.up[x] == 0:
            return 'iso'
        if self.down[x] == 0:
            return 'min'
        if self.up[x] == 0:
            return 'max'
        return 'mid'

    def height(self, comp_mask=None):
        # longest chain (number of elements) within the given set
        n = self.n
        best = [0] * n
        for j in range(n):  # labels are natural (canon keeps downs[j] < j? not guaranteed)
            pass
        memo = {}

        def h(x):
            if x in memo:
                return memo[x]
            v = 1 + max([h(i) for i in range(n) if self.down[x] >> i & 1], default=0)
            memo[x] = v
            return v
        S = range(n) if comp_mask is None else [i for i in range(n) if comp_mask >> i & 1]
        return max(h(x) for x in S)

    def graded(self):
        """Every maximal chain has the same number of elements."""
        n = self.n
        lens = set()
        mins = [x for x in range(n) if self.down[x] == 0]

        def covers(x):
            return [y for y in range(n) if self.up[x] >> y & 1 and
                    not any(self.up[x] >> z & 1 and self.up[z] >> y & 1 for z in range(n))]

        def walk(x, l):
            c = covers(x)
            if not c:
                lens.add(l)
            for y in c:
                walk(y, l + 1)
        for x in mins:
            walk(x, 1)
        return len(lens) == 1

    def linext(self):
        n = self.n
        out = []

        def rec(placed, seq):
            if len(seq) == n:
                out.append(tuple(seq))
                return
            for x in range(n):
                if not placed >> x & 1 and self.down[x] & ~placed == 0:
                    seq.append(x)
                    rec(placed | 1 << x, seq)
                    seq.pop()
        rec(0, [])
        return out


# --------------------------------------------------------- Moebius side
def set_partitions(n):
    def rec(i, rgs, k):
        if i == n:
            yield tuple(rgs)
            return
        for b in range(k + 1):
            rgs.append(b)
            yield from rec(i + 1, rgs, max(k, b + 1))
            rgs.pop()
    yield from rec(0, [], 0)


def omega_c_coeffs(P):
    """a[k] = sum_{|pi|=k} (-1)^{k-1} mu(pi,1hat), from the definition."""
    n = P.n
    OP = []
    for rgs in set_partitions(n):
        k = max(rgs) + 1
        edges = set()
        for (i, j) in P.relations:
            if rgs[i] != rgs[j]:
                edges.add((rgs[i], rgs[j]))
        indeg = [0] * k
        adj = [[] for _ in range(k)]
        for a, b in edges:
            adj[a].append(b)
            indeg[b] += 1
        stack = [b for b in range(k) if indeg[b] == 0]
        seen = 0
        while stack:
            a = stack.pop()
            seen += 1
            for b in adj[a]:
                indeg[b] -= 1
                if indeg[b] == 0:
                    stack.append(b)
        if seen != k:
            continue
        pm = 0
        for i in range(n):
            for j in range(i + 1, n):
                if rgs[i] == rgs[j]:
                    pm |= 1 << (i * n + j)
        OP.append((k, pm))
    OP.sort()                      # 1hat (k=1) first
    mu = []
    for idx, (k, pm) in enumerate(OP):
        if idx == 0:
            assert k == 1
            mu.append(1)
            continue
        s = 0
        for jdx in range(idx):
            k2, pm2 = OP[jdx]
            if k2 < k and pm & ~pm2 == 0:
                s += mu[jdx]
        mu.append(-s)
    a = [0] * (n + 1)
    for (k, pm), m_ in zip(OP, mu):
        a[k] += (-1) ** (k - 1) * m_
    return a, len(OP)


def binom_poly(m, k):
    """C(m,k) as the polynomial m(m-1)...(m-k+1)/k!, valid for negative m."""
    num = 1
    for i in range(k):
        num *= (m - i)
    return Fraction(num, factorial(k))


def ev(a, m):
    return sum(a[k] * binom_poly(m, k) for k in range(len(a)))


def h_from_values(vals, n):
    """vals[m] for m = 0..n+1 of a poly of degree <= n with value 0 at 0.
    Returns h_0..h_n with sum_m vals[m] x^m = sum h_j x^{j+1}/(1-x)^{n+1}."""
    # multiply sum vals[m] x^m by (1-x)^{n+1}; coefficients x^1..x^{n+1}
    coef = [(-1) ** i * comb(n + 1, i) for i in range(n + 2)]
    out = []
    for e in range(1, n + 2):
        out.append(sum(coef[i] * vals[e - i] for i in range(n + 2) if 0 <= e - i < len(vals)))
    return out  # out[j] = h_j


# --------------------------------------------------------- map enumeration
def maps_all(P, M, strict):
    """All (strictly) order-preserving f : P -> [M], literal backtracking."""
    n = P.n
    order = P.linext()[0]
    f = [0] * n

    def rec(t):
        if t == n:
            yield tuple(f)
            return
        x = order[t]
        lo = 1
        for i in range(n):
            if P.down[x] >> i & 1:
                lo = max(lo, f[i] + (1 if strict else 0))
        for v in range(lo, M + 1):
            f[x] = v
            yield from rec(t + 1)
        f[x] = 0
    yield from rec(0)


def maps_surj(P, strict):
    """(Strictly) order-preserving f onto [k], all k: yields (f, k)."""
    n = P.n
    for k in range(1, n + 1):
        for f in maps_all(P, k, strict):
            if len(set(f)) == k:
                yield f, k


def good_T_mask(P, f, strict_ineq):
    """Bitmask over components T for which no T-free cluster U violates.
    strict_ineq=True: violation is min f(U) > max f(P\\U) (anchoring).
    strict_ineq=False: violation is min f(U) >= max f(P\\U) (D_T)."""
    r = P.r
    full = (1 << r) - 1
    if r == 1:
        return 1
    cmin = [min(f[i] for i in range(P.n) if P.comps[c] >> i & 1) for c in range(r)]
    cmax = [max(f[i] for i in range(P.n) if P.comps[c] >> i & 1) for c in range(r)]
    bad = 0
    for cm in range(1, full):
        mn = min(cmin[c] for c in range(r) if cm >> c & 1)
        mx = max(cmax[c] for c in range(r) if not cm >> c & 1)
        if (mn > mx) if strict_ineq else (mn >= mx):
            bad |= full & ~cm          # every T outside U is violated
    return full & ~bad


def good_T_mask_lower(P, f, strict_ineq):
    """Lower-level-set control: violation = max f(U) < min f(P\\U)
    (strict_ineq) or max f(U) <= min f(P\\U)."""
    r = P.r
    full = (1 << r) - 1
    if r == 1:
        return 1
    cmin = [min(f[i] for i in range(P.n) if P.comps[c] >> i & 1) for c in range(r)]
    cmax = [max(f[i] for i in range(P.n) if P.comps[c] >> i & 1) for c in range(r)]
    bad = 0
    for cm in range(1, full):
        mx = max(cmax[c] for c in range(r) if cm >> c & 1)
        mn = min(cmin[c] for c in range(r) if not cm >> c & 1)
        if (mx < mn) if strict_ineq else (mx <= mn):
            bad |= full & ~cm
    return full & ~bad


# --------------------------------------------------------- words
def labelling(P, T, kind):
    """kind='T': lambda_T; kind='0': lambda_0 (isolated points, T included,
    listed in increasing element order, before the non-isolated maxima)."""
    n = P.n
    ks = [P.kind(x) for x in range(n)]
    Tsing = bin(P.comps[T]).count('1') == 1
    tpt = (P.comps[T].bit_length() - 1) if Tsing else None
    mins = [x for x in range(n) if ks[x] == 'min']
    mids = [x for x in P.linext()[0] if ks[x] == 'mid']
    isos = [x for x in range(n) if ks[x] == 'iso']
    maxs = [x for x in range(n) if ks[x] == 'max']
    if kind == 'T':
        seq = mins + mids + [x for x in isos if x != tpt] + maxs + ([tpt] if Tsing else [])
    else:
        seq = mins + mids + isos + maxs
    lam = [0] * n
    for i, x in enumerate(seq):
        lam[x] = i
    for (i, j) in P.relations:
        assert lam[i] < lam[j]
    return lam


def word(f, lam, strict):
    n = len(f)
    if strict:
        return tuple(sorted(range(n), key=lambda x: (f[x], -lam[x])))
    return tuple(sorted(range(n), key=lambda x: (f[x], lam[x])))


def last_piece_mask(P, w):
    n = P.n
    pref = 0
    last_cut = 0
    for p in range(1, n):
        pref |= 1 << w[p - 1]
        # prefix a union of components?
        if all((pref & c) in (0, c) for c in P.comps):
            last_cut = p
    return sum(1 << w[i] for i in range(last_cut, n))


def in_B(P, w, T):
    return P.comps[T] & ~last_piece_mask(P, w) == 0


def des(w, lam):
    return sum(1 for i in range(len(w) - 1) if lam[w[i]] > lam[w[i + 1]])


def cyc_classes(P, lam):
    seen = set()
    out = []
    for w in P.linext():
        if w in seen:
            continue
        cls = set()
        n = P.n
        pref = 0
        cls.add(w)
        for p in range(1, n):
            pref |= 1 << w[p - 1]
            if all((pref & c) in (0, c) for c in P.comps):
                cls.add(w[p:] + w[:p])
        seen |= cls
        u = min(cls)
        cdes = des(u, lam) + (1 if lam[u[-1]] > lam[u[0]] else 0)
        # cdes constant on the class?
        for v in cls:
            assert des(v, lam) + (1 if lam[v[-1]] > lam[v[0]] else 0) == cdes
        out.append(cdes)
    return out


# --------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=7)
    ap.add_argument('--nall', type=int, default=6,
                    help='n bound for the all-maps (non-surjective) literal count')
    ap.add_argument('--lmax', type=int, default=5,
                    help='n bound for the arbitrary-labelling control')
    ap.add_argument('--nbij', type=int, default=6,
                    help='n bound for the map-by-map check of the bijection of Prop. S')
    ap.add_argument('--twocomp', action='store_true',
                    help='only check h_C(Q+T) = W_P - t W_Q W_T (two components)')
    args = ap.parse_args()
    random.seed(1)
    levels = posets_upto(args.nmax)
    if args.twocomp:
        sys.exit(two_comp(levels, args.nmax))
    cnts = [len(levels[n]) for n in range(1, args.nmax + 1)]
    print('[iso] iso classes by n:', cnts, '(A000112: 1,2,5,16,63,318,2045)')
    assert cnts == [1, 2, 5, 16, 63, 318, 2045][:args.nmax]

    C = dict(pairs=0, posets=0, omega_bad=0, Rall_pairs=0, Rall_bad=0, Rsurj_bad=0,
             R1=0, R1_bad=0, R2=0, R2_bad=0, Bplus_bad=0, Rp=0, Rp_bad=0,
             dual_bad=0, S=0, S_bad=0, Sbij=0, Sbij_bad=0, Sp_bad=0,
             naive=0, lower=0, lowerw=0, mixed=0, plain=0, reverse=0, reverse_full=0,
             shift_any=0, shift_any_tot=0, pal_graded=0, lam0=0, lam0_iso_pairs=0,
             any_lab=0, any_lab_tot=0, signbug=0, Tdep=0, disc=0,
             unimodal_bad=0)
    for n in range(1, args.nmax + 1):
        for downs in levels[n]:
            P = Poset(downs)
            C['posets'] += 1
            if C['posets'] % 200 == 0:
                print(f"  {C['posets']} posets", file=sys.stderr, flush=True)
            a, nop = omega_c_coeffs(P)
            OmC = [ev(a, m) for m in range(0, n + 2)]
            hC = h_from_values(OmC, n)
            Pd = P.dual()
            ad, _ = omega_c_coeffs(Pd)
            if ad != a:
                C['dual_bad'] += 1
            hCd = h_from_values([ev(ad, m) for m in range(n + 2)], n)
            tr = list(hC)
            while tr and tr[-1] == 0:
                tr.pop()
            trd = list(hCd)
            while trd and trd[-1] == 0:
                trd.pop()
            if trd != tr[::-1]:
                C['reverse'] += 1
            if hCd != hC[::-1]:
                C['reverse_full'] += 1
            # unimodality of trimmed h
            peak = tr.index(max(tr))
            if any(tr[i] > tr[i + 1] for i in range(peak)) or \
               any(tr[i] < tr[i + 1] for i in range(peak, len(tr) - 1)):
                C['unimodal_bad'] += 1
            # target: (-1)^n Omega_C(P,-m), m = 0..n+1
            target = [(-1) ** n * ev(a, -m) for m in range(0, n + 2)]
            if n % 2 == 1:
                if any(ev(a, -m) != target[m] for m in range(n + 2)):
                    C['signbug'] += 1
            # ---- literal surjective counts, all T at once
            s_aw = [[0] * (n + 1) for _ in range(P.r)]   # weak anchored onto [k]
            s_D = [[0] * (n + 1) for _ in range(P.r)]    # strict D_T
            s_naive = [[0] * (n + 1) for _ in range(P.r)]
            s_low = [[0] * (n + 1) for _ in range(P.r)]
            s_loww = [[0] * (n + 1) for _ in range(P.r)]
            s_mixed = [[0] * (n + 1) for _ in range(P.r)]
            s_plain = [0] * (n + 1)
            lamT = [labelling(P, T, 'T') for T in range(P.r)]
            lam0 = labelling(P, 0, '0')
            desB = [[0] * n for _ in range(P.r)]
            for f, k in maps_surj(P, strict=False):
                gw = good_T_mask(P, f, True)
                gD = good_T_mask(P, f, False)
                for T in range(P.r):
                    if gw >> T & 1:
                        s_aw[T][k] += 1
                    if gD >> T & 1:
                        s_mixed[T][k] += 1
                    if n >= 2:
                        C['R1'] += 1
                        w = word(f, lamT[T], False)
                        if bool(gw >> T & 1) != in_B(P, w, T):
                            C['R1_bad'] += 1
            for f, k in maps_surj(P, strict=True):
                s_plain[k] += 1
                gw = good_T_mask(P, f, True)
                gD = good_T_mask(P, f, False)
                gl = good_T_mask_lower(P, f, True)
                glw = good_T_mask_lower(P, f, False)
                for T in range(P.r):
                    if gD >> T & 1:
                        s_D[T][k] += 1
                    if gw >> T & 1:
                        s_naive[T][k] += 1
                    if gl >> T & 1:
                        s_low[T][k] += 1
                    if glw >> T & 1:
                        s_loww[T][k] += 1
                    if n >= 2:
                        C['R2'] += 1
                        w = word(f, lamT[T], True)
                        if bool(gD >> T & 1) != in_B(P, w, T):
                            C['R2_bad'] += 1
                        Tsing = bin(P.comps[T]).count('1') == 1
                        if Tsing and P.r < n:     # isolated T, not an antichain
                            w0 = word(f, lam0, True)
                            if bool(gD >> T & 1) != in_B(P, w0, T):
                                C['lam0'] += 1

            def poly_from_s(s, m):
                return sum(s[k] * comb(m, k) for k in range(n + 1))
            Rbar_by_T = []
            for T in range(P.r):
                C['pairs'] += 1
                if any(poly_from_s(s_aw[T], m) != OmC[m] for m in range(n + 2)):
                    C['omega_bad'] += 1
                vals = [poly_from_s(s_D[T], m) for m in range(n + 2)]
                Rbar_by_T.append(vals)
                if vals != target:
                    C['Rsurj_bad'] += 1
                if [poly_from_s(s_naive[T], m) for m in range(n + 2)] != target:
                    C['naive'] += 1
                if [poly_from_s(s_low[T], m) for m in range(n + 2)] != target:
                    C['lower'] += 1
                if [poly_from_s(s_loww[T], m) for m in range(n + 2)] != target:
                    C['lowerw'] += 1
                if [poly_from_s(s_mixed[T], m) for m in range(n + 2)] != target:
                    C['mixed'] += 1
                # B+
                if n >= 2:
                    dist = [0] * n
                    for w in P.linext():
                        if in_B(P, w, T):
                            dist[des(w, lamT[T])] += 1
                    if dist + [0] != hC:
                        C['Bplus_bad'] += 1
            if [poly_from_s(s_plain, m) for m in range(n + 2)] != target:
                C['plain'] += 1
            if P.r > 1:
                C['disc'] += 1
            # ---- fully literal all-maps count for n <= nall
            if n <= args.nall:
                M = n + 1
                hist = [[0] * (M + 1) for _ in range(P.r)]
                for f in maps_all(P, M, strict=True):
                    gD = good_T_mask(P, f, False)
                    mx = max(f)
                    for T in range(P.r):
                        if gD >> T & 1:
                            hist[T][mx] += 1
                for T in range(P.r):
                    C['Rall_pairs'] += 1
                    cum = 0
                    vals = [0]
                    for m in range(1, M + 1):
                        cum += hist[T][m]
                        vals.append(cum)
                    if vals != target[:M + 1]:
                        C['Rall_bad'] += 1
            # ---- R' (lambda_0 is separated)
            if n >= 2:
                C['Rp'] += 1
                cd = cyc_classes(P, lam0)
                if [sum(comb(m + c - 1, n) if m + c - 1 >= 0 else 0 for c in cd)
                        for m in range(n + 2)] != target:
                    C['Rp_bad'] += 1
            # ---- S, S'
            if n >= 2:
                h2 = P.height() <= 2
                shift = all(target[m] == OmC[m - 1] for m in range(1, n + 2))
                trimmed = hC[:n - 1]
                palS = trimmed == trimmed[::-1] and hC[n - 1] == 0 and hC[n] == 0
                pal = tr == tr[::-1]           # trimmed of trailing zeros
                if h2:
                    C['S'] += 1
                    if not shift or not palS:
                        C['S_bad'] += 1
                    # explicit bijection, m = n
                    for T in (range(P.r) if n <= args.nbij else []):
                        Tsing = bin(P.comps[T]).count('1') == 1
                        tpt = (P.comps[T].bit_length() - 1) if Tsing else None
                        m = n
                        img = set()
                        for f in maps_all(P, m, strict=True):
                            if not good_T_mask(P, f, False) >> T & 1:
                                continue
                            g = tuple(f[x] - 1 if (P.kind(x) == 'max' or x == tpt) else f[x]
                                      for x in range(n))
                            C['Sbij'] += 1
                            ok = all(1 <= v <= m - 1 for v in g) and \
                                all(g[i] <= g[j] for (i, j) in P.relations) and \
                                (good_T_mask(P, g, True) >> T & 1)
                            if not ok or g in img:
                                C['Sbij_bad'] += 1
                            img.add(g)
                        nanch = sum(1 for g in maps_all(P, m - 1, strict=False)
                                    if good_T_mask(P, g, True) >> T & 1)
                        if nanch != len(img):
                            C['Sbij_bad'] += 1
                else:
                    C['shift_any_tot'] += 1
                    if not shift:
                        C['shift_any'] += 1
                predicted = (P.r == 1 and P.graded()) or h2
                if pal != predicted:
                    C['Sp_bad'] += 1
                allgraded = all(Poset_sub_graded(P, c) for c in P.comps)
                if pal != allgraded:
                    C['pal_graded'] += 1
            # ---- T-independence of the literal count
            if any(v != Rbar_by_T[0] for v in Rbar_by_T):
                C['Tdep'] += 1
            # ---- arbitrary natural labellings (control), n <= lmax
            if 2 <= n <= args.lmax and P.r > 1:
                for L in P.linext():
                    lam = [0] * n
                    for i, x in enumerate(L):
                        lam[x] = i
                    for T in range(P.r):
                        C['any_lab_tot'] += 1
                        bad = False
                        for f, k in maps_surj(P, strict=True):
                            gD = good_T_mask(P, f, False) >> T & 1
                            if bool(gD) != in_B(P, word(f, lam, True), T):
                                bad = True
                                break
                        if bad:
                            C['any_lab'] += 1
        print(f'  n={n} done', file=sys.stderr, flush=True)

    # ---------------- E: non-convexity and sampled interior description
    E = Poset([0, 0, 1 << 1, 1 << 1])   # 0 isolated, 1 < 2, 1 < 3
    Tc = E.compof[1]

    def inR(x):
        r = E.r
        for cm, U in E.cl_by_cmask.items():
            if cm >> Tc & 1:
                continue
            mn = min(x[i] for i in range(4) if U >> i & 1)
            mx = max(x[i] for i in range(4) if not U >> i & 1)
            if mn > mx:
                return False
        return all(0 <= v <= 1 for v in x) and all(x[i] <= x[j] for (i, j) in E.relations)
    p1, p2 = (1, 0, 0, 1), (1, 0, 1, 0)
    mid = tuple(Fraction(a + b, 2) for a, b in zip(p1, p2))
    print('[E] nonconvex example:', inR(p1), inR(p2), 'midpoint in R_T:', inR(mid))
    assert inR(p1) and inR(p2) and not inR(mid)

    # interior description: points in the claimed open set stay in R_T under
    # small perturbations; points of R_T outside it have a nearby point outside R_T
    def claimed_int(P_, T_, x):
        if not all(0 < v < 1 for v in x):
            return False
        if not all(x[i] < x[j] for (i, j) in P_.relations):
            return False
        for cm, U in P_.cl_by_cmask.items():
            if cm >> T_ & 1:
                continue
            mn = min(x[i] for i in range(P_.n) if U >> i & 1)
            mx = max(x[i] for i in range(P_.n) if not U >> i & 1)
            if not mn < mx:
                return False
        return True

    def inR_(P_, T_, x):
        if not all(0 <= v <= 1 for v in x):
            return False
        if not all(x[i] <= x[j] for (i, j) in P_.relations):
            return False
        for cm, U in P_.cl_by_cmask.items():
            if cm >> T_ & 1:
                continue
            mn = min(x[i] for i in range(P_.n) if U >> i & 1)
            mx = max(x[i] for i in range(P_.n) if not U >> i & 1)
            if mn > mx:
                return False
        return True
    Ebad = 0
    Etests = 0
    for downs in levels[min(5, args.nmax)]:
        P_ = Poset(downs)
        if P_.r == 1:
            continue
        for T_ in range(P_.r):
            for _ in range(60):
                # grid points with denominator 4 (hit boundaries often)
                x = [Fraction(random.randint(0, 4), 4) for _ in range(P_.n)]
                if not inR_(P_, T_, x):
                    continue
                Etests += 1
                ci = claimed_int(P_, T_, x)
                eps = Fraction(1, 1000)
                # interior test: all 3^n perturbations by +-eps stay in R_T
                interior = all(inR_(P_, T_, [x[i] + eps * d[i] for i in range(P_.n)])
                               for d in itertools.product((-1, 0, 1), repeat=P_.n))
                if ci != interior:
                    Ebad += 1
    print(f'[E] interior description: {Etests} sampled points of R_T (n=5, grid 1/4), '
          f'claimed-interior vs eps-box test disagree on {Ebad}')

    print(f"posets {C['posets']}, (P,T) pairs {C['pairs']}, disconnected {C['disc']}")
    print(f"[omega]  Theorem Omega literal vs Moebius: bad {C['omega_bad']} / {C['pairs']}")
    print(f"[R-surj] Theorem R (surjective literal):   bad {C['Rsurj_bad']} / {C['pairs']}")
    print(f"[R-all]  Theorem R (all maps, m<=n+1, n<={args.nall}): bad {C['Rall_bad']} / {C['Rall_pairs']}")
    print(f"[Tdep]   OmegaBar literal depends on T: {C['Tdep']} posets")
    print(f"[R1]     bad {C['R1_bad']} / {C['R1']} (surjective weak map, T) cases")
    print(f"[R2]     bad {C['R2_bad']} / {C['R2']} (surjective strict map, T) cases")
    print(f"[B+]     bad {C['Bplus_bad']} / {C['pairs']}")
    print(f"[R']     bad {C['Rp_bad']} / {C['Rp']}")
    print(f"[dual]   bad {C['dual_bad']} / {C['posets']}")
    print(f"[S]      height<=2 posets {C['S']}, bad {C['S_bad']}; "
          f"bijection: {C['Sbij']} maps checked, bad {C['Sbij_bad']}")
    print(f"[S']     classification mismatches {C['Sp_bad']} (n>=2)")
    print(f"[U]      non-unimodal h_C: {C['unimodal_bad']}")
    print(f"[lower-D] strict maps, lower level sets with <= (dual form of R via star): "
          f"bad {C['lowerw']} / {C['pairs']}")
    print('CONTROLS (each must be > 0):')
    for key, lab in [('naive', 'strict + > anchoring'), ('lower', 'strict, lower level sets, <'),
('mixed', 'weak maps + D_T'),
                     ('plain', 'Stanley OmegaBar, no anchoring (per poset)'),
                     ('reverse', 'h(P*) = reverse h(P), trimmed (per poset)'),
                     ('reverse_full', 'h(P*) = reverse h(P), length n+1 (per poset)'),
                     ('pal_graded', 'pal iff all components graded (per poset, n>=2)'),
                     ('lam0', 'R2 under lambda_0 with isolated T ((map,T) cases)'),
                     ('signbug', 'planted bug: drop (-1)^n (odd-n posets)')]:
        print(f'  [ctl-{key}] {lab}: fails on {C[key]}')
    print(f"  [ctl-shift-any] shift identity with a 3-chain: fails on {C['shift_any']} / {C['shift_any_tot']}")
    print(f"  [ctl-any-lab] R2 under arbitrary natural labelling, n<={args.lmax}: "
          f"fails on {C['any_lab']} / {C['any_lab_tot']} (labelling, T)")
    ok = (C['omega_bad'] == C['Rsurj_bad'] == C['Rall_bad'] == C['R1_bad'] == C['R2_bad']
          == C['Bplus_bad'] == C['Rp_bad'] == C['dual_bad'] == C['S_bad'] == C['Sbij_bad']
          == C['Sp_bad'] == C['Tdep'] == C['lowerw'] == Ebad == 0)
    ctl = all(C[k] > 0 for k in ['naive', 'lower', 'mixed', 'plain', 'reverse',
                                 'pal_graded', 'lam0', 'signbug', 'shift_any', 'any_lab'])
    print('ALL CLAIMS HOLD:', ok, '| ALL CONTROLS FIRE:', ctl)
    sys.exit(0 if ok and ctl else 1)


def W(P):
    """W_P(t) = sum_{w in Lin P} t^{des w}, natural labelling = a linear extension."""
    L0 = P.linext()
    lam = [0] * P.n
    for i, x in enumerate(L0[0]):
        lam[x] = i
    out = [0] * max(P.n, 1)
    for w in L0:
        out[des(w, lam)] += 1
    return out


def subposet(P, mask):
    idx = [i for i in range(P.n) if mask >> i & 1]
    pos = {x: k for k, x in enumerate(idx)}
    return Poset([sum(1 << pos[i] for i in idx if P.down[x] >> i & 1) for x in idx])


def two_comp(levels, nmax):
    tot = bad = ctl = 0
    for n in range(2, nmax + 1):
        for downs in levels[n]:
            P = Poset(downs)
            if P.r != 2:
                continue
            tot += 1
            a, _ = omega_c_coeffs(P)
            h = [int(x) for x in h_from_values([ev(a, m) for m in range(n + 2)], n)]
            WP = W(P) + [0, 0]
            WQ = W(subposet(P, P.comps[0]))
            WT = W(subposet(P, P.comps[1]))
            prod = [0] * (n + 2)
            for i, x in enumerate(WQ):
                for j, y in enumerate(WT):
                    prod[i + j + 1] += x * y          # t * W_Q * W_T
            rhs = [WP[k] - prod[k] for k in range(n + 1)]
            if rhs != h:
                bad += 1
            # control: drop the factor t
            prod0 = [0] * (n + 2)
            for i, x in enumerate(WQ):
                for j, y in enumerate(WT):
                    prod0[i + j] += x * y
            if [WP[k] - prod0[k] for k in range(n + 1)] != h:
                ctl += 1
    print(f'[two-comp] h_C(Q+T) = W_P - t W_Q W_T: bad {bad} / {tot} two-component posets, n <= {nmax}')
    print(f'[ctl-two-comp] same without the factor t: fails on {ctl} / {tot}')
    return 0 if bad == 0 and ctl > 0 else 1


def Poset_sub_graded(P, mask):
    idx = [i for i in range(P.n) if mask >> i & 1]
    pos = {x: k for k, x in enumerate(idx)}
    downs = [sum(1 << pos[i] for i in idx if P.down[x] >> i & 1) for x in idx]
    return Poset(downs).graded()


if __name__ == '__main__':
    main()
