#!/usr/bin/env python3
"""Independent audit of notes/fixed_point_formula.md
(notes/audit_fixed_point_formula.md).

Plain Python 3, exact rational arithmetic, no dependencies.  Imports nothing
from this repository; in particular not fixed_point_formula.py.  Faces are
built by a method none of the earlier scripts uses: the cocircuits (sign
vectors of the rays) are found by linear algebra, and the covectors are the
closure of {0} and the cocircuits under oriented-matroid composition
X o Y.  This works for any real arrangement, reflection or not, and any
finite-order linear symmetry, orthogonal or not.

For (A, V, g) with V a top-cone and g a finite-order symmetry with gV = V,
L = lin V, LL^g = g-stable flats inside L, the checks are:

  [2.1]   f_g(Y) := sum_{faces F of V in Y, gF = F} (-1)^dim F det(g|span F)
          equals [Y in L] (-1)^dim Y det(g|Y), for every Y in Lambda(V)^g.
          (Step 1 of the EZ proof; determinants computed directly.)
  [par]   det(g|X) = (-1)^(dim X - dim X^g) for every g-stable flat X.
  [EZ]    #V^g = sum_{X in LL^g} chi_{V_X}(gbar),
          chi_{V_X}(gbar) = (-1)^codim X det(gbar) mu_{Lambda(V)^g}(X, R^d),
          det(gbar) = det(g) / det(g|X), both computed directly.
  [CF]    chi_V(g) = sum_{Y in LL^g} mu_{LL^g}(0, Y) c(Y, g), with c(Y, g)
          counted directly as distinct g-fixed restrictions to A_Y of the
          chambers of V.
  [F]     c(Y, g) = 0 if a hyperplane through Y contains Fix(g), else the
          number of chambers of A_Y restricted to Fix(g) inside |V|; the
          restricted arrangement is built in coordinates on Fix(g) and its
          chambers are enumerated by the same covector closure.
  [P]     L = 0  =>  chi_V(g) = #V^g.
  [V]     a hyperplane contains L and Fix(g)  =>  chi_V(g) = 0.
  [B]     Lemma B(a): X in Lambda(V)^g, a = cl(Fix g)  =>  X cap a in Lambda(V).
  [W]     g != 1, Fix(g) a flat  =>  sum_{X in LL^g, X cap Fix g = 0}
          mu_{Lambda(V)^g}(X, R^d) = 0.  Reported, not asserted, when
          Fix(g) is not a flat.
  [Wcl]   g != 1, cl(Fix g) != R^d  =>  the same sum over X cap cl(Fix g) = 0
          vanishes (the variant the note proves but did not compute).
  [Wweak] g != 1, cl(Fix g) != R^d (Fix(g) lies in a hyperplane)  =>  the
          [W] sum, over X cap Fix(g) = 0, vanishes (proved in the audit).
          Reported: whether the [W] sum is nonzero whenever cl(Fix g) = R^d.
  [braid] for posets P on n <= 5 points and g in Aut(P): mu(OP(P)^g) from
          order-preserving partitions, mu(Lambda(C_P)^g) from the braid
          arrangement, the right side of CF-braid, and the right side of
          [Thm, eq. closed]; all four must agree with the note's signs.

Negative controls (must FAIL somewhere, else the instrument is reported
broken): [2.1] with the orientation sign det(g|span F) replaced by 1; [EZ]
without det(gbar); [CF] with all chambers of A_Y in |V| instead of fixed
ones; [W] on symmetries whose fixed space is not a flat.

Run (from compute/):  python3 audit_fixed_point_formula.py          (full)
                      python3 audit_fixed_point_formula.py --quick  (small)
Exit status 0 iff every asserted check passes and every control fires.
"""

import argparse
import itertools
import random
import sys
from collections import defaultdict
from fractions import Fraction

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
    return cond


# ---------------------------------------------------------------- algebra


def F(x):
    return Fraction(x)


def rref(rows, ncols):
    """Row-reduced echelon form; returns (rows, pivot columns)."""
    M = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return M[:r], piv


def rank(rows, ncols):
    return len(rref(rows, ncols)[1]) if rows else 0


def nullspace(rows, ncols):
    """Basis of {x : r.x = 0 for r in rows}."""
    if not rows:
        return [[F(int(i == j)) for i in range(ncols)] for j in range(ncols)]
    R, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [F(0)] * ncols
        v[f] = F(1)
        for i, c in enumerate(piv):
            v[c] = -R[i][f]
        basis.append(v)
    return basis


def det(M):
    n = len(M)
    if n == 0:
        return F(1)
    A = [list(r) for r in M]
    d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            if A[i][c] != 0:
                f = A[i][c] / A[c][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return d


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def matvec(A, v):
    return [sum(a * b for a, b in zip(row, v)) for row in A]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def det_on_subspace(M, basis):
    """det of x -> Mx restricted to the M-stable subspace with this basis."""
    k = len(basis)
    if k == 0:
        return F(1)
    n = len(basis[0])
    # coordinates of M b_j in the basis: solve [b_1 .. b_k] c = M b_j
    cols = []
    T = [[basis[j][i] for j in range(k)] for i in range(n)]
    for b in basis:
        y = matvec(M, b)
        aug = [T[i] + [y[i]] for i in range(n)]
        R, piv = rref(aug, k + 1)
        assert k not in piv, "subspace not M-stable"
        c = [F(0)] * k
        for i, p in enumerate(piv):
            c[p] = R[i][k]
        cols.append(c)
    return det([[cols[j][i] for j in range(k)] for i in range(k)])


def sgn(x):
    return (x > 0) - (x < 0)


def popcount(m):
    return bin(m).count("1")


def bits(m):
    out = []
    while m:
        low = m & -m
        out.append(low.bit_length() - 1)
        m ^= low
    return out


# ---------------------------------------------------------------- covectors


def compose(X, Y):
    p, n = X
    z = ~(p | n)
    return (p | (Y[0] & z), n | (Y[1] & z))


def sign_vector(forms, x):
    p = n = 0
    for i, a in enumerate(forms):
        s = sgn(dot(a, x))
        if s > 0:
            p |= 1 << i
        elif s < 0:
            n |= 1 << i
    return (p, n)


def covectors(forms, dim):
    """All covectors (p, n) of the arrangement of these linear forms on R^dim
    (forms need not span; none may be zero).  Cocircuits: for each
    independent set T of r-1 forms (r = rank), any vector of ker T outside the
    common kernel; covectors: closure of {0} and cocircuits under o."""
    m = len(forms)
    r = rank(forms, dim)
    if r == 0:
        return {(0, 0)}
    common = rank(forms, dim)
    coc = set()
    for T in itertools.combinations(range(m), r - 1):
        rows = [forms[i] for i in T]
        if rank(rows, dim) != r - 1:
            continue
        for v in nullspace(rows, dim):
            sv = sign_vector(forms, v)
            if sv != (0, 0):
                coc.add(sv)
                coc.add((sv[1], sv[0]))
                break
    assert common == r
    cov = {(0, 0)} | coc
    frontier = list(coc)
    cl = list(coc)
    while frontier:
        nxt = []
        for X in frontier:
            for C in cl:
                Z = compose(X, C)
                if Z not in cov:
                    cov.add(Z)
                    nxt.append(Z)
        frontier = nxt
    return cov


# ---------------------------------------------------------------- arrangements


class Arr:
    def __init__(self, name, forms, gens, wgens=None):
        self.name = name
        self.forms = [[F(x) for x in a] for a in forms]
        self.d = d = len(forms[0])
        self.N = N = len(forms)
        self.full = (1 << N) - 1
        assert rank(self.forms, d) == d, "not essential"
        self.cov = covectors(self.forms, d)
        self.topes = sorted(c for c in self.cov if (c[0] | c[1]) == self.full)
        self.tidx = {t: i for i, t in enumerate(self.topes)}
        self.flats = sorted({self.full ^ (p | n) for p, n in self.cov})
        self.rk = {Z: rank([self.forms[i] for i in bits(Z)], d) for Z in self.flats}
        self.dim = {Z: d - self.rk[Z] for Z in self.flats}
        self.basis = {Z: nullspace([self.forms[i] for i in bits(Z)], d) for Z in self.flats}
        self.G = self._close(gens)
        if wgens is None:
            self.Wkeys = None
        else:
            W = self._close(wgens)
            self.Wkeys = {e["key"] for e in W}
        for e in self.G:
            e["inW"] = self.Wkeys is not None and e["key"] in self.Wkeys
        self._cache = {}

    # -- group elements
    def _action(self, M):
        """For each hyperplane e: a_e o M = lam * a_pi(e).  Then the sign of
        Mx on e is sign(lam) times the sign of x on pi(e)."""
        pi, sg = [], []
        for a in self.forms:
            b = [sum(a[i] * M[i][j] for i in range(self.d)) for j in range(self.d)]
            hit = None
            for k, c in enumerate(self.forms):
                # b proportional to c ?
                j0 = next(j for j in range(self.d) if c[j] != 0)
                lam = b[j0] / c[j0]
                if lam != 0 and all(b[j] == lam * c[j] for j in range(self.d)):
                    hit = (k, sgn(lam))
                    break
            assert hit is not None, "matrix does not preserve the arrangement"
            pi.append(hit[0])
            sg.append(hit[1])
        return tuple(pi), tuple(sg)

    def _mk(self, M):
        pi, sg = self._action(M)
        dM = det(M)
        assert dM in (1, -1), dM
        I = [[F(int(i == j)) for j in range(self.d)] for i in range(self.d)]
        return {"M": M, "pi": pi, "sg": sg, "det": int(dM),
                "key": tuple(tuple(r) for r in M), "id": M == I}

    def _close(self, gens):
        d = self.d
        I = [[F(int(i == j)) for j in range(d)] for i in range(d)]
        gens = [[[F(x) for x in r] for r in g] for g in gens]
        seen = {}
        start = self._mk(I)
        seen[start["key"]] = start
        frontier = [start]
        while frontier:
            nxt = []
            for e in frontier:
                for g in gens:
                    M = matmul(g, e["M"])
                    k = tuple(tuple(r) for r in M)
                    if k not in seen:
                        seen[k] = self._mk(M)
                        nxt.append(seen[k])
            frontier = nxt
            assert len(seen) < 100000
        return list(seen.values())

    def act(self, e, X):
        p, n = X
        pi, sg = e["pi"], e["sg"]
        P = Nn = 0
        for i in range(self.N):
            j = pi[i]
            s = 1 if (p >> j) & 1 else (-1 if (n >> j) & 1 else 0)
            s *= sg[i]
            if s > 0:
                P |= 1 << i
            elif s < 0:
                Nn |= 1 << i
        return (P, Nn)

    def act_zero(self, e, Z):
        pi = e["pi"]
        out = 0
        for i in range(self.N):
            if (Z >> pi[i]) & 1:
                out |= 1 << i
        return out

    def act_restr(self, e, X, Z):
        """g acting on a chamber of A_Y (sign vector X supported on Z(Y))."""
        P, Nn = self.act(e, X)
        return (P & Z, Nn & Z)

    # -- linear algebra of g
    def fix_basis(self, e):
        k = ("fix", e["key"])
        if k not in self._cache:
            M = e["M"]
            rows = [[M[i][j] - (1 if i == j else 0) for j in range(self.d)]
                    for i in range(self.d)]
            self._cache[k] = nullspace(rows, self.d)
        return self._cache[k]

    def cl_fix(self, e):
        """Zero set of the smallest flat containing Fix(g)."""
        k = ("cl", e["key"])
        if k not in self._cache:
            B = self.fix_basis(e)
            Z = 0
            for i, a in enumerate(self.forms):
                if all(dot(a, b) == 0 for b in B):
                    Z |= 1 << i
            self._cache[k] = Z
        return self._cache[k]

    def dim_meet(self, Z1, Z2):
        Z = Z1 | Z2
        return self.d - rank([self.forms[i] for i in bits(Z)], self.d)

    def dim_cap_fix(self, e, Z):
        k = ("cf", e["key"], Z)
        if k not in self._cache:
            rows = [self.forms[i] for i in bits(Z)]
            M = e["M"]
            rows += [[M[i][j] - (1 if i == j else 0) for j in range(self.d)]
                     for i in range(self.d)]
            self._cache[k] = self.d - rank(rows, self.d)
        return self._cache[k]

    def det_on(self, e, Z):
        k = ("det", e["key"], Z)
        if k not in self._cache:
            self._cache[k] = int(det_on_subspace(e["M"], self.basis[Z]))
        return self._cache[k]


# ---------------------------------------------------------------- cones


def smax_of(arr, topeset):
    """Sign pattern (S_max signs) of the top-cone with these topes."""
    p, n = arr.full, arr.full
    for t in topeset:
        p &= t[0]
        n &= t[1]
    return (p, n)


def topes_of(arr, s):
    return [t for t in arr.topes if not (t[0] & s[1]) and not (t[1] & s[0])]


def all_cones(arr):
    """All top-cones, as their S_max sign patterns: closure of the full set
    under intersection with half-spaces."""
    full = frozenset(range(len(arr.topes)))
    half = []
    for i in range(arr.N):
        plus = frozenset(k for k, t in enumerate(arr.topes) if (t[0] >> i) & 1)
        half.append(plus)
        half.append(full - plus)
    seen = {full}
    stack = [full]
    while stack:
        V = stack.pop()
        for h in half:
            U = V & h
            if U and U not in seen:
                seen.add(U)
                stack.append(U)
    return [smax_of(arr, [arr.topes[k] for k in V]) for V in seen]


def canon(arr, s, group):
    return min(arr.act(e, s) for e in group)


def sample_cones(arr, count, seed, maxk=3):
    """Random top-cones with a nontrivial stabilizer: pick g != 1, a tope T
    and a few hyperplanes; impose T's signs on their <g>-orbits."""
    rng = random.Random(seed)
    nonid = [e for e in arr.G if not e["id"]]
    out = {}
    tries = 0
    while len(out) < count and tries < 200 * count:
        tries += 1
        g = rng.choice(nonid)
        T = rng.choice(arr.topes)
        S = rng.sample(range(arr.N), rng.randint(1, maxk))
        cond = (sum(1 << i for i in S if (T[0] >> i) & 1),
                sum(1 << i for i in S if (T[1] >> i) & 1))
        # orbit of the condition under <g>
        cur, total, ok = cond, (0, 0), True
        for _ in range(64):
            total = (total[0] | cur[0], total[1] | cur[1])
            if total[0] & total[1]:
                ok = False
                break
            cur = arr.act(g, cur)
            if cur == cond:
                break
        if not ok:
            continue
        V = topes_of(arr, total)
        if not V:
            continue
        s = smax_of(arr, V)
        out[s] = True
    return list(out)


# ---------------------------------------------------------------- Mobius


def mu_to_top(elems):
    """mu(X, R^d) in a poset of flats given by zero sets (X <= Y iff
    Z(X) contains Z(Y)); the top R^d has zero set 0."""
    order = sorted(elems, key=popcount)
    assert order[0] == 0
    mu = {}
    for X in order:
        if X == 0:
            mu[X] = 1
            continue
        mu[X] = -sum(mu[Y] for Y in mu if Y != X and (Y & ~X) == 0)
    return mu


def mu_from_bottom(elems, bottom):
    order = sorted(elems, key=popcount, reverse=True)
    assert order[0] == bottom
    mu = {}
    for Y in order:
        if Y == bottom:
            mu[Y] = 1
            continue
        mu[Y] = -sum(mu[X] for X in mu if X != Y and (Y & ~X) == 0)
    return mu


# ---------------------------------------------------------------- Lemma F


def restricted_chambers(arr, e, Z, s):
    """Number of chambers of A_Y restricted to Fix(g) lying in |V|, computed in
    coordinates on Fix(g); None if a hyperplane through Y contains Fix(g)."""
    B = arr.fix_basis(e)
    k = len(B)
    forms = []
    for i in bits(Z):
        f = [dot(arr.forms[i], b) for b in B]
        if all(x == 0 for x in f):
            return None
        forms.append(f)
    if not forms:
        return 1
    key = ("rc", e["key"], Z)
    if key not in arr._cache:
        arr._cache[key] = covectors(forms, k)
    cov = arr._cache[key]
    idx = bits(Z)
    full = (1 << len(idx)) - 1
    sp = sum(1 << j for j, i in enumerate(idx) if (s[0] >> i) & 1)
    sn = sum(1 << j for j, i in enumerate(idx) if (s[1] >> i) & 1)
    return sum(1 for p, n in cov if (p | n) == full and not (p & sn) and not (n & sp))


# ---------------------------------------------------------------- one (V, g)


class Stats:
    def __init__(self):
        self.c = defaultdict(lambda: [0, 0])  # name -> [fail, pass]
        self.cnt = defaultdict(int)

    def rec(self, name, ok):
        self.c[name][bool(ok)] += 1


def analyse(arr, s, V, faces_V, lam, e, st, lemma_f=True):
    d = arr.d
    detg = e["det"]
    lamg = [Z for Z in lam if arr.act_zero(e, Z) == Z]
    mut = mu_to_top(lamg)
    chi = (-1) ** d * detg * mut[arr.full]
    ZL = s[0] | s[1]                       # S_max; Y in L iff Z(Y) contains S_max
    LL = [Z for Z in lamg if (Z & ZL) == ZL]
    inL = set(LL)
    ZLc = min(LL, key=popcount)            # zero set of L itself (closure of S_max)
    nfix = sum(1 for t in V if arr.act(e, t) == t)

    # [2.1] Step 1 of EZ, and its orientation-free negative control
    fixed_faces = [X for X in faces_V if arr.act(e, X) == X]
    for Y in lamg:
        f = f1 = 0
        for X in fixed_faces:
            Zx = arr.full ^ (X[0] | X[1])
            if (Zx & Y) == Y:              # span F inside Y
                f += (-1) ** arr.dim[Zx] * arr.det_on(e, Zx)
                f1 += (-1) ** arr.dim[Zx]
        want = (Y in inL) * (-1) ** arr.dim[Y] * arr.det_on(e, Y)
        st.rec("2.1", check(f == want, f"[2.1] {arr.name} Y={Y}"))
        st.rec("neg:2.1-no-orientation", f1 == want)
        # [par]
        st.rec("par", check(arr.det_on(e, Y) ==
                            (-1) ** (arr.dim[Y] - arr.dim_cap_fix(e, Y)), "[par]"))

    # [EZ]
    ez = ez_nodet = 0
    for X in LL:
        detbar = detg * arr.det_on(e, X)   # det(g)/det(g|X), both +-1
        ez += (-1) ** (d - arr.dim[X]) * detbar * mut[X]
        ez_nodet += (-1) ** (d - arr.dim[X]) * mut[X]
    st.rec("EZ", check(ez == nfix, f"[EZ] {arr.name} s={s}"))
    st.rec("neg:EZ-no-detbar", ez_nodet == nfix)

    # [CF] and [F]
    mub = mu_from_bottom(LL, arr.full)
    cf = cf_all = 0
    for Y in LL:
        ks = {(t[0] & Y, t[1] & Y) for t in V}
        c = sum(1 for K in ks if arr.act_restr(e, K, Y) == K)
        cf += mub[Y] * c
        cf_all += mub[Y] * len(ks)
        if lemma_f and not e["id"]:
            r = restricted_chambers(arr, e, Y, s)
            st.rec("F", check((r or 0) == c, f"[F] {arr.name}"))
    st.rec("CF", check(cf == chi, f"[CF] {arr.name} s={s}"))
    st.rec("neg:CF-all-chambers", cf_all == chi)

    # [P]
    if ZLc == arr.full:
        st.rec("P", check(chi == nfix, "[P]"))

    if not e["id"]:
        clf = arr.cl_fix(e)
        dimfix = len(arr.fix_basis(e))
        flat = arr.dim[clf] == dimfix
        # [V]
        crit = (ZLc & clf) != 0
        if crit:
            st.rec("V", check(chi == 0, "[V]"))
        grp = "W" if e["inW"] else "G\\W"
        st.cnt[(grp, "nz" if chi else ("z-V" if crit else "z-other"))] += 1
        # [B]  Lemma B(a) with a = cl(Fix g)
        for X in lamg:
            m = (X | clf)
            # closure of X|clf as a flat: all forms vanishing on the meet
            meet_dim = arr.dim_meet(X, clf)
            hits = [Z for Z in lam if (Z & m) == m and arr.dim[Z] == meet_dim]
            st.rec("B", check(len(hits) == 1, "[B]"))
        # [W]
        sW = sum(mut[X] for X in LL if arr.dim_cap_fix(e, X) == 0)
        if flat:
            st.rec("W", check(sW == 0, f"[W] {arr.name}"))
        else:
            st.rec("W-nonflat", sW == 0)
            st.cnt[(grp, "W-nonflat-tested")] += 1
            st.cnt[(grp, "W-nonflat-fails")] += sW != 0
            # cross-tab: does the Fix(g) form hold exactly when cl(Fix g) != R^d?
            st.cnt[("xtab", (clf != 0, sW == 0))] += 1
            if clf != 0:
                diff = [X for X in LL if arr.dim_cap_fix(e, X) == 0
                        and arr.dim_meet(X, clf) != 0]
                st.cnt[("xdiff", bool(diff))] += 1
        # [Wweak] the Fix(g) form under the weaker hypothesis cl(Fix g) != R^d,
        # i.e. Fix(g) lies in some hyperplane of A (proof in the audit, C.3)
        if clf != 0:
            st.rec("Wweak", check(sW == 0, f"[Wweak] {arr.name}"))
        # [Wcl]
        if clf != 0:
            sWc = sum(mut[X] for X in LL if arr.dim_meet(X, clf) == 0)
            st.rec("Wcl", check(sWc == 0, f"[Wcl] {arr.name}"))
        else:
            st.cnt["Wcl-not-applicable"] += 1
    return chi, nfix


def cone_faces(arr, s):
    faces = [X for X in arr.cov if not (X[0] & s[1]) and not (X[1] & s[0])]
    lam = sorted({arr.full ^ (X[0] | X[1]) for X in faces})
    return faces, lam


def run_arr(arr, cones, log, label, lemma_f=True, reps_by=None):
    """cones: list of S_max patterns.  If reps_by is a group, reduce the
    cones to orbit representatives under it first."""
    st = Stats()
    if reps_by is not None:
        seen, reps = set(), []
        for s in cones:
            c = canon(arr, s, reps_by)
            if c not in seen:
                seen.add(c)
                reps.append(s)
        cones = reps
    pairs = defaultdict(int)
    for s in cones:
        V = topes_of(arr, s)
        faces, lam = cone_faces(arr, s)
        stab = [e for e in arr.G if arr.act(e, s) == s]
        for e in stab:
            analyse(arr, s, V, faces, lam, e, st, lemma_f=lemma_f)
            pairs["W" if e["inW"] else "G\\W"] += 1
    log(f"== {label}: d={arr.d}, hyperplanes={arr.N}, covectors={len(arr.cov)}, "
        f"chambers={len(arr.topes)}, flats={len(arr.flats)}, |G|={len(arr.G)}, "
        f"cones={len(cones)}, pairs (V,g): {dict(pairs)}")
    for grp in ("W", "G\\W"):
        c = {k[1]: v for k, v in st.cnt.items() if isinstance(k, tuple) and k[0] == grp}
        if c:
            log(f"   g != 1 in {grp}: chi != 0 on {c.get('nz', 0)}, zero by Cor. V on "
                f"{c.get('z-V', 0)}, zero otherwise on {c.get('z-other', 0)}; "
                f"Fix(g) not a flat on {c.get('W-nonflat-tested', 0)}, "
                f"Prop. W sum != 0 on {c.get('W-nonflat-fails', 0)} of them")
    xt = {k[1]: v for k, v in st.cnt.items() if isinstance(k, tuple) and k[0] == "xtab"}
    xd = {k[1]: v for k, v in st.cnt.items() if isinstance(k, tuple) and k[0] == "xdiff"}
    if xd:
        log(f"   Fix(g) not a flat, cl(Fix g) != R^d: index sets {{X^g = 0}} and "
            f"{{X cap cl(Fix g) = 0}} differ on {xd.get(True, 0)} of {sum(xd.values())} pairs")
    if xt:
        log("   Fix(g) not a flat, (cl(Fix g) != R^d, Prop. W sum = 0) -> pairs: "
            + ", ".join(f"{k}: {v}" for k, v in sorted(xt.items())))
    for k in sorted(st.c):
        bad, good = st.c[k]
        tag = "control" if k.startswith("neg:") or k == "W-nonflat" else "assert"
        log(f"   [{k}] holds on {good}/{good + bad}   ({tag})")
    return st


# ---------------------------------------------------------------- examples


def forms_B(n):
    out = [[int(i == k) for i in range(n)] for k in range(n)]
    for i, j in itertools.combinations(range(n), 2):
        for sj in (1, -1):
            v = [0] * n
            v[i], v[j] = 1, sj
            out.append(v)
    return out


def forms_D(n):
    return forms_B(n)[n:]


def forms_F4():
    out = forms_B(4)
    for s in itertools.product((1, -1), repeat=3):
        out.append([1, *s])
    return out


def refl(a):
    n = len(a)
    aa = sum(F(x) * x for x in a)
    return [[F(int(i == j)) - 2 * F(a[i]) * a[j] / aa for j in range(n)] for i in range(n)]


def signed_perm_gens(n):
    gens = [refl([int(k == 0) for k in range(n)])]
    for i in range(n - 1):
        v = [0] * n
        v[i], v[i + 1] = 1, -1
        gens.append(refl(v))
    return gens


def D_gens(n):
    gens = []
    for i in range(n - 1):
        v = [0] * n
        v[i], v[i + 1] = 1, -1
        gens.append(refl(v))
    v = [0] * n
    v[n - 2], v[n - 1] = 1, 1
    gens.append(refl(v))
    return gens


def F4_gens():
    return [refl([0, 1, -1, 0]), refl([0, 0, 1, -1]), refl([0, 0, 0, 1]),
            refl([1, -1, -1, -1])]


def braid_forms(n):
    """A_{n-1} in coordinates y_i = x_i - x_n (i < n): forms x_i - x_j."""
    out, pairs = [], []
    for i, j in itertools.combinations(range(n), 2):
        v = [0] * (n - 1)
        v[i] = 1
        if j < n - 1:
            v[j] = -1
        out.append(v)
        pairs.append((i, j))
    return out, pairs


def perm_matrix_y(n, p):
    """Matrix of x -> (x_{p^{-1}(i)})_i on R^n / R(1..1), in y-coordinates."""
    # x = (y_1..y_{n-1}, 0); permuted x' with x'_{p(i)} = x_i; y'_i = x'_i - x'_n
    M = [[F(0)] * (n - 1) for _ in range(n - 1)]
    pinv = [0] * n
    for i in range(n):
        pinv[p[i]] = i
    for i in range(n - 1):
        a = pinv[i]
        b = pinv[n - 1]
        if a < n - 1:
            M[i][a] += 1
        if b < n - 1:
            M[i][b] -= 1
    return M


def braid_arr(n, with_minus=True):
    forms, _ = braid_forms(n)
    gens = []
    for i in range(n - 1):
        p = list(range(n))
        p[i], p[i + 1] = p[i + 1], p[i]
        gens.append(perm_matrix_y(n, p))
    W = list(gens)
    if with_minus:
        gens = gens + [[[F(-int(i == j)) for j in range(n - 1)] for i in range(n - 1)]]
    return Arr(f"A{n - 1}", forms, gens, W)


def hex6():
    """Non-reflection arrangement in R^3 with the non-orthogonal rational
    symmetry h of order 6 acting on (x, y); hyperplanes: the <h>-orbit of the
    form x + z, the orbit of y + 2z, and z = 0.  G = <h, -1>."""
    h = [[0, -1, 0], [1, 1, 0], [0, 0, 1]]
    forms = []

    def orbit(a):
        a = [F(x) for x in a]
        out = []
        cur = a
        for _ in range(6):
            if not any(all(cur[j] * c[k] == cur[k] * c[j] for j in range(3) for k in range(3))
                       for c in out):
                out.append(cur)
            cur = [sum(cur[i] * h[i][j] for i in range(3)) for j in range(3)]
        return out

    forms = orbit([1, 0, 1]) + orbit([0, 1, 2]) + [[F(0), F(0), F(1)]]
    minus = [[-int(i == j) for j in range(3)] for i in range(3)]
    return Arr("hex6", forms, [h, minus], wgens=[])


def tetra7():
    """x_i = 0 and the four planes normal to (1, +-1, +-1): not a reflection
    arrangement; G = signed permutations (order 48), which contains the
    reflections in x_i = x_j, none of whose mirrors is in A."""
    forms = [[1, 0, 0], [0, 1, 0], [0, 0, 1],
             [1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1]]
    return Arr("tetra7", forms, signed_perm_gens(3), wgens=[])


# ---------------------------------------------------------------- braid case


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def all_posets(n):
    """All posets on range(n) as frozensets of strict pairs (a, b), a < b in P."""
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    out = set()
    # build by transitive closure of acyclic relations; enumerate up to n=5
    # via natural labellings: every poset is a relabelling of one whose order
    # extends 0 < 1 < ... < n-1.
    nat = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for m in range(1 << len(nat)):
        R = {nat[k] for k in range(len(nat)) if (m >> k) & 1}
        ok = all(((a, c) in R) for (a, b) in R for (b2, c) in R if b == b2)
        if ok:
            out.add(frozenset(R))
    reps = {}
    for R in out:
        key = min(tuple(sorted((p[a], p[b]) for a, b in R))
                  for p in itertools.permutations(range(n)))
        reps.setdefault(key, R)
    del pairs
    return [frozenset(k) for k in reps]


def auts(n, R):
    return [p for p in itertools.permutations(range(n))
            if frozenset((p[a], p[b]) for a, b in R) == R]


def lin_exts(n, R, elems):
    out = []
    for w in itertools.permutations(elems):
        pos = {x: i for i, x in enumerate(w)}
        if all(pos[a] < pos[b] for a, b in R if a in pos and b in pos):
            out.append(w)
    return out


def components(n, R):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    for a, b in R:
        parent[find(a)] = find(b)
    comp = defaultdict(list)
    for x in range(n):
        comp[find(x)].append(x)
    return [tuple(sorted(c)) for c in comp.values()]


def is_op(n, R, part):
    """Quotient digraph acyclic?"""
    blk = {x: i for i, B in enumerate(part) for x in B}
    k = len(part)
    edges = {(blk[a], blk[b]) for a, b in R if blk[a] != blk[b]}
    indeg = [0] * k
    for a, b in edges:
        indeg[b] += 1
    q = [i for i in range(k) if indeg[i] == 0]
    seen = 0
    while q:
        v = q.pop()
        seen += 1
        for a, b in edges:
            if a == v:
                indeg[b] -= 1
                if indeg[b] == 0:
                    q.append(b)
    return seen == k


def canon_part(part):
    return tuple(sorted(tuple(sorted(B)) for B in part))


def mu_lattice_partitions(parts, finer_first=True):
    """mu(0hat, 1hat) of a set of partitions ordered by refinement; 0hat =
    the finest, 1hat = the coarsest (must be present)."""
    parts = list(parts)

    def leq(p, q):  # p refines q
        blk = {x: i for i, B in enumerate(q) for x in B}
        return all(len({blk[x] for x in B}) == 1 for B in p)
    parts.sort(key=lambda p: -len(p))
    mu = []
    for i, p in enumerate(parts):
        if i == 0:
            mu.append(1)
        else:
            mu.append(-sum(mu[j] for j in range(i) if leq(parts[j], p)))
    return mu[-1]


def num_mobius(o):
    m, k, res = o, 2, 1
    while k * k <= m:
        if m % k == 0:
            m //= k
            if m % k == 0:
                return 0
            res = -res
        k += 1
    if m > 1:
        res = -res
    return res


def order_of(p):
    n = len(p)
    q, o = list(p), 1
    while q != list(range(n)):
        q = [p[x] for x in q]
        o += 1
    return o


def sign_of(p):
    s, seen = 1, set()
    for i in range(len(p)):
        if i in seen:
            continue
        j, L = i, 0
        while j not in seen:
            seen.add(j)
            j = p[j]
            L += 1
        s *= (-1) ** (L - 1)
    return s


def e_C(R, elems):
    """Number of rotation classes of words on elems meeting Lin(P|elems)."""
    elems = list(elems)
    Rr = {(a, b) for a, b in R if a in elems and b in elems}
    classes = set()
    for w in lin_exts(len(elems), Rr, elems):
        rots = [w[i:] + w[:i] for i in range(len(w))]
        classes.add(min(rots))
    return len(classes)


def braid_one(n, R, p, arr, Vmap):
    """Returns tuple (mu_OP, mu_Lambda, cf_rhs, closed_rhs) with signs as in
    the note: compare sgn(g)(-1)^{n-3} mu_OP with CF-braid and eq. closed."""
    pt = [canon_part(q) for q in set_partitions(range(n))]
    fixed_op = []
    for q in pt:
        if is_op(n, R, q) and canon_part([[p[x] for x in B] for B in q]) == q:
            fixed_op.append(q)
    mu_op = mu_lattice_partitions(fixed_op)
    # Lambda(C_P)^g via the arrangement
    s = Vmap[R]
    _, lam = cone_faces(arr, s)
    M = perm_matrix_y(n, p)
    e = arr._mk(M)
    lamg = [Z for Z in lam if arr.act_zero(e, Z) == Z]
    mu_lam = mu_to_top(lamg)[arr.full]
    # CF-braid
    K = components(n, R)
    kidx = {x: i for i, c in enumerate(K) for x in c}
    gK = [kidx[p[c[0]]] for c in K]
    cf = 0
    for sig in set_partitions(range(len(K))):
        sig = canon_part(sig)
        if canon_part([[gK[i] for i in B] for B in sig]) != sig:
            continue
        # mu_{Pi(K)^g}(sigma, 1hat): g-stable coarsenings of sigma
        coars = [canon_part(t) for t in set_partitions(range(len(K)))]
        coars = [t for t in coars
                 if canon_part([[gK[i] for i in B] for B in t]) == t
                 and all(any(set(B) <= set(C) for C in t) for B in sig)]
        m = mu_lattice_partitions(coars)
        prod = 1
        done = set()
        for B in sig:
            if B in done:
                continue
            orb, cur = [], B
            while cur not in orb:
                orb.append(cur)
                cur = canon_part([[gK[i] for i in cur]])[0]
            done |= set(orb)
            pts = [x for i in B for x in K[i]]
            k = len(orb)
            pk = list(range(n))
            for _ in range(k):
                pk = [p[x] for x in pk]
            if any(pk[x] != x for x in pts):
                prod = 0
                break
            prod *= len(lin_exts(n, R, pts))
        cf += m * prod
    # eq. closed: F(P, g) = partitions into exactly o blocks, unions of
    # components, permuted cyclically by g
    o = order_of(list(p))
    closed = 0
    if num_mobius(o):
        for sig in set_partitions(range(len(K))):
            if len(sig) != o:
                continue
            blocks = [frozenset(x for i in B for x in K[i]) for B in sig]
            img = {frozenset(p[x] for x in B) for B in blocks}
            if img != set(blocks):
                continue
            # cyclic: the orbit of one block is everything
            B0, orb, cur = blocks[0], set(), blocks[0]
            while cur not in orb:
                orb.add(cur)
                cur = frozenset(p[x] for x in cur)
            if len(orb) != o:
                continue
            closed += e_C(R, sorted(B0))
        closed *= num_mobius(o)
    return mu_op, mu_lam, cf, closed, sign_of(p)


def braid_check(nmax, log):
    st = Stats()
    for n in range(3, nmax + 1):
        arr = braid_arr(n, with_minus=False)
        _, pairs = braid_forms(n)
        Vmap = {}
        cnt = 0
        for R in all_posets(n):
            cond_p = cond_n = 0
            for k, (i, j) in enumerate(pairs):     # form x_i - x_j, i < j
                if (i, j) in R:                      # i <_P j: x_i < x_j
                    cond_n |= 1 << k
                elif (j, i) in R:
                    cond_p |= 1 << k
            V = topes_of(arr, (cond_p, cond_n))
            Vmap[R] = smax_of(arr, V)
            for p in auts(n, R):
                mu_op, mu_lam, cf, closed, sg = braid_one(n, R, p, arr, Vmap)
                lhs = sg * (-1) ** (n - 3) * mu_op
                st.rec("braid:Lambda=OP", check(mu_lam == mu_op, f"[braid] {n} {R} {p}"))
                st.rec("braid:CF-braid", check(lhs == cf, f"[CFb] {n} {R} {p}"))
                st.rec("braid:eq-closed", check(lhs == closed, f"[closed] {n} {R} {p}"))
                cnt += 1
        log(f"== braid n={n}: {cnt} (P, g) pairs, P up to relabelling")
    for k in sorted(st.c):
        bad, good = st.c[k]
        log(f"   [{k}] holds on {good}/{good + bad}")
    return st


# ---------------------------------------------------------------- driver


def controls(stats_list, log):
    """Negative controls must fail somewhere; positive controls must hold."""
    tot = defaultdict(lambda: [0, 0])
    for st in stats_list:
        for k, v in st.c.items():
            tot[k][0] += v[0]
            tot[k][1] += v[1]
    ok = True
    for k in ("neg:2.1-no-orientation", "neg:EZ-no-detbar", "neg:CF-all-chambers",
              "W-nonflat"):
        fired = tot[k][0] > 0
        log(f"   negative control {k}: fails on {tot[k][0]} of {sum(tot[k])} -> "
            f"{'FIRES' if fired else 'DID NOT FIRE'}")
        ok &= check(fired, f"control {k} did not fire")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    log = print
    stats = []

    # positive controls on known numbers
    A3 = braid_arr(4)
    B3 = Arr("B3", forms_B(3), signed_perm_gens(3), signed_perm_gens(3))
    check(len(A3.topes) == 24 and len(B3.topes) == 48, "chamber counts A3/B3")
    cA3, cB3 = all_cones(A3), all_cones(B3)
    check(len(cA3) == 219 and len(cB3) == 941, "top-cone counts 219/941")
    log(f"positive control: A3 / B3 chambers {len(A3.topes)} / {len(B3.topes)}, "
        f"top-cones {len(cA3)} / {len(cB3)} (expect 24/48, 219/941)")
    # reproduce two rows of the note's table, on W-orbit representatives
    W_A3 = [e for e in A3.G if e["inW"]]
    stats.append(run_arr(A3, cA3, log, "A3 (all cones up to W; G = +-W)", reps_by=W_A3))
    stats.append(run_arr(B3, cB3, log, "B3 (all cones up to W; G = W)", reps_by=B3.G))

    # new arrangements and symmetry classes
    T7 = tetra7()
    stats.append(run_arr(T7, all_cones(T7), log, "tetra7 (all cones; G = signed perms, not W)"))
    H6 = hex6()
    stats.append(run_arr(H6, all_cones(H6), log,
                         "hex6 (all cones; G = <h,-1>, h non-orthogonal of order 6)"))
    if not a.quick:
        A4 = braid_arr(5)
        W_A4 = [e for e in A4.G if e["inW"]]
        stats.append(run_arr(A4, all_cones(A4), log, "A4 (all cones up to W; G = +-W)",
                             reps_by=W_A4))
        F4 = Arr("F4", forms_F4(), F4_gens(), F4_gens())
        check(len(F4.topes) == 1152, "F4 chambers")
        mu = mu_to_top(F4.flats)[F4.full]
        check(mu == 1 * 5 * 7 * 11, "mu(L(F4)) = 385")
        log(f"positive control: F4 chambers {len(F4.topes)} (1152), "
            f"mu(L(F4)) = {mu} (1*5*7*11 = 385)")
        stats.append(run_arr(F4, sample_cones(F4, 60, a.seed) + [(0, 0)], log,
                             "F4 (60 sampled cones + all chambers; G = W(F4))",
                             lemma_f=True))
        D5 = Arr("D5", forms_D(5), signed_perm_gens(5), D_gens(5))
        check(len(D5.topes) == 1920, "D5 chambers")
        log(f"positive control: D5 chambers {len(D5.topes)} (1920), |G| = {len(D5.G)} (3840)")
        stats.append(run_arr(D5, sample_cones(D5, 40, a.seed + 1), log,
                             "D5 (40 sampled cones; G = W(B5) incl. odd sign changes)"))
        B5 = Arr("B5", forms_B(5), signed_perm_gens(5), signed_perm_gens(5))
        check(len(B5.topes) == 3840, "B5 chambers")
        stats.append(run_arr(B5, sample_cones(B5, 25, a.seed + 2), log,
                             "B5 (25 sampled cones; G = W)", lemma_f=False))
    stats.append(braid_check(4 if a.quick else 5, log))
    controls(stats, log)
    if FAIL:
        log(f"FAILED ({len(FAIL)}): " + "; ".join(FAIL[:10]))
        sys.exit(1)
    log("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
