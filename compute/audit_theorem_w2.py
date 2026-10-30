#!/usr/bin/env python3
"""Independent audit of Theorem W'' (notes/audit_theorem_w2.md).

Plain Python 3, no dependencies, exact rational arithmetic (Betti numbers by
rank mod p, which is exact for the concentrated answers checked).
Imports nothing from this repository.  Faces are computed by Fourier-Motzkin
feasibility of strict sign systems, flat by flat (not by covector closure).

Setting: A a finite real central essential arrangement in R^d, V a top-cone,
g a finite-order linear map with gA = A and gV = V, U = Fix(g),
M = Lambda(V)^g, and

  S(g) := sum_{X in M, X cap U = 0} mu_M(X, R^d).

Theorem W'': if U lies in no hyperplane of A, then S(g) = (-1)^k m(V^U),
k = dim U, m(V^U) >= 1, where V^U is the top-cone of A^U = {H cap U} with
|V^U| = |V| cap U; if U lies in a hyperplane, S(g) = 0.

Checks (per pair (V, g), g in Stab(V)):
  [W2b]    U in no hyperplane  =>  S(g) = (-1)^k m(V^U)
  [m>=1]   m(V^U) >= 1
  [W2a]    U in a hyperplane   =>  S(g) = 0
  [hall]   S(g) = chi~(Delta(Q')), Q' = {X in M : X != R^d, X cap U != 0}
  [pi]     pi(X) = X cap U is a flat of A^U lying in the proper part P_U
  [sigma]  sigma(Z) = cl(Z) lies in Q' (g-stable, in Lambda(V), proper, meets U)
  [adj]    Z <= pi(X)  <=>  sigma(Z) <= X, for all X in Q', Z in P_U
  [pisig]  pi(sigma(Z)) = Z ;  [sigpi] sigma(pi(X)) <= X
  [cl]     sigma(pi(X)) is the closure cl(X cap U) and is idempotent
  [homol]  reduced Betti numbers of Delta(P_U) over Q: only degree k-2,
           of rank m(V^U) (via ranks mod p; exact, see reduced_betti)
  [rho]    for a chamber C of V^U, the chamber cycle is a nonzero cycle
           of Delta(P_U), on distinct chains
  [chi]    sum over X in L^g with X cap U = 0 of chi_{V_X}(gbar), each term
           computed in its own quotient arrangement A_X/X, equals m(V^U)
           (or 0 if U lies in a hyperplane)
  [sgn]    (-1)^d det(g) = (-1)^k
  [fixch]  #V^g = #chambers(V^U), m(V^U) <= #V^g, equality if V^U pointed
  [m(V)]   m(V) >= 1 and Delta(Lambda-bar(V)) has homology only in degree
           d-2, for every top-cone V (pointed or not)

Negative controls (must fail somewhere): W2b without the sign; W2b with
m(V) in place of m(V^U); W2b with #V^g in place of m(V^U); sigma(Z) = Z without closure; the chamber cycle
with all signs +1; "S(g) = 0" asserted with no hypothesis on U.

Run (from compute/):  python3 audit_theorem_w2.py          (full)
                      python3 audit_theorem_w2.py --quick  (small cases)
Exit status 0 iff every asserted check passes and every control fires.
"""

import argparse
import sys
from fractions import Fraction as Fr
from math import gcd
from collections import defaultdict

# ---------------------------------------------------------------- linear algebra


def rref(rows):
    """Row-reduced echelon form (Fractions) of a list of vectors; zero rows dropped."""
    m = [[Fr(x) for x in r] for r in rows]
    if not m:
        return []
    n = len(m[0])
    out, piv_row = [], 0
    for c in range(n):
        p = None
        for r in range(piv_row, len(m)):
            if m[r][c] != 0:
                p = r
                break
        if p is None:
            continue
        m[piv_row], m[p] = m[p], m[piv_row]
        pv = m[piv_row][c]
        m[piv_row] = [x / pv for x in m[piv_row]]
        for r in range(len(m)):
            if r != piv_row and m[r][c] != 0:
                f = m[r][c]
                m[r] = [a - f * b for a, b in zip(m[r], m[piv_row])]
        piv_row += 1
        if piv_row == len(m):
            break
    return [tuple(r) for r in m[:piv_row]]


def nullspace(rows, n):
    """Basis of {x in Q^n : r.x = 0 for all r in rows}."""
    R = rref(rows)
    pivots = []
    for r in R:
        for c in range(n):
            if r[c] != 0:
                pivots.append(c)
                break
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for f in free:
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for r, pc in zip(R, pivots):
            v[pc] = -r[f]
        basis.append(tuple(v))
    return basis


def key(vectors):
    """Canonical key of a subspace given by spanning vectors."""
    return tuple(rref(vectors))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def det(m):
    m = [[Fr(x) for x in r] for r in m]
    n = len(m)
    d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for r in range(c + 1, n):
            f = m[r][c] / m[c][c]
            m[r] = [a - f * b for a, b in zip(m[r], m[c])]
    return d


def matmul(a, b):
    return tuple(tuple(sum(a[i][t] * b[t][j] for t in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def matvec(a, v):
    return tuple(dot(r, v) for r in a)


def vecmat(v, a):
    return tuple(sum(v[t] * a[t][j] for t in range(len(v))) for j in range(len(a[0])))


def ident(n):
    return tuple(tuple(Fr(int(i == j)) for j in range(n)) for i in range(n))


def solve_combo(rows, v):
    """Coefficients c with sum c_i rows_i = v (rows independent); None if none."""
    n = len(rows)
    # Solve via rref of the augmented transpose.
    aug = [[rows[i][j] for i in range(n)] + [v[j]] for j in range(len(v))]
    R = rref(aug)
    c = [Fr(0)] * n
    for r in R:
        lead = next(i for i in range(n + 1) if r[i] != 0)
        if lead == n:
            return None
        c[lead] = r[n]
    return tuple(c)


def rank_q(mat):
    return len(rref(mat)) if mat else 0


P = 2 ** 31 - 1


def rank_mod_p(mat):
    """Rank over F_p of an integer matrix.  rank_p <= rank_Q, which is all the
    Betti computation needs (see reduced_betti)."""
    rows = [{j: int(x) % P for j, x in enumerate(r) if int(x) % P} for r in mat]
    rows = [r for r in rows if r]
    rank = 0
    pivots = {}
    for r in rows:
        while r:
            c = min(r)
            if c in pivots:
                pr = pivots[c]
                f = r[c]
                for j, v in pr.items():
                    nv = (r.get(j, 0) - f * v) % P
                    if nv:
                        r[j] = nv
                    else:
                        r.pop(j, None)
            else:
                inv = pow(r[c], P - 2, P)
                pivots[c] = {j: v * inv % P for j, v in r.items()}
                rank += 1
                break
    return rank


# ------------------------------------------------- Fourier-Motzkin feasibility


def _norm(r):
    g = 0
    for x in r:
        g = gcd(g, abs(x))
    return tuple(x // g for x in r) if g else tuple(r)


def _int_row(r):
    den = 1
    for x in r:
        den = den * Fr(x).denominator // gcd(den, Fr(x).denominator)
    return tuple(int(Fr(x) * den) for x in r)


def strictly_feasible(rows):
    """Is there x with r.x > 0 for every r in rows?  Exact Fourier-Motzkin."""
    cur = {_norm(_int_row(r)) for r in rows}
    while True:
        if not cur:
            return True
        if any(all(x == 0 for x in r) for r in cur):
            return False
        j = len(next(iter(cur))) - 1
        pos = [r for r in cur if r[j] > 0]
        neg = [r for r in cur if r[j] < 0]
        nxt = {_norm(r[:j]) for r in cur if r[j] == 0}
        for p in pos:
            for q in neg:
                nxt.add(_norm(tuple(-q[j] * p[t] + p[j] * q[t] for t in range(j))))
        cur = nxt


# ------------------------------------------------------------- arrangements


class Arr:
    """Central essential arrangement given by normals in Q^d."""

    def __init__(self, normals):
        self.normals = [tuple(Fr(x) for x in a) for a in normals]
        self.n = len(self.normals)
        self.d = len(self.normals[0])
        assert len(rref(self.normals)) == self.d, "not essential"
        self._flats()
        self._faces()

    def zero_set(self, vectors):
        return frozenset(i for i, a in enumerate(self.normals)
                         if all(dot(a, v) == 0 for v in vectors))

    def _flats(self):
        full = frozenset()
        self.flat_basis = {full: list(ident(self.d))}
        frontier = [full]
        while frontier:
            new = []
            for Z in frontier:
                for i in range(self.n):
                    if i in Z:
                        continue
                    B = nullspace([self.normals[j] for j in Z | {i}], self.d)
                    Z2 = self.zero_set(B)
                    if Z2 not in self.flat_basis:
                        self.flat_basis[Z2] = B
                        new.append(Z2)
            frontier = new
        self.flat_dim = {Z: len(B) for Z, B in self.flat_basis.items()}
        self.top = full
        self.bottom = frozenset(range(self.n))

    def _faces(self):
        faces = []
        for Z, B in self.flat_basis.items():
            others = [i for i in range(self.n) if i not in Z]
            rows = {i: tuple(dot(self.normals[i], b) for b in B) for i in others}
            partial = [()]
            for i in others:
                ext = []
                for sv in partial:
                    for s in (1, -1):
                        cand = sv + (s,)
                        sysrows = [tuple(c * x for x in rows[others[t]])
                                   for t, c in enumerate(cand)]
                        if strictly_feasible(sysrows):
                            ext.append(cand)
                partial = ext
            for sv in partial:
                full = [0] * self.n
                for i, s in zip(others, sv):
                    full[i] = s
                faces.append(tuple(full))
        self.faces = faces
        self.face_zero = {F: frozenset(i for i in range(self.n) if F[i] == 0) for F in faces}
        self.chambers = [F for F in faces if not self.face_zero[F]]
        self.rays = {}
        for F in faces:
            Z = self.face_zero[F]
            if self.flat_dim[Z] == 1:
                v = self.flat_basis[Z][0]
                i = next(i for i in range(self.n) if F[i] != 0)
                if (dot(self.normals[i], v) > 0) != (F[i] > 0):
                    v = tuple(-x for x in v)
                self.rays[F] = v

    def point(self, F):
        """A relative-interior point of the face F (sum of its rays)."""
        rs = [v for R, v in self.rays.items() if conformal(R, F)]
        if not rs:
            return tuple(Fr(0) for _ in range(self.d))
        return tuple(sum(c) for c in zip(*rs))

    def act(self, g):
        """Signed permutation of hyperplanes induced by g: j -> (i, sign),
        with a_j g = lambda a_i, sign = sign(lambda).  None if g does not preserve A."""
        res = []
        for a in self.normals:
            ag = vecmat(a, g)
            hit = None
            for i, b in enumerate(self.normals):
                k = next(t for t in range(self.d) if b[t] != 0)
                lam = ag[k] / b[k]
                if lam != 0 and all(ag[t] == lam * b[t] for t in range(self.d)):
                    hit = (i, 1 if lam > 0 else -1)
                    break
            if hit is None:
                return None
            res.append(hit)
        return res

    def act_face(self, perm, F):
        return tuple(s * F[i] for (i, s) in perm)

    def act_flat(self, perm, Z):
        return frozenset(j for j, (i, s) in enumerate(perm) if i in Z)


def conformal(R, F):
    return all(r == 0 or r == f for r, f in zip(R, F))


# ----------------------------------------------------------------- top-cones


class Cone:
    def __init__(self, arr, chambers):
        self.arr = arr
        self.chambers = frozenset(chambers)
        n = arr.n
        self.smax = {}
        for e in range(n):
            signs = {C[e] for C in self.chambers}
            if len(signs) == 1:
                self.smax[e] = signs.pop()
        self.faces = [F for F in arr.faces
                      if all(F[e] in (0, s) for e, s in self.smax.items())]
        # [GT] Lemma 0.1(a)-free definition: Lambda(V) = spans of faces of V.
        self.lam = sorted({arr.face_zero[F] for F in self.faces},
                          key=lambda Z: arr.flat_dim[Z])
        self.lin = frozenset(self.smax)   # zero set of L = lin V (L = cap h_e)
        self.pointed = arr.flat_dim[arr.zero_set(nullspace(
            [arr.normals[e] for e in self.smax], arr.d))] == 0

    def m(self):
        return (-1) ** self.arr.d * mu_bottom_top(self.lam, self.arr)


def cone_from_signs(arr, signs):
    ch = [C for C in arr.chambers if all(C[e] == s for e, s in signs.items())]
    assert ch, "empty cone"
    return Cone(arr, ch)


def all_top_cones(arr):
    allc = frozenset(arr.chambers)
    seen = {allc}
    stack = [allc]
    while stack:
        V = stack.pop()
        for e in range(arr.n):
            for s in (1, -1):
                W = frozenset(C for C in V if C[e] == s)
                if W and W != V and W not in seen:
                    seen.add(W)
                    stack.append(W)
    return [Cone(arr, V) for V in seen]


# ------------------------------------------------------------------- posets


def leq(Z1, Z2):
    """Flat with zero set Z1 is contained in flat with zero set Z2."""
    return Z1 >= Z2


def mu_to_top(elements, arr):
    """mu(X, top) for X in a finite poset of flats (by inclusion) containing the top."""
    els = sorted(elements, key=lambda Z: -arr.flat_dim[Z])
    top = els[0]
    mu = {}
    for X in els:
        if X == top:
            mu[X] = 1
        else:
            mu[X] = -sum(mu[Y] for Y in mu if Y != X and leq(X, Y))
    return mu


def mu_bottom_top(elements, arr):
    mu = mu_to_top(elements, arr)
    bot = min(elements, key=lambda Z: arr.flat_dim[Z])
    return mu[bot]


def reduced_euler(elements, lt):
    """chi~ of the order complex: -1 + sum over chains (-1)^(len-1)."""
    order = list(elements)
    # Topological order by number of elements below.
    below = {x: [y for y in order if lt(y, x)] for x in order}
    order.sort(key=lambda x: len(below[x]))
    h = {}
    for x in order:
        h[x] = 1 - sum(h[y] for y in below[x])
    return -1 + sum(h.values())


def chains(elements, lt):
    out = defaultdict(list)
    els = list(elements)
    above = {x: [y for y in els if lt(x, y)] for x in els}

    def rec(c):
        out[len(c) - 1].append(tuple(c))
        for y in above[c[-1]]:
            rec(c + [y])
    for x in els:
        rec([x])
    return out


def reduced_betti(elements, lt):
    """Reduced Betti numbers of the order complex, as a dict degree -> rank,
    computed with ranks over F_p, p = 2^31 - 1.  Since rank_p <= rank_Q, each
    Betti number over F_p bounds the one over Q from above, and both have the
    same alternating sum (chi~).  So when the F_p answer is concentrated in a
    single degree, the Q answer is identical: that is how the checks use it."""
    ch = chains(elements, lt)
    if not ch:
        return {-1: 1}
    top = max(ch)
    idx = {q: {c: i for i, c in enumerate(ch[q])} for q in ch}
    ranks = {}
    # boundary d_q : C_q -> C_{q-1}, with C_{-1} = Q (augmentation)
    for q in range(0, top + 1):
        rows = []
        for c in ch[q]:
            row = [0] * (len(ch[q - 1]) if q > 0 else 1)
            if q == 0:
                row[0] = 1
            else:
                for i in range(len(c)):
                    face = c[:i] + c[i + 1:]
                    row[idx[q - 1][face]] += (-1) ** i
            rows.append(row)
        ranks[q] = rank_mod_p(rows)
    betti = {}
    dims = {q: len(ch[q]) for q in ch}
    dims[-1] = 1
    for q in range(-1, top + 1):
        rk_out = ranks.get(q, 0) if q >= 0 else 0
        rk_in = ranks.get(q + 1, 0)
        b = dims[q] - rk_out - rk_in
        if b:
            betti[q] = b
    return betti


# ------------------------------------------------------- the theorem objects


def fixed_space(g, d):
    return nullspace([tuple(g[i][j] - (1 if i == j else 0) for j in range(d))
                      for i in range(d)], d)


def restrict(arr, U):
    """A^U in coordinates of the basis U (rows).  Returns (ArrU, map i -> (j, sign))."""
    reps, keymap, mp = [], {}, []
    for a in arr.normals:
        r = tuple(dot(a, u) for u in U)
        assert any(r), "U lies in a hyperplane"
        k = next(t for t in range(len(r)) if r[t] != 0)
        s = 1 if r[k] > 0 else -1
        nr = tuple(x / r[k] for x in r)
        if nr not in keymap:
            keymap[nr] = len(reps)
            reps.append(nr)
        mp.append((keymap[nr], s))
    return Arr(reps), mp


def lift(vec_u, U):
    return tuple(sum(c * u[t] for c, u in zip(vec_u, U)) for t in range(len(U[0])))


def cap_dim(arr, ZX, Urows_perp):
    """dim(X cap U) for flat X (zero set ZX), U given by annihilator rows."""
    return len(nullspace([arr.normals[i] for i in ZX] + Urows_perp, arr.d))


def quotient_chi(arr, cone, ZX, g):
    """chi_{V_X}(gbar) = (-1)^codim det(gbar) mu(Lambda(V_X)^gbar), computed in
    coordinates on R^d/X from the quotient arrangement A_X/X."""
    q = rref([arr.normals[i] for i in ZX])      # basis of X^perp: y = q x
    c = len(q)
    if c == 0:
        return 1
    qn = [solve_combo(q, arr.normals[i]) for i in sorted(ZX)]
    gbar = tuple(solve_combo(q, vecmat(r, g)) for r in q)   # q g = gbar q
    arrX = get_arr(qn)
    signs = {}
    for t, i in enumerate(sorted(ZX)):
        if i in cone.smax:
            signs[t] = cone.smax[i]
    coneX = cone_from_signs(arrX, signs)
    perm = arrX.act(gbar)
    assert perm is not None
    MX = [Z for Z in coneX.lam if arrX.act_flat(perm, Z) == Z]
    mu = mu_bottom_top(MX, arrX)
    return (-1) ** c * det(gbar) * mu


_ARR_CACHE = {}


def get_arr(normals):
    k = tuple(tuple(Fr(x) for x in a) for a in normals)
    if k not in _ARR_CACHE:
        _ARR_CACHE[k] = Arr(k)
    return _ARR_CACHE[k]


def chamber_cycle(arrU, coneU, C, signed=True):
    """rho_C as a dict chain -> coefficient, chains of zero sets of A^U,
    plus whether all flags gave distinct chains."""
    k = arrU.d
    fs = [F for F in arrU.faces if conformal(F, C) and F != C
          and arrU.flat_dim[arrU.face_zero[F]] >= 1]
    bydim = defaultdict(list)
    for F in fs:
        bydim[arrU.flat_dim[arrU.face_zero[F]]].append(F)
    flags = [[F] for F in bydim[1]]
    for i in range(2, k):
        flags = [fl + [F] for fl in flags for F in bydim[i] if conformal(fl[-1], F)]
    pC = arrU.point(C)
    rho = defaultdict(Fr)
    seen = set()
    distinct = True
    for fl in flags:
        ch = tuple(arrU.face_zero[F] for F in fl)
        if ch in seen:
            distinct = False
        seen.add(ch)
        eps = det([arrU.point(F) for F in fl] + [pC]) if signed else 1
        rho[ch] += (1 if eps > 0 else -1) if signed else 1
    return {c: v for c, v in rho.items() if v}, distinct, len(flags)


def boundary(chain):
    out = defaultdict(Fr)
    for c, v in chain.items():
        if len(c) == 1:
            out[()] += v
        else:
            for i in range(len(c)):
                out[c[:i] + c[i + 1:]] += (-1) ** i * v
    return {c: v for c, v in out.items() if v}


# -------------------------------------------------------------- groups


def closure(gens, d, cap=5000):
    I = ident(d)
    G = {I}
    frontier = [I]
    while frontier:
        new = []
        for a in frontier:
            for b in gens:
                c = matmul(a, b)
                if c not in G:
                    G.add(c)
                    new.append(c)
        frontier = new
        assert len(G) <= cap, "group too large / infinite"
    return sorted(G)


def finite_order(g, d, cap=120):
    I = ident(d)
    p = g
    for _ in range(cap):
        if p == I:
            return True
        p = matmul(p, g)
    return False


def M_(rows):
    return tuple(tuple(Fr(x) for x in r) for r in rows)


def perm_matrix(p):
    n = len(p)
    return M_([[1 if p[j] == i else 0 for j in range(n)] for i in range(n)])


def neg(d):
    return M_([[-1 if i == j else 0 for j in range(d)] for i in range(d)])


def unit(i, d):
    return tuple(1 if t == i else 0 for t in range(d))


def examples():
    ex = {}
    # A1^3: coordinate hyperplanes; signed permutations (48).
    ex["coord3"] = ([unit(i, 3) for i in range(3)],
                    [perm_matrix((1, 0, 2)), perm_matrix((1, 2, 0)),
                     M_([[-1, 0, 0], [0, 1, 0], [0, 0, 1]])])
    # G2 in the hexagonal-lattice basis: a, b, a-b, a+b, 2a-b, a-2b; dihedral 12.
    ex["G2"] = ([(1, 0), (0, 1), (1, -1), (1, 1), (2, -1), (1, -2)],
                [M_([[0, -1], [1, -1]]), M_([[0, 1], [1, 0]]), neg(2)])
    # A2 x A1: a, b, a-b, c; D6 x Z2 (24), non-orthogonal in these coordinates.
    ex["A2xA1"] = ([(1, 0, 0), (0, 1, 0), (1, -1, 0), (0, 0, 1)],
                   [M_([[0, -1, 0], [1, -1, 0], [0, 0, 1]]),
                    M_([[0, 1, 0], [1, 0, 0], [0, 0, 1]]),
                    M_([[-1, 0, 0], [0, -1, 0], [0, 0, 1]]),
                    M_([[1, 0, 0], [0, 1, 0], [0, 0, -1]])])
    # x_i = 0 and x1+x2+x3 = 0; S3 x Z2.
    ex["coordsum3"] = ([unit(i, 3) for i in range(3)] + [(1, 1, 1)],
                       [perm_matrix((1, 0, 2)), perm_matrix((1, 2, 0)), neg(3)])
    # cyc3: x_i, x_i + 2 x_{i+1}, x1+x2+x3; <cyclic shift, -1> (6), no reflections.
    ex["cyc3"] = ([unit(i, 3) for i in range(3)]
                  + [tuple(1 if t == i else (2 if t == (i + 1) % 3 else 0) for t in range(3))
                     for i in range(3)] + [(1, 1, 1)],
                  [perm_matrix((1, 2, 0)), neg(3)])
    # K4: x_i = 0 and sum = 0 in R^4; S4 x Z2 (48).
    ex["K4"] = ([unit(i, 4) for i in range(4)] + [(1, 1, 1, 1)],
                [perm_matrix((1, 0, 2, 3)), perm_matrix((1, 2, 3, 0)), neg(4)])
    # cyc4: x_i, x_i + x_{i+1} (mod 4), sum; dihedral(8) x Z2.
    ex["cyc4"] = ([unit(i, 4) for i in range(4)]
                  + [tuple(1 if t in (i, (i + 1) % 4) else 0 for t in range(4)) for i in range(4)]
                  + [(1, 1, 1, 1)],
                  [perm_matrix((1, 2, 3, 0)), perm_matrix((3, 2, 1, 0)), neg(4)])
    # K5: x_i = 0 and sum = 0 in R^5; S5 x Z2 (240).
    ex["K5"] = ([unit(i, 5) for i in range(5)] + [(1, 1, 1, 1, 1)],
                [perm_matrix((1, 0, 2, 3, 4)), perm_matrix((1, 2, 3, 4, 0)), neg(5)])
    return ex


QUICK = ["coord3", "G2", "A2xA1", "coordsum3", "cyc3"]
FULL = QUICK + ["K4", "cyc4", "K5"]


# ------------------------------------------------------------------ driver


class Tally:
    def __init__(self):
        self.ok = defaultdict(int)
        self.bad = defaultdict(int)
        self.examples = {}

    def check(self, tag, cond, info=None):
        if cond:
            self.ok[tag] += 1
        else:
            self.bad[tag] += 1
            self.examples.setdefault(tag, info)


def analyse_pair(arr, cone, g, perm, T, NC, stats):
    d = arr.d
    U = fixed_space(g, d)
    k = len(U)
    Uperp = [tuple(g[i][j] - (1 if i == j else 0) for j in range(d)) for i in range(d)]
    M = [Z for Z in cone.lam if arr.act_flat(perm, Z) == Z]
    mu = mu_to_top(M, arr)
    meets = {Z: cap_dim(arr, Z, Uperp) > 0 for Z in M}
    S = sum(mu[Z] for Z in M if not meets[Z])
    in_hyp = any(all(dot(a, u) == 0 for u in U) for a in arr.normals)
    detg = det(g)
    T.check("sgn", (-1) ** d * detg == (-1) ** k)

    # chi-form, each term in its own quotient arrangement
    LG = [Z for Z in M if cone.lin <= Z]       # g-stable flats inside L
    chisum = sum(quotient_chi(arr, cone, Z, g) for Z in LG if not meets[Z])
    # Lemma B(b): X cap U = 0 forces X inside L
    T.check("Lb", all(cone.lin <= Z for Z in M if not meets[Z]))

    # "S = 0 for every g != 1" must fail somewhere
    NC["nohyp"] += 1 if (S != 0 and k < d) else 0
    if in_hyp:
        stats["W2a"] += 1
        T.check("W2a", S == 0, (cone.chambers, g))
        T.check("chi", chisum == 0, (S, chisum))
        return
    stats["W2b"] += 1
    arrU, mp = restrict(arr, U)
    signs = {}
    consistent = True
    for e, s in cone.smax.items():
        j, sg = mp[e]
        if signs.get(j, s * sg) != s * sg:
            consistent = False
        signs[j] = s * sg
    T.check("VUcone", consistent)
    coneU = cone_from_signs(arrU, signs)
    # |V^U| = |V| cap U: compare chamber interior points lifted to R^d
    T.check("VU=", all(all(c * dot(arr.normals[e], lift(arrU.point(C), U)) > 0
                           for e, c in cone.smax.items()) for C in coneU.chambers)
            and all(any(c * dot(arr.normals[e], lift(arrU.point(C), U)) < 0
                        for e, c in cone.smax.items())
                    for C in arrU.chambers if C not in coneU.chambers))
    m = coneU.m()
    stats["mmax"] = max(stats["mmax"], m)
    if not coneU.pointed:
        stats["VUnonpointed"] += 1
    if k == arr.d:
        stats["g=1"] += 1
    else:
        stats[f"k={k}"] += 1
        stats["mmax_g"] = max(stats["mmax_g"], m)
        if not coneU.pointed:
            stats["VUnp_g"] += 1
    # remark after Thm W'': g-fixed chambers of V <-> chambers of V^U, so
    # m(V^U) <= #V^g with equality when V^U is pointed
    nfix = sum(1 for C in cone.chambers if arr.act_face(perm, C) == C)
    T.check("fixch", nfix == len(coneU.chambers) and m <= nfix
            and (m == nfix or not coneU.pointed), (nfix, len(coneU.chambers), m))
    NC["#Vg"] += 1 if m != nfix else 0
    T.check("W2b", S == (-1) ** k * m, (S, k, m))
    T.check("m>=1", m >= 1, m)
    T.check("chi", chisum == m, (chisum, m))
    NC["nosign"] += 1 if S != m else 0
    NC["m(V)"] += 1 if S != (-1) ** k * cone.m() else 0

    # --- Galois connection Q' <-> P_U
    Qp = [Z for Z in M if Z != arr.top and meets[Z]]
    PU = [Z for Z in coneU.lam if Z != arrU.top and Z != arrU.bottom]
    sub_U = {Z: key([lift(v, U) for v in arrU.flat_basis[Z]]) for Z in arrU.flat_basis}
    from_key = {v: Z for Z, v in sub_U.items()}

    def pi(X):
        W = nullspace([arr.normals[i] for i in X] + Uperp, d)
        return from_key.get(key(W))           # None if X cap U is not a flat of A^U

    def sigma(Z, close=True):
        W = [lift(v, U) for v in arrU.flat_basis[Z]]
        if close:
            return arr.zero_set(W)
        return ("raw", key(W))

    Qset, Pset = set(Qp), set(PU)
    pimap = {X: pi(X) for X in Qp}
    sigmap = {Z: sigma(Z) for Z in PU}
    T.check("pi", all(pimap[X] in Pset for X in Qp))
    T.check("sigma", all(sigmap[Z] in Qset for Z in PU))
    T.check("pisig", all(pimap[sigmap[Z]] == Z for Z in PU))
    T.check("sigpi", all(leq(sigmap[pimap[X]], X) for X in Qp))
    T.check("adj", all(leq(Z, pimap[X]) == leq(sigmap[Z], X) for X in Qp for Z in PU))
    T.check("cl", all(sigmap[pimap[X]] == arr.zero_set(
        nullspace([arr.normals[i] for i in X] + Uperp, d)) and
        sigmap[pimap[sigmap[pimap[X]]]] == sigmap[pimap[X]] for X in Qp))
    # negative control: no closure -> sigma(Z) is the bare subspace Z, which is
    # usually not a flat of A
    NC["noclose"] += sum(1 for Z in PU
                         if key([lift(v, U) for v in arrU.flat_basis[Z]])
                         != key(arr.flat_basis[sigmap[Z]]))

    def ltA(a, b):
        return a != b and leq(a, b)
    chiQ = reduced_euler(Qp, ltA)
    chiP = reduced_euler(PU, ltA)
    T.check("hall", S == chiQ == chiP, (S, chiQ, chiP))

    # --- homology of Delta(P_U) and the chamber cycle
    if len(PU) <= 400:
        b = reduced_betti(PU, ltA)
        T.check("homol", b == {k - 2: m}, (b, k, m))
        stats["homol"] += 1
    if k >= 2:
        C = sorted(coneU.chambers)[0]
        rho, distinct, nfl = chamber_cycle(arrU, coneU, C)
        T.check("rho", distinct and len(rho) == nfl and not boundary(rho)
                and all(z in Pset for c in rho for z in c), (len(rho), nfl))
        rho1, _, _ = chamber_cycle(arrU, coneU, C, signed=False)
        NC["rho+1"] += 1 if boundary(rho1) else 0


def run(names, out):
    T = Tally()
    NC = defaultdict(int)
    exs = examples()
    total = defaultdict(int)
    for name in names:
        normals, gens = exs[name]
        arr = get_arr(normals)
        d = arr.d
        G = closure(gens, d)
        perms = {}
        for g in G:
            p = arr.act(g)
            T.check("G", p is not None and finite_order(g, d))
            perms[g] = p
        cones = all_top_cones(arr)
        # orbit representatives
        rep_of = {}
        reps = []
        for V in cones:
            if V.chambers in rep_of:
                continue
            reps.append(V)
            for g in G:
                rep_of[frozenset(arr.act_face(perms[g], C) for C in V.chambers)] = V
        stats = defaultdict(int)
        npointed = 0
        for V in cones:
            mV = V.m()
            T.check("m(V)", mV >= 1, mV)
            if not V.pointed:
                npointed += 1
            if True:
                lam_bar = [Z for Z in V.lam if Z not in (arr.top, arr.bottom)]
                if len(lam_bar) <= 400:
                    b = reduced_betti(lam_bar, lambda a, c: a != c and leq(a, c))
                    T.check("m(V)", b == {d - 2: mV}, (b, mV))
            # positive control: pointed cone => m(V) = #V
            if V.pointed:
                T.check("pointed", mV == len(V.chambers))
        # positive control: V = all chambers => m = |mu(L(A))|
        allV = Cone(arr, arr.chambers)
        T.check("Folkman", allV.m() == abs(mu_bottom_top(list(arr.flat_basis), arr)))
        npairs = 0
        for V in reps:
            for g in G:
                if frozenset(arr.act_face(perms[g], C) for C in V.chambers) != V.chambers:
                    continue
                npairs += 1
                analyse_pair(arr, V, g, perms[g], T, NC, stats)
        line = (f"{name:10s} d={d} n={arr.n:2d} chambers={len(arr.chambers):3d} "
                f"faces={len(arr.faces):4d} cones={len(cones):5d} "
                f"(non-pointed {npointed:4d}) |G|={len(G):3d} orbits={len(reps):4d} "
                f"pairs={npairs:5d} W2a={stats['W2a']:4d} W2b={stats['W2b']:4d} "
                f"(g=1: {stats['g=1']}, V^U non-pointed: {stats['VUnonpointed']}) "
                f"max m(V^U)={stats['mmax']} homology-checked={stats['homol']}\n"
                f"{'':10s} g != 1 with Fix(g) in no hyperplane, by k = dim Fix(g): "
                + ", ".join(f"k={kk}: {stats[f'k={kk}']}" for kk in range(1, d) if stats[f'k={kk}'])
                + f"; V^U non-pointed: {stats['VUnp_g']}; max m(V^U) for g != 1: {stats['mmax_g']}")
        print(line, file=out)
        for kk, v in stats.items():
            total[kk] = total[kk] + v if not kk.startswith("mmax") else max(total[kk], v)
    return T, NC, total


EXPECT_CHAMBERS = {"coord3": 8, "G2": 12, "A2xA1": 12, "coordsum3": 14,
                   "K4": 30, "K5": 62}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args(argv)
    names = QUICK if args.quick else FULL
    out = sys.stdout
    print("Audit of Theorem W'' -- exact arithmetic, Fourier-Motzkin faces", file=out)
    ok = True
    # positive control: chamber counts
    exs = examples()
    for nm, c in EXPECT_CHAMBERS.items():
        if nm in names:
            got = len(get_arr(exs[nm][0]).chambers)
            print(f"[control] chambers {nm}: {got} (expected {c})", file=out)
            ok &= got == c
    T, NC, total = run(names, out)
    print("", file=out)
    for tag in sorted(set(T.ok) | set(T.bad)):
        print(f"[{tag}] checks={T.ok[tag] + T.bad[tag]} failures={T.bad[tag]}", file=out)
        if T.bad[tag]:
            ok = False
            print(f"   first failure: {T.examples[tag]}", file=out)
    print("", file=out)
    print("Negative controls (count of instances where the wrong statement fails; must be > 0):",
          file=out)
    for tag in ("nosign", "m(V)", "#Vg", "noclose", "rho+1", "nohyp"):
        print(f"[neg:{tag}] fires on {NC[tag]}", file=out)
        ok &= NC[tag] > 0
    print("", file=out)
    print(f"totals: W2a pairs {total['W2a']}, W2b pairs {total['W2b']} "
          f"(of which g = 1: {total['g=1']}, g != 1: {total['W2b'] - total['g=1']}, "
          f"V^U non-pointed: {total['VUnonpointed']}, of which g != 1: {total['VUnp_g']}), max m(V^U) for g != 1 = {total['mmax_g']}, "
          f"max m(V^U) = {total['mmax']}", file=out)
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED", file=out)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
