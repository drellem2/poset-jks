"""Independent audit script for notes/vanishing_criterion.md.

Plain Python 3, exact rational arithmetic (fractions.Fraction), no
third-party packages and no imports from any other script in compute/.

Method (chosen to differ from compute/vanishing_criterion.py, which builds
faces from parabolic cosets of a Weyl group):
- an arrangement is a list of integer normal vectors in Q^d; any central
  essential arrangement is allowed, reflection arrangement or not;
- flats are closed sets of hyperplanes, found by exact null spaces;
- faces are sign vectors of explicit rational points, generated from 0 by
  repeatedly moving a point p of a face a little along a ray v
  (p + eps v, eps chosen so the nonzero signs of p are kept); this is the
  geometric form of "every covector is a composition of cocircuits";
- symmetries are rational matrices; their action on hyperplanes, chambers and
  flats is computed from the matrices;
- chi_V(g) is computed from the definition (-1)^d det(g) mu(Lambda(V)^g),
  with Lambda(V) the spans of the faces lying in |V|;
- the right side of Formula Z is computed separately: Z*(V,g) by linear
  algebra on Fix(g), mu_{L(A)^g}(0, X) in the full g-fixed lattice, and
  m_X(V) by building the restricted arrangement {H cap U : H > X} in
  coordinates on U = Fix(g) and computing the support lattice of the cone
  |V| cap U from that arrangement's own faces;
- type A is also tested with no arrangement code at all: flats are set
  partitions, Fix(+-w) and the transversality conditions are solved by
  linear algebra in R^n, and mu is computed by recursion in the fixed
  partition lattice (formula (H) is not used).

Usage (from compute/):
  python3 audit_vanishing_criterion.py           full run (about 1-2 min)
  python3 audit_vanishing_criterion.py --quick   small arrangements only
Exit status 0 iff every asserted check passes.
"""

import sys
from fractions import Fraction as Fr
from itertools import product, permutations

# ------------------------------------------------------------ linear algebra


def rref(rows, ncols):
    """Row-reduce a list of rows (Fractions). Returns (reduced rows, pivots)."""
    M = [[Fr(x) for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(M)):
            if M[i][c] != 0:
                p = i
                break
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
    if not rows:
        return 0
    return len(rref(rows, ncols)[1])


def nullspace(rows, ncols):
    """Basis of {x : r.x = 0 for all rows}."""
    if not rows:
        return [tuple(Fr(int(i == j)) for j in range(ncols)) for i in range(ncols)]
    R, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * ncols
        v[f] = Fr(1)
        for i, c in enumerate(piv):
            v[c] = -R[i][f]
        basis.append(tuple(v))
    return basis


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def matmul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return tuple(tuple(sum(A[i][t] * B[t][j] for t in range(k)) for j in range(m))
                 for i in range(n))


def matvec(A, v):
    return tuple(sum(a * x for a, x in zip(row, v)) for row in A)


def transpose(A):
    return tuple(zip(*A))


def ident(d):
    return tuple(tuple(Fr(int(i == j)) for j in range(d)) for i in range(d))


def det(A):
    M = [list(map(Fr, r)) for r in A]
    n = len(M)
    D = Fr(1)
    for c in range(n):
        p = None
        for i in range(c, n):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            D = -D
        D *= M[c][c]
        for i in range(c + 1, n):
            f = M[i][c] / M[c][c]
            if f:
                M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return D


def inverse(A):
    n = len(A)
    M = [list(map(Fr, A[i])) + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
    R, piv = rref(M, 2 * n)
    assert piv == list(range(n))
    return tuple(tuple(R[i][n:]) for i in range(n))


def mat_order(g, cap=200):
    d = len(g)
    I = ident(d)
    h = g
    for k in range(1, cap + 1):
        if h == I:
            return k
        h = matmul(g, h)
    raise ValueError("order too large")


def sgn(x):
    return (x > 0) - (x < 0)


def proportional(a, b):
    """Return c with a = c b (c != 0), or None."""
    c = None
    for x, y in zip(a, b):
        if y == 0:
            if x != 0:
                return None
        else:
            q = Fr(x) / y
            if c is None:
                c = q
            elif q != c:
                return None
    return c


def mobius_from_bottom(elems, leq):
    """mu(bottom, x) for x in elems; elems must contain a unique bottom."""
    order = sorted(elems, key=lambda x: sum(1 for y in elems if leq(y, x)))
    mu = {}
    for x in order:
        below = [y for y in order if y in mu and leq(y, x) and y != x]
        mu[x] = 1 if not below else -sum(mu[y] for y in below)
    return mu


def mobius_number(theorem_elems, leq):
    """mu(0^, 1^) of a bounded finite poset (by recursion from the bottom)."""
    mu = mobius_from_bottom(theorem_elems, leq)
    top = max(theorem_elems, key=lambda x: sum(1 for y in theorem_elems if leq(y, x)))
    return mu[top]


def mobius_int(k):
    res, p, m = 1, 2, k
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    if m > 1:
        res = -res
    return res


def lcm(a, b):
    from math import gcd
    return a * b // gcd(a, b)


# ------------------------------------------------------------ arrangements


class Arr:
    """A central essential arrangement given by normals (tuples) in Q^d."""

    def __init__(self, normals, d, faces=True):
        self.d = d
        self.N = [tuple(Fr(x) for x in a) for a in normals]
        self.m = len(self.N)
        assert self.m == 0 or rank(self.N, d) == d, "not essential"
        for i in range(self.m):
            for j in range(i):
                assert proportional(self.N[i], self.N[j]) is None, "repeated hyperplane"
        self._flats()
        if faces:
            self._faces()
        else:
            self.faces = None

    # flats: zero set (frozenset of hyperplane indices) -> basis of the flat
    def closure_of_space(self, basis):
        return frozenset(e for e in range(self.m)
                         if all(dot(self.N[e], v) == 0 for v in basis))

    def _flats(self):
        top = frozenset()
        self.flats = {top: nullspace([], self.d)}
        frontier = [top]
        while frontier:
            new = []
            for S in frontier:
                for e in range(self.m):
                    if e in S:
                        continue
                    B = nullspace([self.N[i] for i in S | {e}], self.d)
                    T = self.closure_of_space(B)
                    if T not in self.flats:
                        self.flats[T] = B
                        new.append(T)
            frontier = new
        self.zero = frozenset(range(self.m))
        assert self.flats[self.zero] == [] or self.m == 0

    def dim(self, S):
        return len(self.flats[S])

    @staticmethod
    def leq(S, T):
        """flat with zero set S is contained in flat with zero set T."""
        return S >= T

    def signs(self, p):
        return tuple(sgn(dot(a, p)) for a in self.N)

    def _faces(self):
        d = self.d
        rays = []
        for S, B in self.flats.items():
            if len(B) == 1:
                rays.append(B[0])
                rays.append(tuple(-x for x in B[0]))
        origin = tuple(Fr(0) for _ in range(d))
        faces = {self.signs(origin): origin}
        frontier = [origin]
        while frontier:
            new = []
            for p in frontier:
                vp = [dot(a, p) for a in self.N]
                for v in rays:
                    vv = [dot(a, v) for a in self.N]
                    eps = Fr(1)
                    for x, y in zip(vp, vv):
                        if x != 0 and y != 0:
                            eps = min(eps, abs(x) / (2 * abs(y)))
                    q = tuple(a + eps * b for a, b in zip(p, v))
                    s = self.signs(q)
                    if s not in faces:
                        faces[s] = q
                        new.append(q)
            frontier = new
        self.faces = faces                # sign vector -> rational point
        if d == 0:
            self.chambers = [()]
        else:
            self.chambers = [s for s in faces if 0 not in s]
        self.ch_index = {s: i for i, s in enumerate(self.chambers)}
        self.nch = len(self.chambers)

    def zero_set(self, s):
        return frozenset(e for e, x in enumerate(s) if x == 0)


# ------------------------------------------------------------ symmetries


class Sym:
    """A finite-order linear symmetry g of an arrangement."""

    def __init__(self, A, g):
        self.A = A
        self.g = g
        d = A.d
        gi = inverse(g) if d else ()
        self.perm = []
        self.psgn = []
        for a in A.N:
            f = tuple(sum(a[i] * gi[i][j] for i in range(d)) for j in range(d))
            hit = None
            for e2, b in enumerate(A.N):
                c = proportional(f, b)
                if c is not None:
                    hit = (e2, sgn(c))
                    break
            assert hit is not None, "g does not preserve A"
            self.perm.append(hit[0])
            self.psgn.append(hit[1])
        self.order = mat_order(g) if d else 1
        self.det = det(g) if d else Fr(1)
        assert self.det in (1, -1)
        I = ident(d)
        self.U = nullspace([tuple(g[i][j] - I[i][j] for j in range(d)) for i in range(d)], d) if d else []
        self.hypU = frozenset(e for e in range(A.m) if all(dot(A.N[e], u) == 0 for u in self.U))
        self.chperm = ([A.ch_index[self.act_signs(s)] for s in A.chambers]
                       if A.faces is not None else None)

    def act_signs(self, s):
        out = [0] * self.A.m
        for e, x in enumerate(s):
            out[self.perm[e]] = x * self.psgn[e]
        return tuple(out)

    def act_flat(self, S):
        return frozenset(self.perm[e] for e in S)

    def act_cone(self, V):
        out = 0
        x = V
        while x:
            low = x & -x
            out |= 1 << self.chperm[low.bit_length() - 1]
            x ^= low
        return out


def group_closure(gens, d):
    I = ident(d)
    G = {I}
    frontier = [I]
    while frontier:
        new = []
        for h in frontier:
            for s in gens:
                k = matmul(s, h)
                if k not in G:
                    G.add(k)
                    new.append(k)
        frontier = new
    return G


def class_reps(G):
    G = list(G)
    inv = {g: inverse(g) for g in G}
    seen = set()
    reps = []
    for g in G:
        if g in seen:
            continue
        cl = {matmul(matmul(h, g), inv[h]) for h in G}
        seen |= cl
        reps.append((g, len(cl)))
    return reps


# ------------------------------------------------------------ cones


def all_cones(A):
    half = []
    for e in range(A.m):
        p = n = 0
        for i, s in enumerate(A.chambers):
            if s[e] > 0:
                p |= 1 << i
            else:
                n |= 1 << i
        half += [p, n]
    full = (1 << A.nch) - 1
    seen = {full}
    frontier = [full]
    while frontier:
        new = []
        for V in frontier:
            for H in half:
                c = V & H
                if c and c != V and c not in seen:
                    seen.add(c)
                    new.append(c)
        frontier = new
    return sorted(seen)


def cone_constraints(A, V):
    """dict e -> sign for the hyperplanes with all of V on one side (S_max)."""
    chs = [A.chambers[i] for i in range(A.nch) if (V >> i) & 1]
    out = {}
    for e in range(A.m):
        s = {c[e] for c in chs}
        if len(s) == 1:
            out[e] = s.pop()
    return out


def chambers_of_constraints(A, cons):
    V = 0
    for i, c in enumerate(A.chambers):
        if all(c[e] == s for e, s in cons.items()):
            V |= 1 << i
    return V


def lam(A, cons):
    """Lambda(V): zero sets of the faces of A inside |V|."""
    return {A.zero_set(s) for s in A.faces
            if all(s[e] * t >= 0 for e, t in cons.items())}


def lineality(A, cons):
    """Zero set of the lineality flat L = cap_{e in S_max} H_e."""
    B = nullspace([A.N[e] for e in cons], A.d)
    return A.closure_of_space(B)


def chi_def(A, gs, cons):
    """(-1)^d det(g) mu(Lambda(V)^g) from the definition."""
    if A.d == 0:
        return 1
    L = [S for S in lam(A, cons) if gs.act_flat(S) == S]
    mu = mobius_number(L, Arr.leq)
    return (-1) ** A.d * int(gs.det) * mu


# ------------------------------------------------------------ Formula Z data


class GData:
    """Per-g data: the g-fixed lattice, its mu, Z(g)-candidates, Z*(g)."""

    def __init__(self, A, gs):
        self.A, self.gs = A, gs
        self.fixed = [S for S in A.flats if gs.act_flat(S) == S]
        self.mu = mobius_from_bottom(self.fixed, Arr.leq)   # mu(0, X)
        k = len(gs.U)
        self.meets0 = {}
        for S in self.fixed:
            B = A.flats[S]
            self.meets0[S] = rank(list(B) + list(gs.U), A.d) == len(B) + k
        # X + U in no hyperplane: no e in S (H_e > X) with H_e > U
        self.transverse = {S: not (S & gs.hypU) for S in self.fixed}
        self.zstar = [S for S in self.fixed if self.meets0[S] and self.transverse[S]]
        self._restr = {}

    def restricted(self, S):
        """Arrangement {H cap U : H > X} in coordinates on U, and the map
        e -> (index in the restricted arrangement, sign of the scalar)."""
        if S in self._restr:
            return self._restr[S]
        A, U = self.A, self.gs.U
        forms, emap = [], {}
        for e in sorted(S):
            f = tuple(dot(A.N[e], u) for u in U)
            assert any(f), "H > X contains U, X not in Z*"
            hit = None
            for j, b in enumerate(forms):
                c = proportional(f, b)
                if c is not None:
                    hit = (j, sgn(c))
                    break
            if hit is None:
                forms.append(f)
                hit = (len(forms) - 1, 1)
            emap[e] = hit
        B = Arr(forms, len(U))
        self._restr[S] = (B, emap)
        return B, emap

    def m_X(self, S, cons, consistency=None):
        """m of the top-cone |V| cap U of {H cap U : H > X}."""
        B, emap = self.restricted(S)
        rc = {}
        for e, t in cons.items():
            assert e in S, "constraint hyperplane does not contain X"
            j, c = emap[e]
            want = t * c
            if j in rc and rc[j] != want:
                if consistency is not None:
                    consistency.append((S, e))
                return None
            rc[j] = want
        if B.d == 0:
            return 1
        Lm = lam(B, rc)
        return (-1) ** B.d * mobius_number(list(Lm), Arr.leq)


def chi_Z(gd, cons, Lzero, variant="Z"):
    """Right side of Formula Z (and deliberately wrong variants)."""
    A = gd.A
    tot = 0
    for S in gd.fixed:
        if not (S >= Lzero):          # X inside L
            continue
        if variant == "no_transverse":
            if not gd.meets0[S]:
                continue
            if not gd.transverse[S]:
                tot += gd.mu[S]       # m undefined; use 1
                continue
        elif variant == "no_meet":
            if not gd.transverse[S]:
                continue
        elif not (gd.meets0[S] and gd.transverse[S]):
            continue
        if variant == "m_one":
            tot += gd.mu[S]
            continue
        if variant == "unfixed_mu":
            tot += gd.mu_full[S] * gd.m_X(S, cons)
            continue
        if variant == "no_meet" and not gd.meets0[S]:
            tot += gd.mu[S]
            continue
        tot += gd.mu[S] * gd.m_X(S, cons)
    return tot


def localized_sum(A, gs, gd, cons, Lzero, Xs):
    """Step 5 of the proof of Theorem Z, tested: for X in Z(V,g),
    sum_{Z in Z(V,g), Z > X} chi_{V_Z}(gbar) with chi_{V_Z}(gbar) computed as
    (-1)^{codim Z} det(gbar) mu_{Lambda(V)^g}(Z, R^d) (Lemma A form)."""
    Lv = [S for S in lam(A, cons) if gs.act_flat(S) == S]
    top = frozenset()
    res = {}
    for X in Xs:
        tot = 0
        for Z in gd.fixed:
            if not (Z >= Lzero and gd.meets0[Z] and Arr.leq(X, Z)):
                continue
            up = [S for S in Lv if Arr.leq(Z, S)]
            mu = mobius_from_bottom(up, Arr.leq)[top]
            dZ = A.dim(Z)
            dgZ = det_restricted(gs.g, A.flats[Z]) if dZ else Fr(1)
            dbar = gs.det / dgZ
            tot += (-1) ** (A.d - dZ) * int(dbar) * mu
        res[X] = tot
    return res


def det_restricted(g, B):
    """det of g on the g-stable subspace spanned by the basis B."""
    k = len(B)
    if k == 0:
        return Fr(1)
    # solve g b_j = sum_i c_ij b_i
    d = len(B[0])
    cols = []
    for b in B:
        gb = matvec(g, b)
        # least: solve B^T c = gb (B has full column rank)
        rows = [list(B[i][r] for i in range(k)) + [gb[r]] for r in range(d)]
        R, piv = rref(rows, k + 1)
        assert k not in piv, "subspace not g-stable"
        c = [Fr(0)] * k
        for i, p in enumerate(piv):
            c[p] = R[i][k]
        cols.append(c)
    M = tuple(tuple(cols[j][i] for j in range(k)) for i in range(k))
    return det(M)


def witness_cone(A, gs, S):
    """A g-fixed chamber K of A_X, and V# = {C : C_e = K_e for e in S}."""
    U = gs.U
    # a point of U off every H > X: try small integer combinations
    k = len(U)
    for coeffs in product(range(-3, 4), repeat=k):
        p = tuple(sum(c * u[i] for c, u in zip(coeffs, U)) for i in range(A.d))
        if all(dot(A.N[e], p) != 0 for e in S):
            cons = {e: sgn(dot(A.N[e], p)) for e in S}
            return cons, chambers_of_constraints(A, cons)
    raise AssertionError("no point of U off the hyperplanes through X")


# ------------------------------------------------------------ examples


def refl(alpha):
    a = [Fr(x) for x in alpha]
    aa = dot(a, a)
    d = len(a)
    return tuple(tuple(Fr(int(i == j)) - 2 * a[i] * a[j] / aa for j in range(d)) for i in range(d))


def braid(n):
    """A_{n-1} in coordinates y_i = x_i - x_n (i < n); group +-S_n."""
    d = n - 1

    def form(i, j):
        v = [0] * d
        if i < d:
            v[i] += 1
        if j < d:
            v[j] -= 1
        return tuple(v)
    normals = [form(i, j) for i in range(n) for j in range(i + 1, n)]

    def perm_matrix(w):
        # (gx)_{w(i)} = x_i on R^n, induced on y = x - x_n
        cols = []
        for i in range(d):
            x = [0] * n
            x[i] = 1
            gx = [0] * n
            for t in range(n):
                gx[w[t]] = x[t]
            cols.append(tuple(Fr(gx[r] - gx[n - 1]) for r in range(d)))
        return tuple(tuple(cols[j][i] for j in range(d)) for i in range(d))
    gens = []
    for i in range(n - 1):
        w = list(range(n))
        w[i], w[i + 1] = w[i + 1], w[i]
        gens.append(perm_matrix(w))
    gens.append(tuple(tuple(-x for x in r) for r in ident(d)))
    return normals, d, gens, perm_matrix


def typeB(n):
    normals = []
    for i in range(n):
        v = [0] * n
        v[i] = 1
        normals.append(tuple(v))
    for i in range(n):
        for j in range(i + 1, n):
            for s in (1, -1):
                v = [0] * n
                v[i], v[j] = 1, s
                normals.append(tuple(v))
    gens = []
    for i in range(n - 1):
        v = [0] * n
        v[i], v[i + 1] = 1, -1
        gens.append(refl(v))
    v = [0] * n
    v[-1] = 1
    gens.append(refl(v))
    return normals, n, gens


def typeD4():
    normals = []
    for i in range(4):
        for j in range(i + 1, 4):
            for s in (1, -1):
                v = [0] * 4
                v[i], v[j] = 1, s
                normals.append(tuple(v))
    simple = [(1, -1, 0, 0), (0, 1, -1, 0), (0, 0, 1, -1), (0, 0, 1, 1)]
    return normals, 4, simple


def typeF4():
    normals = set()
    def canon(v):
        v = tuple(Fr(x) for x in v)
        for x in v:
            if x != 0:
                return v if x > 0 else tuple(-y for y in v)
    for i in range(4):
        v = [0] * 4
        v[i] = 1
        normals.add(canon(v))
    for i in range(4):
        for j in range(i + 1, 4):
            for s in (1, -1):
                v = [0] * 4
                v[i], v[j] = 1, s
                normals.add(canon(v))
    for signs in product((1, -1), repeat=3):
        normals.add(canon((1,) + signs))
    simple = [(0, 1, -1, 0), (0, 0, 1, -1), (0, 0, 0, 1), (Fr(1, 2), Fr(-1, 2), Fr(-1, 2), Fr(-1, 2))]
    return sorted(normals), 4, simple


def coxeter(simple):
    c = ident(len(simple[0]))
    for a in simple:
        c = matmul(c, refl(a))
    return c


def examples(quick):
    """name -> (normals, d, group generators)."""
    ex = {}
    for n in ((3, 4) if quick else (3, 4, 5)):
        N, d, gens, _ = braid(n)
        ex["A%d" % (n - 1)] = (N, d, gens)
    for n in ((2, 3) if quick else (2, 3)):
        N, d, gens = typeB(n)
        ex["B%d" % n] = (N, d, gens)
    # rank 1
    ex["rank1"] = ([(1,)], 1, [((Fr(-1),),)])
    # coordinate lines in R^2 with the swap (a reflection whose mirror is NOT in A)
    ex["coord2"] = ([(1, 0), (0, 1)], 2, [((0, 1), (1, 0)), ((-1, 0), (0, 1))])
    # three lines y = 0, y = x, y = -x with s(x, y) = (-x, y) and (x, -y)
    ex["tri2"] = ([(0, 1), (1, -1), (1, 1)], 2, [((-1, 0), (0, 1)), ((1, 0), (0, -1))])
    # a non-reflection arrangement in R^3: x_i = 0 and x1+x2+x3 = 0, group S_3 x {+-1}
    ex["coordsum3"] = ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1)], 3,
                       [((0, 1, 0), (1, 0, 0), (0, 0, 1)), ((0, 0, 1), (1, 0, 0), (0, 1, 0)),
                        ((-1, 0, 0), (0, -1, 0), (0, 0, -1))])
    return ex


def as_mat(g):
    return tuple(tuple(Fr(x) for x in r) for r in g)


# ------------------------------------------------------------ the main audit


class Log:
    def __init__(self, out):
        self.out = out
        self.counts = {}
        self.fails = {}
        self.examples = {}

    def check(self, tag, ok, info=""):
        self.counts[tag] = self.counts.get(tag, 0) + 1
        if not ok:
            self.fails[tag] = self.fails.get(tag, 0) + 1
            if tag not in self.examples:
                self.examples[tag] = info

    def p(self, *a):
        print(*a, file=self.out)


def run_arrangement(name, data, log, neg):
    N, d, gens = data
    A = Arr(N, d)
    G = group_closure([as_mat(g) for g in gens], d)
    reps = class_reps(G)
    cones = all_cones(A)
    log.p("%-10s d=%d hyperplanes=%d chambers=%d top-cones=%d |G|=%d classes=%d"
          % (name, d, A.m, A.nch, len(cones), len(G), len(reps)))
    full = (1 << A.nch) - 1
    pairs = 0
    stats = {"nonzero": 0, "corV": 0, "nomu": 0, "cancel": 0}
    for g, csize in reps:
        gs = Sym(A, g)
        gd = GData(A, gs)
        gd.mu_full = mobius_from_bottom(list(A.flats), Arr.leq)
        k = len(gs.U)
        # sign rule (-1)^d det g = (-1)^{dim Fix g}
        log.check("[sgn]", (-1) ** d * gs.det == (-1) ** k)
        # Theorem Z, second display: mu(0,X) = chi_full of A^X at g|X
        for S in gd.zstar:
            dX = A.dim(S)
            dg = det_restricted(g, A.flats[S])
            log.check("[Zfull]", dg == (-1) ** dX and (-1) ** dX * dg * gd.mu[S] == gd.mu[S])
        # down-set claim (step 7): every g-stable flat below X in Z(V,g) meets U in 0
        for S in gd.fixed:
            if gd.meets0[S]:
                for T in gd.fixed:
                    if Arr.leq(T, S):
                        log.check("[down]", gd.meets0[T])
        some_nonzero = False
        for V in cones:
            if gs.act_cone(V) != V:
                continue
            pairs += 1
            cons = cone_constraints(A, V)
            Lz = lineality(A, cons)
            chi = chi_def(A, gs, cons)
            if chi != 0:
                some_nonzero = True
            # lineality as claimed in S: lin = cap of S_max; g-stable
            log.check("[linstable]", gs.act_flat(Lz) == Lz)
            zv = [S for S in gd.zstar if S >= Lz]
            ms = {S: gd.m_X(S, cons) for S in zv}
            for S in zv:
                log.check("[m>=1]", ms[S] is not None and ms[S] >= 1, (name, S))
            rhs = sum(gd.mu[S] * ms[S] for S in zv)
            log.check("[Z]", chi == rhs, (name, g, V, chi, rhs))
            # step 5 of the proof (localized identities) on every X in Z(V,g)
            Xs = [S for S in gd.fixed if S >= Lz and gd.meets0[S]]
            loc = localized_sum(A, gs, gd, cons, Lz, Xs)
            for X in Xs:
                psi = ms[X] if X in ms else 0
                log.check("[loc]", loc[X] == psi, (name, X, loc[X], psi))
            # Cor. V: a hyperplane containing L and U forces Z*(V,g) empty
            corv = any(e in Lz for e in gs.hypU)
            if corv:
                log.check("[corV]", not zv and chi == 0)
            # S1: pointed cones
            if A.dim(Lz) == 0:
                nfix = sum(1 for i in range(A.nch) if (V >> i) & 1 and gs.chperm[i] == i)
                log.check("[S1]", chi == nfix)
                log.check("[S1zero=corV]", (chi == 0) == corv)
            # S2: Fix g = 0
            if k == 0 and d > 0:
                log.check("[S2]", (chi == 0) if V != full else chi == gd.mu[frozenset()])
            # PC(a)
            if chi != 0:
                log.check("[PCa]", any(gd.mu[S] != 0 for S in zv))
            nz = [gd.mu[S] for S in zv if gd.mu[S] != 0]
            if chi != 0:
                stats["nonzero"] += 1
            elif corv:
                stats["corV"] += 1
            elif not nz:
                stats["nomu"] += 1
            else:
                stats["cancel"] += 1
                if (name, gs.order) not in stats.setdefault("cancel_classes", set()):
                    stats["cancel_classes"].add((name, gs.order))
                    log.p("  cancellation: g of order %d, dim Fix %d, det %d, cone with dim L = %d; "
                          "terms (dim X, mu, m_X) = %s" % (
                              gs.order, k, gs.det, A.dim(Lz),
                              [(A.dim(S), gd.mu[S], ms[S]) for S in zv]))
            coh = len({sgn(gd.mu[S]) for S in gd.zstar if gd.mu[S] != 0}) <= 1
            if coh and nz:
                log.check("[PCb]", chi != 0)
            # negative controls (each must fail somewhere overall)
            for var in ("no_transverse", "no_meet", "m_one", "unfixed_mu"):
                neg.setdefault(var, [0, 0])
                neg[var][0] += 1
                try:
                    val = chi_Z(gd, cons, Lz, var)
                except AssertionError:
                    val = None
                if val != chi:
                    neg[var][1] += 1
        # Theorem S
        cand = [S for S in gd.zstar if gd.mu[S] != 0]
        log.check("[S]", some_nonzero == bool(cand), (name, g))
        if cand:
            # minimal X among the candidates
            for X in cand:
                minimal = not any(T != X and Arr.leq(T, X) for T in cand)
                cons, Vs = witness_cone(A, gs, X)
                ok = gs.act_cone(Vs) == Vs and Vs != 0
                cons2 = cone_constraints(A, Vs)
                ok = ok and lineality(A, cons2) == X and set(cons2) == set(X)
                chi = chi_def(A, gs, cons2)
                if minimal:
                    log.check("[Switness]", ok and chi == gd.mu[X], (name, X, chi, gd.mu[X]))
                else:
                    neg.setdefault("nonminimal_witness", [0, 0])
                    neg["nonminimal_witness"][0] += 1
                    if chi != gd.mu[X]:
                        neg["nonminimal_witness"][1] += 1
        # S3: involutions
        if gs.order == 2:
            log.check("[S3mu]", all(gd.mu[S] != 0 and sgn(gd.mu[S]) == (-1) ** A.dim(S) for S in gd.zstar))
            E = nullspace([tuple(g[i][j] + int(i == j) for j in range(d)) for i in range(d)], d)
            for S in gd.zstar:
                log.check("[S3inE]", rank(list(E) + list(A.flats[S]), d) == len(E))
            if len(E) == 1:      # a reflection
                alpha = E[0]
                line_flat = A.closure_of_space([alpha])
                is_flat = A.dim(line_flat) == 1
                # the mirror is Fix(g), a hyperplane of R^d; it lies in A iff some
                # hyperplane of A contains it
                mirror_in_A = bool(gs.hypU)
                claim = is_flat
                # "every reflection is sign-coherent", without the mirror hypothesis
                neg.setdefault("PCc_without_mirror_hyp", [0, 0])
                neg["PCc_without_mirror_hyp"][0] += 1
                if len({sgn(gd.mu[S]) for S in gd.zstar if gd.mu[S]}) > 1:
                    neg["PCc_without_mirror_hyp"][1] += 1
                if mirror_in_A:
                    log.check("[S3refl]", claim == some_nonzero, (name, g))
                    log.check("[PCc-refl]", all(A.dim(S) == 1 for S in gd.zstar))
                else:
                    log.p("  %s: reflection with mirror not in A: Rα flat=%s, nonzero on some cone=%s, "
                          "Z*(g) = %s with mu %s" % (name, is_flat, some_nonzero,
                                                    [A.dim(S) for S in gd.zstar],
                                                    [gd.mu[S] for S in gd.zstar]))
                    neg.setdefault("S3_without_mirror_hyp", [0, 0])
                    neg["S3_without_mirror_hyp"][0] += 1
                    if claim != some_nonzero:
                        neg["S3_without_mirror_hyp"][1] += 1
        # Theorem A on the braid arrangements in coordinates
        if name.startswith("A") and name[1:].isdigit():
            n = d + 1
            rule = typeA_rule_from_matrix(g, n)
            log.check("[A-root]", rule == some_nonzero, (name, g))
    log.p("  pairs (class rep g, g-stable V): %d   chi!=0 %d, Cor.V zeros %d, "
          "no nonzero mu %d, cancellations %d" % (pairs, stats["nonzero"], stats["corV"],
                                                 stats["nomu"], stats["cancel"]))
    return A, stats


def typeA_rule_from_matrix(g, n):
    """Recover eps and w from the y-coordinate matrix; apply the stated rule."""
    d = n - 1
    # lift: x in R^n_0 ; act on e_i - e_n images
    for eps in (1, -1):
        for w in permutations(range(n)):
            ok = True
            for i in range(d):
                x = [0] * n
                x[i] = 1
                gx = [0] * n
                for t in range(n):
                    gx[w[t]] = eps * x[t]
                col = tuple(Fr(gx[r] - gx[n - 1]) for r in range(d))
                if any(g[r][i] != col[r] for r in range(d)):
                    ok = False
                    break
            if ok:
                return stated_rule(cycle_type(w), eps)
    raise AssertionError


def cycle_type(w):
    seen, ct = set(), []
    for i in range(len(w)):
        if i in seen:
            continue
        k, j = 0, i
        while j not in seen:
            seen.add(j)
            j = w[j]
            k += 1
        ct.append(k)
    return sorted(ct, reverse=True)


def stated_rule(ct, eps):
    """Theorem A, in the 'acts freely + mu(ord g)' form AND the explicit form;
    asserts that the two forms agree and returns the common value."""
    from functools import reduce
    ow = reduce(lcm, ct, 1)
    if eps == 1:
        free = all(k == ow for k in ct)
        og = ow
        explicit = len(set(ct)) == 1 and mobius_int(ct[0]) != 0
    else:
        free = len({lcm(2, k) for k in ct}) == 1
        og = lcm(2, ow)
        explicit = any(m % 2 == 1 and mobius_int(m) != 0 and all(k in (m, 2 * m) for k in ct)
                       for m in range(1, max(ct) + 1))
    form1 = free and mobius_int(og) != 0
    assert form1 == explicit, (ct, eps)
    return form1


# ------------------------------------------------------------ type A by partitions


def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def int_partitions(n, m=None):
    if m is None:
        m = n
    if n == 0:
        yield []
        return
    for k in range(min(n, m), 0, -1):
        for p in int_partitions(n - k, k):
            yield [k] + p


def perm_of_type(ct):
    w, start = [], 0
    for k in ct:
        for i in range(k):
            w.append(start + (i + 1) % k)
        start += k
    return w


def typeA_bruteforce(n, ct, eps, parts, checks=None):
    """Some X in Z*(g) with mu_{L^g}(0, X) != 0, by linear algebra in R^n and
    recursion in the fixed partition lattice. Returns (bool, #Z*, mu values)."""
    w = perm_of_type(ct)
    # matrix of g on R^n: g e_i = eps e_{w(i)}
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        M[w[i]][i] = eps
    # Fix(g) inside R^n_0
    rows = [tuple(M[i][j] - int(i == j) for j in range(n)) for i in range(n)] + [tuple([1] * n)]
    U = nullspace(rows, n)
    def stable(p):
        blocks = {frozenset(b) for b in p}
        return all(frozenset(w[i] for i in b) in blocks for b in blocks)
    fixed = []
    for p in parts:
        if stable(p):
            fixed.append(frozenset(frozenset(b) for b in p))
    # basis of X_pi (sum-zero, constant on blocks)
    def basis(p):
        bl = sorted(p, key=lambda b: min(b))
        out = []
        last = bl[-1]
        for b in bl[:-1]:
            v = [0] * n
            for i in b:
                v[i] += len(last)
            for i in last:
                v[i] -= len(b)
            out.append(tuple(v))
        return out
    def coarser_or_eq(p, q):   # p coarser than q  <=>  X_p subset X_q
        return all(any(b <= c for c in p) for b in q)
    # mu(0, X_pi) in L^g: bottom 0 is X_{one block}
    leq = lambda a, b: coarser_or_eq(a, b)
    mu = mobius_from_bottom(fixed, leq)
    zs = []
    for p in fixed:
        B = basis(p)
        if rank(B + U, n) != len(B) + len(U):
            continue
        # X + U inside H_ij ?
        span = B + U
        bad = False
        for i in range(n):
            for j in range(i + 1, n):
                if all(v[i] == v[j] for v in span):
                    bad = True
                    break
            if bad:
                break
        if not bad:
            zs.append(p)
    vals = [mu[p] for p in zs]
    if checks is not None:
        checks["H"] = all(mu[p] == formula_H(w, p) for p in fixed)
        checks["Zchar"] = set(zs) == {p for p in fixed if zstar_combinatorial(w, ct, eps, p)}
        if eps == -1:
            checks["Zchar_noparity"] = set(zs) == {p for p in fixed
                                                   if zstar_combinatorial(w, ct, eps, p, parity=False)}
    return any(v != 0 for v in vals), len(zs), vals


def block_perm_type(w, p):
    """Cycle type of the permutation w-bar induced by w on the blocks of p."""
    blocks = list(p)
    idx = {b: i for i, b in enumerate(blocks)}
    img = [idx[frozenset(w[i] for i in b)] for b in blocks]
    return cycle_type(img)


def formula_H(w, p):
    """(H): mu(Pi_b^{w-bar}) = (-1)^{r-1} mu(l) l^{r-1} (r-1)! if all cycles of
    w-bar have one length l (r = b / l), and 0 otherwise."""
    from math import factorial
    ct = block_perm_type(w, p)
    if len(set(ct)) != 1:
        return 0
    l, r = ct[0], len(ct)
    return (-1) ** (r - 1) * mobius_int(l) * l ** (r - 1) * factorial(r - 1)


def zstar_combinatorial(w, ct, eps, p, parity=True):
    """The combinatorial description of Z*(g) in the proofs of (A+) and (A-)."""
    cyc, pos, start = {}, {}, 0
    for c, k in enumerate(ct):
        for i in range(k):
            cyc[start + i] = c
            pos[start + i] = i
        start += k
    n = len(w)
    if eps == 1:
        # pi meet cyc = 0^: no block holds two points of one cycle
        for b in p:
            if len({cyc[i] for i in b}) != len(b):
                return False
        # pi join cyc = 1^: connectivity of blocks and cycles
        parent = list(range(n))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for b in p:
            b = sorted(b)
            for i in b[1:]:
                parent[find(i)] = find(b[0])
        for i in range(n):
            j = w[i]
            parent[find(i)] = find(j)
        return len({find(i) for i in range(n)}) == 1
    # eps = -1
    if any(l % 2 == 0 for l in block_perm_type(w, p)):
        return False
    for b in p:
        odd_pts = [i for i in b if ct[cyc[i]] % 2 == 1]
        if len(odd_pts) > 1:
            return False
        for i in b:
            for j in b:
                if (parity and i < j and cyc[i] == cyc[j] and ct[cyc[i]] % 2 == 0
                        and (pos[i] - pos[j]) % 2 == 0):
                    return False
    return True


def ord_on_sum_zero(ct, eps):
    n = sum(ct)
    w = perm_of_type(ct)
    # act on R^n / R(1,...,1) (isomorphic to R^n_0 as a <g>-module),
    # coordinates y_r = x_r - x_n, basis the classes of e_1, ..., e_{n-1}
    d = n - 1
    cols = []
    for i in range(d):
        x = [0] * n
        x[i] = 1
        gx = [0] * n
        for t in range(n):
            gx[w[t]] = eps * x[t]
        cols.append(tuple(Fr(gx[r] - gx[n - 1]) for r in range(d)))
    g = tuple(tuple(cols[j][i] for j in range(d)) for i in range(d))
    return mat_order(g)


def run_typeA_partitions(log, nmax, neg, extra=()):
    from functools import reduce
    log.p("Theorem A by set partitions (no arrangement code, no formula (H)):")
    for n in range(3, nmax + 1):
        parts = list(set_partitions(list(range(n))))
        nz_list = []
        for ct in int_partitions(n):
            for eps in (1, -1):
                chk = {}
                got, nzs, vals = typeA_bruteforce(n, ct, eps, parts, chk)
                rule = stated_rule(ct, eps)
                log.check("[A-part]", got == rule, (n, ct, eps))
                log.check("[A-H]", chk["H"], (n, ct, eps))
                log.check("[A-Zchar]", chk["Zchar"], (n, ct, eps))
                if eps == -1:
                    neg.setdefault("A-_drop_parity_condition", [0, 0])
                    neg["A-_drop_parity_condition"][0] += 1
                    if not chk["Zchar_noparity"]:
                        neg["A-_drop_parity_condition"][1] += 1
                    # wrong rule: m squarefree but not required odd
                    wrong = any(mobius_int(m) != 0 and all(k in (m, 2 * m) for k in ct)
                                for m in range(1, max(ct) + 1))
                    neg.setdefault("A-_m_not_odd", [0, 0])
                    neg["A-_m_not_odd"][0] += 1
                    if wrong != got:
                        neg["A-_m_not_odd"][1] += 1
                if eps == 1:
                    # every coefficient equals mu(o) (sign coherence for S_n)
                    o = reduce(lcm, ct, 1)
                    log.check("[A+coef]", all(v == mobius_int(o) for v in vals))
                if got:
                    nz_list.append(("-" if eps < 0 else "") + "(" + ",".join(map(str, ct)) + ")")
        log.p("  n=%d: %d set partitions; classes nonzero on some cone: %s" % (n, len(parts), " ".join(nz_list)))
    for ct in extra:
        n = sum(ct)
        parts = list(set_partitions(list(range(n))))
        chk = {}
        got, nzs, vals = typeA_bruteforce(n, ct, -1, parts, chk)
        log.check("[A-part]", got == stated_rule(ct, -1), (n, ct, -1))
        log.check("[A-H]", chk["H"], (n, ct))
        log.check("[A-Zchar]", chk["Zchar"], (n, ct))
        log.p("  n=%d: -(%s): |Z*(g)| = %d, nonzero on some cone: %s" % (n, ",".join(map(str, ct)), nzs, got))
    # ord(-w) = lcm(2, ord w) on R^n_0
    for n in range(3, min(nmax, 7) + 1):
        for ct in int_partitions(n):
            ow = reduce(lcm, ct, 1)
            log.check("[ord]", ord_on_sum_zero(ct, -1) == lcm(2, ow), (n, ct))
    # negative control: n = 2 breaks it (-(12) is the identity on R^2_0)
    neg.setdefault("ord_n2", [0, 0])
    neg["ord_n2"][0] += 1
    if ord_on_sum_zero([2], -1) != lcm(2, 2):
        neg["ord_n2"][1] += 1


# ------------------------------------------------------------ hand computations, section 6


def hand_checks(log):
    log.p("Section 6 and S2 examples (Coxeter elements, full cone, mu(L(A)^c)):")
    # B3 Coxeter element c: e1 -> e2 -> e3 -> -e1
    N, d, _ = typeB(3)
    A = Arr(N, d, faces=False)
    c = as_mat(((0, 0, -1), (1, 0, 0), (0, 1, 0)))
    gs = Sym(A, c)
    gd = GData(A, gs)
    log.check("[B3c-order]", gs.order == 6)
    log.check("[B3c-fix0]", len(gs.U) == 0)
    c3 = matmul(c, matmul(c, c))
    log.check("[B3c-cube]", c3 == tuple(tuple(-x for x in r) for r in ident(3)))
    ell = A.closure_of_space([(Fr(1), Fr(-1), Fr(1))])
    log.check("[B3c-line]", A.dim(ell) == 1)
    log.check("[B3c-chain]", sorted(A.dim(S) for S in gd.fixed) == [0, 1, 3])
    log.check("[B3c-mu0]", gd.mu[frozenset()] == 0)
    # the B3 Coxeter element given as a product of simple reflections is conjugate:
    cc = coxeter([(1, -1, 0), (0, 1, -1), (0, 0, 1)])
    log.check("[B3c-coxeter]", mat_order(cc) == 6 and GData(A, Sym(A, cc)).mu[frozenset()] == 0)
    # B2 reflection s(x,y) = (-x, y)
    N, d, _ = typeB(2)
    A2 = Arr(N, d)
    s = as_mat(((-1, 0), (0, 1)))
    gs2 = Sym(A2, s)
    full = (1 << A2.nch) - 1
    chi = chi_def(A2, gs2, {})
    log.check("[B2s-full]", chi == -1)
    gd2 = GData(A2, gs2)
    log.check("[B2s-Z*]", [A2.dim(S) for S in gd2.zstar] == [1] and gd2.mu[gd2.zstar[0]] == -1)
    # Coxeter elements of A_n (by permutations), B_n, D_4, F_4: mu(L(A)^c)
    res = {}
    for n in (3, 4, 5, 6):
        Nn, dn, _, pm = braid(n)
        An = Arr(Nn, dn, faces=False)
        cn = pm(list(range(1, n)) + [0])
        g = GData(An, Sym(An, cn))
        res["A%d" % (n - 1)] = (len(Sym(An, cn).U), g.mu[frozenset()])
    for n in (2, 3, 4):
        Nn, dn, _ = typeB(n)
        Bn = Arr(Nn, dn, faces=False)
        simple = []
        for i in range(n - 1):
            v = [0] * n
            v[i], v[i + 1] = 1, -1
            simple.append(tuple(v))
        v = [0] * n
        v[-1] = 1
        simple.append(tuple(v))
        cn = coxeter(simple)
        g = GData(Bn, Sym(Bn, cn))
        res["B%d" % n] = (len(Sym(Bn, cn).U), g.mu[frozenset()])
    Nn, dn, simple = typeD4()
    D4 = Arr(Nn, dn, faces=False)
    cn = coxeter(simple)
    res["D4"] = (len(Sym(D4, cn).U), GData(D4, Sym(D4, cn)).mu[frozenset()])
    Nn, dn, simple = typeF4()
    F4 = Arr(Nn, dn, faces=False)
    cn = coxeter(simple)
    res["F4"] = (len(Sym(F4, cn).U), GData(F4, Sym(F4, cn)).mu[frozenset()])
    for k in sorted(res):
        log.p("  Coxeter element of %s: dim Fix = %d, mu(L(A)^c) = %d" % (k, res[k][0], res[k][1]))
        log.check("[cox-fix0]", res[k][0] == 0)
    vanish = {k for k in res if res[k][1] == 0}
    log.check("[cox-vanish]", vanish == {"A3", "B3", "D4"}, vanish)
    # positive controls: Folkman m(all) = |mu(L(A))|
    for name, Arr_, val in (("B3", A, 15), ("D4", D4, 45), ("F4", F4, 385)):
        mu = mobius_from_bottom(list(Arr_.flats), Arr.leq)[frozenset()]
        log.check("[pos:|mu(L)|]", abs(mu) == val, (name, mu))


def run(quick=False, out=sys.stdout):
    log = Log(out)
    neg = {}
    ex = examples(quick)
    lie4 = None
    for name in ex:
        A, stats = run_arrangement(name, ex[name], log, neg)
        if name == "A3":
            # positive control: chi_all on S_4 classes is the Lie_4 character
            for ct, val in (([1, 1, 1, 1], 6), ([2, 1, 1], 0), ([2, 2], -2), ([3, 1], 0), ([4], 0)):
                _, _, _, pm = braid(4)
                g = pm(perm_of_type(ct))
                log.check("[pos:Lie4]", chi_def(A, Sym(A, g), {}) == val, ct)
        if name == "tri2":
            # the explicit cancellation: upper half-plane cone, s(x,y) = (-x,y)
            s = as_mat(((-1, 0), (0, 1)))
            gs = Sym(A, s)
            cons = {0: 1}
            gd = GData(A, gs)
            log.p("  tri2, V = {y >= 0}, s = (-x, y): chi_def = %d; Z*(V,s) terms (dim X, mu, m_X) = %s"
                  % (chi_def(A, gs, cons),
                     [(A.dim(S), gd.mu[S], gd.m_X(S, cons)) for S in gd.zstar if S >= lineality(A, cons)]))
    run_typeA_partitions(log, 5 if quick else 8, neg,
                         () if quick else ([6, 3], [9], [3, 3, 3], [6, 2, 1]))
    if not quick:
        hand_checks(log)
    log.p("")
    log.p("%-22s %8s %8s" % ("check", "checks", "fails"))
    ok = True
    for tag in sorted(log.counts):
        f = log.fails.get(tag, 0)
        log.p("%-22s %8d %8d" % (tag, log.counts[tag], f))
        if f:
            ok = False
            log.p("   first failure:", log.examples[tag])
    log.p("")
    log.p("negative controls (wrong variants; each must fail at least once):")
    for var in sorted(neg):
        tot, bad = neg[var]
        log.p("  %-24s %6d of %6d differ" % (var, bad, tot))
        if bad == 0:
            ok = False
            log.p("   NEGATIVE CONTROL DID NOT FIRE")
    log.p("")
    log.p("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return ok, log, neg


if __name__ == "__main__":
    ok, _, _ = run(quick="--quick" in sys.argv)
    sys.exit(0 if ok else 1)
