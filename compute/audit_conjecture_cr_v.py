"""Independent audit code for notes/conjecture_cr_v.md.

Plain Python 3, exact arithmetic (Fractions), no third-party packages and no
imports from any other script in compute/.

Methods (chosen to differ from compute/conjecture_cr_v.py where possible):
- faces are found by building covectors hyperplane by hyperplane, each sign
  vector tested for feasibility by exact Fourier-Motzkin elimination;
- top-cones are found by splitting the set of all chambers along hyperplanes;
- M = Lambda(V)^g is built from the zero sets of the faces of V; the lattice
  property, complements and modularity are decided by brute force on the poset;
- chi_V(g) is computed four ways: the definition (-1)^d det(g) mu(M); Formula Z
  of notes/vanishing_criterion.md; Theorem CF of notes/fixed_point_formula.md
  (g-fixed chambers of localizations); and, for selected pairs, the trace of g
  on the top reduced homology of the order complex of the proper part of
  Lambda(V) (all of Lambda(V), not only its g-fixed part), by linear algebra.

Usage:
    python3 audit_conjecture_cr_v.py            # everything (about 10-20 min)
    python3 audit_conjecture_cr_v.py --quick    # controls + counterexample
"""

import sys
import itertools
import random
from fractions import Fraction
from math import gcd

F = Fraction


# ---------------------------------------------------------------- linear algebra

def rref(rows, ncols):
    """Row-reduce a list of rows (Fractions). Returns (rows, pivot columns)."""
    m = [list(map(F, r)) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        inv = 1 / m[r][c]
        m[r] = [x * inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
        if r == len(m):
            break
    return m[:r], piv


def rank(rows, ncols):
    return len(rref(rows, ncols)[1]) if rows else 0


def nullspace(rows, ncols):
    """Basis (list of vectors) of {x : rows . x = 0}."""
    if not rows:
        return [[F(int(i == j)) for j in range(ncols)] for i in range(ncols)]
    m, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [F(0)] * ncols
        v[f] = F(1)
        for i, c in enumerate(piv):
            v[c] = -m[i][f]
        basis.append(v)
    return basis


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def matvec(A, v):
    return [dot(r, v) for r in A]


def det(A):
    n = len(A)
    m = [list(map(F, r)) for r in A]
    d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if m[i][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for i in range(c + 1, n):
            f = m[i][c] / m[c][c]
            m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return d


def inverse(A):
    n = len(A)
    m, piv = rref([list(A[i]) + [F(int(i == j)) for j in range(n)] for i in range(n)], 2 * n)
    assert piv == list(range(n))
    return [r[n:] for r in m]


def primitive(v):
    """Scale a rational vector to a primitive integer vector (sign kept)."""
    den = 1
    for x in v:
        den = den * F(x).denominator // gcd(den, F(x).denominator)
    w = [int(F(x) * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    return tuple(x // g for x in w) if g else tuple(w)


# ------------------------------------------------------- Fourier-Motzkin feasibility

def strict_feasible(rows, k):
    """Is {y in R^k : r.y > 0 for all r in rows} nonempty? (homogeneous, exact)"""
    rows = {primitive(r) for r in rows}
    for var in range(k):
        if any(all(x == 0 for x in r) for r in rows):
            return False
        pos = [r for r in rows if r[var] > 0]
        neg = [r for r in rows if r[var] < 0]
        new = {r for r in rows if r[var] == 0}
        for p in pos:
            for n in neg:
                new.add(primitive([-n[var] * a + p[var] * b for a, b in zip(p, n)]))
        rows = new
    return not rows


def feasible(normals, signs):
    """Is the sign vector `signs` (on the first len(signs) normals) realized?"""
    d = len(normals[0])
    eqs = [normals[i] for i, s in enumerate(signs) if s == 0]
    B = nullspace(eqs, d)            # columns of a basis of the zero space
    k = len(B)
    rows = []
    for i, s in enumerate(signs):
        if s != 0:
            rows.append([s * dot(normals[i], b) for b in B])
    if k == 0:
        return not rows
    return strict_feasible(rows, k)


# ------------------------------------------------------------------ arrangements

class Arrangement:
    def __init__(self, normals, name=""):
        self.name = name
        self.normals = [tuple(map(F, n)) for n in normals]
        self.n = len(normals)
        self.d = len(normals[0])
        prims = [primitive(n) for n in self.normals]
        negs = {tuple(-x for x in p) for p in prims}
        assert len(set(prims)) == self.n and not (set(prims) & negs), "repeated hyperplane"
        assert rank(self.normals, self.d) == self.d, "not essential"
        self._covectors()
        self._flats()

    def _covectors(self):
        covs = [()]
        for i in range(self.n):
            new = []
            for c in covs:
                for s in (0, 1, -1):
                    if feasible(self.normals[:i + 1], c + (s,)):
                        new.append(c + (s,))
            covs = new
        self.covectors = covs
        self.chambers = [c for c in covs if 0 not in c]
        self.chamber_index = {c: i for i, c in enumerate(self.chambers)}
        # bitmasks
        self.cov_masks = []
        for c in covs:
            p = sum(1 << i for i, s in enumerate(c) if s > 0)
            m = sum(1 << i for i, s in enumerate(c) if s < 0)
            z = sum(1 << i for i, s in enumerate(c) if s == 0)
            self.cov_masks.append((p, m, z))

    def zero_space(self, zmask):
        rows = [self.normals[i] for i in range(self.n) if zmask >> i & 1]
        return nullspace(rows, self.d)

    def closure(self, vecs):
        """Zero mask of cl(span vecs): all hyperplanes containing the vectors."""
        return sum(1 << i for i in range(self.n)
                   if all(dot(self.normals[i], v) == 0 for v in vecs))

    def _flats(self):
        full = (1 << self.n) - 1
        flats = {0: self.d}      # zero mask -> dim ; mask 0 is R^d
        frontier = [0]
        while frontier:
            nxt = []
            for z in frontier:
                for i in range(self.n):
                    if not z >> i & 1:
                        sp = self.zero_space(z | (1 << i))
                        c = self.closure(sp)
                        if c not in flats:
                            flats[c] = len(sp)
                            nxt.append(c)
            frontier = nxt
        self.flats = flats
        self.bottom = full_mask = self.closure([[F(0)] * self.d])
        assert flats.get(full_mask) == 0
        # every covector zero set must be a flat
        for (_, _, z) in self.cov_masks:
            assert z in flats

    @staticmethod
    def leq(x, y):
        """flat x <= flat y (as subspaces) iff zero(y) subset of zero(x)."""
        return y & ~x == 0

    def top_cones(self):
        """All top-cones, as frozensets of chamber indices."""
        allc = frozenset(range(len(self.chambers)))
        seen = {allc}
        stack = [allc]
        while stack:
            V = stack.pop()
            for e in range(self.n):
                plus = frozenset(c for c in V if self.chambers[c][e] > 0)
                if plus and len(plus) < len(V):
                    for W in (plus, V - plus):
                        if W not in seen:
                            seen.add(W)
                            stack.append(W)
        return sorted(seen, key=lambda V: (-len(V), sorted(V)))


class Sym:
    """A finite-order linear symmetry g of an arrangement."""

    def __init__(self, arr, g):
        self.arr = arr
        self.g = [list(map(F, r)) for r in g]
        d = arr.d
        gi = inverse(self.g)
        prim = {primitive(n): (i, 1) for i, n in enumerate(arr.normals)}
        prim.update({tuple(-x for x in primitive(n)): (i, -1) for i, n in enumerate(arr.normals)})
        self.perm, self.sign = [], []
        for n in arr.normals:
            m = [sum(n[k] * gi[k][j] for k in range(d)) for j in range(d)]   # n g^{-1}
            j, s = prim[primitive(m)]
            self.perm.append(j)
            self.sign.append(s)
        self.det = det(self.g)
        self.U = nullspace([[self.g[i][j] - (i == j) for j in range(d)] for i in range(d)], d)
        self.dimU = len(self.U)

    def act_cov(self, c):
        out = [0] * len(c)
        for e, s in enumerate(c):
            out[self.perm[e]] = s * self.sign[e]
        return tuple(out)

    def act_mask(self, z):
        out = 0
        for e in range(self.arr.n):
            if z >> e & 1:
                out |= 1 << self.perm[e]
        return out

    def chamber_perm(self):
        A = self.arr
        return [A.chamber_index[self.act_cov(c)] for c in A.chambers]


def group_closure(gens):
    gens = [tuple(tuple(F(x) for x in r) for r in g) for g in gens]
    d = len(gens[0])
    I = tuple(tuple(F(int(i == j)) for j in range(d)) for i in range(d))
    G = {I}
    frontier = [I]
    while frontier:
        nxt = []
        for a in frontier:
            for g in gens:
                b = tuple(tuple(r) for r in matmul([list(r) for r in a], [list(r) for r in g]))
                if b not in G:
                    G.add(b)
                    nxt.append(b)
        frontier = nxt
    return [[list(r) for r in g] for g in G]


def conj_classes(G):
    key = lambda g: tuple(tuple(r) for r in g)
    rest = {key(g): g for g in G}
    invs = {key(g): inverse(g) for g in G}
    reps = []
    while rest:
        k, g = next(iter(rest.items()))
        reps.append(g)
        for h in G:
            c = key(matmul(matmul(h, g), invs[key(h)]))
            rest.pop(c, None)
    return reps


# ----------------------------------------------------------------- posets / lattices

def mobius_from_bottom(elems, leq, bot):
    """mu(bot, x) for all x in elems; elems sorted so that x<y implies x first."""
    mu = {}
    for x in elems:
        if x == bot:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if leq(y, x) and y != x and leq(bot, y))
    return mu


def mobius_interval(elems, leq, a, b):
    sub = [x for x in elems if leq(a, x) and leq(x, b)]
    return mobius_from_bottom(sub, leq, a)[b]


class Lattice:
    """A finite poset given by elements and leq; checks it is a lattice."""

    def __init__(self, elems, leq, rankf):
        self.E = list(elems)
        self.leq = leq
        self.rk = rankf
        N = len(self.E)
        self.le = [[leq(self.E[i], self.E[j]) for j in range(N)] for i in range(N)]
        self.bot = next(i for i in range(N) if all(self.le[i][j] for j in range(N)))
        self.top = next(i for i in range(N) if all(self.le[j][i] for j in range(N)))
        self.join = [[None] * N for _ in range(N)]
        self.meet = [[None] * N for _ in range(N)]
        self.is_lattice = True
        for i in range(N):
            for j in range(N):
                ub = [k for k in range(N) if self.le[i][k] and self.le[j][k]]
                mins = [k for k in ub if all(self.le[k][l] for l in ub)]
                lb = [k for k in range(N) if self.le[k][i] and self.le[k][j]]
                maxs = [k for k in lb if all(self.le[l][k] for l in lb)]
                if len(mins) != 1 or len(maxs) != 1:
                    self.is_lattice = False
                    return
                self.join[i][j] = mins[0]
                self.meet[i][j] = maxs[0]

    def mu(self):
        order = sorted(range(len(self.E)), key=lambda i: self.rk(self.E[i]))
        mu = {}
        for x in order:
            mu[x] = 1 if x == self.bot else -sum(mu[y] for y in mu if self.le[y][x] and y != x)
        return mu[self.top]

    def complements(self, i):
        return [j for j in range(len(self.E))
                if self.meet[i][j] == self.bot and self.join[i][j] == self.top]

    def uncomplemented(self):
        return [i for i in range(len(self.E)) if not self.complements(i)]

    def is_modular(self):
        N = len(self.E)
        for x in range(N):
            for z in range(N):
                if not self.le[x][z]:
                    continue
                for y in range(N):
                    if self.join[x][self.meet[y][z]] != self.meet[self.join[x][y]][z]:
                        return False
        return True


# ------------------------------------------------------------------- per-pair data

class Pair:
    """(A, V, g): everything the audit needs."""

    def __init__(self, arr, V, sym):
        self.arr, self.V, self.sym = arr, V, sym
        A = arr
        n, d = A.n, A.d
        chs = [A.chambers[c] for c in V]
        self.smax = {e: chs[0][e] for e in range(n) if all(c[e] == chs[0][e] for c in chs)}
        sp = sum(1 << e for e, s in self.smax.items() if s > 0)
        sm = sum(1 << e for e, s in self.smax.items() if s < 0)
        self.sp, self.sm = sp, sm
        # faces of V and Lambda(V)
        self.face_ids = [k for k, (p, m, z) in enumerate(A.cov_masks) if not (m & sp) and not (p & sm)]
        self.Lam = sorted({A.cov_masks[k][2] for k in self.face_ids}, key=lambda z: A.flats[z])
        # lineality space L = intersection of S_max hyperplanes
        self.Lmask = A.closure(A.zero_space(sp | sm))
        self.dimL = A.flats[self.Lmask]
        self.M = [z for z in self.Lam if sym.act_mask(z) == z]
        self.lat = Lattice(self.M, A.leq, lambda z: A.flats[z])
        assert self.lat.is_lattice, "Lambda(V)^g is not a lattice"
        self.mu = self.lat.mu()
        self.chi = (-1) ** d * sym.det * self.mu
        self.unc = [self.M[i] for i in self.lat.uncomplemented()]

    # helpers
    def in_hyperplane(self, vecs):
        A = self.arr
        return any(all(dot(A.normals[e], v) == 0 for v in vecs) for e in range(A.n))

    def flat_basis(self, z):
        return self.arr.zero_space(z)

    def dim_sum(self, X, Y):
        vs = X + Y
        return rank(vs, self.arr.d) if vs else 0

    def fixed_chambers(self):
        p = self.sym.chamber_perm()
        return sum(1 for c in self.V if p[c] == c)

    def in_V_cone(self, x):
        A = self.arr
        return all(s * dot(A.normals[e], x) >= 0 for e, s in self.smax.items())


def restricted_cone_data(arr, smax, Xmask, Ubasis, want_interior_test=False):
    """For X in Z*: the arrangement B_X = {H cap U : H contains X} on U and the
    cone C = |V| cap U. Returns (m_X, number of chambers of B_X in C, B, cone)."""
    k = len(Ubasis)
    if k == 0:
        return 1, 1, None, None
    traces = {}
    for e in range(arr.n):
        if Xmask >> e & 1:
            t = [dot(arr.normals[e], b) for b in Ubasis]
            assert any(t), "U inside a hyperplane through X"
            p = primitive(t)
            q = tuple(-x for x in p)
            if p not in traces and q not in traces:
                traces[p] = []
            key = p if p in traces else q
            traces[key].append(e)
    keys = list(traces)
    B = Arrangement(keys, "restriction")
    cons = {}
    for e, s in smax.items():
        t = primitive([dot(arr.normals[e], b) for b in Ubasis])
        if t in traces:
            j, sg = keys.index(t), 1
        else:
            j, sg = keys.index(tuple(-x for x in t)), -1
        assert cons.get(j, s * sg) == s * sg
        cons[j] = s * sg
    Vc = frozenset(i for i, c in enumerate(B.chambers) if all(c[j] == s for j, s in cons.items()))
    assert Vc
    one = Sym(B, [[F(int(i == j)) for j in range(k)] for i in range(k)])
    P = Pair(B, Vc, one)
    m = (-1) ** k * P.mu
    return m, len(Vc), B, cons


def formula_Z(P):
    """Formula Z of notes/vanishing_criterion.md. Returns (value, terms)."""
    A, g = P.arr, P.sym
    stable = sorted([z for z in A.flats if g.act_mask(z) == z], key=lambda z: A.flats[z])
    mu0 = mobius_from_bottom(stable, A.leq, A.bottom)
    terms = []
    for X in stable:
        if not A.leq(X, P.Lmask):
            continue
        BX = A.zero_space(X)
        if P.dim_sum(BX, g.U) != len(BX) + g.dimU:      # X cap U != 0
            continue
        if P.in_hyperplane(BX + g.U):
            continue
        m, _, _, _ = restricted_cone_data(A, P.smax, X, g.U)
        terms.append((A.flats[X], mu0[X], m))
    return sum(mu * m for _, mu, m in terms), terms


def formula_CF(P):
    """Theorem CF of notes/fixed_point_formula.md: sum over g-stable flats Y in L
    of mu_{L^g}(0, Y) times the number of g-fixed chambers of A_Y inside |V|."""
    A, g = P.arr, P.sym
    LG = sorted([z for z in A.flats if g.act_mask(z) == z and A.leq(z, P.Lmask)],
                key=lambda z: A.flats[z])
    mu = mobius_from_bottom(LG, A.leq, A.bottom)
    total = 0
    for Y in LG:
        idx = [e for e in range(A.n) if Y >> e & 1]
        Ks = {tuple(c[e] for e in idx) for c in A.chambers}
        pos = {e: i for i, e in enumerate(idx)}
        cnt = 0
        for K in Ks:
            if any(K[pos[e]] != s for e, s in P.smax.items()):
                continue
            gK = [0] * len(idx)
            for e in idx:
                gK[pos[g.perm[e]]] = K[pos[e]] * g.sign[e]
            if tuple(gK) == K:
                cnt += 1
        total += mu[Y] * cnt
    return total


def homology_trace(P):
    """Trace of g on the top reduced homology of the order complex of the proper
    part of Lambda(V) (all of it), d >= 3. Returns (dim H, trace)."""
    A, g = P.arr, P.sym
    d = A.d
    prop = [z for z in P.Lam if z != A.bottom and z != 0]
    # maximal chains of length d-1 (top simplices, dimension d-2); in Lambda(V)
    # the proper part has ranks 1..d-1 and every chain has distinct dims
    bydim = {}
    for z in prop:
        bydim.setdefault(A.flats[z], []).append(z)

    def chains(k):   # chains with k elements, all ranks? no: any k-subsets ordered
        out = []

        def ext(ch):
            if len(ch) == k:
                out.append(tuple(ch))
                return
            last = ch[-1] if ch else None
            for z in prop:
                if last is None or (z != last and A.leq(last, z) and A.flats[z] > A.flats[last]):
                    ext(ch + [z])
        ext([])
        return out

    top = chains(d - 1)
    low = chains(d - 2)
    li = {c: i for i, c in enumerate(low)}
    # boundary matrix rows = low chains, cols = top chains
    cols = []
    for c in top:
        col = {}
        for i in range(len(c)):
            f = c[:i] + c[i + 1:]
            col[li[f]] = col.get(li[f], 0) + (-1) ** i
        cols.append(col)
    # kernel of boundary: solve over Q
    rows = [[F(0)] * len(top) for _ in range(len(low))]
    for j, col in enumerate(cols):
        for i, v in col.items():
            rows[i][j] = F(v)
    rows = [r for r in rows if any(r)]
    m, piv = rref(rows, len(top)) if rows else ([], [])
    free = [c for c in range(len(top)) if c not in piv]
    basis = []
    for f in free:
        v = [F(0)] * len(top)
        v[f] = F(1)
        for i, c in enumerate(piv):
            v[c] = -m[i][f]
        basis.append(v)
    ti = {c: i for i, c in enumerate(top)}
    gimg = [ti[tuple(g.act_mask(z) for z in c)] for c in top]   # g preserves order, sign +1
    tr = F(0)
    for f, v in zip(free, basis):
        w = [F(0)] * len(top)
        for j, x in enumerate(v):
            if x:
                w[gimg[j]] += x
        tr += w[f]      # coordinate of g v on the basis vector with free index f
    return len(basis), tr


# ------------------------------------------------------------- example arrangements

def braid(n):
    """A_{n-1} essentialized in coordinates y on the sum-zero subspace of R^n
    (basis b_i = e_i - e_n, i < n), with the group +-S_n."""
    k = n - 1
    Bm = [[F(int(i == j)) - F(int(i == n - 1)) for j in range(k)] for i in range(n)]  # n x k
    normals = []
    for i in range(n):
        for j in range(i + 1, n):
            normals.append([Bm[i][c] - Bm[j][c] for c in range(k)])
    BtB = matmul([list(r) for r in zip(*Bm)], Bm)
    pinv = matmul(inverse(BtB), [list(r) for r in zip(*Bm)])

    def perm_mat(p):
        Pm = [[F(int(p[j] == i)) for j in range(n)] for i in range(n)]
        return matmul(matmul(pinv, Pm), Bm)
    gens = [perm_mat([1, 0] + list(range(2, n))), perm_mat(list(range(1, n)) + [0]),
            [[F(-int(i == j)) for j in range(k)] for i in range(k)]]
    return normals, gens


def signed_perm_gens(d):
    gens = []
    for i in range(d - 1):
        gens.append([[F(int((r == i and c == i + 1) or (r == i + 1 and c == i) or
                            (r == c and r not in (i, i + 1)))) for c in range(d)] for r in range(d)])
    gens.append([[F(-1 if (r == c == 0) else int(r == c)) for c in range(d)] for r in range(d)])
    return gens


def B_arr(d):
    normals = [[int(i == j) for j in range(d)] for i in range(d)]
    for i in range(d):
        for j in range(i + 1, d):
            for s in (1, -1):
                normals.append([int(k == i) + s * int(k == j) for k in range(d)])
    return normals


def orbit_arrangement(seeds, G):
    """Hyperplanes {n g^{-1}} for n in seeds, g in G (normals up to sign)."""
    out = {}
    for n in seeds:
        for g in G:
            gi = inverse(g)
            m = primitive([sum(F(n[k]) * gi[k][j] for k in range(len(n))) for j in range(len(n))])
            q = tuple(-x for x in m)
            if m not in out and q not in out:
                out[m] = 1
    return [list(k) for k in out]


def blockdiag(*Ms):
    d = sum(len(M) for M in Ms)
    out = [[F(0)] * d for _ in range(d)]
    o = 0
    for M in Ms:
        for i in range(len(M)):
            for j in range(len(M)):
                out[o + i][o + j] = F(M[i][j])
        o += len(M)
    return out


R6 = [[1, -1], [1, 0]]          # order 6 on Z^2 (acting on column vectors)
ROT4 = [[0, -1], [1, 0]]


def c6c4():
    normals = []
    for u in [(1, 3), (2, -1), (3, 2)]:
        for w in [(1, 0), (-1, 0), (0, 1), (0, -1)]:
            normals.append(list(u) + list(w))
    # the group acts on points; the forms (u, w) transform as row vectors by g^{-1};
    # take the point action a = (R6^{-T}) + I, b = I + ROT4^{-T}
    a = blockdiag([list(r) for r in zip(*inverse([[F(x) for x in r] for r in R6]))], [[1, 0], [0, 1]])
    b = blockdiag([[1, 0], [0, 1]], [list(r) for r in zip(*inverse([[F(x) for x in r] for r in ROT4]))])
    return normals, [a, b]


# ---------------------------------------------------------------- the audit itself

FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("  FAIL:", msg)


def counterexample():
    print("== [CX] the counterexample of section 0 ==")
    normals, gens = c6c4()
    A = Arrangement(normals, "C6xC4")
    G = group_closure(gens)
    print("  hyperplanes", A.n, "faces", len(A.covectors), "chambers", len(A.chambers),
          "flats", len(A.flats), "|G| =", len(G))
    for g in G:
        Sym(A, g)            # raises if g does not preserve A
    g = [[F(-1), 0, 0, 0], [0, F(-1), 0, 0], [0, 0, F(1), 0], [0, 0, 0, F(1)]]
    gl = [list(map(F, r)) for r in g]
    check(any(h == gl for h in G), "g in the group")
    sym = Sym(A, g)
    # V = {x4 <= x1 + 3 x2 <= -x4}: halfspaces of H_{(1,3),(0,-1)} and H_{(1,3),(0,1)}
    e1 = normals.index([1, 3, 0, -1])   # x1+3x2-x4 >= 0
    e2 = normals.index([1, 3, 0, 1])    # x1+3x2+x4 <= 0
    V = frozenset(i for i, c in enumerate(A.chambers) if c[e1] > 0 and c[e2] < 0)
    check(V in set(A.top_cones()), "(a) V is a top-cone")
    p = sym.chamber_perm()
    check(frozenset(p[c] for c in V) == V, "(a) gV = V")
    P = Pair(A, V, sym)
    print("  |V| =", len(V), "chambers; S_max =", sorted(P.smax.items()), "dim L =", P.dimL)
    check(sorted(P.smax) == sorted([e1, e2]), "S_max is exactly the two facet hyperplanes")
    # (b) the lattice
    print("  M = Lambda(V)^g has", len(P.M), "elements:")
    names = {}
    for z in P.M:
        B = A.zero_space(z)
        names[z] = "dim%d span%s" % (len(B), [list(map(int, primitive(b))) for b in B])
        print("    ", names[z])
    check(len(P.M) == 9, "(b) |M| = 9")
    check(P.lat.is_lattice, "(b) M is a lattice")
    lat = P.lat
    for i, z in enumerate(P.M):
        comps = [names[P.M[j]] for j in lat.complements(i)]
        print("     complements of", names[z], "->", comps[:3], "..." if len(comps) > 3 else "")
    check(not P.unc, "(b) every element of M has a complement")
    check(not lat.is_modular(), "(c) M is not modular")
    print("  mu(M) =", P.mu, " det g =", sym.det, " chi(def) =", P.chi)
    check(P.chi == 0, "(d) chi = 0 by definition")
    z, terms = formula_Z(P)
    print("  Formula Z: terms (dim X, mu, m_X) =", terms, " sum =", z)
    check(z == 0, "(d) Formula Z gives 0")
    cf = formula_CF(P)
    print("  Theorem CF (fixed chambers of localizations) =", cf)
    check(cf == 0, "(d) CF gives 0")
    h, tr = homology_trace(P)
    print("  order complex of proper part of Lambda(V) (|Lambda(V)| = %d): dim H_2 = %d, "
          "trace of g = %s" % (len(P.Lam), h, tr))
    check(tr == 0, "(d) trace of g on H_2 is 0")
    # m(V) by Theorem 1 equals dim H_{d-2}
    Pone = Pair(A, V, Sym(A, [[F(int(i == j)) for j in range(4)] for i in range(4)]))
    check(h == Pone.mu * (-1) ** 4, "dim H_2 = m(V)")
    # face-level Lefschetz identity (2.2) of [FP]
    fixedV = P.fixed_chambers()
    Lg = [zz for zz in P.M if A.leq(zz, P.Lmask)]
    rhs = 0
    for X in Lg:
        BX = A.zero_space(X)
        dX = len(BX)
        # det(g|_X): g maps X to X; matrix in basis BX
        gB = [matvec(sym.g, b) for b in BX]
        coords = []
        for w in gB:
            m_, piv = rref([list(r) for r in zip(*(BX + [w]))], dX + 1)
            # solve BX c = w
            sol = [F(0)] * dX
            for r, c in zip(m_, piv):
                if c < dX:
                    sol[c] = r[dX]
            coords.append(sol)
        dgX = det([list(r) for r in zip(*coords)]) if dX else 1
        rhs += (-1) ** dX * dgX * mobius_interval(P.M, A.leq, X, 0)
    print("  (2.2): (-1)^d det g #V^g =", fixedV * sym.det, " RHS =", rhs)
    check(fixedV * sym.det == rhs, "(2.2) of [FP] on the counterexample")
    # direct fixed-face Lefschetz count f_g(Y) on each Y in M (eq. (2.1) of [FP])
    for Y in P.M:
        fg = 0
        for k in P.face_ids:
            c = A.covectors[k]
            if not A.leq(A.cov_masks[k][2], Y):
                continue
            if sym.act_cov(c) != c:
                continue
            S = A.cov_masks[k][2]
            BS = A.zero_space(S)
            gB = [matvec(sym.g, b) for b in BS]
            coords = []
            for w in gB:
                m_, piv = rref([list(r) for r in zip(*(BS + [w]))], len(BS) + 1)
                sol = [F(0)] * len(BS)
                for r, cc in zip(m_, piv):
                    if cc < len(BS):
                        sol[cc] = r[len(BS)]
                coords.append(sol)
            dg = det([list(r) for r in zip(*coords)]) if BS else 1
            fg += (-1) ** len(BS) * dg
        exp = 0
        # compute det(g|Y) for expectation
        if A.leq(Y, P.Lmask):
            BY = A.zero_space(Y)
            gB = [matvec(sym.g, b) for b in BY]
            coords = []
            for w in gB:
                m_, piv = rref([list(r) for r in zip(*(BY + [w]))], len(BY) + 1)
                sol = [F(0)] * len(BY)
                for r, cc in zip(m_, piv):
                    if cc < len(BY):
                        sol[cc] = r[len(BY)]
                coords.append(sol)
            exp = (-1) ** len(BY) * (det([list(r) for r in zip(*coords)]) if BY else 1)
        check(fg == exp, "(2.1) f_g(Y) on %s" % names[Y])
    print("  fixed-face Lefschetz numbers f_g(Y) agree with (2.1) on all 9 Y")
    print("  #V^g =", fixedV, "; U lies in a hyperplane:", P.in_hyperplane(sym.U),
          "; dim L cap U =", len(P.flat_basis(P.Lmask)) + sym.dimU - P.dim_sum(P.flat_basis(P.Lmask), sym.U))
    return A, G


def controls():
    print("== [CTL] positive controls ==")
    # A_3 on all chambers: Lie_4 character 6, 0, -2, 0, 0 at e, (12), (12)(34), (123), (1234)
    normals, gens = braid(4)
    A = Arrangement(normals, "A3")
    allc = frozenset(range(len(A.chambers)))

    def perm_y(p):
        n = 4
        k = 3
        Bm = [[F(int(i == j)) - F(int(i == n - 1)) for j in range(k)] for i in range(n)]
        BtB = matmul([list(r) for r in zip(*Bm)], Bm)
        pinv = matmul(inverse(BtB), [list(r) for r in zip(*Bm)])
        Pm = [[F(int(p[j] == i)) for j in range(n)] for i in range(n)]
        return matmul(matmul(pinv, Pm), Bm)
    vals = []
    for p in ([0, 1, 2, 3], [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0]):
        P = Pair(A, allc, Sym(A, perm_y(p)))
        vals.append(P.chi)
    print("  A3 all chambers, chi at e,(12),(12)(34),(123),(1234):", vals)
    check(vals == [6, 0, -2, 0, 0], "Lie_4 character")
    # A_2: Lie_3 = 2, 0, -1; and -s_12 cancels on all chambers with terms (0,1,1),(1,-1,1)
    normals, gens = braid(3)
    A2 = Arrangement(normals, "A2")
    allc = frozenset(range(len(A2.chambers)))

    def perm3(p, sgn=1):
        n, k = 3, 2
        Bm = [[F(int(i == j)) - F(int(i == n - 1)) for j in range(k)] for i in range(n)]
        BtB = matmul([list(r) for r in zip(*Bm)], Bm)
        pinv = matmul(inverse(BtB), [list(r) for r in zip(*Bm)])
        Pm = [[F(sgn * int(p[j] == i)) for j in range(n)] for i in range(n)]
        return matmul(matmul(pinv, Pm), Bm)
    vals = [Pair(A2, allc, Sym(A2, perm3(p))).chi for p in ([0, 1, 2], [1, 0, 2], [1, 2, 0])]
    print("  A2 all chambers, chi at e,(12),(123):", vals)
    check(vals == [2, 0, -1], "Lie_3 character")
    P = Pair(A2, allc, Sym(A2, perm3([1, 0, 2], -1)))
    z, terms = formula_Z(P)
    print("  A2, g = -s12, all chambers: chi =", P.chi, " Formula Z terms", sorted(terms),
          " fixed chambers", P.fixed_chambers())
    check(P.chi == 0 and sorted(terms) == [(0, 1, 1), (1, -1, 1)] and P.fixed_chambers() == 2,
          "A2 -s12 cancellation of [VC] section 5")
    # B_2 reflection: chi = -1 on all chambers
    B2 = Arrangement(B_arr(2), "B2")
    s = [[F(-1), 0], [0, F(1)]]
    P = Pair(B2, frozenset(range(len(B2.chambers))), Sym(B2, s))
    print("  B2 reflection, all chambers: chi =", P.chi)
    check(P.chi == -1, "B2 reflection chi = -1 ([VC] section 6)")
    # B_3 Coxeter element vanishes on every cone ([VC] section 6)
    B3 = Arrangement(B_arr(3), "B3")
    c = [[F(0), F(0), F(-1)], [F(1), 0, 0], [0, F(1), 0]]     # signed 3-cycle, one sign change
    sym = Sym(B3, c)
    p = sym.chamber_perm()
    vals = set()
    for V in B3.top_cones():
        if frozenset(p[x] for x in V) == V:
            vals.add(Pair(B3, V, sym).chi)
    print("  B3 Coxeter element (order", order(c), "), values on all stable cones:", vals)
    check(vals == {0}, "B3 Coxeter element vanishes on every cone")
    # pair counts of [PCV] section 4 (class representatives, every g-stable cone)
    for name, (normals, gens), exp in [
            ("A2 (+-S3)", braid(3), (30, 24)),
            ("A3 (+-S4)", braid(4), (300, 266)),
            ("B2", (B_arr(2), signed_perm_gens(2)), (45, 41)),
            ("B3", (B_arr(3), signed_perm_gens(3)), (1106, 998))]:
        A = Arrangement(normals, name)
        res = sweep(A, conj_classes(group_closure(gens)), quiet=True)
        print("  %s: pairs %d, chi != 0 %d, complemented %d (non-modular %d), "
              "CR_V counterexamples %d" % (name, res["pairs"], res["nonzero"], res["compl"],
                                          res["compl_nonmod"], res["crv_cex"]))
        check((res["pairs"], res["nonzero"]) == exp, "[PCV] counts for " + name)
        STATS[name] = res
    # homology trace = (-1)^d mu(M) (Baclawski-Bjorner) on all chambers of A3, B3 for every class
    for A, gens in [(Arrangement(braid(4)[0]), braid(4)[1]), (B3, signed_perm_gens(3))]:
        allc = frozenset(range(len(A.chambers)))
        for g in conj_classes(group_closure(gens)):
            P = Pair(A, allc, Sym(A, g))
            h, tr = homology_trace(P)
            check(tr == (-1) ** A.d * P.mu, "homology trace control")
    print("  homology trace equals (-1)^d mu(Lambda^g) on all chambers of A3, B3, every class")


def order(g):
    d = len(g)
    I = [[F(int(i == j)) for j in range(d)] for i in range(d)]
    h, k = [list(map(F, r)) for r in g], 1
    while h != I:
        h = matmul(h, [list(map(F, r)) for r in g])
        k += 1
    return k


STATS = {}


def classify_R3(A, g, sym):
    """Lemma R3 table data for g = +-(reflection) in rank 3."""
    d = 3
    Pm = nullspace([[sym.g[i][j] - (i == j) for j in range(d)] for i in range(d)], d)
    Mm = nullspace([[sym.g[i][j] + (i == j) for j in range(d)] for i in range(d)], d)
    if len(Pm) + len(Mm) != 3 or {len(Pm), len(Mm)} != {1, 2}:
        return None
    E, Ep = (Pm, Mm) if len(Pm) == 2 else (Mm, Pm)
    flats = A.flats
    lines_in_E = [z for z, k in flats.items() if k == 1 and rank(E + A.zero_space(z), 3) == 2]
    planes_cont_Ep = [z for z, k in flats.items() if k == 2 and rank(A.zero_space(z) + Ep, 3) == 2]
    e = int(A.closure(E) in flats and flats[A.closure(E)] == 2)
    ep = int(flats[A.closure(Ep)] == 1)
    a, p = len(lines_in_E), len(planes_cont_Ep)
    lam = 0
    for P_ in planes_cont_Ep:
        Q = nullspace(_perp(A.zero_space(P_)) + _perp(E), 3)     # P cap E
        if len(Q) == 1 and flats.get(A.closure(Q)) == 1:
            lam += 1
    return e, ep, a, p, lam


def _perp(B):
    return nullspace([list(b) for b in B], 3)


def sweep(A, gs, quiet=False, rank3_checks=False, cone_filter=None):
    """All pairs (g in gs, g-stable top-cone V). Checks every proven statement."""
    res = dict(pairs=0, nonzero=0, zeros=0, compl=0, compl_nonmod=0, crv_cex=0, cex=[],
               P=0, Q=0, K=0, Ln_iv=0, Ln=0, R3=0, thm3_L=0, Z=0, CF=0, F=0, dimL2=0)
    cones = A.top_cones()
    d = A.d
    for g in gs:
        sym = Sym(A, g)
        p = sym.chamber_perm()
        U = sym.U
        clU = A.closure(U)
        Uhyp = any(clU >> e & 1 for e in range(A.n))
        for V in cones:
            if frozenset(p[x] for x in V) != V:
                continue
            if cone_filter and not cone_filter(V):
                continue
            P = Pair(A, V, sym)
            res["pairs"] += 1
            chi = P.chi
            lat = P.lat
            idx = {z: i for i, z in enumerate(P.M)}
            if chi:
                res["nonzero"] += 1
            else:
                res["zeros"] += 1
            complemented = not P.unc
            if complemented:
                res["compl"] += 1
                if not lat.is_modular():
                    res["compl_nonmod"] += 1
                if chi == 0:
                    res["crv_cex"] += 1
                    res["cex"].append((g, V, len(P.M), P.dimL))
            else:
                check(chi == 0, "Crapo: uncomplemented element forces chi = 0")
            # Formula Z and CF
            z, terms = formula_Z(P)
            check(z == chi, "Formula Z on %s" % A.name)
            res["Z"] += 1
            if d <= 3 or res["pairs"] % 7 == 0:
                check(formula_CF(P) == chi, "CF on %s" % A.name)
                res["CF"] += 1
            LB = A.zero_space(P.Lmask)
            LUhyp = P.in_hyperplane(LB + U)
            clLU = A.closure(LB + U)
            # Lemma F side claims
            check(clU in idx and clLU in idx, "Lemma F: cl(U), cl(L+U) in M")
            for X in A.flats:
                if A.leq(X, P.Lmask) and sym.act_mask(X) == X:
                    check(X in idx, "Lemma F: stable flats in L lie in M")
            for i, Y in enumerate(P.M):
                if not A.leq(Y, P.Lmask):
                    # a g-fixed face of V, nonzero, inside Y, whose span lies in cl(U)
                    ok = False
                    for k in P.face_ids:
                        zz = A.cov_masks[k][2]
                        if zz == A.bottom or not A.leq(zz, Y) or not A.leq(zz, clU):
                            continue
                        c = A.covectors[k]
                        if sym.act_cov(c) == c:
                            ok = True
                            break
                    check(ok, "Lemma F(a,b)")
            res["F"] += 1
            # Lemma K for every W in M containing U
            for i, W in enumerate(P.M):
                if not A.leq(clU, W):
                    continue
                WB = A.zero_space(W)
                rhs = set()
                for X in A.flats:
                    if sym.act_mask(X) != X or not A.leq(X, P.Lmask):
                        continue
                    XB = A.zero_space(X)
                    if P.dim_sum(XB, WB) != len(XB) + len(WB):
                        continue
                    if P.in_hyperplane(XB + WB):
                        continue
                    rhs.add(X)
                lhs = {P.M[j] for j in lat.complements(i)}
                check(lhs == rhs, "Lemma K")
                res["K"] += 1
            # Theorem Q
            if LUhyp:
                res["Q"] += 1
                check(chi == 0, "Q: chi = 0")
                check(clLU != 0 and not lat.complements(idx[clLU]), "Q: cl(L+U) uncomplemented")
                check(not lat.complements(idx[clU]), "Q: cl(U) uncomplemented")
            # Theorem P
            if P.dimL == 0:
                res["P"] += 1
                if Uhyp:
                    check(chi == 0 and not lat.complements(idx[clU]), "P: hyperplane case")
                else:
                    check(chi == P.fixed_chambers() and chi >= 1, "P: chi = #V^g")
            # Proposition Ln
            if P.dimL == 1:
                res["Ln"] += 1
                LcapU = len(LB) + len(U) - P.dim_sum(LB, U)
                if LUhyp:
                    check(chi == 0, "Ln(i)")
                elif Uhyp:
                    check(LcapU == 0, "Ln(ii) L cap U = 0")
                    mL, _, _, _ = restricted_cone_data(A, P.smax, P.Lmask, U)
                    check(chi == -mL and chi != 0, "Ln(ii) value")
                elif LcapU == 1:
                    m0, _, _, _ = restricted_cone_data(A, P.smax, A.bottom, U)
                    check(chi == m0 and chi >= 1, "Ln(iii)")
                else:
                    res["Ln_iv"] += 1
                    _, c0, B0, cons = restricted_cone_data(A, P.smax, A.bottom, U)
                    _, cL, _, _ = restricted_cone_data(A, P.smax, P.Lmask, U)
                    check(chi == c0 - cL and chi >= 0, "Ln(iv) chi = c0 - cL")
                    # trace criterion: every trace meeting int C is a trace of some H' > L
                    tracesL = set()
                    for e in range(A.n):
                        if P.Lmask >> e & 1:
                            t = primitive([dot(A.normals[e], b) for b in U])
                            tracesL.add(t)
                            tracesL.add(tuple(-x for x in t))
                    crit = True
                    for e in range(A.n):
                        t = [dot(A.normals[e], b) for b in U]
                        if not any(t):
                            continue
                        # meets int C: exists y, t.y = 0, constraints strict
                        rows = []
                        for f, s in P.smax.items():
                            rows.append([s * dot(A.normals[f], b) for b in U])
                        N = nullspace([t], len(U))
                        r2 = [[dot(r, nb) for nb in N] for r in rows]
                        if strict_feasible(r2, len(N)) and primitive(t) not in tracesL:
                            crit = False
                    check((c0 == cL) == crit, "Ln(iv) trace criterion")
                    if d == 3 and chi == 0:
                        check(not lat.complements(idx[P.Lmask]), "Theorem 3: L uncomplemented")
                        res["thm3_L"] += 1
            if d == 3 and P.dimL == 2:
                res["dimL2"] += 1
                check(set(P.Lam) == set(A.flats), "d=3, dim L=2: Lambda(V) = L(A)")
            if d <= 3:
                check((chi == 0) == bool(P.unc), "Theorem 3 (CR_V) in rank <= 3")
    if d == 3 and rank3_checks:
        allc = frozenset(range(len(A.chambers)))
        for g in gs:
            sym = Sym(A, g)
            stable = [z for z in A.flats if sym.act_mask(z) == z]
            lat = Lattice(sorted(stable, key=lambda z: A.flats[z]), A.leq, lambda z: A.flats[z])
            check(lat.is_lattice, "L(A)^g lattice")
            mu = lat.mu()
            check((mu == 0) == bool(lat.uncomplemented()), "Lemma R3")
            res["R3"] += 1
            data = classify_R3(A, g, sym)
            if data:
                e, ep, a, pp, lam = data
                pred = {(1, 1): 1 - pp, (1, 0): 0, (0, 1): a - lam, (0, 0): a + pp - lam - 1}[(e, ep)]
                check(mu == pred, "Lemma R3 table row (e,e')=(%d,%d)" % (e, ep))
                if ep == 0:
                    check(pp <= 1, "R3: e'=0 forces p<=1")
                res.setdefault("R3rows", {}).setdefault((e, ep), 0)
                res["R3rows"][(e, ep)] += 1
    sys.stdout.flush()
    if not quiet:
        print("  %-28s d=%d n=%2d pairs %6d zeros %4d compl %6d (non-mod %6d) CR_V cex %3d | "
              "P %d Q %d K %d Ln %d (iv %d) R3 %d" % (
                  A.name, d, A.n, res["pairs"], res["zeros"], res["compl"], res["compl_nonmod"],
                  res["crv_cex"], res["P"], res["Q"], res["K"], res["Ln"], res["Ln_iv"], res["R3"]))
    return res


def rank3_families():
    """Rank <= 3 arrangements with their groups (every group element is used)."""
    fam = []
    fam.append(("A2 (+-S3)",) + tuple(braid(3)))
    fam.append(("B2",) + (B_arr(2), signed_perm_gens(2)))
    # hexagonal 6 lines in R^2 with D6 x +-1
    R6m = [[F(x) for x in r] for r in R6]
    refl = [[F(0), F(1)], [F(1), F(0)]]
    G = group_closure([R6m, refl])
    fam.append(("hexagon 6 lines R^2 (D6)", orbit_arrangement([(1, 0), (1, 2)], G), [R6m, refl]))
    fam.append(("A3 (+-S4)",) + tuple(braid(4)))
    fam.append(("B3",) + (B_arr(3), signed_perm_gens(3)))
    fam.append(("B3 minus {z=0} (B2 x +-1)", [n for n in B_arr(3) if n != [0, 0, 1]],
                [blockdiag(*[[g[0], g[1]]], [[1]]) for g in signed_perm_gens(2)] +
                [blockdiag([[1, 0], [0, 1]], [[-1]])]))
    fam.append(("A3 minus a plane", None, None))
    # generic 4 planes in R^3 with -1 and a permutation symmetry
    fam.append(("generic 4 (x,y,z,x+y+z) S3x+-1", [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1]],
                [[[0, 1, 0], [1, 0, 0], [0, 0, 1]], [[0, 1, 0], [0, 0, 1], [1, 0, 0]],
                 [[-1, 0, 0], [0, -1, 0], [0, 0, -1]]]))
    # hexagonal prism type: C6 or D6 on (x,y), z -> -z
    for name, seeds, gens in [
        ("C6 x <z->-z> seeds (1,0,1)", [(1, 0, 1)], [blockdiag(R6m, [[1]]), blockdiag([[1, 0], [0, 1]], [[-1]])]),
        ("D6 x <z->-z> seeds (1,0,0),(0,0,1),(1,1,2)", [(1, 0, 0), (0, 0, 1), (1, 1, 2)],
         [blockdiag(R6m, [[1]]), blockdiag(refl, [[1]]), blockdiag([[1, 0], [0, 1]], [[-1]])]),
        ("D4 x <z->-z> seeds (1,0,1),(1,1,0)", [(1, 0, 1), (1, 1, 0)],
         [blockdiag(ROT4, [[1]]), blockdiag(refl, [[1]]), blockdiag([[1, 0], [0, 1]], [[-1]])]),
        ("C3 rotation x +-1 seeds (1,2,0),(1,0,0)", [(1, 2, 0), (1, 0, 0)],
         [[[0, 1, 0], [0, 0, 1], [1, 0, 0]], [[-1, 0, 0], [0, -1, 0], [0, 0, -1]]]),
        ("D3 diag seeds (1,0,0),(1,1,1),(1,-1,0)", [(1, 0, 0), (1, 1, 1), (1, -1, 0)],
         [[[0, 1, 0], [0, 0, 1], [1, 0, 0]], [[0, 1, 0], [1, 0, 0], [0, 0, 1]]]),
        ("C4 x z->-z seeds (1,2,1)", [(1, 2, 1)], [blockdiag(ROT4, [[1]]), blockdiag([[1, 0], [0, 1]], [[-1]])]),
        ("hexagon 12 type: D6 lines + axis seeds (1,0,1),(0,0,1),(1,2,0)", [(1, 0, 1), (0, 0, 1), (1, 2, 0)],
         [blockdiag(R6m, [[1]]), blockdiag(refl, [[-1]])]),
    ]:
        gens = [[[F(x) for x in r] for r in g] for g in gens]
        fam.append((name, orbit_arrangement(seeds, group_closure(gens)), gens))
    return fam


def random_rank3(seed, count):
    """Random small orbit arrangements in R^3 under random finite groups."""
    rnd = random.Random(seed)
    R6m = [[F(x) for x in r] for r in R6]
    refl = [[F(0), F(1)], [F(1), F(0)]]
    zneg = blockdiag([[1, 0], [0, 1]], [[-1]])
    groups = [
        ("D6xz", [blockdiag(R6m, [[1]]), blockdiag(refl, [[1]]), zneg]),
        ("C6", [blockdiag(R6m, [[1]])]),
        ("D4xz", [blockdiag(ROT4, [[1]]), blockdiag(refl, [[1]]), zneg]),
        ("C4z", [blockdiag(ROT4, [[-1]])]),
        ("S3x-1", [[[0, 1, 0], [1, 0, 0], [0, 0, 1]], [[0, 1, 0], [0, 0, 1], [1, 0, 0]],
                   [[-1, 0, 0], [0, -1, 0], [0, 0, -1]]]),
        ("C3", [[[0, 1, 0], [0, 0, 1], [1, 0, 0]]]),
        ("rot6z", [blockdiag(R6m, [[-1]])]),
        ("C2xC2xC2", [blockdiag([[-1, 0], [0, 1]], [[1]]), blockdiag([[1, 0], [0, -1]], [[1]]), zneg]),
    ]
    out = []
    tries = 0
    while len(out) < count and tries < 200:
        tries += 1
        gname, gens = rnd.choice(groups)
        gens = [[[F(x) for x in r] for r in g] for g in gens]
        G = group_closure(gens)
        seeds = [tuple(rnd.randint(-2, 2) for _ in range(3)) for _ in range(rnd.randint(1, 2))]
        seeds = [s for s in seeds if any(s)]
        if not seeds:
            continue
        normals = orbit_arrangement(seeds, G)
        if len(normals) > 12 or rank([list(map(F, n)) for n in normals], 3) < 3:
            continue
        out.append(("random %s seeds %s" % (gname, seeds), normals, gens))
    return out


def main():
    args = set(sys.argv[1:])
    quick = "--quick" in args
    only = args & {"--r3", "--r4"}
    if not only:
        controls()
        counterexample()
    if quick:
        print("ALL CHECKS PASSED" if not FAILS else "FAILURES: %d" % len(FAILS))
        return
    if not only or "--r3" in only:
        rank3_sweep()
    if not only or "--r4" in only:
        rank4_sweep()
    print("ALL CHECKS PASSED" if not FAILS else "FAILURES: %d" % len(FAILS))
    sys.exit(1 if FAILS else 0)


def rank3_sweep():
    print("== [R<=3] exhaustive sweep in rank <= 3, every group element, every stable cone ==")
    tot = dict(pairs=0, zeros=0, P=0, Q=0, K=0, Ln=0, Ln_iv=0, R3=0, thm3_L=0, dimL2=0, crv_cex=0)
    rows3 = {}
    fams = rank3_families() + random_rank3(7, 14)
    for name, normals, gens in fams:
        if normals is None:     # A3 minus a plane: D3 roots minus x1 - x2, group fixing it
            normals = [n for n in braid(4)[0]][1:]
            A = Arrangement(normals, name)
            G = [g for g in group_closure(braid(4)[1]) if _preserves(A, g)]
        else:
            A = Arrangement(normals, name)
            G = group_closure(gens)
        r = sweep(A, G, rank3_checks=True)
        for k in tot:
            tot[k] += r[k]
        for k, v in r.get("R3rows", {}).items():
            rows3[k] = rows3.get(k, 0) + v
    print("  rank<=3 totals:", tot, " R3 table rows exercised:", rows3)


def rank4_sweep():
    print("== [R4] rank 4 ==")
    normals, gens = c6c4()
    A = Arrangement(normals, "R^4 C6 x C4")
    I4 = [[F(int(i == j)) for j in range(4)] for i in range(4)]
    G = [g for g in group_closure(gens) if g != I4]      # g = 1: chi = m(V) >= 1, nothing to test
    print("  C6 x C4: %d top-cones (the g = 1 pairs, skipped)" % len(A.top_cones()))
    r = sweep(A, G)
    fam = {}
    for g, V, m, dL in r["cex"]:
        key = (tuple(int(g[i][i]) for i in range(4)), m, dL)
        fam[key] = fam.get(key, 0) + 1
    print("  CR_V counterexamples by (diag g, |M|, dim L):", fam)
    STATS["c6c4"] = r
    nA, gA = braid(5)
    A4 = Arrangement(nA, "A4 (+-S5) classes")
    r = sweep(A4, [g for g in conj_classes(group_closure(gA)) if g != I4])
    print("  A4: %d top-cones (the g = 1 pairs, skipped)" % len(A4.top_cones()))
    STATS["A4"] = r


def _preserves(A, g):
    try:
        Sym(A, g)
        return True
    except KeyError:
        return False


if __name__ == "__main__":
    main()
