#!/usr/bin/env python3
"""Independent audit of Proposition W' and of Theorem G* for symmetries
outside the reflection group (notes/audit_prop_w_prime.md).

Plain Python 3, no dependencies.  Imports nothing from this repository; in
particular not fixed_point_formula.py or audit_fixed_point_formula.py.

Setting: A a finite real central essential arrangement in R^d, V a top-cone,
g a finite-order linear map with gA = A and gV = V, U = Fix(g),
M = Lambda(V)^g (g-stable flats X with dim(X cap |V|) = dim X).

  S(g) := sum_{X in M, X cap U = 0} mu_M(X, R^d).

Checks:
  [Wp]    U lies in a hyperplane of A  =>  S(g) = 0          (Prop. W').
  [Wex]   U lies in no hyperplane     =>  S(g) = (-1)^{dim U} m(V^U), where
          V^U is the top-cone of the restricted arrangement A^U in U with
          |V^U| = |V| cap U, and m = (-1)^rank mu(Lambda(V^U)).  A^U is built
          in coordinates on U and Lambda(V^U) from its own faces.
  [m>=1]  m(V^U) >= 1 on every such pair, so S(g) != 0 (sharpness).
  [sgn]   (-1)^d det(g) = (-1)^{dim U}, det computed directly.
  [G*]    tr(g | (Gamma_V + Lune)/Lune) = chi_V(g) := (-1)^d det(g) mu(M),
          the trace computed by exact elimination mod p = 2^31 - 1 on the
          chamber space, Lune = span of the non-singleton top-lunes.
  [q=m]   dim (Gamma_V + Lune)/Lune = m(V).
  [rho]   chain level: g . rho_C = sign det(g) rho_{gC} for every chamber C,
          rho_C built from flags of faces with eps = sign det(b(F_1..F_d)).

Negative controls (must fail somewhere): [Wex] with #V^U in place of m(V^U);
[Wex] without the sign (-1)^{dim U}; [G*] without det(g); [G*] with the
permutation character #V^g; [rho] with sign +1.

Run (from compute/):  python3 audit_prop_w_prime.py          (full, ~1 min)
                      python3 audit_prop_w_prime.py --quick  (seconds)
Exit status 0 iff every asserted check passes and every control fires.
"""

import argparse
import itertools
import sys
from collections import Counter, defaultdict
from fractions import Fraction as Fr
from math import gcd

P = 2**31 - 1
FAIL = []


# ---------------------------------------------------------------- linear algebra

def rref(rows):
    """Reduced row echelon form over Q; returns (rows, pivots)."""
    m = [[Fr(x) for x in r] for r in rows]
    piv = []
    r = 0
    ncol = len(m[0]) if m else 0
    for c in range(ncol):
        k = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if k is None:
            continue
        m[r], m[k] = m[k], m[r]
        inv = 1 / m[r][c]
        m[r] = [x * inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    return m[:r], piv


def rank(rows):
    return len(rref(rows)[0]) if rows else 0


def nullspace(rows, n):
    if not rows:
        return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    red, piv = rref(rows)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for i, p in enumerate(piv):
            v[p] = -red[i][f]
        basis.append(v)
    return basis


def det(m):
    m = [[Fr(x) for x in r] for r in m]
    n = len(m)
    d = Fr(1)
    for c in range(n):
        k = next((i for i in range(c, n) if m[i][c] != 0), None)
        if k is None:
            return Fr(0)
        if k != c:
            m[c], m[k] = m[k], m[c]
            d = -d
        d *= m[c][c]
        for i in range(c + 1, n):
            f = m[i][c] / m[c][c]
            if f:
                m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return d


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
            for i in range(len(a))]


def matinv(a):
    n = len(a)
    red, piv = rref([list(a[i]) + [Fr(int(i == j)) for j in range(n)] for i in range(n)])
    return [r[n:] for r in red]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def sgn(x):
    return (x > 0) - (x < 0)


def primitive(v):
    """Scale a nonzero rational vector to a primitive integer vector."""
    den = 1
    for x in v:
        den = den * Fr(x).denominator // gcd(den, Fr(x).denominator)
    w = [int(Fr(x) * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    return tuple(x // g for x in w)


# ---------------------------------------------------------------- arrangements

class Arr:
    """Arrangement given by integer normals (one per hyperplane)."""

    def __init__(self, name, normals, d):
        self.name, self.d = name, d
        canon = {}
        for n in normals:
            p = primitive(n)
            q = tuple(-x for x in p)
            if p not in canon and q not in canon:
                canon[p] = True
        self.n = [list(map(Fr, p)) for p in canon]
        self.N = len(self.n)
        assert rank(self.n) == d, "not essential"
        self._flats()
        self._faces()

    def closure(self, z):
        rows = [self.n[e] for e in z]
        r = rank(rows)
        return frozenset(e for e in range(self.N) if rank(rows + [self.n[e]]) == r)

    def _flats(self):
        top = frozenset()
        flats = {top}
        frontier = [top]
        while frontier:
            new = []
            for z in frontier:
                for e in range(self.N):
                    if e not in z:
                        c = self.closure(z | {e})
                        if c not in flats:
                            flats.add(c)
                            new.append(c)
            frontier = new
        self.flats = flats
        self.dim = {z: self.d - rank([self.n[e] for e in z]) for z in flats}

    def _faces(self):
        cocirc = []
        for z, k in self.dim.items():
            if k == 1:
                v = nullspace([self.n[e] for e in z], self.d)[0]
                s = tuple(sgn(dot(nn, v)) for nn in self.n)
                cocirc += [(s, v), (tuple(-x for x in s), [-x for x in v])]
        self.rays = cocirc
        zero = tuple([0] * self.N)
        cov = {zero}
        frontier = [zero]
        while frontier:
            new = []
            for X in frontier:
                for c, _ in cocirc:
                    Y = tuple(x if x else y for x, y in zip(X, c))
                    if Y not in cov:
                        cov.add(Y)
                        new.append(Y)
            frontier = new
        self.cov = sorted(cov, key=lambda s: sum(1 for x in s if x))
        self.chambers = [c for c in self.cov if 0 not in c]
        self.cidx = {c: i for i, c in enumerate(self.chambers)}

    def zset(self, F):
        return frozenset(e for e, x in enumerate(F) if x == 0)

    # --- symmetries
    def perm_of(self, g):
        """(pi, s): n_e g^{-1} = lam n_{pi(e)}, s_e = sign(lam)."""
        gi = matinv(g)
        pi, s = [], []
        for nn in self.n:
            m = [dot(nn, [gi[k][j] for k in range(self.d)]) for j in range(self.d)]
            hit = None
            for f, nf in enumerate(self.n):
                i0 = next(i for i in range(self.d) if nf[i] != 0)
                lam = m[i0] / nf[i0]
                if lam != 0 and all(m[i] == lam * nf[i] for i in range(self.d)):
                    hit = (f, sgn(lam))
                    break
            if hit is None:
                return None
            pi.append(hit[0])
            s.append(hit[1])
        return pi, s

    def act(self, ps, F):
        pi, s = ps
        out = [0] * self.N
        for e, x in enumerate(F):
            out[pi[e]] = s[e] * x
        return tuple(out)


def group_closure(gens, d):
    I = tuple(tuple(Fr(int(i == j)) for j in range(d)) for i in range(d))
    G = {I}
    frontier = [I]
    gens = [tuple(tuple(Fr(x) for x in r) for r in g) for g in gens]
    while frontier:
        new = []
        for a in frontier:
            for b in gens:
                c = tuple(tuple(r) for r in matmul(a, b))
                if c not in G:
                    G.add(c)
                    new.append(c)
        frontier = new
    return [[list(r) for r in g] for g in G]


def signed_perms(d):
    out = []
    for p in itertools.permutations(range(d)):
        for s in itertools.product([1, -1], repeat=d):
            out.append([[s[i] if j == p[i] else 0 for j in range(d)] for i in range(d)])
    return out


# ---------------------------------------------------------------- the arrangements

def arr_B3():
    n = [[1 if k == i else 0 for k in range(3)] for i in range(3)]
    n += [[1 if k == i else (s if k == j else 0) for k in range(3)]
          for i, j in itertools.combinations(range(3), 2) for s in (1, -1)]
    return Arr("B3", n, 3), signed_perms(3), signed_perms(3)


def arr_A3():
    # A3 realized as D3: x_i +- x_j; G = W(B3) contains -1 and the odd sign
    # changes, which are not in W(A3) = W(D3).
    n = [[1 if k == i else (s if k == j else 0) for k in range(3)]
         for i, j in itertools.combinations(range(3), 2) for s in (1, -1)]
    G = signed_perms(3)
    W = [g for g in G if sum(1 for r in g for x in r if x < 0) % 2 == 0]
    return Arr("A3", n, 3), G, W


def arr_tetra7():
    n = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1], [1, 1, -1], [1, -1, 1], [-1, 1, 1]]
    return Arr("tetra7", n, 3), signed_perms(3), None


def arr_hex():
    # h has order 6, is not orthogonal, and Fix(h) = z-axis lies in no hyperplane.
    h = [[0, -1, 0], [1, 1, 0], [0, 0, 1]]
    hi = matinv([[Fr(x) for x in r] for r in h])
    n0 = [Fr(1), Fr(0), Fr(1)]
    normals = [[0, 0, 1]]
    v = n0
    for _ in range(6):
        normals.append(v)
        v = [dot(v, [hi[k][j] for k in range(3)]) for j in range(3)]
    G = group_closure([h, [[-1, 0, 0], [0, -1, 0], [0, 0, -1]]], 3)
    return Arr("hex7", normals, 3), G, None


def arr_A4():
    # A4 in coordinates y_i = x_i - x_5 (i = 1..4); G = +-S_5.
    n = [[1 if k == i else (-1 if k == j else 0) for k in range(4)]
         for i, j in itertools.combinations(range(4), 2)]
    n += [[1 if k == i else 0 for k in range(4)] for i in range(4)]

    def mat(p):  # permutation p of {0..4} acting on x, in y-coordinates
        # y_i = x_i - x_4; (p.x)_{p(j)} = x_j.  Column j of matrix = image of y-basis e_j.
        cols = []
        for j in range(4):
            x = [0] * 5
            x[j] = 1          # e_j in y-coords is x = e_j (with x_4 = 0)
            px = [0] * 5
            for a in range(5):
                px[p[a]] = x[a]
            cols.append([px[i] - px[4] for i in range(4)])
        return [[cols[j][i] for j in range(4)] for i in range(4)]
    S5 = [mat(p) for p in itertools.permutations(range(5))]
    G = S5 + [[[-x for x in r] for r in g] for g in S5]
    return Arr("A4", n, 4), G, S5


def arr_D4():
    n = [[1 if k == i else (s if k == j else 0) for k in range(4)]
         for i, j in itertools.combinations(range(4), 2) for s in (1, -1)]
    Hd = [[Fr(x, 2) for x in r] for r in
          ([1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1])]
    G = group_closure([[[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
                       [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0]],
                       [[-1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]], Hd], 4)
    W = [g for g in G if all(x in (0, 1, -1) for r in g for x in r)
         and sum(1 for r in g for x in r if x < 0) % 2 == 0]
    return Arr("D4", n, 4), G, W


# ---------------------------------------------------------------- cones

def all_cones(A):
    full = (1 << len(A.chambers)) - 1
    half = []
    for e in range(A.N):
        for s in (1, -1):
            m = 0
            for i, c in enumerate(A.chambers):
                if c[e] == s:
                    m |= 1 << i
            half.append(m)
    seen = {full}
    frontier = [full]
    while frontier:
        new = []
        for v in frontier:
            for h in half:
                w = v & h
                if w and w not in seen:
                    seen.add(w)
                    new.append(w)
        frontier = new
    return seen


def chamber_perm(A, ps):
    return [A.cidx[A.act(ps, c)] for c in A.chambers]


def map_mask(mask, cp):
    out = 0
    i = 0
    while mask:
        if mask & 1:
            out |= 1 << cp[i]
        mask >>= 1
        i += 1
    return out


def orbit_reps(A, cones, cps):
    rest = set(cones)
    reps = []
    while rest:
        v = min(rest)
        stab = []
        orb = set()
        for k, cp in enumerate(cps):
            w = map_mask(v, cp)
            orb.add(w)
            if w == v:
                stab.append(k)
        rest -= orb
        reps.append((v, stab))
    return reps


# ---------------------------------------------------------------- Mobius

def mobius_to_top(elems, dim):
    """mu(X, top) on a poset of flats (zero sets), X <= Y iff z(X) >= z(Y)."""
    order = sorted(elems, key=lambda z: -dim[z])
    top = order[0]
    mu = {top: 1}
    for X in order[1:]:
        mu[X] = -sum(mu[Y] for Y in mu if Y < X)  # Y strictly above X: z(Y) proper subset
    return mu, top


def lambda_of(A, chmask):
    """S_max signs, faces of V, Lambda(V) as zero sets."""
    ch = [A.chambers[i] for i in range(len(A.chambers)) if chmask >> i & 1]
    smax = {}
    for e in range(A.N):
        vals = {c[e] for c in ch}
        if len(vals) == 1:
            smax[e] = vals.pop()
    faces = [F for F in A.cov if all(F[e] in (0, s) for e, s in smax.items())]
    lam = {A.zset(F) for F in faces}
    return smax, faces, lam, ch


# ---------------------------------------------------------------- restriction to U

def restricted(A, U, smax):
    """A^U in coordinates on U, and the sign constraints of |V| cap U."""
    k = len(U)
    rn = {}
    for e in range(A.N):
        r = [dot(A.n[e], u) for u in U]
        if any(r):
            rn[e] = r
    B = Arr("rest", list(rn.values()), k) if k >= 1 else None
    cons = {}
    for e, s in smax.items():
        r = rn[e]
        p = primitive(r)
        for f, nf in enumerate(B.n):
            if tuple(int(x) for x in nf) == p:
                cons[f] = cons.get(f, set()) | {s}
            elif tuple(-int(x) for x in nf) == p:
                cons[f] = cons.get(f, set()) | {-s}
    mask = 0
    for i, c in enumerate(B.chambers):
        if all(c[f] in ss and len(ss) == 1 for f, ss in cons.items()):
            mask |= 1 << i
    return B, mask


def m_of(B, mask):
    _, _, lam, _ = lambda_of(B, mask)
    mu, top = mobius_to_top(lam, B.dim)
    bottom = max(lam, key=len)
    return (-1) ** B.d * mu[bottom], bin(mask).count("1")


# ---------------------------------------------------------------- Lune and traces

def lune_rows(A):
    rows = []
    for H in A.cov:
        if not any(H):
            continue
        z = [e for e in range(A.N) if H[e] == 0]  # L(H, D) = {C : C_e = D_e, e in z(H)}
        for D in A.chambers:
            if all(D[e] == H[e] for e in range(A.N) if H[e] != 0):
                rows.append(tuple(1 if all(C[e] == D[e] for e in z) else 0
                                  for C in A.chambers))
    return [list(r) for r in set(rows)]


def rref_mod(rows, n):
    m = [[x % P for x in r] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        k = next((i for i in range(r, len(m)) if m[i][c]), None)
        if k is None:
            continue
        m[r], m[k] = m[k], m[r]
        inv = pow(m[r][c], P - 2, P)
        m[r] = [x * inv % P for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                f = m[i][c]
                m[i] = [(a - f * b) % P for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    return m[:r], piv


def reduce_mod(v, basis, piv):
    """v minus its components along an RREF basis (zeroes the pivot entries)."""
    v = [x % P for x in v]
    for row, p in zip(basis, piv):
        c = v[p]
        if c:
            v = [(a - c * b) % P for a, b in zip(v, row)]
    return v


def trace_quot(qb, qp, lb, lp, cp):
    """Trace of the chamber permutation cp on (span qb + span lb)/span lb.

    lb is an RREF basis of Lune; qb an RREF basis of the remainders of Gamma_V,
    which vanish on the pivots lp.  g.r reduced mod Lune is a combination of
    qb, and its coefficient on qb[i] is its entry at qp[i]."""
    n = len(cp)
    t = 0
    for row, p in zip(qb, qp):
        img = [0] * n
        for i in range(n):
            img[cp[i]] = row[i]
        t += reduce_mod(img, lb, lp)[p]
    t %= P
    return t if t <= P // 2 else t - P


# ---------------------------------------------------------------- chamber cycles

def rho_chains(A):
    """rho_C as dict (span chain) -> coeff, via eps = sign det(b(F_1),...,b(F_d))."""
    ray_of = {}
    for s, v in A.rays:
        ray_of[s] = v
    b = {}
    for F in A.cov:
        if not any(F):
            continue
        v = [Fr(0)] * A.d
        for s, w in ray_of.items():
            if all(x == 0 or x == y for x, y in zip(s, F)):
                v = [a + c for a, c in zip(v, w)]
        b[F] = v
    below = defaultdict(list)
    for F in b:
        for G in b:
            if F != G and all(x == 0 or x == y for x, y in zip(F, G)):
                below[G].append(F)
    dimF = {F: A.dim[A.zset(F)] for F in b}
    rho = {}
    for C in A.chambers:
        chain = defaultdict(int)

        def walk(flag):
            top = flag[0]
            if dimF[top] == 1:
                fl = flag  # F_1 < ... < F_d = C
                eps = sgn(det([b[F] for F in fl]))
                key = tuple(A.zset(F) for F in fl[:-1])
                chain[key] += (-1) ** (A.d - 1) * eps
                return
            for F in below[top]:
                if dimF[F] == dimF[top] - 1:
                    walk([F] + flag)
        walk([C])
        rho[C] = {k: v for k, v in chain.items() if v}
    return rho


# ---------------------------------------------------------------- driver

class Stats:
    def __init__(self):
        self.c = defaultdict(lambda: [0, 0])  # name -> [fails, checks]
        self.tab = Counter()
        self.values = Counter()

    def check(self, name, ok, info=""):
        self.c[name][1] += 1
        if not ok:
            self.c[name][0] += 1
            if not name.startswith("neg:") and len(FAIL) < 20:
                FAIL.append((name, info))


def run_arr(A, G, W, cones, st, log, rho_check=True):
    d = A.d
    Gps = []
    Gmat = []
    for g in G:
        ps = A.perm_of(g)
        assert ps is not None, "g does not preserve A"
        Gps.append(ps)
        Gmat.append(g)
    Wset = None if W is None else {tuple(tuple(r) for r in w) for w in W}
    cps = [chamber_perm(A, ps) for ps in Gps]
    lr = lune_rows(A)
    Nc = len(A.chambers)
    lune_b, lune_p = rref_mod(lr, Nc)
    flats_mu, _ = mobius_to_top(A.flats, A.dim)
    mu_full = flats_mu[max(A.flats, key=len)]
    st.check("lune-dim", len(lune_b) == Nc - abs(mu_full),
             f"{A.name} {len(lune_b)} {Nc} {mu_full}")
    log(f"  {A.name}: {A.N} hyperplanes, {len(A.cov)} faces, {Nc} chambers, "
        f"|mu(L(A))| = {abs(mu_full)}, dim Lune = {len(lune_b)}, |G| = {len(G)}")
    gdet = [det(g) for g in Gmat]
    gfix = [nullspace([[Fr(g[i][j]) - (i == j) for j in range(d)] for i in range(d)], d)
            for g in Gmat]
    reps = orbit_reps(A, cones, cps)
    log(f"  {A.name}: {len(cones)} cones, {len(reps)} G-orbits")
    rcache = {}
    for v, stab in reps:
        smax, faces, lam, ch = lambda_of(A, v)
        rows = [reduce_mod([1 if j == i else 0 for j in range(Nc)], lune_b, lune_p)
                for i in range(Nc) if v >> i & 1]
        sb, sp = rref_mod(rows, Nc)
        q = len(sb)
        mu_lam, top = mobius_to_top(lam, A.dim)
        mV = (-1) ** d * mu_lam[frozenset(range(A.N))]
        st.check("q=m", q == mV, f"{A.name} q={q} m={mV}")
        st.check("m>=1(V)", mV >= 1)
        for k in stab:
            ps, g, dg, U = Gps[k], Gmat[k], gdet[k], gfix[k]
            inW = Wset is not None and tuple(tuple(r) for r in g) in Wset
            M = [X for X in lam if frozenset(ps[0][e] for e in X) == X]
            mu, top = mobius_to_top(M, A.dim)
            bottom = max(M, key=len)
            chi = (-1) ** d * dg * mu[bottom]
            # ---- [G*]
            tr = trace_quot(sb, sp, lune_b, lune_p, cps[k])
            st.check("G*", tr == chi, f"{A.name} tr={tr} chi={chi}")
            st.check("neg:G*-no-det", tr == (-1) ** d * mu[bottom])
            nfix = sum(1 for i in range(Nc) if v >> i & 1 and cps[k][i] == i)
            st.check("neg:G*-perm", tr == nfix)
            cls = "id" if len(U) == d else ("W" if inW else ("G-W" if Wset is not None
                                                             else "nonrefl"))
            st.tab[(A.name, "G*", cls)] += 1
            if len(U) == d:
                continue
            # ---- Weisner sum S(g)
            dimXU = {}
            for X in M:
                rr = [[dot(A.n[e], u) for u in U] for e in X]
                dimXU[X] = len(U) - (rank(rr) if rr else 0)
            S = sum(mu[X] for X in M if dimXU[X] == 0)
            inhyp = [e for e in range(A.N) if all(dot(A.n[e], u) == 0 for u in U)]
            isflat = bool(inhyp) and A.dim[A.closure(frozenset(inhyp))] == len(U)
            st.check("sgn", (-1) ** d * dg == (-1) ** len(U))
            if inhyp:
                st.check("Wp", S == 0, f"{A.name} S={S}")
                kind = "flat" if isflat else "nonflat-inhyp"
                st.tab[(A.name, "W", kind, S == 0)] += 1
            else:
                key = (tuple(tuple(u) for u in U), tuple(sorted(smax.items())))
                if key not in rcache:
                    B, bm = restricted(A, U, smax)
                    rcache[key] = m_of(B, bm)
                mU, nU = rcache[key]
                st.check("Wex", S == (-1) ** len(U) * mU,
                         f"{A.name} S={S} dimU={len(U)} m={mU}")
                st.check("m>=1", mU >= 1, f"{A.name} m={mU}")
                st.check("neg:Wex-count", S == (-1) ** len(U) * nU)
                st.check("neg:Wex-nosign", S == mU)
                st.tab[(A.name, "W", "nohyp", S == 0)] += 1
                st.values[(A.name, len(U), mU)] += 1
    # ---- chain level rho
    if rho_check:
        rho = rho_chains(A)
        for ps, g, dg in zip(Gps, Gmat, gdet):
            for C in A.chambers:
                img = defaultdict(int)
                for key, c in rho[C].items():
                    img[tuple(frozenset(ps[0][e] for e in X) for X in key)] += c
                gC = A.act(ps, C)
                want = {k2: sgn(dg) * c for k2, c in rho[gC].items()}
                st.check("rho", dict(img) == want, f"{A.name}")
                st.check("neg:rho-nosign", dict(img) == rho[gC])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    log = print
    st = Stats()
    log("audit_prop_w_prime.py: Prop. W' exact form and G* for g outside W")
    builders = [arr_A3, arr_B3, arr_tetra7, arr_hex]
    if not args.quick:
        builders += [arr_A4, arr_D4]
    for bld in builders:
        A, G, W = bld()
        cones = all_cones(A)
        run_arr(A, G, W, cones, st, log)
        if A.name in ("A3", "B3", "A4", "D4"):
            exp = {"A3": (24, 219), "B3": (48, 941), "A4": (120, 4231),
                   "D4": (192, 12313)}[A.name]
            st.check("pos:counts", (len(A.chambers), len(cones)) == exp,
                     f"{A.name} {len(A.chambers)} {len(cones)}")
        if A.name == "D4":
            st.check("pos:counts", len(G) == 1152)
    log("")
    log("check                      fails / checks")
    for name in sorted(st.c):
        f, n = st.c[name]
        log(f"  {name:24s} {f:7d} / {n}")
    log("")
    log("pairs (V, g) by class of g (G* checks):")
    for key in sorted(k for k in st.tab if k[1] == "G*"):
        log(f"  {key[0]:7s} {key[2]:8s} {st.tab[key]}")
    log("")
    log("Weisner sum S(g), g != 1, by position of Fix(g): (arrangement, kind, S == 0): pairs")
    for key in sorted((k for k in st.tab if k[1] == "W"), key=str):
        log(f"  {key[0]:7s} {key[2]:14s} S==0:{str(key[3]):5s} {st.tab[key]}")
    log("")
    log("Fix(g) in no hyperplane: (arrangement, dim Fix g, m(V^U)): pairs")
    for key in sorted(st.values):
        log(f"  {key}: {st.values[key]}")
    ok = True
    for name, (f, n) in st.c.items():
        if name.startswith("neg:"):
            if f == 0:
                ok = False
                log(f"NEGATIVE CONTROL DID NOT FIRE: {name}")
        elif f:
            ok = False
    if n == 0:
        ok = False
    for x in FAIL:
        log("FAIL", x)
    log("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
