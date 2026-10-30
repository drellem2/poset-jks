#!/usr/bin/env python3
"""Independent audit of notes/general_theory.md, framework (a) (mg-7ab20).

Companion to notes/audit_general_theory_cones.md.  Imports nothing from this
repository (in particular not compute/general_theory.py).  Plain Python 3,
no dependencies.

Method.
  * Exact integer/rational arithmetic.  Rays = exact kernels of (d-1)-subsets
    of normals.  Faces = closure of {O} under right Tits multiplication by
    rays (every face F is r_1 r_2 ... r_k for its rays r_i, since
    r_1 + e r_2 + e^2 r_3 + ... lies in the relative interior of F).
  * A top-cone is a nonempty set {C : C_e = s_e, e in S}; all of them are
    enumerated with chamber bitmasks.  F(V) = faces with signs in {0, s_e}
    on S_max.  Lambda(V) = zero sets of faces in F(V).
  * Homology of order complexes: reduced, over GF(p), all degrees.
  * Localizations are built independently: faces of A_X are the restrictions
    of all faces of A to the hyperplanes containing X.

Checks (exit status 0 iff all pass):
  [thm1]   H~_*(Delta(proper Lambda(V)); GF(p)) is zero outside degree d-2 and
           has rank m(V) = (-1)^d mu(0, R^d) >= 0 there (p = 2 and a large p).
  [loc]    Lemma 0.1(c): (-1)^codim X mu_{Lambda(V)}(X, top) equals m of the
           independently localized cone V_X, for every flat X in lin V.
  [zas]    Theorem 2 / Cor. 1.1: #V = sum_{X flat in lin V} m(V_X).
  [rho]    The chamber cycles rho_C (C in V) span H~_{d-2}(Lambda(V)): the
           rank of their span equals m(V).  (Audit Prop. A.)
  [lune]   With ambient orientations, sum_{C in L(H,D)} rho_C = 0 exactly
           for every non-singleton top-lune.  (Audit Prop. B.)
  [eqv]    (B_2, B_3) g rho_C = det(g) rho_{gC} for every signed
           permutation g and chamber C.
  [prop3]  Prop. 3: (a) span{lunes in V} = Lie_L(Gamma_V)^perp (dimensions and
           orthogonality); (b) c_X depends only on span x, equals #V_X, and
           sum_X mu(0,X) c_X = m(V); q(V) <= dim Lie_L <= m(V); (c) equality.
  [sal]    Saliola's e_0 in k Sigma_L: x e_0 = 0 for x != O, e_0^2 = e_0,
           e_0 - O supported on faces != O.
  [braid]  Lambda(C_P) = OP(P)^op (as sets of partitions, order reversed),
           m(C_P) = e_C(P) and Lemma 1.3, for all labeled posets n <= 5;
           Lemma 1.3 also for random posets n = 6, 7.
  [CTL]    Positive controls: each must FAIL and does.

Run (from compute/):  python3 audit_general_theory_cones.py
"""

import itertools
import random
import sys
from fractions import Fraction

P_BIG = 1000003


# ----------------------------------------------------------------- linear algebra

def rank_mod(rows, p):
    """Rank over GF(p) of a list of sparse rows {col: int}."""
    pivots = {}
    r = 0
    for row in rows:
        row = {c: v % p for c, v in row.items() if v % p}
        while row:
            c = min(row)
            if c in pivots:
                prow = pivots[c]
                f = row[c]
                for cc, vv in prow.items():
                    nv = (row.get(cc, 0) - f * vv) % p
                    if nv:
                        row[cc] = nv
                    else:
                        row.pop(cc, None)
            else:
                inv = pow(row[c], p - 2, p)
                row = {cc: (vv * inv) % p for cc, vv in row.items()}
                pivots[c] = row
                r += 1
                break
    return r


def nullspace_Q(rows, ncols):
    """Exact rational nullspace basis of a dense integer matrix."""
    m = [[Fraction(x) for x in row] for row in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        inv = 1 / m[r][c]
        m[r] = [x * inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncols
        v[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -m[i][fc]
        basis.append(v)
    return basis


def _rank_rows(rows):
    m = [[Fraction(x) for x in row] for row in rows]
    r = 0
    ncols = len(m[0]) if m else 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if pr is None:
            continue
        m[r], m[pr] = m[pr], m[r]
        for i in range(r + 1, len(m)):
            if m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def det(mat):
    m = [[Fraction(x) for x in row] for row in mat]
    n = len(m)
    d = Fraction(1)
    for c in range(n):
        pr = next((i for i in range(c, n) if m[i][c] != 0), None)
        if pr is None:
            return Fraction(0)
        if pr != c:
            m[c], m[pr] = m[pr], m[c]
            d = -d
        d *= m[c][c]
        for i in range(c + 1, n):
            f = m[i][c] / m[c][c]
            m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return d


def sgn(x):
    return (x > 0) - (x < 0)


# ----------------------------------------------------------------- arrangements

class Arr:
    def __init__(self, name, normals):
        self.name = name
        self.N = [tuple(v) for v in normals]
        self.n = len(self.N)
        self.d = len(self.N[0])
        assert _rank_rows(self.N) == self.d, "not essential"
        self._rays()
        self._faces()

    def sv(self, x):
        return tuple(sgn(sum(a * b for a, b in zip(nv, x))) for nv in self.N)

    def _rays(self):
        rays = {}
        for sub in itertools.combinations(range(self.n), self.d - 1):
            rows = [self.N[i] for i in sub]
            if self.d > 1 and _rank_rows(rows) != self.d - 1:
                continue
            ns = nullspace_Q(rows, self.d) if self.d > 1 else [[Fraction(1)]]
            assert len(ns) == 1
            v = ns[0]
            den = 1
            for x in v:
                den = den * x.denominator
            v = [int(x * den) for x in v]
            for s in (1, -1):
                w = tuple(s * x for x in v)
                key = self.sv(w)
                rays.setdefault(key, w)
        self.rays = rays          # sign vector -> integer point

    def _faces(self):
        O = tuple([0] * self.n)
        faces = {O}
        frontier = [O]
        while frontier:
            new = []
            for F in frontier:
                for r in self.rays:
                    G = tprod(F, r)
                    if G not in faces:
                        faces.add(G)
                        new.append(G)
            frontier = new
        self.O = O
        self.faces = sorted(faces)
        self.chambers = [F for F in self.faces if 0 not in F]
        self.cidx = {C: i for i, C in enumerate(self.chambers)}
        # rank of a zero set (codim of the flat)
        self._rk = {}
        # interior point of each face: sum of its rays
        self.pt = {}
        for F in self.faces:
            v = [0] * self.d
            for r, w in self.rays.items():
                if leq(r, F):
                    v = [a + b for a, b in zip(v, w)]
            self.pt[F] = tuple(v)
            assert self.sv(v) == F
        # masks
        self.mask = {}
        for e in range(self.n):
            for s in (1, -1):
                mk = 0
                for i, C in enumerate(self.chambers):
                    if C[e] == s:
                        mk |= 1 << i
                self.mask[(e, s)] = mk

    def z(self, F):
        return frozenset(e for e in range(self.n) if F[e] == 0)

    def codim(self, Z):
        if Z not in self._rk:
            self._rk[Z] = _rank_rows([self.N[e] for e in Z]) if Z else 0
        return self._rk[Z]

    def topcones(self):
        full = (1 << len(self.chambers)) - 1
        seen = set()
        for choice in itertools.product((0, 1, -1), repeat=self.n):
            mk = full
            for e, s in enumerate(choice):
                if s:
                    mk &= self.mask[(e, s)]
                    if not mk:
                        break
            if mk and mk not in seen:
                seen.add(mk)
        return sorted(seen)


def tprod(F, G):
    return tuple(f if f else g for f, g in zip(F, G))


def leq(F, G):
    return all(f == 0 or f == g for f, g in zip(F, G))


# ----------------------------------------------------------------- posets

def mobius_from_bottom_to(elems, le, bottom):
    """mu(bottom, y) for all y."""
    order = sorted(elems, key=lambda y: sum(1 for x in elems if le(x, y)))
    mu = {}
    for y in order:
        if y == bottom:
            mu[y] = 1
        elif le(bottom, y):
            mu[y] = -sum(mu[x] for x in order if x != y and le(bottom, x) and le(x, y) and x in mu)
        else:
            mu[y] = 0
    return mu


def mu_interval(elems, le, a, b):
    sub = [y for y in elems if le(a, y) and le(y, b)]
    mu = mobius_from_bottom_to(sub, le, a)
    return mu[b]


def chains(elems, lt):
    """All nonempty chains (as tuples, increasing)."""
    elems = list(elems)
    up = {x: [y for y in elems if lt(x, y)] for x in elems}
    out = []

    def ext(ch):
        out.append(tuple(ch))
        for y in up[ch[-1]]:
            ext(ch + [y])
    for x in elems:
        ext([x])
    return out


def reduced_homology_ranks(elems, lt, p):
    """Ranks of reduced homology over GF(p) of the order complex, by degree."""
    chs = chains(elems, lt)
    bydim = {}
    for c in chs:
        bydim.setdefault(len(c) - 1, []).append(c)
    bydim[-1] = [()]
    top = max(bydim)
    idx = {k: {c: i for i, c in enumerate(v)} for k, v in bydim.items()}
    rk = {}
    for k in range(0, top + 1):
        rows = []
        for c in bydim[k]:
            row = {}
            for j in range(len(c)):
                f = c[:j] + c[j + 1:]
                row[idx[k - 1][f]] = row.get(idx[k - 1][f], 0) + (-1) ** j
            rows.append(row)
        rk[k] = rank_mod(rows, p)
    rk[top + 1] = 0
    rk[-1] = 0
    return {k: len(bydim[k]) - rk[k] - rk[k + 1] for k in range(-1, top + 1)}


# ----------------------------------------------------------------- cone data

class Cone:
    def __init__(self, A, mk):
        self.A = A
        self.mk = mk
        self.V = [C for i, C in enumerate(A.chambers) if mk >> i & 1]
        self.Smax = {}
        for e in range(A.n):
            ss = {C[e] for C in self.V}
            if len(ss) == 1:
                self.Smax[e] = ss.pop()
        self.FV = [F for F in A.faces
                   if all(F[e] in (0, s) for e, s in self.Smax.items())]
        self.Lam = sorted({A.z(F) for F in self.FV}, key=len, reverse=True)
        self.bottom = frozenset(range(A.n))
        self.top = frozenset()
        S = frozenset(self.Smax)
        self.flatsL = [Z for Z in self.Lam if Z >= S]
        self.SigmaL = [F for F in A.faces if all(F[e] == 0 for e in self.Smax)]

    @staticmethod
    def le(Y1, Y2):        # Y1 subset Y2 as subspaces  <=> z(Y1) superset z(Y2)
        return Y1 >= Y2

    @staticmethod
    def lt(Y1, Y2):
        return Y1 > Y2

    def m(self):
        return (-1) ** self.A.d * mu_interval(self.Lam, self.le, self.bottom, self.top)

    def proper(self):
        return [Z for Z in self.Lam if Z != self.bottom and Z != self.top]


def localized_m(A, cone, Z):
    """m of the localized cone V_X, X the flat with zero set Z, built from the
    faces of A_X = restrictions of all faces to the hyperplanes in Z."""
    Zs = sorted(Z)
    locfaces = {tuple(F[e] for e in Zs) for F in A.faces}
    pos = {e: i for i, e in enumerate(Zs)}
    for e in cone.Smax:
        assert e in pos
    cf = [G for G in locfaces
          if all(G[pos[e]] in (0, s) for e, s in cone.Smax.items())]
    lam = {frozenset(Zs[i] for i in range(len(Zs)) if G[i] == 0) for G in cf}
    r = A.codim(Z)
    bot = frozenset(Zs)
    if r == 0:
        return 1, sum(1 for G in cf if 0 not in G)
    mu = mu_interval(list(lam), Cone.le, bot, frozenset())
    nch = sum(1 for G in cf if 0 not in G)
    return (-1) ** r * mu, nch


def rho(A, C):
    """Ambient-oriented chamber cycle of C: dict chain-of-zero-sets -> coeff."""
    fs = [F for F in A.faces if F != A.O and F != C and leq(F, C)]
    bydim = {}
    for F in fs:
        bydim.setdefault(A.d - A.codim(A.z(F)), []).append(F)
    out = {}

    def ext(fl):
        k = len(fl)
        if k == A.d - 1:
            s = sgn(det([A.pt[F] for F in fl] + [A.pt[C]]))
            assert s != 0
            key = tuple(A.z(F) for F in fl)
            out[key] = out.get(key, 0) + s
            return
        for G in bydim.get(k + 1, []):
            if not fl or leq(fl[-1], G):
                ext(fl + [G])
    ext([])
    return out


def boundary_is_zero(chain):
    acc = {}
    for c, v in chain.items():
        for j in range(len(c)):
            f = c[:j] + c[j + 1:]
            acc[f] = acc.get(f, 0) + (-1) ** j * v
    return all(x == 0 for x in acc.values())


def lune_of(A, H, D):
    """L(H, D) = {C : HC = D} for D >= H, i.e. the chambers agreeing with D
    on z(H) (a one-line unwinding of the Tits product)."""
    Z = A.z(H)
    cache = A.__dict__.setdefault("_lunecache", {})
    if Z not in cache:
        g = {}
        for C in A.chambers:
            g.setdefault(tuple(C[e] for e in sorted(Z)), set()).add(C)
        cache[Z] = {k: frozenset(v) for k, v in g.items()}
    return cache[Z][tuple(D[e] for e in sorted(Z))]


def lunes(A):
    """All non-singleton top-lunes L(H, D), H != O, D >= H, as frozensets."""
    out = set()
    for H in A.faces:
        if H == A.O:
            continue
        for D in A.chambers:
            if leq(H, D):
                out.add(lune_of(A, H, D))
    return out


def lunes_by_tits(A):
    """Same set computed literally from the Tits product (small A only)."""
    out = set()
    for H in A.faces:
        if H == A.O:
            continue
        for D in A.chambers:
            if leq(H, D):
                out.add(frozenset(C for C in A.chambers if tprod(H, C) == D))
    return out


# ----------------------------------------------------------------- the audit

FAIL = []


def check(tag, ok, msg=""):
    if not ok:
        FAIL.append(f"{tag} {msg}")
    return ok


def audit_arr(A, cones=None, do_hom=True, do_prop3=True, do_sal=True, log=print):
    allcones = A.topcones()
    if cones is None:
        cones = allcones
    LU = lunes(A)
    if len(A.faces) <= 200:
        check("[lune]", LU == lunes_by_tits(A), f"{A.name} lune description")
    rhos = {C: rho(A, C) for C in A.chambers}
    for C, r in rhos.items():
        check("[rho]", boundary_is_zero(r), f"{A.name} rho not a cycle")
    # [lune] exact vanishing of lune sums
    nl = 0
    for L in LU:
        acc = {}
        for C in L:
            for k, v in rhos[C].items():
                acc[k] = acc.get(k, 0) + v
        nl += 1
        check("[lune]", all(v == 0 for v in acc.values()), f"{A.name} lune sum nonzero")
    # Lune generator vectors
    lunevecs = [{A.cidx[C]: 1 for C in L} for L in LU]
    rkLune = rank_mod(lunevecs, P_BIG)
    stats = dict(cones=0, hom=0, rho=0, prop3=0, sal=0, maxm=0)
    for mk in cones:
        K = Cone(A, mk)
        stats["cones"] += 1
        m = K.m()
        stats["maxm"] = max(stats["maxm"], m)
        check("[thm1]", m >= 0, f"{A.name} m<0")
        # [loc] + [zas]
        tot = 0
        for Z in K.flatsL:
            mloc, nch = localized_m(A, K, Z)
            via_mu = (-1) ** A.codim(Z) * mu_interval(K.Lam, K.le, Z, K.top) if Z else 1
            check("[loc]", mloc == via_mu, f"{A.name} {sorted(Z)}")
            tot += mloc
        check("[zas]", tot == len(K.V), f"{A.name} #V={len(K.V)} sum={tot}")
        prop = K.proper()
        if do_hom and A.d >= 2:
            for p in (2, P_BIG):
                h = reduced_homology_ranks(prop, K.lt, p) if prop else {-1: 1}
                ok = all((v == 0) for k, v in h.items() if k != A.d - 2) and h.get(A.d - 2, 0) == m
                check("[thm1]", ok, f"{A.name} p={p} h={h} m={m}")
            stats["hom"] += 1
        # [rho] span of chamber cycles equals m (top homology = top cycles)
        if A.d >= 2:
            keys = {}
            rows = []
            for C in K.V:
                row = {}
                for k, v in rhos[C].items():
                    row[keys.setdefault(k, len(keys))] = v
                rows.append(row)
            rr = rank_mod(rows, P_BIG)
            check("[rho]", rr == m, f"{A.name} span={rr} m={m}")
            stats["rho"] += 1
        if do_prop3:
            prop3(A, K, m, LU, lunevecs, rkLune)
            stats["prop3"] += 1
        if do_sal and len(K.SigmaL) <= 80:
            saliola(A, K)
            stats["sal"] += 1
    log(f"  {A.name}: d={A.d} n={A.n} faces={len(A.faces)} chambers={len(A.chambers)} "
        f"top-cones={len(allcones)} audited={stats['cones']} hom={stats['hom']} "
        f"rho={stats['rho']} prop3={stats['prop3']} saliola={stats['sal']} "
        f"lunes={nl} max m={stats['maxm']}")
    return allcones


def prop3(A, K, m, LU, lunevecs, rkLune):
    V = K.V
    vi = {C: i for i, C in enumerate(V)}
    nonO = [H for H in K.SigmaL if H != A.O]
    # action stays in V
    for H in nonO:
        for C in V:
            check("[prop3]", tprod(H, C) in vi, f"{A.name} action leaves V")
    # Lie_L(Gamma_V): z with H z = 0 for all H != O in Sigma_L
    rows = []
    for H in nonO:
        for D in V:
            row = [0] * len(V)
            for C in V:
                if tprod(H, C) == D:
                    row[vi[C]] += 1
            if any(row):
                rows.append(row)
    exact = len(V) <= 48
    if exact:
        lie = nullspace_Q(rows, len(V)) if rows else [[Fraction(int(i == j)) for j in range(len(V))]
                                                        for i in range(len(V))]
        dlie = len(lie)
    else:
        dlie = len(V) - rank_mod([{i: v for i, v in enumerate(r) if v} for r in rows], P_BIG)
    # lunes inside V
    lin = [L for L in LU if L <= set(V)]
    lv = [[1 if C in L else 0 for C in V] for L in lin]
    rlin = rank_mod([{i: v for i, v in enumerate(r) if v} for r in lv], P_BIG) if lv else 0
    check("[prop3]", rlin + dlie == len(V), f"{A.name} (a) dims {rlin}+{dlie}!={len(V)}")
    if exact:
        for z in lie:
            for row in lv:
                check("[prop3]", sum(a * b for a, b in zip(z, row)) == 0, f"{A.name} (a) not perp")
    # lunes inside V are exactly L(H,D), H in Sigma_L \ O (Lemma L)
    lin2 = {lune_of(A, H, D) for H in nonO for D in V if leq(H, D)}
    check("[prop3]", lin2 == set(lin), f"{A.name} Lemma L")
    # (b) c_X depends only on span, equals #V_X; sum mu(0,X) c_X = m
    cX = {}
    for x in K.SigmaL:
        Z = A.z(x)
        c = sum(1 for C in V if tprod(x, C) == C)
        if Z in cX:
            check("[prop3]", cX[Z] == c, f"{A.name} c_X not well defined")
        cX[Z] = c
    check("[prop3]", set(cX) == set(K.flatsL), f"{A.name} supports of Sigma_L != flats in L")
    for Z, c in cX.items():
        _, nch = localized_m(A, K, Z)
        check("[prop3]", c == nch, f"{A.name} c_X != #V_X")
    mu0 = mobius_from_bottom_to(K.flatsL, K.le, K.bottom)
    mult = sum(mu0[Z] * cX[Z] for Z in K.flatsL)
    check("[prop3]", mult == m, f"{A.name} [Gamma:S0]={mult} m={m}")
    # q(V)
    gv = [{A.cidx[C]: 1} for C in V]
    q = rank_mod(lunevecs + gv, P_BIG) - rkLune
    check("[prop3]", q <= dlie <= m, f"{A.name} q={q} lie={dlie} m={m}")
    check("[prop3]", q == m, f"{A.name} q={q} m={m}")


def alg_mul(a, b):
    out = {}
    for x, u in a.items():
        for y, v in b.items():
            k = tprod(x, y)
            out[k] = out.get(k, 0) + u * v
    return {k: v for k, v in out.items() if v}


def saliola_e0(A, K, wrong=False):
    """Saliola (4.1): e_X = x - sum_{Y > X} x e_Y, X in the support lattice."""
    sup = {}
    for x in K.SigmaL:
        sup.setdefault(A.z(x), x)
    order = sorted(sup, key=len)            # largest flats (small zero sets) first
    e = {}
    for X in order:
        x = sup[X]
        val = {x: 1}
        for Y in e:
            if Y < X:                       # Y > X as subspaces
                t = e[Y] if wrong else alg_mul({x: 1}, e[Y])
                for k, v in t.items():
                    val[k] = val.get(k, 0) - v
        e[X] = {k: v for k, v in val.items() if v}
    return e[K.bottom]


def saliola(A, K, e0=None):
    if e0 is None:
        e0 = saliola_e0(A, K)
    ok = True
    for x in K.SigmaL:
        if x != A.O:
            ok &= not alg_mul({x: 1}, e0)
    ok &= alg_mul(e0, e0) == e0
    ok &= e0.get(A.O) == 1
    check("[sal]", ok, f"{A.name}")
    return ok


# ----------------------------------------------------------------- braid / posets

def braid(n):
    """Essential braid arrangement of S_n in R^{n-1} (x_n = 0)."""
    N = []
    pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            v = [0] * (n - 1)
            if i < n - 1:
                v[i] += 1
            if j < n - 1:
                v[j] -= 1
            N.append(v)
            pairs.append((i, j))     # normal is x_i - x_j
    return N, pairs


def all_posets(n):
    """All labeled posets on range(n), as sets of strict relations (a, b)."""
    pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
    res = []

    def closed(R):
        for (a, b) in R:
            for (c, d) in R:
                if b == c and (a, d) not in R:
                    return False
        return True

    # build by acyclic transitive relations: choose for each unordered pair
    up = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for choice in itertools.product((0, 1, -1), repeat=len(up)):
        R = set()
        for (a, b), c in zip(up, choice):
            if c == 1:
                R.add((a, b))
            elif c == -1:
                R.add((b, a))
        if closed(R):
            res.append(frozenset(R))
    return res


def components(n, R):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for a, b in R:
        par[f(a)] = f(b)
    comp = {}
    for x in range(n):
        comp.setdefault(f(x), []).append(x)
    return [frozenset(c) for c in comp.values()]


def lin_ext(elems, R):
    elems = list(elems)
    out = []

    def rec(w, rest):
        if not rest:
            out.append(tuple(w))
            return
        for x in rest:
            if not any((y, x) in R for y in rest if y != x):
                rec(w + [x], [y for y in rest if y != x])
    rec([], elems)
    return out


def e_C(elems, R):
    L = set(lin_ext(elems, R))
    seen = set()
    cnt = 0
    for w in L:
        if w in seen:
            continue
        cnt += 1
        for k in range(len(w)):
            seen.add(w[k:] + w[:k])
    return cnt


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | {first}] + p[i + 1:]
        yield p + [frozenset([first])]


def lemma13(n, R):
    K = components(n, R)
    lhs = len(lin_ext(range(n), R))
    rhs = 0
    for sig in set_partitions(K):
        prod = 1
        for blk in sig:
            B = frozenset().union(*blk)
            RB = {(a, b) for a, b in R if a in B and b in B}
            prod *= e_C(B, RB)
        rhs += prod
    return lhs, rhs


def lemma13_wrong(n, R):
    K = components(n, R)
    rhs = 0
    for sig in set_partitions(K):
        prod = 1
        for blk in sig:
            B = frozenset().union(*blk)
            RB = {(a, b) for a, b in R if a in B and b in B}
            prod *= len(lin_ext(B, RB))
        rhs += prod
    return rhs


def OP(n, R):
    """Order-preserving partitions: quotient digraph acyclic."""
    out = set()
    for part in set_partitions(range(n)):
        blk = {x: i for i, b in enumerate(part) for x in b}
        edges = {(blk[a], blk[b]) for a, b in R if blk[a] != blk[b]}
        # acyclic?
        k = len(part)
        indeg = {i: 0 for i in range(k)}
        for a, b in edges:
            indeg[b] += 1
        q = [i for i in range(k) if indeg[i] == 0]
        seen = 0
        while q:
            i = q.pop()
            seen += 1
            for a, b in edges:
                if a == i:
                    indeg[b] -= 1
                    if indeg[b] == 0:
                        q.append(b)
        if seen == k:
            out.add(frozenset(frozenset(b) for b in part))
    return out


def zset_to_partition(n, Z, pairs):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            x = par[x]
        return x
    for e in Z:
        i, j = pairs[e]
        par[f(i)] = f(j)
    blocks = {}
    for x in range(n):
        blocks.setdefault(f(x), set()).add(x)
    return frozenset(frozenset(b) for b in blocks.values())


def refines(p1, p2):
    return all(any(b <= c for c in p2) for b in p1)


def audit_braid(n, log=print):
    N, pairs = braid(n)
    A = Arr(f"braid{n}", N)
    cones = A.topcones()
    posets = all_posets(n)
    check("[braid]", len(cones) == len(posets), f"n={n} #cones {len(cones)} != #posets {len(posets)}")
    seenP = set()
    for mk in cones:
        K = Cone(A, mk)
        R = set()
        for e, s in K.Smax.items():
            i, j = pairs[e]
            # sign s of x_i - x_j on V: s = -1 means x_i < x_j, i.e. i <_P j
            R.add((i, j) if s == -1 else (j, i))
        R = frozenset(R)
        seenP.add(R)
        # Lin P = chambers of V
        lp = lin_ext(range(n), R)
        check("[braid]", len(lp) == len(K.V), f"n={n} |Lin|")
        parts = {zset_to_partition(n, Z, pairs): Z for Z in K.Lam}
        op = OP(n, R)
        check("[braid]", set(parts) == op, f"n={n} Lambda != OP")
        for p1, Z1 in parts.items():
            for p2, Z2 in parts.items():
                check("[braid]", refines(p1, p2) == Cone.le(Z2, Z1), "order")
        m = K.m()
        check("[braid]", m == e_C(range(n), R), f"n={n} m != e_C")
        lhs, rhs = lemma13(n, R)
        check("[braid]", lhs == rhs, f"n={n} Lemma 1.3")
    check("[braid]", seenP == set(posets), f"n={n} cones != posets")
    log(f"  braid n={n}: {len(cones)} cones = {len(posets)} labeled posets; "
        "Lambda=OP^op, m=e_C, Lemma 1.3 checked")
    return A


def random_poset(n, rng, prob):
    perm = list(range(n))
    rng.shuffle(perm)
    R = set()
    for a in range(n):
        for b in range(a + 1, n):
            if rng.random() < prob:
                R.add((perm[a], perm[b]))
    changed = True
    while changed:
        changed = False
        for (a, b) in list(R):
            for (c, d) in list(R):
                if b == c and (a, d) not in R:
                    R.add((a, d))
                    changed = True
    return frozenset(R)


# ----------------------------------------------------------------- equivariance

def signed_perms(d):
    for perm in itertools.permutations(range(d)):
        for signs in itertools.product((1, -1), repeat=d):
            yield perm, signs


def act(g, x):
    perm, signs = g
    y = [0] * len(x)
    for i in range(len(x)):
        y[perm[i]] = signs[i] * x[i]
    return tuple(y)


def gdet(g):
    perm, signs = g
    M = [[0] * len(perm) for _ in perm]
    for i in range(len(perm)):
        M[perm[i]][i] = signs[i]
    return int(det(M))


def check_equivariance(A):
    rhos = {C: rho(A, C) for C in A.chambers}
    zrep = {}
    for F in A.faces:
        zrep.setdefault(A.z(F), F)
    cnt = 0
    for g in signed_perms(A.d):
        dg = gdet(g)
        zmap = {Z: A.z(A.sv(act(g, A.pt[F]))) for Z, F in zrep.items()}
        for C in A.chambers:
            gC = A.sv(act(g, A.pt[C]))
            img = {}
            for k, v in rhos[C].items():
                kk = tuple(zmap[Z] for Z in k)
                img[kk] = img.get(kk, 0) + v
            want = {k: dg * v for k, v in rhos[gC].items()}
            check("[eqv]", img == want, f"{A.name}")
            cnt += 1
    return cnt


# ----------------------------------------------------------------- controls

def controls(log=print):
    """Each control must FAIL its predicate."""
    res = {}
    # (1) Theorem 2 summed over ALL of Lambda(V) instead of flats in lin V.
    A = Arr("A3", braid(4)[0])
    bad = 0
    for mk in A.topcones():
        K = Cone(A, mk)
        s = sum((-1) ** A.codim(Z) * mu_interval(K.Lam, K.le, Z, K.top) if Z else 1
                for Z in K.Lam)
        bad += s != len(K.V)
    res["zas_over_all_Lambda"] = bad > 0
    # (2) Non-convex chamber set (two opposite chambers of A_2): the
    #     Zaslavsky/wedge statements must fail for the analogous Lambda.
    A2 = Arr("A2", braid(3)[0])
    C1 = A2.chambers[0]
    C2 = tuple(-x for x in C1)
    Vbad = [C1, C2]
    FV = [F for F in A2.faces if leq(F, C1) or leq(F, C2)]
    lam = sorted({A2.z(F) for F in FV}, key=len, reverse=True)
    m = (-1) ** 2 * mu_interval(lam, Cone.le, frozenset(range(A2.n)), frozenset())
    # lineality of a non-convex set: no S_max; the sum over L=R^2 of all flats
    tot = sum((-1) ** A2.codim(Z) * mu_interval(lam, Cone.le, Z, frozenset()) if Z else 1
              for Z in lam)
    res["nonconvex_zas"] = tot != len(Vbad)
    # (3) Lemma 1.3 with |Lin(P|_B)| in place of e_C(P|_B): 2-antichain.
    R = frozenset()
    res["lemma13_with_Lin"] = lemma13_wrong(2, R) != len(lin_ext(range(2), R))
    # (4) Prop. 3 with the whole face monoid F(V) in place of Sigma_L:
    #     the multiplicity formula fails on some non-pointed proper cone.
    bad = 0
    for mk in A.topcones():
        K = Cone(A, mk)
        if not K.flatsL or len(K.V) == len(A.chambers):
            continue
        rows = []
        vi = {C: i for i, C in enumerate(K.V)}
        for H in K.FV:
            if H == A.O:
                continue
            for D in K.V:
                row = [0] * len(K.V)
                for C in K.V:
                    if tprod(H, C) == D:
                        row[vi[C]] += 1
                if any(row):
                    rows.append(row)
        dl = len(nullspace_Q(rows, len(K.V))) if rows else len(K.V)
        bad += dl != K.m()
    res["prop3_with_FV"] = bad > 0
    # (5) Saliola recursion without the left factor x: x e_0 = 0 fails.
    K = Cone(A, (1 << len(A.chambers)) - 1)
    e0w = saliola_e0(A, K, wrong=True)
    okw = all(not alg_mul({x: 1}, e0w) for x in K.SigmaL if x != A.O) and alg_mul(e0w, e0w) == e0w
    res["saliola_wrong_recursion"] = not okw
    # (6) lune relation with incoherent orientations (normalize each rho_C so
    #     its lexicographically first coefficient is +1): some lune fails.
    rh = {}
    for C in A.chambers:
        r = rho(A, C)
        k0 = min(r, key=lambda k: [sorted(z) for z in k])
        s = 1 if r[k0] > 0 else -1
        rh[C] = {k: s * v for k, v in r.items()}
    bad = 0
    for L in lunes(A):
        acc = {}
        for C in L:
            for k, v in rh[C].items():
                acc[k] = acc.get(k, 0) + v
        bad += any(acc.values())
    res["lune_incoherent_signs"] = bad > 0
    # (7) chamber-cycle span off top-cones: for the non-convex pair
    #     {C_0, C_2} of A_3 the two cycles cannot span the rank-3 group.
    ch = A.chambers
    FV = [F for F in A.faces if leq(F, ch[0]) or leq(F, ch[2])]
    lam = [Z for Z in {A.z(F) for F in FV} if Z and len(Z) != A.n]
    h = reduced_homology_ranks(lam, Cone.lt, P_BIG)
    keys = {}
    rows = []
    for C in (ch[0], ch[2]):
        row = {}
        for k, v in rho(A, C).items():
            row[keys.setdefault(k, len(keys))] = v
        rows.append(row)
    res["rho_span_nonconvex"] = rank_mod(rows, P_BIG) != h.get(A.d - 2, 0)
    # (8) homology instrument on known spaces: a circle (proper part of the
    #     face lattice of a square) and S^0 (two incomparable points).
    sq = ["a", "b", "c", "d", "ab", "bc", "cd", "da"]
    lt = lambda x, y: len(x) == 1 and len(y) == 2 and x in y
    h = reduced_homology_ranks(sq, lt, 2)
    res["hom_instrument_circle"] = h.get(1) == 1 and h.get(0) == 0
    h = reduced_homology_ranks(["x", "y"], lambda u, v: False, 2)
    res["hom_instrument_S0"] = h.get(0) == 1
    for k, v in res.items():
        log(f"  [CTL] {k}: {'fires' if v else 'DOES NOT FIRE'}")
        check("[CTL]", v, k)
    return all(res.values())


# ----------------------------------------------------------------- main

def arrangements():
    def B(n):
        N = []
        for i in range(n):
            v = [0] * n
            v[i] = 1
            N.append(v)
        for i in range(n):
            for j in range(i + 1, n):
                for s in (1, -1):
                    v = [0] * n
                    v[i], v[j] = 1, s
                    N.append(v)
        return N

    def D(n):
        N = []
        for i in range(n):
            for j in range(i + 1, n):
                for s in (1, -1):
                    v = [0] * n
                    v[i], v[j] = 1, s
                    N.append(v)
        return N
    generic5 = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1), (1, 2, -3)]
    rng = random.Random(20261030)

    def rnd(k, d, b):
        out = []
        while len(out) < k:
            v = tuple(rng.randint(-b, b) for _ in range(d))
            if any(v) and all(_rank_rows([v, w]) == 2 for w in out):
                out.append(v)
        return out
    rnd7 = rnd(7, 3, 3)
    rnd6 = rnd(6, 4, 2)
    return B, D, generic5, rnd7, rnd6


def main():
    out = []
    log = lambda s: (print(s), out.append(s))
    log("audit_general_theory_cones.py (mg-7ab20)")
    B, D, generic5, rnd7, rnd6 = arrangements()
    log("[arrangements: all top-cones unless noted]")
    audit_arr(Arr("A2", braid(3)[0]), log=log)
    audit_arr(Arr("B2", B(2)), log=log)
    audit_arr(Arr("A3", braid(4)[0]), log=log)
    audit_arr(Arr("B3", B(3)), log=log)
    audit_arr(Arr("generic5", generic5), log=log)
    audit_arr(Arr("rand7_R3", rnd7), log=log)
    A4 = Arr("A4", braid(5)[0])
    audit_arr(A4, do_hom=True, do_sal=False, log=log)
    R4 = Arr("rand6_R4", rnd6)
    audit_arr(R4, do_sal=False, log=log)
    D4 = Arr("D4", D(4))
    rng = random.Random(7)
    allc = D4.topcones()
    sample = rng.sample(allc, 60)
    audit_arr(D4, cones=sample, do_sal=False, log=log)
    log("[eqv] g rho_C = det(g) rho_{gC}:")
    for A in (Arr("B2", B(2)), Arr("B3", B(3))):
        log(f"  {A.name}: {check_equivariance(A)} (g, C) pairs")
    log("[braid]")
    for n in (2, 3, 4, 5):
        audit_braid(n, log=log)
    rng = random.Random(11)
    cnt = 0
    for n in (6, 7):
        for _ in range(60):
            R = random_poset(n, rng, rng.choice((0.1, 0.2, 0.35)))
            lhs, rhs = lemma13(n, R)
            check("[braid]", lhs == rhs, f"Lemma 1.3 random n={n}")
            cnt += 1
    log(f"  Lemma 1.3 on {cnt} random posets with n = 6, 7")
    log("[CTL]")
    controls(log=log)
    log("RESULT: " + ("ALL CHECKS PASS" if not FAIL else f"{len(FAIL)} FAILURES"))
    for f in FAIL[:30]:
        log("  FAIL " + f)
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
