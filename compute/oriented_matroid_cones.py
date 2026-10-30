#!/usr/bin/env python3
"""Checks for notes/oriented_matroid_cones.md.  Plain Python 3, no imports
from the other scripts in this directory.

An oriented matroid M is given by a chirotope chi on r-subsets of E = [n].
Its covectors are generated from the cocircuits by composition.  For every
nonempty T-convex set of topes V = {T : T_S = s} (all s in {+,0,-}^E) we use

  F(V)      = covectors X with X_e in {0, s_e} for e in S (closed faces),
  Lambda(V) = {z(X) : X in F(V)}, ordered by REVERSE inclusion of zero sets
              (bottom E = z(0), top {} = z(tope)),
  m(V)      = (-1)^r mu_{Lambda(V)}(E, {}),
  S_max(V)  = elements of constant sign on V.

Checks (each one is a statement of the note):
  [chi]     chi satisfies the chirotope axioms (alternating, bases of a
            matroid, 3-term Grassmann-Pluecker); the covector set is closed
            under composition and negation, and cocircuit elimination holds.
  [nonreal] (non-Pappus only) the zero set of chi is exactly the 8 Pappus
            lines other than the perturbed one, so the underlying matroid is
            the non-Pappus matroid, which is not representable over any
            field by Pappus's theorem.
  [sphere]  Delta(L - 0) has the Z/p-homology of S^{r-1}, its top cycle
            space is spanned by one cycle omega with all coefficients +-1,
            and every tope boundary Delta((0,T)) has the homology of S^{r-2}.
  [lem02]   Lemma 0.2-OM: for every s in {+,*,-}^E, K(s) = {X != 0 : X
            conforms to s} is empty, has the homology of a sphere (exactly
            when K(s) = -K(s)), or is acyclic; acyclic whenever s has a
            nonzero entry and some tope conforms to s.  Also every fibre K_Z
            of Theorem 1 is a sphere of dimension r - rk Z - 1 if S_max is
            contained in Z, and acyclic otherwise.
  [flatL]   every flat Z containing S_max(V) lies in Lambda(V).
  [zas]     #V = sum_{flats Z >= S_max(V)} (-1)^{rk Z} mu_Lambda(Z, {})
            (Theorem 2-OM).
  [wedge]   reduced homology of Delta(proper part of Lambda(V)) is zero
            except in degree r-2, where it has rank m(V) (Theorem 1-OM).
  [brown]   sum_{Z >= S_max} mu(E, Z) c_Z = m(V), c_Z = #{T in V : T >= X}
            for any X with z(X) = Z (Prop. 3(b)-OM).
  [rho]     the chamber cycles rho_C, C in V, span the top cycle space of
            Delta(proper part of Lambda(V)) (Theorem C(i)-OM).
  [propB]   C -> rho_C (all topes) has rank |mu(L(M))| and kills every
            non-singleton lune, at chain level over Z (Prop. B-OM).
  [q=m]     q(V) = dim Gamma_V/(Gamma_V cap Lune) = m(V), exactly over Q
            (Theorem C(ii)-OM); and span{non-singleton lunes in V} has
            dimension #V - m(V) (Theorem C(iii), (G1)).
  [eq]      Aut(M) = signed permutations preserving the covectors; for g in
            Aut(M): g.omega = det(g) omega defines det(g), and
            g.rho_C = det(g) rho_{gC} at chain level; for every g in
            Stab(V): tr(g | H~_{r-2}(Lambda(V))) (Lefschetz, from fixed
            chains) = det(g) tr(g | (Gamma_V + Lune)/Lune) (Theorem C(iv)).
            Control: the count of cones on which the identity holds with
            det omitted.

Exit status 0 iff every asserted check passes.

Run from compute/:  python3 oriented_matroid_cones.py [--quick]
"""

import argparse
import itertools
import sys
from fractions import Fraction

PR = 2147483647  # prime for homology ranks over GF(p)


# ---------------------------------------------------------------------------
# linear algebra


def rank_mod_p(rows, p=PR):
    """Rank over GF(p) of sparse rows given as dicts col -> int."""
    pivots = {}
    rank = 0
    for row in rows:
        r = {k: v % p for k, v in row.items() if v % p}
        while r:
            c = min(r)
            if c in pivots:
                prow = pivots[c]
                f = r[c]
                for k, v in prow.items():
                    nv = (r.get(k, 0) - f * v) % p
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
            else:
                inv = pow(r[c], p - 2, p)
                r = {k: v * inv % p for k, v in r.items()}
                pivots[c] = r
                rank += 1
                break
    return rank


def kernel_mod_p(cols_of_rows, ncols, p=PR):
    """Basis of {x : sum_j x_j row_j = 0} where cols_of_rows[j] is a sparse
    vector (dict) -- i.e. the left kernel of the matrix with these rows."""
    # Augment each row with an identity tag and eliminate.
    pivots = {}
    kernel = []
    for j, row in enumerate(cols_of_rows):
        r = {("v", k): v % p for k, v in row.items() if v % p}
        r[("t", j)] = 1
        while True:
            vk = [k for k in r if k[0] == "v"]
            if not vk:
                kernel.append({k[1]: v for k, v in r.items()})
                break
            c = min(vk)
            if c in pivots:
                prow = pivots[c]
                f = r[c]
                for k, v in prow.items():
                    nv = (r.get(k, 0) - f * v) % p
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
            else:
                inv = pow(r[c], p - 2, p)
                r = {k: v * inv % p for k, v in r.items()}
                pivots[c] = r
                break
    return kernel


def rref_q(rows, ncols):
    """Reduced row echelon form over Q of dense rows; returns (rows, pivots)."""
    M = [[Fraction(x) for x in row] for row in rows]
    piv = []
    rk = 0
    for c in range(ncols):
        pr = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[rk], M[pr] = M[pr], M[rk]
        inv = 1 / M[rk][c]
        M[rk] = [x * inv for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[rk])]
        piv.append(c)
        rk += 1
    return M[:rk], piv


def rank_q(vectors):
    if not vectors:
        return 0
    return len(rref_q(vectors, len(vectors[0]))[1])


def solve_q(basis, v):
    """Coordinates of v in the (independent) list basis, over Q."""
    k = len(basis)
    n = len(v)
    # Solve sum_i c_i basis_i = v via elimination on the transposed system.
    A = [[Fraction(basis[i][j]) for i in range(k)] + [Fraction(v[j])] for j in range(n)]
    R, piv = rref_q(A, k + 1)
    assert k not in piv, "v not in span"
    c = [Fraction(0)] * k
    for row, pc in zip(R, piv):
        c[pc] = row[k]
    return c


# ---------------------------------------------------------------------------
# chirotopes and covectors


def det(m):
    m = [[Fraction(x) for x in row] for row in m]
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


def chirotope_from_vectors(vecs):
    r = len(vecs[0])
    return {B: sgn(det([vecs[i] for i in B]))
            for B in itertools.combinations(range(len(vecs)), r)}


def chi_eval(chi, tup):
    """chi on an arbitrary tuple (alternating extension)."""
    if len(set(tup)) < len(tup):
        return 0
    perm = sorted(range(len(tup)), key=lambda i: tup[i])
    # sign of the sorting permutation
    s = 1
    seen = [False] * len(perm)
    for i in range(len(perm)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = perm[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s * chi[tuple(sorted(tup))]


def check_chirotope(chi, n, r):
    """Alternating by construction; check bases form a matroid (exchange) and
    the 3-term Grassmann-Pluecker relations.  Returns (ok, message)."""
    bases = [frozenset(B) for B, v in chi.items() if v]
    if not bases:
        return False, "chi identically zero"
    bset = set(bases)
    for B1 in bases:
        for B2 in bases:
            for x in B1 - B2:
                if not any((B1 - {x}) | {y} in bset for y in B2 - B1):
                    return False, "basis exchange fails"
    for sigma in itertools.combinations(range(n), r - 2):
        rest = [e for e in range(n) if e not in sigma]
        for ys in itertools.combinations(rest, 4):
            y1, y2, y3, y4 = ys
            t = lambda a, b: chi_eval(chi, sigma + (a, b))
            vals = {t(y1, y2) * t(y3, y4), -t(y1, y3) * t(y2, y4),
                    t(y1, y4) * t(y2, y3)}
            if not (vals == {0} or {-1, 1} <= vals):
                return False, "3-term GP fails at %s %s" % (sigma, ys)
    return True, "ok"


def cocircuits(chi, n, r):
    out = set()
    for A in itertools.combinations(range(n), r - 1):
        y = tuple(chi_eval(chi, A + (e,)) for e in range(n))
        if any(y):
            out.add(y)
            out.add(tuple(-v for v in y))
    return sorted(out)


def compose(x, y):
    return tuple(a if a else b for a, b in zip(x, y))


def covectors_from_cocircuits(cc, n):
    L = {tuple([0] * n)} | set(cc)
    frontier = set(cc)
    while frontier:
        new = set()
        for x in frontier:
            for y in list(L):
                for z in (compose(x, y), compose(y, x)):
                    if z not in L:
                        new.add(z)
        L |= new
        frontier = new
    return sorted(L)


def check_covectors(L, cc):
    Ls = set(L)
    for x in L:
        if tuple(-v for v in x) not in Ls:
            return False, "not closed under negation"
    for x in L:
        for y in L:
            if compose(x, y) not in Ls:
                return False, "not closed under composition"
    # cocircuit elimination: for X, Y cocircuits, X != -Y, e in S(X,Y), there
    # is a cocircuit Z with Z_e = 0 and Z^+ <= X^+ u Y^+, Z^- <= X^- u Y^-.
    for x in cc:
        for y in cc:
            if x == tuple(-v for v in y):
                continue
            for e in range(len(x)):
                if x[e] and x[e] == -y[e]:
                    if not any(z[e] == 0 and all(
                            zz == 0 or zz == a or zz == b
                            for zz, a, b in zip(z, x, y)) for z in cc):
                        return False, "cocircuit elimination fails"
    return True, "ok"


def zeros(x):
    return frozenset(i for i, v in enumerate(x) if v == 0)


def leq(x, y):
    """Face order: x <= y iff x_e in {0, y_e} for all e."""
    return all(a == 0 or a == b for a, b in zip(x, y))


# ---------------------------------------------------------------------------
# order complexes


def chains_of(elems, less):
    """All nonempty chains of the poset (elems, less), as increasing tuples of
    indices into elems, grouped by length."""
    n = len(elems)
    up = [[j for j in range(n) if less(elems[i], elems[j])] for i in range(n)]
    out = {}
    stack = [(i,) for i in range(n)]
    while stack:
        c = stack.pop()
        out.setdefault(len(c), []).append(c)
        for j in up[c[-1]]:
            stack.append(c + (j,))
    return out


def boundary_rows(chs, k):
    """Rows (one per k-chain) of the boundary map C_{k} -> C_{k-1} (chains of
    length k = (k-1)-simplices); returned as dicts over (k-1)-chain indices."""
    idx = {c: i for i, c in enumerate(chs.get(k - 1, []))}
    rows = []
    for c in chs.get(k, []):
        row = {}
        for i in range(len(c)):
            f = c[:i] + c[i + 1:]
            row[idx[f]] = row.get(idx[f], 0) + (-1) ** i
        rows.append(row)
    return rows


def reduced_betti(elems, less, p=PR):
    """Reduced Betti numbers (index = degree, -1..top) of Delta(poset) over
    GF(p).  Empty poset: betti[-1] = 1."""
    if not elems:
        return {-1: 1}
    chs = chains_of(elems, less)
    top = max(chs)
    ranks = {}
    for k in range(1, top + 1):
        if k == 1:
            ranks[1] = 1 if chs[1] else 0  # augmentation C_0 -> Z
        else:
            ranks[k] = rank_mod_p(boundary_rows(chs, k), p)
    betti = {}
    for k in range(1, top + 1):
        dimc = len(chs[k])
        betti[k - 1] = dimc - ranks[k] - ranks.get(k + 1, 0)
    betti[-1] = 0
    return {d: b for d, b in betti.items() if b}


def sphere_betti(dim):
    return {dim: 1}


# ---------------------------------------------------------------------------
# examples


def pappus_points():
    """A realization of the Pappus configuration: A,B,C on one line, a,b,c on
    another, X = Ab.aB, Y = Ac.aC, Z = Bc.bC; returns 9 homogeneous vectors
    and the index triple (X, Y, Z) of the Pappus line."""
    def line(p, q):
        return (p[1] * q[2] - p[2] * q[1], p[2] * q[0] - p[0] * q[2],
                p[0] * q[1] - p[1] * q[0])

    def meet(l1, l2):
        x = line(l1, l2)
        return tuple(Fraction(v, 1) / x[2] for v in x)

    A, B, C = (0, 0, 1), (2, 0, 1), (7, 0, 1)
    a, b, c = (1, 3, 1), (4, 3, 1), (13, 3, 1)
    X = meet(line(A, b), line(a, B))
    Y = meet(line(A, c), line(a, C))
    Z = meet(line(B, c), line(b, C))
    pts = [A, B, C, a, b, c, X, Y, Z]
    return [tuple(Fraction(v) for v in p) for p in pts], (6, 7, 8)


def non_pappus(sign):
    vecs, xyz = pappus_points()
    chi = chirotope_from_vectors(vecs)
    pap_zero = sorted(B for B, v in chi.items() if v == 0)
    assert xyz in pap_zero
    chi2 = dict(chi)
    chi2[xyz] = sign
    return chi2, pap_zero, xyz


def braid_vectors(n):
    """e_i - e_j (i < j) in the basis e_1-e_2, ..., e_{n-1}-e_n of the
    sum-zero hyperplane: e_i - e_j = sum_{k=i}^{j-1} (e_k - e_{k+1})."""
    out = []
    for i, j in itertools.combinations(range(n), 2):
        out.append(tuple(1 if i <= k < j else 0 for k in range(n - 1)))
    return out


def type_b_vectors(n):
    out = []
    for i in range(n):
        out.append(tuple(1 if k == i else 0 for k in range(n)))
    for i, j in itertools.combinations(range(n), 2):
        out.append(tuple(1 if k in (i, j) else 0 for k in range(n)))
        out.append(tuple(1 if k == i else (-1 if k == j else 0) for k in range(n)))
    return out


# ---------------------------------------------------------------------------
# automorphisms


def automorphisms(L, n):
    """Signed permutations g = (perm, sgn) with g(L) = L, where
    (g x)_{perm[e]} = sgn[e] x_e.  Backtracking on the cocircuits."""
    Ls = set(L)
    cc = [x for x in L if any(x) and not any(
        y != x and any(y) and leq(y, x) for y in L)]
    out = []

    def act(perm, sg, x):
        y = [0] * n
        for e in range(n):
            y[perm[e]] = sg[e] * x[e]
        return tuple(y)

    def partial_ok(perm, sg):
        k = len(perm)
        # every cocircuit restricted to the first k coordinates must map to
        # the restriction of some cocircuit on the image coordinates
        img = perm
        restr = {tuple(y[img[e]] for e in range(k)) for y in cc}
        for x in cc:
            if tuple(sg[e] * x[e] for e in range(k)) not in restr:
                return False
        return True

    def rec(perm, sg):
        if len(perm) == n:
            if all(act(perm, sg, x) in Ls for x in cc):
                out.append((tuple(perm), tuple(sg)))
            return
        for t in range(n):
            if t in perm:
                continue
            for s in (1, -1):
                perm.append(t)
                sg.append(s)
                if partial_ok(perm, sg):
                    rec(perm, sg)
                perm.pop()
                sg.pop()

    rec([], [])
    return out


def act_cov(g, x):
    perm, sg = g
    y = [0] * len(x)
    for e in range(len(x)):
        y[perm[e]] = sg[e] * x[e]
    return tuple(y)


def act_set(g, Z):
    return frozenset(g[0][e] for e in Z)


# ---------------------------------------------------------------------------
# the main run


def mobius_from_bottom(elems, less, bottom):
    """mu(bottom, x) for all x in elems."""
    n = len(elems)
    above = {x: sum(1 for y in elems if less(y, x)) for x in elems}
    mu = {}
    for x in sorted(elems, key=lambda x: above[x]):  # bottom first
        if x == bottom:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if less(y, x))
    return mu


def mobius_to_top(elems, less, top):
    """mu(x, top) for all x in elems."""
    n = len(elems)
    below = {elems[i]: sum(1 for j in range(n) if less(elems[i], elems[j])) for i in range(n)}
    order = sorted(elems, key=lambda x: below[x])  # top first
    mu = {}
    for x in order:
        if x == top:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if less(x, y))
    return mu


def run(name, chi, n, r, out, quick=False, extra=None):
    ok = True

    def report(tag, good, total, note=""):
        nonlocal ok
        flag = good == total
        ok = ok and flag
        out.write("  [%s] %d/%d%s\n" % (tag, good, total, note))

    out.write("[%s] rank=%d n=%d\n" % (name, r, n))
    good, msg = check_chirotope(chi, n, r)
    cc = cocircuits(chi, n, r)
    L = covectors_from_cocircuits(cc, n)
    good2, msg2 = check_covectors(L, cc)
    report("chi", int(good and good2), 1, " (%s; %s)" % (msg, msg2))
    if extra:
        g_, t_, note = extra(chi)
        report("nonreal", g_, t_, note)
    zero = tuple([0] * n)
    topes = [x for x in L if all(x)]
    tidx = {t: i for i, t in enumerate(topes)}
    flats = sorted({zeros(x) for x in L}, key=lambda Z: -len(Z))
    rkZ = {}
    # rank of a flat: r minus the length of a maximal chain of covectors above
    for Z in flats:
        rkZ[Z] = None
    covs_by_z = {}
    for x in L:
        covs_by_z.setdefault(zeros(x), []).append(x)
    # dim(x) = length of the longest chain 0 < ... < x
    dimx = {zero: 0}
    for x in sorted(L, key=lambda x: -len(zeros(x))):
        if x == zero:
            continue
        dimx[x] = 1 + max(dimx[y] for y in dimx if y != x and leq(y, x) and zeros(y) > zeros(x))
    for Z in flats:
        rkZ[Z] = r - dimx[covs_by_z[Z][0]]
    out.write("  covectors=%d topes=%d flats=%d\n" % (len(L), len(topes), len(flats)))
    assert all(dimx[t] == r for t in topes)

    # [sphere]
    nz = [x for x in L if x != zero]
    chs = chains_of(nz, lambda a, b: a != b and leq(a, b))
    b = reduced_betti(nz, lambda a, b: a != b and leq(a, b))
    top_rows = boundary_rows(chs, r)
    ker = kernel_mod_p(top_rows, len(chs[r - 1]))
    s_ok = b == sphere_betti(r - 1) and len(ker) == 1
    omega = {}
    if s_ok:
        k0 = ker[0]
        f = pow(k0[min(k0)], PR - 2, PR)
        for j, v in k0.items():
            v = v * f % PR
            v = v - PR if v > PR // 2 else v
            omega[chs[r][j]] = v
        s_ok = all(abs(v) == 1 for v in omega.values()) and len(omega) == len(chs[r])
        # integral cycle check
        bd = {}
        for c, v in omega.items():
            for i in range(len(c)):
                fc = c[:i] + c[i + 1:]
                bd[fc] = bd.get(fc, 0) + (-1) ** i * v
        s_ok = s_ok and all(v == 0 for v in bd.values())
    nb = 0
    for T in topes:
        below = [x for x in nz if x != T and leq(x, T)]
        if reduced_betti(below, lambda a, b: a != b and leq(a, b)) == sphere_betti(r - 2):
            nb += 1
    report("sphere", int(s_ok) + nb, 1 + len(topes),
           " (L-0 is a homology S^%d with a +-1 fundamental cycle; tope boundaries)" % (r - 1))

    # [lem02] trichotomy over all s in {+,*,-}^n
    betti_cache = {}

    def kbetti(K):
        key = frozenset(K)
        if key not in betti_cache:
            Kl = sorted(key)
            betti_cache[key] = reduced_betti(Kl, lambda a, b: a != b and leq(a, b))
        return betti_cache[key]

    good = total = 0
    svecs = itertools.product((1, 0, -1), repeat=n)
    if quick:
        svecs = itertools.islice(svecs, 0, None, 7)
    for s in svecs:
        K = [x for x in nz if all(a == 0 or c == 0 or a == c for a, c in zip(x, s))]
        bt = kbetti(K)
        sym = set(K) == {tuple(-v for v in x) for x in K}
        has_tope = any(all(x) for x in K)
        if not K:
            g = True
        elif sym:
            # a sphere of dimension (max dim in K) - 1
            dK = max(dimx[x] for x in K)
            g = bt == sphere_betti(dK - 1)
        else:
            g = bt == {}
        if has_tope and any(s):
            g = g and bt == {}
        good += g
        total += 1
    report("lem02", good, total, " (sign conditions s; %d distinct K)" % len(betti_cache))

    # Lune
    lunes = set()
    for H in nz:
        zH = zeros(H)
        for D in topes:
            if leq(H, D):
                lunes.add(frozenset(tidx[C] for C in topes
                                    if all(C[e] == D[e] for e in zH)))
    lunes = sorted(lunes, key=sorted)
    assert all(len(l) > 1 for l in lunes)
    NT = len(topes)
    lune_rows = [[1 if i in l else 0 for i in range(NT)] for l in lunes]
    R, piv = rref_q(lune_rows, NT)
    nonpiv = [c for c in range(NT) if c not in piv]
    pivrow = {c: R[i] for i, c in enumerate(piv)}

    def quot(i):
        """Image of tope i in Gamma/Lune, coordinates on the non-pivot cols."""
        if i in pivrow:
            return [-pivrow[i][c] for c in nonpiv]
        return [Fraction(1 if c == i else 0) for c in nonpiv]

    qimg = [quot(i) for i in range(NT)]

    # full flat lattice and |mu|
    lessZ = lambda A, B: A != B and A > B   # reverse inclusion
    muL = mobius_to_top(flats, lessZ, frozenset())
    mu_all = abs(muL[frozenset(range(n))])
    out.write("  |mu(L(M))|=%d dim Gamma/Lune=%d\n" % (mu_all, len(nonpiv)))

    # chamber cycles rho_C (chains of flats, increasing in Lambda order)
    def rho(C):
        ch = {}
        for c, v in omega.items():
            if nz[c[-1]] != C:
                continue
            for i in range(len(c)):
                fc = c[:i] + c[i + 1:]
                if i == len(c) - 1:
                    key = tuple(zeros(nz[j]) for j in fc)
                    ch[key] = ch.get(key, 0) + (-1) ** i * v
        return {k: v for k, v in ch.items() if v}

    rhos = [rho(C) for C in topes]
    # [propB]
    keys = sorted({k for rr in rhos for k in rr}, key=lambda t: [sorted(z) for z in t])
    kidx = {k: i for i, k in enumerate(keys)}
    rk_rho = rank_mod_p([{kidx[k]: v for k, v in rr.items()} for rr in rhos])
    lune_dead = 0
    for l in lunes:
        tot = {}
        for i in l:
            for k, v in rhos[i].items():
                tot[k] = tot.get(k, 0) + v
        lune_dead += all(v == 0 for v in tot.values())
    report("propB", int(rk_rho == mu_all == len(nonpiv)) + lune_dead, 1 + len(lunes),
           " (rank of C->rho_C = %d; lunes killed at chain level)" % rk_rho)

    # automorphisms and det
    auts = automorphisms(L, n)
    nidx = {x: i for i, x in enumerate(nz)}
    dets = {}
    eq_rho = 0
    for g in auts:
        gom = {tuple(nidx[act_cov(g, nz[j])] for j in c): v for c, v in omega.items()}
        # g preserves order, so images of chains are chains in the same order
        sgn_ = None
        good_g = True
        for c, v in gom.items():
            w = omega.get(c)
            if w is None:
                good_g = False
                break
            s_ = v * w
            if sgn_ is None:
                sgn_ = s_
            elif s_ != sgn_:
                good_g = False
                break
        dets[g] = sgn_ if good_g else None
        if good_g:
            ok_r = True
            for i, C in enumerate(topes):
                gC = tidx[act_cov(g, C)]
                img = {tuple(act_set(g, z) for z in k): v for k, v in rhos[i].items()}
                tgt = {k: sgn_ * v for k, v in rhos[gC].items()}
                if img != tgt:
                    ok_r = False
                    break
            eq_rho += ok_r
    report("eq-rho", eq_rho, len(auts),
           " (|Aut M|=%d signed perms; g.omega = det(g) omega, g.rho_C = det(g) rho_gC)"
           % len(auts))

    # cones
    seen = {}
    for s in itertools.product((1, 0, -1), repeat=n):
        V = frozenset(i for i, T in enumerate(topes)
                      if all(c == 0 or T[e] == c for e, c in enumerate(s)))
        if V and V not in seen:
            seen[V] = s
    cones = list(seen)
    out.write("  cones=%d\n" % len(cones))
    E = frozenset(range(n))
    cnt = dict.fromkeys(["flatL", "zas", "wedge", "fib", "brown", "rho", "q=m",
                         "G1", "eq"], 0)
    ctrl = 0
    stab_sum = 0
    for V in cones:
        Vt = [topes[i] for i in V]
        Smax = {e: Vt[0][e] for e in range(n) if len({t[e] for t in Vt}) == 1}
        SZ = frozenset(Smax)
        FV = [x for x in L if all(x[e] in (0, c) for e, c in Smax.items())]
        Lam = sorted({zeros(x) for x in FV}, key=lambda Z: -len(Z))
        lamset = set(Lam)
        flL = [Z for Z in flats if Z >= SZ]
        cnt["flatL"] += all(Z in lamset for Z in flL)
        muV = mobius_to_top(Lam, lessZ, frozenset())
        mV = (-1) ** r * muV[E]
        zs = sum((-1) ** rkZ[Z] * muV[Z] for Z in flL)
        cnt["zas"] += zs == len(V)
        proper = [Z for Z in Lam if Z != E and Z]
        bt = reduced_betti(proper, lessZ)
        cnt["wedge"] += (bt == ({r - 2: mV} if mV else {})) and mV >= 0
        # fibres K_Z (Lemma 0.2-OM as used in Theorem 1)
        fg = True
        for Z in proper:
            K = [x for x in FV if x != zero and zeros(x) >= Z]
            exp = sphere_betti(r - rkZ[Z] - 1) if Z >= SZ else {}
            if kbetti(K) != exp:
                fg = False
        cnt["fib"] += fg
        # brown
        muB = mobius_from_bottom(flats, lessZ, E)
        cZ = {}
        for Z in flL:
            X = covs_by_z[Z][0]
            cZ[Z] = sum(1 for T in Vt if leq(X, T))
        cnt["brown"] += sum(muB[Z] * cZ[Z] for Z in flL) == mV
        # rho span = cycle space
        pchs = chains_of(proper, lessZ)
        top_len = r - 1
        cyc_dim = bt.get(r - 2, 0)
        pidx = {tuple(proper[j] for j in c): k for k, c in enumerate(pchs.get(top_len, []))}
        rows = []
        inside = True
        for i in V:
            row = {}
            for k, v in rhos[i].items():
                if k not in pidx:
                    inside = False
                else:
                    row[pidx[k]] = v
            rows.append(row)
        cnt["rho"] += inside and rank_mod_p(rows) == cyc_dim == mV
        # q = m over Q
        q = rank_q([qimg[i] for i in V]) if nonpiv else 0
        cnt["q=m"] += q == mV
        lin = [l for l in lunes if l <= V]
        dl = rank_mod_p([{i: 1 for i in l} for l in lin]) if lin else 0
        cnt["G1"] += dl == len(V) - mV
        # equivariance
        stab = [g for g in auts if frozenset(tidx[act_cov(g, topes[i])] for i in V) == V]
        stab_sum += len(stab)
        Vl = sorted(V)
        basis_idx = []
        bvecs = []
        for i in Vl:
            if rank_q(bvecs + [qimg[i]]) > len(bvecs):
                bvecs.append(qimg[i])
                basis_idx.append(i)
        eg = True
        cg = True
        for g in stab:
            # left: Lefschetz number from g-fixed chains of the proper part
            fixed = {}
            for k, cl in pchs.items():
                fixed[k] = sum(1 for c in cl
                               if all(act_set(g, proper[j]) == proper[j] for j in c))
            lef = -1 + sum((-1) ** (k - 1) * v for k, v in fixed.items())
            left = (-1) ** (r - 2) * lef
            # right: trace on the image of Gamma_V in Gamma/Lune
            tr = Fraction(0)
            for pos, i in enumerate(basis_idx):
                gi = tidx[act_cov(g, topes[i])]
                coords = solve_q(bvecs, qimg[gi])
                tr += coords[pos]
            if left != dets[g] * tr:
                eg = False
            if left != tr:
                cg = False
        cnt["eq"] += eg
        ctrl += cg
    for tag in ["flatL", "zas", "wedge", "fib", "brown", "rho", "q=m", "G1", "eq"]:
        report(tag, cnt[tag], len(cones))
    out.write("  [eq] sum of stabiliser orders %d; control (no det twist) holds on %d/%d cones\n"
              % (stab_sum, ctrl, len(cones)))
    out.write("  => %s\n" % ("PASS" if ok else "FAIL"))
    return ok, {"cones": len(cones), "stab_sum": stab_sum, "ctrl": ctrl,
                "auts": len(auts), "mu": mu_all, "topes": len(topes)}


def nonpappus_extra(pap_zero, xyz):
    def f(chi):
        z = sorted(B for B, v in chi.items() if v == 0)
        exp = [B for B in pap_zero if B != xyz]
        good = z == exp and len(pap_zero) == 9
        return int(good), 1, " (zero triples = the 8 Pappus lines without %s)" % (xyz,)
    return f


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args(argv)
    out = sys.stdout
    allok = True
    vecs = braid_vectors(4)
    ok, _ = run("A3 (realizable control)", chirotope_from_vectors(vecs), len(vecs), 3, out, args.quick)
    allok &= ok
    if not args.quick:
        vecs = type_b_vectors(3)
        ok, _ = run("B3 (realizable control)", chirotope_from_vectors(vecs), len(vecs), 3, out)
        allok &= ok
    pvecs, xyz = pappus_points()
    ok, _ = run("Pappus (realizable control)", chirotope_from_vectors(pvecs), 9, 3, out, args.quick)
    allok &= ok
    signs = (1, -1) if not args.quick else (1,)
    for sg in signs:
        chi, pz, xyz = non_pappus(sg)
        good, msg = check_chirotope(chi, 9, 3)
        if not good:
            out.write("[non-Pappus, chi(XYZ)=%+d] not a chirotope: %s\n" % (sg, msg))
            continue
        ok, _ = run("non-Pappus, chi(XYZ)=%+d" % sg, chi, 9, 3, out, args.quick,
                    extra=nonpappus_extra(pz, xyz))
        allok &= ok
    out.write("ALL %s\n" % ("PASS" if allok else "FAIL"))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
