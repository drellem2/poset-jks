#!/usr/bin/env python3
"""Second independent audit of notes/vanishing_criterion.md.

Exact rational arithmetic, no imports from other compute/ scripts.

Checks, for an arrangement A (hyperplane normals over Q) and a finite group G
of rational linear maps preserving A:

  [Z]    Formula Z: chi_V(g) = sum_{X in Z*(V,g)} mu_{L(A)^g}(0,X) m_X(V),
         with chi_V(g) := (-1)^d det(g) mu(Lambda(V)^g) computed from the
         face poset, and m_X(V) computed as (-1)^k mu of the support lattice
         of the restricted cone |V| cap U in the arrangement {H cap U : H > X}.
  [m>=1] every m_X(V) that occurs is >= 1.
  [mu=chi] mu_{L(A)^g}(0,X) = chi^full_{A^X}(g|_X), the latter computed on
         the restriction A^X as its own arrangement (own face poset).
  [S]    Theorem S: some g-stable top-cone has chi != 0  iff  some X in Z*(g)
         has mu(0,X) != 0 (all top-cones enumerated).
  [lune] for every minimal such X and EVERY g-fixed chamber K of A_X, the
         top-lune V# = {C : C subset K} is g-stable, has lin V# = X and
         chi_{V#}(g) = mu(0,X).
  [S3]   involutions: S-criterion equals "some flat X in ker(g+1) with X + Fix g
         in no hyperplane".
  [PC]   per-cone: chi != 0 implies Z*(V,g) carries a nonzero mu; and for
         sign-coherent g the converse.

and, separately, Theorem A (+-S_n) by set partitions for n <= 8, with Z*(g)
computed by linear algebra (not by the tight-pair description).

Run:  python3 audit2_vanishing_criterion.py [--quick]
"""
import itertools
import sys
from fractions import Fraction as Fr

# ---------------------------------------------------------------- linear algebra


def rref(rows):
    """Row-reduce a list of rows (Fractions). Returns (reduced rows, pivots)."""
    M = [list(map(Fr, r)) for r in rows]
    if not M:
        return [], []
    ncol = len(M[0])
    piv = []
    r = 0
    for c in range(ncol):
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


def rank(rows):
    return len(rref(rows)[1]) if rows else 0


def nullspace(rows, n):
    """Basis (list of vectors of length n) of {x : r.x = 0 for r in rows}."""
    if not rows:
        return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    R, piv = rref(rows)
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for i, p in enumerate(piv):
            v[p] = -R[i][f]
        basis.append(v)
    return basis


def matmul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(len(B)))
                       for j in range(len(B[0]))) for i in range(len(A)))


def det(M):
    M = [list(map(Fr, r)) for r in M]
    n = len(M)
    d = Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for i in range(c + 1, n):
            f = M[i][c] / M[c][c]
            M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return d


def inverse(M):
    n = len(M)
    aug = [list(M[i]) + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
    R, piv = rref(aug)
    assert piv[:n] == list(range(n))
    return tuple(tuple(R[i][n:]) for i in range(n))


def ident(n):
    return tuple(tuple(Fr(int(i == j)) for j in range(n)) for i in range(n))


def sgn(x):
    return (x > 0) - (x < 0)


def normalize(v):
    """Scale a nonzero row so that its first nonzero entry is +1."""
    v = [Fr(x) for x in v]
    f = next(x for x in v if x != 0)
    return tuple(x / f for x in v)


# ---------------------------------------------------------------- posets


def mobius_from_bottom(elems, leq, bottom):
    """mu(bottom, x) for all x in a finite poset with the given bottom."""
    order = sorted(elems, key=lambda x: sum(1 for y in elems if leq(y, x)))
    mu = {}
    for x in order:
        if x == bottom:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if y != x and leq(y, x))
    return mu


# ---------------------------------------------------------------- arrangements


class Arrangement:
    """A central essential arrangement in Q^d given by hyperplane normals.

    Flats are represented by frozensets of hyperplane indices (the hyperplanes
    containing the flat). Faces are sign vectors (covectors)."""

    def __init__(self, d, normals, name=""):
        self.name = name
        self.d = d
        seen = []
        for v in normals:
            nv = normalize(v)
            if nv not in seen:
                seen.append(nv)
        self.normals = seen
        self.n = len(seen)
        assert rank(self.normals) == d, "arrangement not essential"
        self._flats()
        self._covectors()

    def closure(self, S):
        S = list(S)
        r = rank([self.normals[e] for e in S]) if S else 0
        return frozenset(e for e in range(self.n)
                         if rank([self.normals[f] for f in S + [e]]) == r)

    def _flats(self):
        top = frozenset()
        self.flat_dim = {top: self.d}
        frontier = [top]
        while frontier:
            new = []
            for F in frontier:
                for e in range(self.n):
                    if e in F:
                        continue
                    G = self.closure(F | {e})
                    if G not in self.flat_dim:
                        self.flat_dim[G] = self.d - rank([self.normals[f] for f in G])
                        new.append(G)
            frontier = new
        self.flats = list(self.flat_dim)
        self.bottom = frozenset(range(self.n))
        assert self.flat_dim[self.bottom] == 0

    def basis(self, F):
        """Basis of the subspace with hyperplane set F."""
        return nullspace([self.normals[e] for e in F], self.d)

    def signvec(self, x):
        return tuple(sgn(sum(a * b for a, b in zip(al, x))) for al in self.normals)

    def _covectors(self):
        coc = set()
        for F, dim in self.flat_dim.items():
            if dim == 1:
                v = self.basis(F)[0]
                s = self.signvec(v)
                coc.add(s)
                coc.add(tuple(-x for x in s))
        cov = {tuple([0] * self.n)} | coc
        frontier = list(coc)
        while frontier:
            new = []
            for x in frontier:
                for c in coc:
                    y = tuple(a if a != 0 else b for a, b in zip(x, c))
                    if y not in cov:
                        cov.add(y)
                        new.append(y)
            frontier = new
        self.covectors = list(cov)
        self.chambers = sorted(c for c in cov if 0 not in c)
        self.chamber_index = {c: i for i, c in enumerate(self.chambers)}
        self.halfspace = []
        for e in range(self.n):
            pos = sum(1 << i for i, c in enumerate(self.chambers) if c[e] > 0)
            neg = sum(1 << i for i, c in enumerate(self.chambers) if c[e] < 0)
            self.halfspace.append((pos, neg))
        self.all_chambers = (1 << len(self.chambers)) - 1

    def zero_set(self, F):
        return frozenset(e for e, s in enumerate(F) if s == 0)

    def leq(self, X, Y):
        """Subspace inclusion X subset Y."""
        return X >= Y

    # -- top-cones, represented by chamber bitmasks
    def top_cones(self):
        seen = {self.all_chambers}
        frontier = [self.all_chambers]
        while frontier:
            new = []
            for m in frontier:
                for pos, neg in self.halfspace:
                    for h in (pos, neg):
                        k = m & h
                        if k and k not in seen:
                            seen.add(k)
                            new.append(k)
            frontier = new
        return sorted(seen)

    def cone_constraints(self, mask):
        """S_max(V) with signs, as a dict e -> sign."""
        chs = [c for i, c in enumerate(self.chambers) if mask >> i & 1]
        S = {}
        for e in range(self.n):
            s = {c[e] for c in chs}
            if len(s) == 1:
                S[e] = s.pop()
        return S

    def mask_of_constraints(self, S):
        m = self.all_chambers
        for e, s in S.items():
            m &= self.halfspace[e][0 if s > 0 else 1]
        return m

    def lin(self, S):
        return self.closure(S.keys()) if S else frozenset()

    def Lambda(self, S):
        """Support lattice of the cone {s_e alpha_e >= 0, e in S}: spans of faces in it."""
        return {self.zero_set(F) for F in self.covectors
                if all(F[e] in (0, s) for e, s in S.items())}


def m_of_cone(arr, S):
    """m(V) = (-1)^d mu_{Lambda(V)}(0, R^d)."""
    Lam = arr.Lambda(S)
    mu = mobius_from_bottom(list(Lam), arr.leq, arr.bottom)
    return (-1) ** arr.d * mu[frozenset()]


# ---------------------------------------------------------------- symmetries


class Sym:
    """A rational linear map g (acting on column vectors) preserving arr."""

    def __init__(self, arr, M):
        self.arr = arr
        self.M = tuple(tuple(Fr(x) for x in r) for r in M)
        Minv = inverse(self.M)
        self.det = det(self.M)
        perm, sig = [None] * arr.n, [None] * arr.n
        for e, al in enumerate(arr.normals):
            # alpha_e(g^{-1} y) = c * alpha_{pi(e)}(y)
            row = [sum(al[k] * Minv[k][j] for k in range(arr.d)) for j in range(arr.d)]
            nr = normalize(row)
            f = arr.normals.index(nr)  # raises if g does not preserve A
            c = next(x for x in row if x != 0)
            perm[e], sig[e] = f, sgn(c)
        self.perm, self.sig = perm, sig
        # chamber permutation
        self.cperm = []
        for C in arr.chambers:
            self.cperm.append(arr.chamber_index[self.act(C)])
        d = arr.d
        self.fix = nullspace([[self.M[i][j] - int(i == j) for j in range(d)]
                              for i in range(d)], d)

    def act(self, F):
        out = [0] * self.arr.n
        for e, s in enumerate(F):
            out[self.perm[e]] = self.sig[e] * s
        return tuple(out)

    def act_mask(self, m):
        out = 0
        i = 0
        while m:
            if m & 1:
                out |= 1 << self.cperm[i]
            m >>= 1
            i += 1
        return out

    def stable_flat(self, X):
        return frozenset(self.perm[e] for e in X) == X


def close_group(arr, gens, limit=5000):
    d = arr.d
    I = ident(d)
    elems = {I}
    frontier = [I]
    gens = [tuple(tuple(Fr(x) for x in r) for r in g) for g in gens]
    while frontier:
        new = []
        for a in frontier:
            for g in gens:
                b = matmul(a, g)
                if b not in elems:
                    elems.add(b)
                    new.append(b)
                    assert len(elems) <= limit
        frontier = new
    return [Sym(arr, M) for M in sorted(elems)]


def conj_classes(group, subset=None):
    """Conjugacy classes of the subgroup `subset` (list of Syms) of itself."""
    H = subset if subset is not None else group
    key = {g.M: g for g in H}
    invs = {g.M: inverse(g.M) for g in H}
    left = set(key)
    classes = []
    while left:
        a = min(left)
        cl = {matmul(matmul(h.M, a), invs[h.M]) for h in H}
        classes.append([key[x] for x in sorted(cl)])
        left -= cl
    return classes


# ---------------------------------------------------------------- the formulas


def chi_def(arr, S, g):
    """(-1)^d det(g) mu(Lambda(V)^g)."""
    Lam = [X for X in arr.Lambda(S) if g.stable_flat(X)]
    mu = mobius_from_bottom(Lam, arr.leq, arr.bottom)
    val = (-1) ** arr.d * g.det * mu[frozenset()]
    assert val.denominator == 1
    return int(val)


MX_STATS = dict(nonpointed=0, max=0, max_nonpointed=0)


class GData:
    """Everything about g that does not depend on the cone."""

    def __init__(self, arr, g):
        self.arr, self.g = arr, g
        U = g.fix
        self.U = U
        k = len(U)
        self.stable = [X for X in arr.flats if g.stable_flat(X)]
        self.mu0 = mobius_from_bottom(self.stable, arr.leq, arr.bottom)
        self.Zstar = []
        for X in self.stable:
            BX = arr.basis(X)
            dX = len(BX)
            cap = dX + k - (rank(BX + U) if BX + U else 0)
            if cap != 0:
                continue
            span = BX + U
            if any(all(sum(a * b for a, b in zip(arr.normals[e], v)) == 0 for v in span)
                   for e in range(arr.n)):
                continue
            self.Zstar.append(X)

    def m_X(self, X, S):
        """Bottom multiplicity of |V| cap U in the arrangement {H cap U : H > X}."""
        arr, U = self.arr, self.U
        k = len(U)
        if k == 0:
            return 1
        forms, idx = [], {}
        for e in sorted(X):
            row = [sum(arr.normals[e][i] * U[j][i] for i in range(arr.d)) for j in range(k)]
            assert any(x != 0 for x in row)
            nr = normalize(row)
            if nr not in forms:
                forms.append(nr)
            idx[e] = (forms.index(nr), sgn(next(x for x in row if x != 0)))
        sub = Arrangement(k, forms)
        T = {}
        for e, s in S.items():
            assert e in X
            f, c = idx[e]
            t = s * c
            assert T.get(f, t) == t, "inconsistent restricted constraints"
            T[f] = t
        assert sub.mask_of_constraints(T) != 0
        m = m_of_cone(sub, T)
        Tmax = sub.cone_constraints(sub.mask_of_constraints(T))
        if sub.lin(Tmax) != sub.bottom:
            MX_STATS['nonpointed'] += 1
            MX_STATS['max_nonpointed'] = max(MX_STATS['max_nonpointed'], m)
        MX_STATS['max'] = max(MX_STATS['max'], m)
        return m

    def Z_terms(self, S):
        L = self.arr.lin(S)
        return [(X, self.mu0[X], self.m_X(X, S)) for X in self.Zstar if self.arr.leq(X, L)]


def restriction(arr, X):
    """A^X = {H cap X : H not > X} as an arrangement in coordinates of X."""
    B = arr.basis(X)
    k = len(B)
    forms = []
    for e in range(arr.n):
        if e in X:
            continue
        forms.append([sum(arr.normals[e][i] * B[j][i] for i in range(arr.d)) for j in range(k)])
    return B, Arrangement(k, forms)


def restricted_map(B, g):
    """Matrix of g|_X in the basis B of a g-stable subspace X."""
    k = len(B)
    cols = []
    for v in B:
        gv = [sum(g.M[i][j] * v[j] for j in range(len(v))) for i in range(len(v))]
        # solve sum c_j B_j = gv
        aug = [[B[j][i] for j in range(k)] + [gv[i]] for i in range(len(v))]
        R, piv = rref(aug)
        assert piv == list(range(k))
        cols.append([R[j][k] for j in range(k)])
    return tuple(tuple(cols[j][i] for j in range(k)) for i in range(k))


# ---------------------------------------------------------------- the audit of one arrangement


def audit_arrangement(arr, group, W=None, out=print, check_mu_chi=True, check_S3=True):
    """Run [Z], [m>=1], [mu=chi], [S], [lune], [S3], [PC] on (arr, group).

    W: subgroup used for orbit representatives of cones (default: group)."""
    W = W or group
    stats = dict(pairs=0, nonzero=0, Z_ok=0, cancel=0, corV=0, noZmu=0,
                 classes=0, S_ok=0, lune=0, mu_chi=0, invol=0, m_terms=0, coherent_pc=0,
                 reflections=[], crapo=[])
    cones = arr.top_cones()
    # W-orbit representatives
    rep = []
    seen = set()
    for m in cones:
        if m in seen:
            continue
        orb = {w.act_mask(m) for w in W}
        seen |= orb
        rep.append(m)
    out(f"  {arr.name}: d={arr.d}, |A|={arr.n}, flats={len(arr.flats)}, "
        f"faces={len(arr.covectors)}, chambers={len(arr.chambers)}, "
        f"top-cones={len(cones)}, orbits={len(rep)}, |G|={len(group)}, |W|={len(W)}")
    gcache = {}

    def gd(g):
        if g.M not in gcache:
            gcache[g.M] = GData(arr, g)
        return gcache[g.M]

    # pairs (V orbit rep, class rep of Stab_G(V))
    for m in rep:
        S = arr.cone_constraints(m)
        stab = [g for g in group if g.act_mask(m) == m]
        for cl in conj_classes(group, stab):
            g = cl[0]
            G = gd(g)
            chi = chi_def(arr, S, g)
            terms = G.Z_terms(S)
            z = sum(mu * mm for _, mu, mm in terms)
            stats['pairs'] += 1
            assert all(mm >= 1 for _, _, mm in terms), "m_X < 1"
            stats['m_terms'] += len(terms)
            if chi != z:
                raise AssertionError(f"Formula Z fails on {arr.name}: chi={chi}, Z={z}, terms={terms}")
            stats['Z_ok'] += 1
            if chi != 0:
                stats['nonzero'] += 1
                assert any(mu != 0 for _, mu, _ in terms)  # PC(a)
            else:
                L = arr.lin(S)
                Ubasis = g.fix
                corV = any(all(sum(a * b for a, b in zip(arr.normals[e], v)) == 0
                               for v in arr.basis(L) + Ubasis) for e in range(arr.n))
                if corV:
                    stats['corV'] += 1
                    assert not terms
                elif any(mu != 0 for _, mu, _ in terms):
                    stats['cancel'] += 1
                else:
                    stats['noZmu'] += 1
            nz = {sgn(G.mu0[X]) for X in G.Zstar if G.mu0[X] != 0}
            if len(nz) <= 1:
                stats['coherent_pc'] += 1
                assert (chi != 0) == any(mu != 0 for _, mu, _ in terms), "PC(b) fails"

    # per class of G: Theorem S, top-lunes, mu = chi^full, involutions
    vanishing = []
    for cl in conj_classes(group):
        g = cl[0]
        G = gd(g)
        stats['classes'] += 1
        some = False
        for m in cones:
            if g.act_mask(m) != m:
                continue
            if chi_def(arr, arr.cone_constraints(m), g) != 0:
                some = True
                break
        crit = any(G.mu0[X] != 0 for X in G.Zstar)
        if some != crit:
            raise AssertionError(f"Theorem S fails on {arr.name} at {g.M}")
        stats['S_ok'] += 1
        if not crit:
            vanishing.append(g)
        # minimal X with mu != 0, every g-fixed chamber of A_X
        good = [X for X in G.Zstar if G.mu0[X] != 0]
        minimal = [X for X in good if not any(Y != X and arr.leq(Y, X) for Y in good)]
        for X in minimal:
            Ks = set()
            for C in arr.chambers:
                r = tuple(C[e] if e in X else 0 for e in range(arr.n))
                if g.act(r) == r:
                    Ks.add(r)
            assert Ks, "no g-fixed chamber of A_X"
            for r in Ks:
                S = {e: r[e] for e in X}
                mask = arr.mask_of_constraints(S)
                assert g.act_mask(mask) == mask
                Smax = arr.cone_constraints(mask)
                assert arr.lin(Smax) == X, "lin of top-lune is not X"
                assert chi_def(arr, Smax, g) == G.mu0[X], "top-lune chi != mu(0,X)"
                stats['lune'] += 1
        if check_mu_chi:
            for X in G.Zstar:
                if X == arr.bottom:
                    assert G.mu0[X] == 1
                    continue
                B, sub = restriction(arr, X)
                h = Sym(sub, restricted_map(B, g))
                assert not h.fix
                full = chi_def(sub, {}, h)
                assert full == G.mu0[X], "mu(0,X) != chi^full_{A^X}(g|X)"
                stats['mu_chi'] += 1
        if check_S3 and matmul(g.M, g.M) == ident(arr.d) and g.M != ident(arr.d):
            stats['invol'] += 1
            d = arr.d
            E = nullspace([[g.M[i][j] + int(i == j) for j in range(d)] for i in range(d)], d)
            s3 = False
            for X in arr.flats:
                BX = arr.basis(X)
                if BX and rank(BX + E) != len(E):
                    continue  # X not inside E
                span = BX + g.fix
                if not any(all(sum(a * b for a, b in zip(arr.normals[e], v)) == 0 for v in span)
                           for e in range(arr.n)):
                    s3 = True
            assert s3 == crit, "S3 criterion fails"
            # every X in Z*(g) of an involution has mu != 0 (Rota)
            assert all(G.mu0[X] != 0 for X in G.Zstar)
            if len(g.fix) == d - 1:
                mirror_in_A = any(all(sum(a * b for a, b in zip(arr.normals[e], v)) == 0
                                      for v in g.fix) for e in range(arr.n))
                line_is_flat = any(len(arr.basis(X)) == 1 and rank(arr.basis(X) + E) == 1
                                   for X in arr.flats)
                coherent = len({sgn(G.mu0[X]) for X in G.Zstar if G.mu0[X] != 0}) <= 1
                stats['reflections'].append((mirror_in_A, line_is_flat, crit, coherent))
                if mirror_in_A:
                    assert crit == line_is_flat, "S3 reflection clause fails"
                    assert coherent, "PC(c) reflection clause fails"
        # Crapo: an uncomplemented element of [0,X] in L(A)^g forces mu(0,X) = 0;
        # the CONJECTURED converse is recorded, not asserted
        for X in G.Zstar:
            I = [Y for Y in G.stable if arr.leq(Y, X)]
            unc = False
            for Y in I:
                if Y in (arr.bottom, X):
                    continue
                if not any(arr.closure(Y | Z) == arr.bottom and (Y & Z) == X for Z in I):
                    unc = True
                    break
            if unc:
                assert G.mu0[X] == 0, "Crapo fails?"
            stats['crapo'].append((G.mu0[X] == 0, unc))
    out("    pairs={pairs} (Z holds on all; chi!=0: {nonzero}; zero by Cor.V: {corV}; "
        "zero, no nonzero mu: {noZmu}; zero by cancellation: {cancel}); "
        "sign-coherent pairs with PC(b) checked: {coherent_pc}; m_X terms: {m_terms}".format(**stats))
    out("    classes={classes}: Theorem S holds on all; top-lunes checked: {lune}; "
        "mu=chi^full checked: {mu_chi}; involution classes (S3): {invol}; "
        "vanishing on every cone: {nv}".format(nv=len(vanishing), **stats))
    refl = stats['reflections']
    out("    reflection classes: {} with mirror in A (S3 clause and PC(c) hold), {} with mirror "
        "not in A: (line flat, nonzero on some cone, sign-coherent) = {}".format(
            sum(1 for r in refl if r[0]), sum(1 for r in refl if not r[0]),
            [r[1:] for r in refl if not r[0]]))
    cr = stats['crapo']
    out("    Crapo on Z*(g) (summed over classes): X tested {}, mu = 0: {}, uncomplemented: {}, "
        "mu = 0 but all complemented (converse fails): {}".format(
            len(cr), sum(1 for z, u in cr if z), sum(1 for z, u in cr if u),
            sum(1 for z, u in cr if z and not u)))
    stats['vanishing'] = vanishing
    return stats


# ---------------------------------------------------------------- arrangements used


def signed_perms(n):
    out = []
    for p in itertools.permutations(range(n)):
        for s in itertools.product((1, -1), repeat=n):
            out.append(tuple(tuple(s[i] if p[i] == j else 0 for j in range(n)) for i in range(n)))
    return out


def typeB(n):
    N = []
    for i in range(n):
        N.append([int(k == i) for k in range(n)])
    for i, j in itertools.combinations(range(n), 2):
        for s in (1, -1):
            N.append([1 if k == i else (s if k == j else 0) for k in range(n)])
    arr = Arrangement(n, N, f"B{n}")
    G = close_group(arr, signed_perms(n))
    return arr, G, None


def typeA(n):
    """Braid arrangement of A_{n-1} in R^n_0, basis f_i = e_i - e_n (i < n).
    Returns arr, G = +-S_n, W = S_n."""
    d = n - 1

    def coords(i):  # e_i - e_n -> f-coords ; e_n -> 0
        return [int(k == i) for k in range(d)] if i < d else [0] * d

    # x = sum c_k f_k : x_i = c_i (i<d), x_n = -sum c
    def form(i, j):
        def x(i):
            return [int(k == i) for k in range(d)] if i < d else [-1] * d
        return [a - b for a, b in zip(x(i), x(j))]
    N = [form(i, j) for i, j in itertools.combinations(range(n), 2)]
    arr = Arrangement(d, N, f"A{n-1}")

    def mat(w, eps):
        cols = []
        for i in range(d):
            ci = coords(w[i])
            cn = coords(w[n - 1])
            cols.append([eps * (a - b) for a, b in zip(ci, cn)])
        return tuple(tuple(cols[j][i] for j in range(d)) for i in range(d))
    gens_W = [mat(p, 1) for p in itertools.permutations(range(n))]
    W = close_group(arr, gens_W)
    G = close_group(arr, gens_W + [mat(tuple(range(n)), -1)])
    return arr, G, W


def b3_minus_one():
    """B3 without the plane z = 0 (8 planes): x=0, y=0, x=+-y, x=+-z, y=+-z.
    Symmetries: signed permutations of (x,y) times z -> +-z (order 16).
    The reflection in z = 0 is a symmetry whose mirror is NOT in A."""
    N = [[1, 0, 0], [0, 1, 0], [1, 1, 0], [1, -1, 0],
         [1, 0, 1], [1, 0, -1], [0, 1, 1], [0, 1, -1]]
    arr = Arrangement(3, N, "B3-minus-{z=0} (8 planes)")
    gens = [((0, 1, 0), (1, 0, 0), (0, 0, 1)), ((-1, 0, 0), (0, 1, 0), (0, 0, 1)),
            ((1, 0, 0), (0, 1, 0), (0, 0, -1))]
    return arr, close_group(arr, gens), None


def hexagon(with_infinity=True):
    """Simplicial rank-3 arrangement from the regular hexagon, in hexagonal-lattice
    coordinates (u, v, z): 6 edge lines, 6 mirrors, and (optionally) z = 0.
    Symmetries D6 x <z -> -z>, rational but NOT orthogonal in these coordinates."""
    N = [[1, 1, -1], [0, 1, -1], [1, 0, 1], [1, 1, 1], [0, 1, 1], [1, 0, -1],
         [0, 1, 0], [1, 0, 0], [1, 1, 0], [1, -1, 0], [2, 1, 0], [1, 2, 0]]
    name = "hexagon 12 lines"
    if with_infinity:
        N.append([0, 0, 1])
        name = "hexagon 13 lines (with z=0)"
    arr = Arrangement(3, N, name)
    rot = ((0, -1, 0), (1, 1, 0), (0, 0, 1))      # (u,v) -> (-v, u+v): rotation by 60 deg
    ref = ((0, 1, 0), (1, 0, 0), (0, 0, 1))       # swap a, b
    zf = ((1, 0, 0), (0, 1, 0), (0, 0, -1))
    return arr, close_group(arr, [rot, ref, zf]), None


def generic(d):
    """d+1 hyperplanes in general position in R^d: normals e_1..e_d, e_1+..+e_d.
    Symmetry group S_{d+1} x {+-1} acting by NON-orthogonal rational maps."""
    N = [[int(i == j) for j in range(d)] for i in range(d)] + [[1] * d]
    arr = Arrangement(d, N, f"generic {d+1} in R^{d}")
    # maps act on points; give them via their action on forms: alpha -> alpha o g^{-1}
    gens = []
    for i in range(d - 1):  # coordinate transpositions
        P = [[int(j == (i + 1 if k == i else i if k == i + 1 else k)) for j in range(d)]
             for k in range(d)]
        gens.append(P)
    # a map swapping the forms e_d and s = e_1+...+e_d up to sign:
    # g^{-T} sends e_d* -> -s*, fixes e_i* (i<d). Compute g from that.
    Fm = [[int(i == j) for j in range(d)] for i in range(d)]
    Fm[d - 1] = [-1] * d   # rows: images of forms e_i*
    # forms transform as alpha -> alpha g^{-1}; row e_i* maps to row Fm[i], i.e. g^{-1} = Fm
    g = inverse(tuple(tuple(Fr(x) for x in r) for r in Fm))
    gens.append(g)
    gens.append(tuple(tuple(-int(i == j) for j in range(d)) for i in range(d)))
    return arr, close_group(arr, gens), None


def deleted_a3():
    """A3 minus one hyperplane (5 planes in R^3, not simplicial), with its
    symmetries inside +-S_4 that preserve the deleted hyperplane."""
    arr4, G4, _ = typeA(4)
    keep = [e for e in range(arr4.n)]
    del keep[0]   # delete x_1 = x_2
    N = [arr4.normals[e] for e in keep]
    arr = Arrangement(3, N, "A3 minus one plane")
    gens = []
    for g in G4:
        try:
            Sym(arr, g.M)
        except ValueError:
            continue
        gens.append(g.M)
    return arr, close_group(arr, gens), None


def is_simplicial(arr):
    for C in arr.chambers:
        facets = 0
        for e in range(arr.n):
            F = tuple(0 if f == e else C[f] for f in range(arr.n))
            if F in set(arr.covectors):
                facets += 1
        if facets != arr.d:
            return False
    return True


# ---------------------------------------------------------------- Theorem A by set partitions


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def canon(p):
    return tuple(sorted(tuple(sorted(b)) for b in p))


def cycle_type(w):
    n = len(w)
    seen, out = set(), []
    for i in range(n):
        if i in seen:
            continue
        j, k = i, 0
        while j not in seen:
            seen.add(j)
            j = w[j]
            k += 1
        out.append(k)
    return tuple(sorted(out, reverse=True))


def perm_of_type(lam):
    w, s = [], 0
    for k in lam:
        w += [s + (i + 1) % k for i in range(k)]
        s += k
    return tuple(w)


def partitions_of_int(n, maxk=None):
    maxk = maxk or n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxk), 0, -1):
        for rest in partitions_of_int(n - k, k):
            yield (k,) + rest


_mu_fixed = {}


def mu_fixed_lattice(b, sigma):
    """mu(0^, 1^) of the lattice of sigma-stable set partitions of [b],
    computed by direct recursion (no Hanlon)."""
    key = (b, cycle_type(sigma))
    if key in _mu_fixed:
        return _mu_fixed[key]
    sigma = perm_of_type(key[1])
    parts = [canon(p) for p in set_partitions(range(b))]
    stable = [p for p in parts if canon([[sigma[i] for i in B] for B in p]) == p]

    def refines(p, q):  # p finer than q
        blk = {}
        for j, B in enumerate(q):
            for i in B:
                blk[i] = j
        return all(len({blk[i] for i in B}) == 1 for B in p)
    stable.sort(key=len, reverse=True)  # finest first
    bot = stable[0]
    assert len(bot) == b
    mu = {}
    for x in stable:
        if x == bot:
            mu[x] = 1
        else:
            mu[x] = -sum(v for y, v in mu.items() if refines(y, x))
    top = stable[-1]
    assert len(top) == 1
    _mu_fixed[key] = mu[top]
    return mu[top]


def mobius_number(n):
    if n == 1:
        return 1
    k, out, m = 2, 1, n
    while k * k <= m:
        if m % k == 0:
            m //= k
            if m % k == 0:
                return 0
            out = -out
        k += 1
    if m > 1:
        out = -out
    return out


def hanlon(b, sigma):
    ct = cycle_type(sigma)
    if len(set(ct)) != 1:
        return 0
    l, r = ct[0], len(ct)
    f = 1
    for i in range(1, r):
        f *= i
    return (-1) ** (r - 1) * mobius_number(l) * l ** (r - 1) * f


def theorem_A_check(n):
    """For every class +-w of S_n: compare (A+)/(A-) with the S-criterion,
    Z*(g) computed by linear algebra in R^n (X_pi cap U, X_pi + U vs H_ij)."""
    parts = [canon(p) for p in set_partitions(range(n))]
    rows = []
    for lam in partitions_of_int(n):
        w = perm_of_type(lam)
        for eps in (1, -1):
            # U = {x in R^n_0 : (gx)_{w(i)} = eps x_i = x_{w(i)}}
            eqs = [[Fr(1)] * n]
            for i in range(n):
                r = [Fr(0)] * n
                r[w[i]] += 1
                r[i] -= eps
                eqs.append(r)
            U = nullspace(eqs, n)
            crit = False
            n_good = 0
            for p in parts:
                if canon([[w[i] for i in B] for B in p]) != p:
                    continue
                # X_pi = sum-zero functions constant on blocks
                X = nullspace([[Fr(1)] * n] + [r for r in ([1 if i == a else -1 if i == b else 0
                                                            for i in range(n)]
                                                           for B in p for a, b in zip(B, B[1:]))],
                              n)
                if X and U and rank(X + U) != len(X) + len(U):
                    continue
                span = X + U
                tight = any(all(v[i] == v[j] for v in span)
                            for i, j in itertools.combinations(range(n), 2))
                if tight:
                    continue
                # mu(0, X_pi) in L(A)^g = mu of wbar-stable partitions of the blocks
                bi = {B: k for k, B in enumerate(p)}
                where = {i: B for B in p for i in B}
                wbar = tuple(bi[where[w[B[0]]]] for B in p)
                mu = mu_fixed_lattice(len(p), wbar)
                assert mu == hanlon(len(p), wbar), "Hanlon formula mismatch"
                if mu != 0:
                    crit = True
                    n_good += 1
            # the stated rules
            if eps == 1:
                rule = len(set(lam)) == 1 and mobius_number(lam[0]) != 0
            else:
                rule = any(m % 2 == 1 and mobius_number(m) != 0 and all(k in (m, 2 * m) for k in lam)
                           for m in range(1, n + 1))
            # the free-action form
            if eps == 1:
                o = 1
                for k in lam:
                    o = o * k // __import__('math').gcd(o, k)
                free = all(k == o for k in lam)
                ordg = o
            else:
                ls = {k if k % 2 == 0 else 2 * k for k in lam}
                free = len(ls) == 1
                ordg = 1
                for k in ls:
                    ordg = ordg * k // __import__('math').gcd(ordg, k)
            free_rule = free and mobius_number(ordg) != 0
            rows.append((eps, lam, crit, rule, free_rule, n_good))
            assert crit == rule == free_rule, f"Theorem A fails at {'+' if eps == 1 else '-'}{lam}"
    return rows


# ---------------------------------------------------------------- main


def main(argv):
    quick = '--quick' in argv
    print("Second audit of notes/vanishing_criterion.md (exact arithmetic)")
    print()
    print("Theorem A by set partitions, Z*(g) by linear algebra, mu by direct recursion:")
    nmax = 6 if quick else 8
    total = 0
    for n in range(3, nmax + 1):
        rows = theorem_A_check(n)
        total += len(rows)
        nz = [('+' if e == 1 else '-') + str(l) for e, l, c, _, _, _ in rows if c]
        print(f"  n={n}: {len(rows)} classes +-w, rule = S-criterion = free-action form on all; "
              f"nonzero on some cone: {len(nz)}")
        if n <= 6:
            print("    nonzero: " + ", ".join(nz))
    print(f"  total classes: {total}")
    print()
    print("Coxeter controls and non-Coxeter probes (Z, S, top-lunes, mu=chi^full, S3, PC):")
    builders = [lambda: typeA(3), lambda: typeA(4), lambda: typeB(2), lambda: typeB(3),
                lambda: generic(3), b3_minus_one, deleted_a3,
                lambda: hexagon(False), lambda: hexagon(True)]
    if not quick:
        builders += [lambda: typeA(5), lambda: generic(4)]
    for b in builders:
        arr, G, W = b()
        print(f"  [{arr.name}] simplicial={is_simplicial(arr)}")
        audit_arrangement(arr, G, W)
    print()
    print("m_X(V) over all terms: all >= 1; max {max}; terms with |V| cap U non-pointed: "
          "{nonpointed} (max m there {max_nonpointed})".format(**MX_STATS))
    print()
    print("ALL CHECKS PASSED")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
