#!/usr/bin/env python3
"""Checks for notes/conjecture_cr_v.md (exact rational arithmetic, no imports from
other compute/ scripts).

For a central essential arrangement A (normals over Q), a finite group G of rational
linear maps preserving A, g in G and a g-stable top-cone V (an intersection of closed
halfspaces of A with nonempty interior), the cone lattice is

  Lambda(V)^g = { span F : F a face of A in |V|, g(span F) = span F },

ordered by inclusion, with the join of flats and the meet computed in the lattice.
chi_V(g) = (-1)^d det(g) mu(Lambda(V)^g). Conjecture CR_V: mu = 0 iff some element
has no complement.

Parts:
  [CTL]  lattice routine controls: the 8-element complemented lattice with mu = 0
         (must report "complemented, mu = 0"), boolean B_3, the pentagon N_5, M_3, a chain.
  [CX]   the counterexample to CR_V of the note (section 0): a 12-hyperplane arrangement in
         R^4, g = diag(-1,-1,1,1), V = {x4 <= x1 + 3 x2 <= -x4}; the 9 flats of Lambda(V)^g,
         mu = 0, every element complemented, and chi = 0 again from Formula Z.
  [REP]  positive control on the arrangements of notes/per_cone_vanishing.md:
         pair counts and zero counts must match its section 4 table.
  [CRV]  new families: fixed G-invariant arrangements built as orbits of seed forms
         (R^3: C_6, D_4, D_6 with z -> -z; R^4: C_5, C_8, C_3 x C_3, C_4, C_12, C_6 x C_4,
         C_6 x C_6 and a swap), A_4 minus one or two hyperplanes, D_4 with W(B_4); every
         class representative g and every g-stable top-cone.
  On every pair: Theorem P (pointed cones: mu = 0 iff Fix g lies in a hyperplane, and then
  cl(Fix g) has no complement), Theorem Q (L + Fix g in a hyperplane: cl(L + Fix g) and
  cl(Fix g) have no complement), Lemma K (the complements of cl(U)), Proposition Ln
  (dim L = 1: chi = c_0 - c_L); CR_V counterexamples are counted and printed, not
  treated as failures; kinds of uncomplemented elements; modularity of complemented
  lattices.

Run:  python3 conjecture_cr_v.py [--quick]
"""
import itertools
import sys
from fractions import Fraction as Fr

# ---------------------------------------------------------------- linear algebra


def rref(rows, ncol):
    M = [list(map(Fr, r)) for r in rows]
    piv, r = [], 0
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
    return M[:r], piv


def rank(rows, n):
    return len(rref(rows, n)[1]) if rows else 0


def nullspace(rows, n):
    if not rows:
        return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    R, piv = rref(rows, n)
    out = []
    for f in (c for c in range(n) if c not in piv):
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for i, p in enumerate(piv):
            v[p] = -R[i][f]
        out.append(v)
    return out


def matmul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0])))
                 for i in range(len(A)))


def det(M):
    M = [list(map(Fr, r)) for r in M]
    n, d = len(M), Fr(1)
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
    R, piv = rref([list(r) + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(M)], 2 * n)
    assert piv[:n] == list(range(n))
    return tuple(tuple(r[n:]) for r in R)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def prim(v):
    """Primitive integer representative of the line through a rational vector, up to sign."""
    from math import gcd
    den = 1
    for x in v:
        den = den * Fr(x).denominator // gcd(den, Fr(x).denominator)
    w = [int(Fr(x) * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    w = [x // g for x in w]
    s = next(x for x in w if x)
    return tuple(w) if s > 0 else tuple(-x for x in w)


# ---------------------------------------------------------------- lattices


def lattice(elems, leq):
    """Finite lattice from a list and an order. Returns dict with mu(0,1), the list of
    uncomplemented elements (indices), the complements of each element, meet, join, and
    whether the lattice is modular."""
    n = len(elems)
    up = [frozenset(j for j in range(n) if leq(elems[i], elems[j])) for i in range(n)]
    down = [frozenset(j for j in range(n) if i in up[j]) for i in range(n)]
    bot = [i for i in range(n) if len(up[i]) == n]
    top = [i for i in range(n) if len(down[i]) == n]
    assert len(bot) == 1 and len(top) == 1, "not bounded"
    bot, top = bot[0], top[0]
    J = [[None] * n for _ in range(n)]
    Mt = [[None] * n for _ in range(n)]
    for a in range(n):
        for b in range(a, n):
            c = up[a] & up[b]
            j = [x for x in c if up[x] >= c]
            c = down[a] & down[b]
            m = [x for x in c if down[x] >= c]
            assert len(j) == 1 and len(m) == 1, "not a lattice"
            J[a][b] = J[b][a] = j[0]
            Mt[a][b] = Mt[b][a] = m[0]
    order = sorted(range(n), key=lambda i: len(down[i]))
    mu = {}
    for i in order:
        mu[i] = 1 if i == bot else -sum(mu[j] for j in down[i] if j != i)
    comps = [[x for x in range(n) if Mt[a][x] == bot and J[a][x] == top] for a in range(n)]
    unc = [a for a in range(n) if not comps[a]]
    # modular: graded by height with h(x)+h(y) = h(x^y)+h(xvy)
    h = {}
    for i in order:
        h[i] = 0 if i == bot else 1 + max(h[j] for j in down[i] if j != i)
    graded = True
    for i in range(n):
        for j in up[i]:
            if j != i and not any(k not in (i, j) and k in up[i] and j in up[k] for k in range(n)):
                if h[j] != h[i] + 1:
                    graded = False
    modular = graded and all(h[a] + h[b] == h[Mt[a][b]] + h[J[a][b]] for a in range(n) for b in range(n))
    return dict(mu=mu[top], unc=unc, comps=comps, bot=bot, top=top, meet=Mt, join=J,
                modular=modular, size=n, mu_all=mu, down=down, up=up)


def poset_from_covers(n, covers):
    rel = {(i, i) for i in range(n)} | set(covers)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(rel):
            for (c, d) in list(rel):
                if b == c and (a, d) not in rel:
                    rel.add((a, d))
                    changed = True
    return list(range(n)), lambda x, y: (x, y) in rel


def part_controls():
    ok = True
    print("[CTL] lattice routine controls")
    # 0, a, b, c, x, y, z, 1  (indices 0..7): the 8-element complemented lattice with mu = 0
    covers = [(0, 1), (0, 2), (0, 3), (1, 5), (1, 6), (2, 4), (2, 5), (3, 4), (4, 7), (5, 7), (6, 7)]
    E, leq = poset_from_covers(8, covers)
    L8 = lattice(E, leq)
    print(f"  8-element lattice: mu = {L8['mu']}, uncomplemented = {L8['unc']}, modular = {L8['modular']}")
    ok &= L8['mu'] == 0 and L8['unc'] == []
    B3 = lattice(list(range(8)), lambda a, b: a & b == a)
    print(f"  boolean B_3: mu = {B3['mu']}, uncomplemented = {B3['unc']}, modular = {B3['modular']}")
    ok &= B3['mu'] == -1 and B3['unc'] == [] and B3['modular']
    E, leq = poset_from_covers(5, [(0, 1), (1, 2), (2, 4), (0, 3), (3, 4)])
    N5 = lattice(E, leq)
    print(f"  pentagon N_5: mu = {N5['mu']}, uncomplemented = {N5['unc']}, modular = {N5['modular']}")
    ok &= N5["mu"] == 1 and N5['unc'] == [] and not N5['modular']
    E, leq = poset_from_covers(5, [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4)])
    M3 = lattice(E, leq)
    print(f"  M_3: mu = {M3['mu']}, uncomplemented = {M3['unc']}, modular = {M3['modular']}")
    ok &= M3['mu'] == 2 and M3['unc'] == [] and M3['modular']
    E, leq = poset_from_covers(4, [(0, 1), (1, 2), (2, 3)])
    C4 = lattice(E, leq)
    print(f"  chain of 4: mu = {C4['mu']}, uncomplemented = {C4['unc']}")
    ok &= C4['mu'] == 0 and C4['unc'] == [1, 2]
    print(f"  {'ok' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------- arrangements


class Arr:
    """Central essential arrangement given by integer normals in Q^d (one per hyperplane).
    Faces are sign vectors (covectors), generated as compositions of cocircuits.
    Flats are bitmasks of the hyperplanes containing them."""

    def __init__(self, d, normals, name):
        self.d, self.name = d, name
        seen, N = set(), []
        for v in normals:
            p = prim(v)
            if any(p) and p not in seen:
                seen.add(p)
                N.append(p)
        self.normals = N
        self.n = len(N)
        assert rank(N, d) == d, "not essential"
        self.full = (1 << self.n) - 1
        self._cl = {}
        # cocircuits
        cocirc = set()
        for S in itertools.combinations(range(self.n), d - 1):
            rows = [N[i] for i in S]
            if rank(rows, d) != d - 1:
                continue
            v = nullspace(rows, d)[0]
            s = tuple((dot(a, v) > 0) - (dot(a, v) < 0) for a in N)
            cocirc.add(s)
            cocirc.add(tuple(-x for x in s))
        cocirc = list(cocirc)
        zero = tuple([0] * self.n)
        cov = {zero} | set(cocirc)
        frontier = set(cocirc)
        while frontier:
            new = set()
            for a in frontier:
                for c in cocirc:
                    b = tuple(x if x else y for x, y in zip(a, c))
                    if b not in cov:
                        new.add(b)
            cov |= new
            frontier = new
        self.covectors = list(cov)
        self.topes = [c for c in self.covectors if 0 not in c]
        self.zmask = {c: sum(1 << i for i, x in enumerate(c) if x == 0) for c in self.covectors}
        self.flats = sorted(set(self.zmask.values()), key=lambda z: -bin(z).count("1"))
        self.dim = {z: d - rank([N[i] for i in range(self.n) if z >> i & 1], d) for z in self.flats}

    def closure_of_vectors(self, vecs):
        """Zero set (bitmask) of the smallest flat containing the given vectors."""
        z = 0
        for i, a in enumerate(self.normals):
            if all(dot(a, v) == 0 for v in vecs):
                z |= 1 << i
        return z

    def basis(self, z):
        return nullspace([self.normals[i] for i in range(self.n) if z >> i & 1], self.d)

    def cones(self):
        """All top-cones, as frozensets of tope indices."""
        T = self.topes
        allc = frozenset(range(len(T)))
        half = []
        for e in range(self.n):
            for s in (1, -1):
                half.append(frozenset(i for i, t in enumerate(T) if t[e] == s))
        seen = {allc}
        frontier = [allc]
        while frontier:
            new = []
            for m in frontier:
                for h in half:
                    k = m & h
                    if k and k not in seen:
                        seen.add(k)
                        new.append(k)
            frontier = new
        return list(seen)

    def faces_of(self, cone):
        """Covectors in the closure of the union of the topes of the cone."""
        T = [self.topes[i] for i in cone]
        # a covector c lies in the closed cone iff c_e in {0, s_e} for every constraint (e, s_e)
        cons = []
        for e in range(self.n):
            s = {t[e] for t in T}
            if len(s) == 1:
                cons.append((e, s.pop()))
        return [c for c in self.covectors if all(c[e] in (0, s) for e, s in cons)], cons


class Sym:
    """A rational linear map preserving the arrangement, with its action on hyperplanes
    (permutation) and on covectors (signed permutation)."""

    def __init__(self, arr, M):
        self.M = M
        self.det = det(M)
        Mi = inverse(M)
        perm, sg = [None] * arr.n, [None] * arr.n
        idx = {p: i for i, p in enumerate(arr.normals)}
        for j, a in enumerate(arr.normals):
            # sign of a_j(g x) = (a_j g) . x ; a_j g = lam a_i
            row = [sum(a[k] * M[k][c] for k in range(arr.d)) for c in range(arr.d)]
            p = prim(row)
            i = idx.get(p)
            if i is None:
                raise ValueError("not a symmetry")
            lam = next(Fr(r) / q for r, q in zip(row, p) if q)
            perm[j], sg[j] = i, (1 if lam > 0 else -1)
        # (g c)_j = sg[j] * c[perm[j]]
        self.cperm, self.csign = perm, sg
        # g maps hyperplane H_i (i = perm[j]) to H_j
        self.hmap = [None] * arr.n
        for j in range(arr.n):
            self.hmap[perm[j]] = j
        self.U = nullspace([[M[i][j] - int(i == j) for j in range(arr.d)] for i in range(arr.d)], arr.d)

    def act_cov(self, c):
        return tuple(self.csign[j] * c[self.cperm[j]] for j in range(len(c)))

    def act_flat(self, z):
        out = 0
        for i in range(len(self.hmap)):
            if z >> i & 1:
                out |= 1 << self.hmap[i]
        return out


def close_group(arr, gens, limit=3000):
    d = arr.d
    I = tuple(tuple(Fr(int(i == j)) for j in range(d)) for i in range(d))
    gens = [tuple(tuple(Fr(x) for x in r) for r in g) for g in gens]
    elems, frontier = {I}, [I]
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
    return [Sym(arr, M) for M in elems]


def class_reps(G):
    key = {g.M: g for g in G}
    inv = {g.M: inverse(g.M) for g in G}
    left, reps = set(key), []
    while left:
        a = min(left)
        cl = {matmul(matmul(h.M, a), inv[h.M]) for h in G}
        reps.append(key[a])
        left -= cl
    return reps


# ---------------------------------------------------------------- one pair (V, g)


def analyse(arr, g, cone):
    faces, cons = arr.faces_of(cone)
    # g-stability of V: g maps the tope set to itself
    tset = {arr.topes[i] for i in cone}
    if {g.act_cov(t) for t in tset} != tset:
        return None
    lam = sorted({arr.zmask[c] for c in faces if g.act_flat(arr.zmask[c]) == arr.zmask[c]})
    leq = lambda x, y: (y & ~x) == 0  # flat x inside flat y iff zero(y) subset zero(x)
    Lt = lattice(lam, leq)
    Lz = 0
    for e, s in cons:
        Lz |= 1 << e
    Lz = arr.closure_of_vectors(arr.basis(Lz))  # lineality space L (a flat)
    U = g.U
    clU = arr.closure_of_vectors(U)
    LU = arr.closure_of_vectors(arr.basis(Lz) + U)
    return dict(lam=lam, L=Lt, Lz=Lz, U=U, clU=clU, LU=LU, cons=cons, faces=faces)


def kinds_of_obstruction(arr, a):
    """Classify the uncomplemented elements: 'clU' if cl(U) is one, 'inL' if some element
    inside L is one, 'other' for the rest."""
    lam, Lt = a['lam'], a['L']
    idx = {z: i for i, z in enumerate(lam)}
    unc = set(Lt['unc'])
    k = set()
    if a['clU'] != 0 and a['clU'] in idx and idx[a['clU']] in unc:
        k.add('clU')
    for i in unc:
        if (lam[i] & a['Lz']) == a['Lz']:  # zero(L) subset zero(X): X inside L
            k.add('inL')
        else:
            k.add('out')
    return k


def part_counterexample():
    """The counterexample of notes/conjecture_cr_v.md section 0, checked on its own."""
    ok = True
    print("[CX] counterexample: A = 12 hyperplanes u.(x1,x2) + w.(x3,x4) = 0, u in {(1,3),(2,-1),(3,2)}, "
          "w in {(+-1,0),(0,+-1)}; g = diag(-1,-1,1,1); V = {x4 <= x1 + 3 x2 <= -x4}")
    N = [list(u) + list(w) for u in ((1, 3), (2, -1), (3, 2)) for w in ((1, 0), (0, 1), (-1, 0), (0, -1))]
    arr = Arr(4, N, "C6 x C4 orbit arrangement")
    g = Sym(arr, [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    # V by its two facets: (1,3,0,-1).x >= 0 and (1,3,0,1).x <= 0
    i1, i2 = arr.normals.index((1, 3, 0, -1)), arr.normals.index((1, 3, 0, 1))
    cone = frozenset(i for i, t in enumerate(arr.topes) if t[i1] == 1 and t[i2] == -1)
    a = analyse(arr, g, cone)
    ok &= arr.n == 12 and a is not None
    lam, Lt = a['lam'], a['L']
    canon = lambda B: tuple(tuple(Fr(x) for x in v) for v in rref(B, 4)[0]) if B else ()
    got = sorted(canon(arr.basis(z)) for z in lam)
    expect = sorted(canon(B) for B in [
        [], [[-3, 1, 0, 0]], [[0, 0, 1, 0]], [[0, 0, 0, 1]], [[-3, 1, 0, 0], [0, 0, 1, 0]],
        [[-3, 1, 0, 0], [0, 0, 0, 1]], [[1, 2, 0, 0], [0, 0, 0, 1]], [[-2, 3, 0, 0], [0, 0, 0, 1]],
        [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]])
    chi = (-1) ** 4 * g.det * Lt['mu']
    print(f"  |Lambda(V)^g| = {len(lam)} (the 9 flats of the note: {got == expect}), mu = {Lt['mu']}, "
          f"uncomplemented elements: {len(Lt['unc'])}, chi = {chi}")
    ok &= got == expect and Lt['mu'] == 0 and not Lt['unc']
    # Formula Z, independently of the lattice: chi = sum over X in Z* of mu(0,X) m_X(V), where
    # Z* = g-stable flats X inside L with X cap U = 0 (here U lies in no hyperplane), and
    # m_X = (-1)^{dim U} mu of the cone |V| cap U for the traces on U of the hyperplanes through X.
    U = a['U']
    Zs = [X for X in arr.flats if g.act_flat(X) == X and (X & a['Lz']) == a['Lz']
          and rank(arr.basis(X) + U, 4) == len(arr.basis(X)) + len(U)]
    total = 0
    for X in Zs:
        below = [Y for Y in arr.flats if g.act_flat(Y) == Y and (X & ~Y) == 0]  # g-stable flats inside X
        mu0X = lattice(below, lambda p, q: (q & ~p) == 0)['mu']
        rows = {e: [dot(arr.normals[e], u) for u in U] for e in range(arr.n) if X >> e & 1}
        sub = Arr(len(U), list(rows.values()), "traces on U")
        sc = []
        for e, sg in a['cons']:   # facet hyperplanes of V contain L, hence X
            p = prim(rows[e])
            lamb = next(Fr(r) / q for r, q in zip(rows[e], p) if q)
            sc.append((sub.normals.index(p), sg * (1 if lamb > 0 else -1)))
        cU = frozenset(i for i, t in enumerate(sub.topes) if all(t[j] == v for j, v in sc))
        faces, _ = sub.faces_of(cU)
        m = (-1) ** len(U) * lattice(sorted({sub.zmask[c] for c in faces}), lambda p, q: (q & ~p) == 0)['mu']
        print(f"  Formula Z term: dim X = {len(arr.basis(X))}, mu(0,X) = {mu0X}, m_X = {m}")
        total += mu0X * m
        ok &= m >= 1
    print(f"  Formula Z: chi = {total}")
    ok &= total == 0 == chi
    print(f"  {'ok' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------- arrangement families


def rot_hex():   # rotation by 60 degrees in hexagonal-lattice coordinates (u, v)
    return [[0, -1], [1, 1]]


def block(*Ms):
    n = sum(len(M) for M in Ms)
    out = [[0] * n for _ in range(n)]
    o = 0
    for M in Ms:
        for i, r in enumerate(M):
            for j, x in enumerate(r):
                out[o + i][o + j] = x
        o += len(M)
    return out


def companion(coeffs):
    """Companion matrix of x^k + c_{k-1} x^{k-1} + ... + c_0 (coeffs = [c_0, ..., c_{k-1}])."""
    k = len(coeffs)
    M = [[0] * k for _ in range(k)]
    for i in range(1, k):
        M[i][i - 1] = 1
    for i in range(k):
        M[i][k - 1] = -coeffs[i]
    return M


def orbit_arrangement(d, gens, seeds, name, extra=()):
    """Union of the G-orbits of the seed normals (forms transform by a -> a g^{-1})."""
    d_ = d
    I = tuple(tuple(Fr(int(i == j)) for j in range(d_)) for i in range(d_))
    G = {I}
    fr = [I]
    gg = [tuple(tuple(Fr(x) for x in r) for r in g) for g in gens]
    while fr:
        new = []
        for a in fr:
            for g in gg:
                b = matmul(a, g)
                if b not in G:
                    G.add(b)
                    new.append(b)
        fr = new
    N = set()
    for s in list(seeds) + list(extra):
        for M in G:
            Mi = inverse(M)
            N.add(prim([sum(Fr(s[k]) * Mi[k][j] for k in range(d_)) for j in range(d_)]))
    arr = Arr(d_, sorted(N), name)
    return arr, close_group(arr, gens)


def typeA(n):
    d = n - 1

    def x(i):
        return [int(k == i) for k in range(d)] if i < d else [-1] * d
    N = [[a - b for a, b in zip(x(i), x(j))] for i, j in itertools.combinations(range(n), 2)]
    arr = Arr(d, N, f"A{n-1}")

    def mat(w, eps):
        def coords(i):
            return [int(k == i) for k in range(d)] if i < d else [0] * d
        cols = [[eps * (a - b) for a, b in zip(coords(w[i]), coords(w[n - 1]))] for i in range(d)]
        return [[cols[j][i] for j in range(d)] for i in range(d)]
    gens = [mat(p, 1) for p in itertools.permutations(range(n))] + [mat(tuple(range(n)), -1)]
    return arr, close_group(arr, gens)


def typeB(n):
    N = [[int(k == i) for k in range(n)] for i in range(n)]
    for i, j in itertools.combinations(range(n), 2):
        for s in (1, -1):
            N.append([1 if k == i else (s if k == j else 0) for k in range(n)])
    arr = Arr(n, N, f"B{n}")
    gens = []
    for p in itertools.permutations(range(n)):
        gens.append([[int(p[j] == i) for j in range(n)] for i in range(n)])
    gens.append([[(-1 if i == j == 0 else int(i == j)) for j in range(n)] for i in range(n)])
    return arr, close_group(arr, gens)


def hexagon(with_inf, extra_seeds=()):
    N = [[1, 1, -1], [0, 1, -1], [1, 0, 1], [1, 1, 1], [0, 1, 1], [1, 0, -1],
         [0, 1, 0], [1, 0, 0], [1, 1, 0], [1, -1, 0], [2, 1, 0], [1, 2, 0]]
    if with_inf:
        N.append([0, 0, 1])
    rot = [[0, -1, 0], [1, 1, 0], [0, 0, 1]]
    ref = [[0, 1, 0], [1, 0, 0], [0, 0, 1]]
    zf = [[1, 0, 0], [0, 1, 0], [0, 0, -1]]
    if extra_seeds:
        return orbit_arrangement(3, [rot, ref, zf], N, f"hexagon {len(N)} + orbits of {list(extra_seeds)}",
                                 extra=extra_seeds)
    arr = Arr(3, N, f"hexagon {len(N)}")
    return arr, close_group(arr, [rot, ref, zf])


def generic(d):
    N = [[int(i == j) for j in range(d)] for i in range(d)] + [[1] * d]
    arr = Arr(d, N, f"generic {d+1} in R^{d}")
    gens = []
    for i in range(d - 1):
        gens.append([[int(j == (i + 1 if k == i else i if k == i + 1 else k)) for j in range(d)]
                     for k in range(d)])
    Fm = [[int(i == j) for j in range(d)] for i in range(d)]
    Fm[d - 1] = [-1] * d
    gens.append(inverse(tuple(tuple(Fr(x) for x in r) for r in Fm)))
    gens.append([[-int(i == j) for j in range(d)] for i in range(d)])
    return arr, close_group(arr, gens)


def b3_minus_one():
    N = [[1, 0, 0], [0, 1, 0], [1, 1, 0], [1, -1, 0], [1, 0, 1], [1, 0, -1], [0, 1, 1], [0, 1, -1]]
    arr = Arr(3, N, "B3 minus {z=0}")
    gens = [[[0, 1, 0], [1, 0, 0], [0, 0, 1]], [[-1, 0, 0], [0, 1, 0], [0, 0, 1]],
            [[1, 0, 0], [0, 1, 0], [0, 0, -1]]]
    return arr, close_group(arr, gens)


def deleted_a3():
    arr4, G4 = typeA(4)
    N = arr4.normals[1:]
    # arr4.normals were deduplicated/reordered by prim; delete the first one
    arr = Arr(3, N, "A3 minus a plane")
    gens = []
    for g in G4:
        try:
            Sym(arr, g.M)
            gens.append(g.M)
        except ValueError:
            pass
    return arr, close_group(arr, gens)


def new_families(quick):
    """Fixed G-invariant arrangements (seeds drawn once from random.Random(1) and then frozen)."""
    R, I2, Q, S = rot_hex(), [[1, 0], [0, 1]], [[0, -1], [1, 0]], [[0, 1], [1, 0]]
    R2 = matmul_l(R, R)
    neg4 = [[-int(i == j) for j in range(4)] for i in range(4)]
    z = [[1, 0, 0], [0, 1, 0], [0, 0, -1]]
    cyc4 = [[0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
    swap = [[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]
    fams = [
        ("R^3 C6 x <z->-z>", 3, [block(R, [[1]]), z], [[-1, -2, 3]]),
        ("R^3 D4 x <z->-z>", 3, [block(Q, [[1]]), block(S, [[1]]), z], [[-2, 0, -2], [1, 2, 3]]),
        ("R^3 D6", 3, [block(R, [[1]]), block(S, [[1]])], [[2, -2, -3]]),
        ("R^4 C5 (companion of Phi_5) x -1", 4, [companion([1, 1, 1, 1]), neg4], [[-1, 2, -2, 0]]),
        ("R^4 C8 (companion of Phi_8)", 4, [companion([1, 0, 0, 0])], [[1, -1, 1, -2], [2, -1, 1, 1]]),
        ("R^4 C3 x C3 x -1", 4, [block(R2, I2), block(I2, R2), neg4], [[0, -2, 0, 2]]),
        ("R^4 C4 (cyclic coordinates) x -1", 4, [cyc4, neg4], [[-1, -1, 2, -1], [-2, -1, 2, 2]]),
    ]
    if not quick:
        fams += [
            ("R^4 C12 (companion of Phi_12)", 4, [companion([1, 0, -1, 0])], [[-2, 1, 0, -1], [2, -2, 0, -2]]),
            ("R^4 C6 x C4", 4, [block(R, I2), block(I2, Q)], [[2, -1, 0, -1]]),
            ("R^4 (C6 x C6) and the swap", 4, [block(R, R), swap], [[2, 1, 0, 1], [-2, 1, -2, 0]]),
        ]
    return fams


def deleted(builder, drop, name):
    """The arrangement of builder() without the hyperplanes whose normals are listed in drop
    (or without the first `drop` normals if drop is an int), with the symmetries that preserve it."""
    arr0, G0 = builder()
    N = arr0.normals[drop:] if isinstance(drop, int) else [p for p in arr0.normals if p not in drop]
    arr = Arr(arr0.d, N, name)
    gens = []
    for g in G0:
        try:
            Sym(arr, g.M)
            gens.append(g.M)
        except ValueError:
            pass
    return arr, close_group(arr, gens)


def typeD4():
    N = []
    for i, j in itertools.combinations(range(4), 2):
        for s in (1, -1):
            N.append([1 if k == i else (s if k == j else 0) for k in range(4)])
    arr = Arr(4, N, "D4 with W(B4)")
    gens = [[[int(p[j] == i) for j in range(4)] for i in range(4)] for p in itertools.permutations(range(4))]
    gens.append([[(-1 if i == j == 0 else int(i == j)) for j in range(4)] for i in range(4)])
    return arr, close_group(arr, gens)


def matmul_l(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


# ---------------------------------------------------------------- the sweep


def sweep(arr, G, stats_name):
    st = dict(pairs=0, zeros=0, pointed=0, P_ok=True, Q_ok=True, K_ok=True, crv_fail=[],
              kinds={}, nonmod_compl=0, compl=0, modular_compl=0, corV=0, line=0, line_ok=True, crvp=0, crvp_fail=0, strict=0, strict_fail=0,
              line_zero=0, line_Lcompl=0)
    cones = arr.cones()
    reps = class_reps(G)
    for g in reps:
        for cone in cones:
            a = analyse(arr, g, cone)
            if a is None:
                continue
            Lt = a['L']
            st['pairs'] += 1
            mu = Lt['mu']
            unc = Lt['unc']
            if mu == 0:
                st['zeros'] += 1
            if (mu == 0) != bool(unc):
                st['crv_fail'].append((g.M, sorted(cone), a['lam']))
            if not unc:
                st['compl'] += 1
                if Lt['modular']:
                    st['modular_compl'] += 1
                else:
                    st['nonmod_compl'] += 1
            idx = {z: i for i, z in enumerate(a['lam'])}
            # Theorem P: pointed cones
            if a['Lz'] == arr.full:
                st['pointed'] += 1
                inhyp = a['clU'] != 0
                if (mu == 0) != inhyp:
                    st['P_ok'] = False
                if inhyp and not (a['clU'] in idx and idx[a['clU']] in unc):
                    st['P_ok'] = False
            # Theorem Q: L + U in a hyperplane
            if a['LU'] != 0:
                st['corV'] += 1
                if not (a['LU'] in idx and idx[a['LU']] in unc):
                    st['Q_ok'] = False
            # Lemma K: complements of cl(U) (when cl(U) != R^d)
            if a['clU'] != 0:
                if a['clU'] not in idx:
                    st['K_ok'] = False
                else:
                    comp = {a['lam'][x] for x in Lt['comps'][idx[a['clU']]]}
                    zstar = set()
                    rk = lambda z: rank([arr.normals[i] for i in range(arr.n) if z >> i & 1], arr.d)
                    for X in arr.flats:
                        if g.act_flat(X) != X or (X & a['Lz']) != a['Lz']:
                            continue  # X must be a g-stable flat inside L
                        if rk(X | a['clU']) == arr.d and (X & a['clU']) == 0:
                            zstar.add(X)  # X cap cl(U) = 0 and X + cl(U) in no hyperplane
                    if comp != zstar:
                        st['K_ok'] = False
            # Proposition Ln: dim L = 1, U in no hyperplane, L cap U = 0
            BL = arr.basis(a['Lz'])
            if len(BL) == 1 and a['clU'] == 0 and rank(BL + a['U'], arr.d) == 1 + len(a['U']):
                st['line'] += 1
                topes = [arr.topes[i] for i in cone]
                c0 = sum(1 for t in topes if g.act_cov(t) == t)
                ZL = [e for e in range(arr.n) if a['Lz'] >> e & 1]
                proj = {tuple(t[e] for e in ZL) for t in topes}
                pos = {e: k for k, e in enumerate(ZL)}
                cL = sum(1 for p in proj
                         if all(g.csign[j] * p[pos[g.cperm[j]]] == p[pos[j]] for j in ZL))
                chi = (-1) ** arr.d * g.det * mu
                if chi != c0 - cL:
                    st['line_ok'] = False
                if chi == 0:
                    st['line_zero'] += 1
                    st['line_Lcompl'] += idx[a['Lz']] not in unc  # L has a complement: CR_V' fails there
            # Conjecture CR_V': a zero has cl(U) or an element inside L without a complement
            # (the strict form, "an element inside L" alone, is counted too when L + U is in no hyperplane)
            if mu == 0:
                st['crvp'] += 1
                inL = any((a['lam'][i] & a['Lz']) == a['Lz'] for i in unc)
                clU = a['clU'] != 0 and idx[a['clU']] in unc
                if not (inL or clU):
                    st['crvp_fail'] += 1
                if a['LU'] == 0:
                    st['strict'] += 1
                    st['strict_fail'] += not inL
            # Theorem Q also gives: L + U in a hyperplane => cl(U) has no complement
            if a['LU'] != 0 and idx[a['clU']] not in unc:
                st['Q_ok'] = False
            if mu == 0:
                k = frozenset(kinds_of_obstruction(arr, a))
                st['kinds'][k] = st['kinds'].get(k, 0) + 1
    return st


def report(name, arr, st):
    kinds = {"+".join(sorted(k)) or "none": v for k, v in st['kinds'].items()}
    print(f"  {name} | n = {arr.n} | pairs {st['pairs']} | zeros {st['zeros']} (not Cor. V: {st['zeros'] - st['corV']}) | pointed {st['pointed']} | "
          f"P {st['P_ok']} | Q {st['Q_ok']} ({st['corV']}) | K {st['K_ok']} | Ln {st['line_ok']} ({st['line']}; zeros {st['line_zero']}, with L complemented {st['line_Lcompl']}) | "
          f"CR_V fails {len(st['crv_fail'])} | CR_V' fails {st['crvp_fail']} of {st['crvp']} | "
          f"'inside L' alone fails {st['strict_fail']} of {st['strict']} | complemented {st['compl']} "
          f"(modular {st['modular_compl']}, non-modular {st['nonmod_compl']}) | obstruction kinds {kinds}",
          flush=True)


def main(argv):
    quick = "--quick" in argv
    ok = part_controls()
    ok &= part_counterexample()
    print("[REP] arrangements of notes/per_cone_vanishing.md section 4 (pairs, zeros must match)")
    expected = {"A2": (30, 6), "A3": (300, 34), "B2": (45, 4), "B3": (1106, 108),
                "generic 4 in R^3": (122, 10), "B3 minus {z=0}": (832, 124),
                "A3 minus a plane": (192, 20), "hexagon 12": (3780, 308), "hexagon 13": (5096, 446),
                "A4": (4634, 342), "generic 5 in R^4": (382, 30)}
    blds = [("A2", lambda: typeA(3)), ("A3", lambda: typeA(4)), ("B2", lambda: typeB(2)),
            ("B3", lambda: typeB(3)), ("generic 4 in R^3", lambda: generic(3)),
            ("B3 minus {z=0}", b3_minus_one), ("A3 minus a plane", deleted_a3),
            ("hexagon 12", lambda: hexagon(False))]
    if not quick:
        blds += [("hexagon 13", lambda: hexagon(True)), ("A4", lambda: typeA(5)),
                 ("generic 5 in R^4", lambda: generic(4))]
    total = 0
    for name, b in blds:
        arr, G = b()
        st = sweep(arr, G, name)
        report(name, arr, st)
        total += st['pairs']
        e = expected[name]
        good = (st['pairs'], st['zeros']) == e and not st['crv_fail'] and st['P_ok'] and st['Q_ok'] and st['K_ok'] and st['line_ok']
        if not good:
            print(f"    MISMATCH or failure: expected (pairs, zeros) = {e}")
            ok = False
    print(f"  total pairs {total}")
    print("[CRV] new families (all g-stable cones, every class representative)")
    fams = [(name, lambda d=d, gens=gens, seeds=seeds, name=name: orbit_arrangement(d, gens, seeds, name))
            for name, d, gens, seeds in new_families(quick)]
    fams.append(("A4 minus a hyperplane", lambda: deleted(lambda: typeA(5), 1, "A4 minus a hyperplane")))
    if not quick:
        fams.append(("A4 minus two hyperplanes", lambda: deleted(lambda: typeA(5), 2, "A4 minus two hyperplanes")))
        fams.append(("D4", typeD4))
    newpairs = newfail = 0
    for name, b in fams:
        try:
            arr, G = b()
        except AssertionError as e:
            print(f"  skip {name}: {e}")
            continue
        st = sweep(arr, G, name)
        report(arr.name, arr, st)
        newpairs += st['pairs']
        newfail += len(st['crv_fail'])
        sizes = {}
        for gM, cone, lam in st['crv_fail']:
            k = (tuple(int(gM[i][i]) for i in range(arr.d)), len(lam))
            sizes[k] = sizes.get(k, 0) + 1
        for (diag, size), cnt in sorted(sizes.items()):
            print(f"    COUNTEREXAMPLES to CR_V: g = diag{diag}, |Lambda(V)^g| = {size}: {cnt} cones")
        ok &= st['P_ok'] and st['Q_ok'] and st['K_ok'] and st['line_ok']
    print(f"  new pairs {newpairs}, counterexamples to CR_V {newfail}")
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
