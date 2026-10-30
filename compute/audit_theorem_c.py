"""Independent audit of Theorem C and Props. A, B of
notes/audit_general_theory_cones.md (notes/audit_theorem_c.md).

Plain Python 3, no dependencies. Imports nothing from this repository; in
particular it does not import audit_general_theory_cones.py or
general_theory.py. Faces are built differently from those scripts: chambers
by a wall-crossing search with a ray-rank test, and the faces of each closed
chamber as the sign vectors of sums of subsets of its rays.

Run (from compute/):  python3 audit_theorem_c.py          (full run)
                      python3 audit_theorem_c.py --quick  (small run)
Exit status 0 iff every check passes and every positive control fires.
"""

import itertools
import random
import sys
from math import gcd

P = 1000003
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
    return cond


# ---------------------------------------------------------------- algebra

def det(M):
    """Exact integer determinant (Bareiss)."""
    A = [list(r) for r in M]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1] if n else 1


def sgn(x):
    return (x > 0) - (x < 0)


def dot(a, x):
    return sum(u * v for u, v in zip(a, x))


def primitive(v):
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    if g == 0:
        return None
    v = [x // g for x in v]
    for x in v:
        if x:
            return tuple(v) if x > 0 else tuple(-y for y in v)


def rank_mod(rows, p=P):
    """Rank over GF(p) of a list of sparse rows {col: int}."""
    piv = {}
    r = 0
    for row in rows:
        row = {c: v % p for c, v in row.items() if v % p}
        while row:
            c = min(row)
            if c in piv:
                prow = piv[c]
                f = row[c]
                for cc, vv in prow.items():
                    nv = (row.get(cc, 0) - f * vv) % p
                    if nv:
                        row[cc] = nv
                    else:
                        row.pop(cc, None)
            else:
                inv = pow(row[c], p - 2, p)
                piv[c] = {cc: vv * inv % p for cc, vv in row.items()}
                r += 1
                break
    return r


def rank_exact(rows):
    """Exact rank over Q of sparse integer rows (fraction-free elimination,
    each row divided by its content)."""
    piv = {}
    r = 0
    for row in rows:
        row = {c: v for c, v in row.items() if v}
        while row:
            c = min(row)
            if c in piv:
                prow = piv[c]
                a, b = row[c], prow[c]
                g = gcd(a, b)
                a, b = a // g, b // g
                new = {}
                for cc in set(row) | set(prow):
                    nv = b * row.get(cc, 0) - a * prow.get(cc, 0)
                    if nv:
                        new[cc] = nv
                g = 0
                for v in new.values():
                    g = gcd(g, v)
                row = {cc: v // g for cc, v in new.items()} if g else {}
            else:
                piv[c] = row
                r += 1
                break
    return r


def rank_dense_exact(vecs):
    return rank_exact([{i: x for i, x in enumerate(v) if x} for v in vecs])


def index_rows(dict_rows):
    """Re-key sparse rows whose keys are arbitrary hashables by integers."""
    keys = {}
    out = []
    for row in dict_rows:
        out.append({keys.setdefault(k, len(keys)): v for k, v in row.items() if v})
    return out


# ---------------------------------------------------------------- arrangements

class Arr:
    """Central arrangement given by integer normals in R^d (must be essential)."""

    def __init__(self, name, normals, seed=1):
        self.name = name
        self.N = [tuple(a) for a in normals]
        self.d = d = len(self.N[0])
        self.n = len(self.N)
        assert rank_dense_exact(self.N) == d, "not essential"
        rng = random.Random(seed)
        # rays: generators of the 1-dimensional flats
        lines = set()
        for sub in itertools.combinations(range(self.n), d - 1):
            rows = [self.N[i] for i in sub]
            v = [(-1) ** j * det([r[:j] + r[j + 1:] for r in rows]) for j in range(d)]
            pv = primitive(v)
            if pv is not None:
                lines.add(pv)
        self.rays = [v for l in sorted(lines) for v in (l, tuple(-x for x in l))]
        self.raysign = [self.sign(r) for r in self.rays]
        # chambers: wall-crossing search from a generic point
        while True:
            x = [rng.randint(-10 ** 6, 10 ** 6) for _ in range(d)]
            s0 = self.sign(x)
            if 0 not in s0:
                break
        assert self.is_chamber(s0)
        seen = {s0}
        todo = [s0]
        while todo:
            s = todo.pop()
            for e in range(self.n):
                t = s[:e] + (-s[e],) + s[e + 1:]
                if t not in seen and self.is_chamber(t):
                    seen.add(t)
                    todo.append(t)
        self.chambers = sorted(seen)
        self.cidx = {c: i for i, c in enumerate(self.chambers)}
        # faces of each closed chamber: signs of sums of subsets of its rays
        faces = {tuple([0] * self.n)}
        self.chamber_rays = {}
        for c in self.chambers:
            R = self.compat_rays(c)
            self.chamber_rays[c] = R
            for k in range(1, len(R) + 1):
                for sub in itertools.combinations(R, k):
                    faces.add(self.sign([sum(r[i] for r in sub) for i in range(d)]))
        self.faces = sorted(faces)
        self.zero = {F: frozenset(e for e in range(self.n) if F[e] == 0) for F in self.faces}
        self.fdim = {}
        self.bary = {}
        for F in self.faces:
            z = self.zero[F]
            self.fdim[F] = d - (rank_dense_exact([self.N[e] for e in z]) if z else 0)
            R = self.compat_rays(F)
            self.bary[F] = tuple(sum(r[i] for r in R) for i in range(d))
            assert F == tuple([0] * self.n) or self.sign(self.bary[F]) == F

    def sign(self, x):
        return tuple(sgn(dot(a, x)) for a in self.N)

    def compat_rays(self, s):
        return [r for r, rs in zip(self.rays, self.raysign)
                if all(u == 0 or u == v for u, v in zip(rs, s))]

    def is_chamber(self, s):
        R = self.compat_rays(s)
        return len(R) >= self.d and rank_dense_exact(R) == self.d

    @staticmethod
    def leq(F, G):
        return all(f == 0 or f == g for f, g in zip(F, G))

    def walls(self, c):
        return [e for e in range(self.n)
                if self.is_chamber(c[:e] + (-c[e],) + c[e + 1:])]

    def simplicial(self):
        return all(len(self.walls(c)) == self.d for c in self.chambers)

    # ---- flags and chamber cycles
    def flags(self, C):
        """Complete flags F_1 < ... < F_{d-1} < C of faces of the closed chamber C."""
        byd = {}
        for F in self.faces:
            if self.fdim[F] >= 1 and self.leq(F, C):
                byd.setdefault(self.fdim[F], []).append(F)
        chains = [[F] for F in byd.get(1, [])]
        for k in range(2, self.d):
            chains = [ch + [G] for ch in chains for G in byd.get(k, []) if self.leq(ch[-1], G)]
        return chains

    def chamber_chain(self, C, eps=True):
        """[C] as {flag tuple of faces (F_1..F_{d-1},C): coefficient}."""
        out = {}
        for fl in self.flags(C):
            pts = [self.bary[F] for F in fl] + [self.bary[C]]
            out[tuple(fl) + (C,)] = sgn(det(pts)) if eps else 1
        return out

    def rho(self, C, eps=True):
        """rho_C = Delta(f)_#(boundary of [C]) as {tuple of zero sets: coeff}."""
        out = {}
        sg = (-1) ** (self.d - 1)
        for fl, v in self.chamber_chain(C, eps).items():
            key = tuple(self.zero[F] for F in fl[:-1])
            out[key] = out.get(key, 0) + sg * v
        return {k: v for k, v in out.items() if v}

    # ---- top-cones
    def cone(self, D, S):
        return [C for C in self.chambers if all(C[e] == D[e] for e in S)]

    def smax(self, V):
        return [e for e in range(self.n) if len({C[e] for C in V}) == 1]

    def lineality_dim(self, V):
        S = self.smax(V)
        return self.d - (rank_dense_exact([self.N[e] for e in S]) if S else 0)

    def cone_faces(self, V):
        return [F for F in self.faces if any(self.leq(F, C) for C in V)]

    def lunes(self):
        """Non-singleton top-lunes L(H, D), H != O, as frozensets of chamber indices."""
        keys = set()
        for H in self.faces:
            z = self.zero[H]
            if len(z) == self.n:
                continue
            zs = sorted(z)
            for D in self.chambers:
                if self.leq(H, D):
                    keys.add((tuple(zs), tuple(D[e] for e in zs)))
        out = set()
        for zs, sv in keys:
            out.add(frozenset(self.cidx[C] for C in self.chambers
                              if tuple(C[e] for e in zs) == sv))
        return sorted(out, key=sorted)


def boundary(chain):
    """Simplicial boundary of {tuple: coeff} (tuples are ordered simplices)."""
    out = {}
    for s, v in chain.items():
        for i in range(len(s)):
            t = s[:i] + s[i + 1:]
            out[t] = out.get(t, 0) + (-1) ** i * v
    return {k: v for k, v in out.items() if v}


class SupportComplex:
    """Delta of the proper part of Lambda = {zero sets of a set of faces}."""

    def __init__(self, arr, faces):
        n = arr.n
        Z = {arr.zero[F] for F in faces}
        self.Z = Z
        self.dim = {}
        for F in faces:
            self.dim[arr.zero[F]] = arr.fdim[F]
        self.d = arr.d
        self.proper = [z for z in Z if 0 < self.dim[z] < arr.d]
        self.proper.sort(key=lambda z: (self.dim[z], sorted(z)))
        up = {z: [w for w in self.proper if self.dim[w] > self.dim[z] and w < z]
              for z in self.proper}
        self.chains = {1: [(z,) for z in self.proper]}
        for k in range(2, arr.d):
            self.chains[k] = [c + (w,) for c in self.chains[k - 1] for w in up[c[-1]]]
        # Moebius from bottom 0 (zero set = everything) to top R^d (empty zero set)
        bot = frozenset(range(n))
        top = frozenset()
        els = sorted(Z, key=lambda z: self.dim[z])
        mu = {}
        for z in els:
            if z == bot:
                mu[z] = 1
            else:
                mu[z] = -sum(mu[w] for w in els if w in mu and w != z and w >= z)
        self.m = (-1) ** arr.d * mu[top] if top in mu else None

    def top_boundary_rows(self):
        top = self.chains[self.d - 1]
        return [boundary({s: 1}) for s in top]

    def dimker(self, exact=False):
        rows = index_rows(self.top_boundary_rows())
        r = rank_exact(rows) if exact else rank_mod(rows)
        return len(self.chains[self.d - 1]) - r


# ---------------------------------------------------------------- arrangements used

def B(n):
    N = []
    for i in range(n):
        v = [0] * n
        v[i] = 1
        N.append(v)
    for i, j in itertools.combinations(range(n), 2):
        for s in (1, -1):
            v = [0] * n
            v[i], v[j] = 1, s
            N.append(v)
    return N


def A_ess(n):
    """Braid arrangement of S_n, essentialized: y_i = x_i - x_n, i < n."""
    N = []
    pairs = []
    for i, j in itertools.combinations(range(n), 2):
        v = [0] * (n - 1)
        v[i] = 1
        if j < n - 1:
            v[j] = -1
        N.append(v)
        pairs.append((i, j))
    return N, pairs


def random_arr(d, k, seed):
    rng = random.Random(seed)
    cand = sorted({primitive(v) for v in itertools.product((-1, 0, 1), repeat=d) if any(v)})
    while True:
        N = rng.sample(cand, k)
        if rank_dense_exact(N) == d:
            return N


def sample_cones(arr, count, seed, nonpointed=None, maxsize=None):
    """Distinct top-cones (as sorted chamber tuples) from random (D, S)."""
    rng = random.Random(seed)
    seen = set()
    out = []
    tries = 0
    while len(out) < count and tries < 200 * count:
        tries += 1
        D = rng.choice(arr.chambers)
        S = rng.sample(range(arr.n), rng.randint(1, arr.n))
        V = tuple(arr.cone(D, S))
        if V in seen or len(V) == len(arr.chambers):
            continue
        if maxsize and len(V) > maxsize:
            continue
        L = arr.lineality_dim(V)
        if nonpointed is True and L == 0:
            continue
        if nonpointed is False and L > 0:
            continue
        seen.add(V)
        out.append(list(V))
    return out


# ---------------------------------------------------------------- checks

def spanning(arr, V, exact=False):
    """Theorem C(i): rank span{rho_C : C in V} = dim H~_{d-2}(Delta(Lambda-bar(V))) = m(V).
    Returns (m, dimker, rank)."""
    K = SupportComplex(arr, arr.cone_faces(V))
    rhos = [arr.rho(C) for C in V]
    tops = set(K.chains[arr.d - 1])
    for r in rhos:
        check(set(r) <= tops, f"{arr.name}: rho_C not supported on Lambda-bar(V)")
        check(not boundary(r), f"{arr.name}: rho_C not a cycle")
    rows = index_rows(rhos)
    if exact:
        rk = rank_exact(rows)
        dk = K.dimker(exact=True)
    else:
        rk = rank_mod(rows)
        dk = K.dimker()
    return K.m, dk, rk


def check_cones(arr, cones, exact=False, log=print, label=""):
    bad = 0
    for V in cones:
        m, dk, rk = spanning(arr, V, exact)
        if not (m == dk == rk):
            bad += 1
            check(False, f"{arr.name}{label}: cone of size {len(V)}: m={m} dimker={dk} rank={rk}")
    log(f"  [span{'-exact' if exact else ''}] {arr.name}{label}: {len(cones)} cones, "
        f"sizes {min(map(len, cones))}..{max(map(len, cones))}, "
        f"lineality dims {sorted({arr.lineality_dim(V) for V in cones})}, failures {bad}")
    return bad


def orientation_check(arr, eps=True):
    """Sum over all chambers of [C] is a cycle (coherent orientation)."""
    tot = {}
    for C in arr.chambers:
        for k, v in arr.chamber_chain(C, eps).items():
            tot[k] = tot.get(k, 0) + v
    return not boundary(tot)


def lune_checks(arr, log=print, exact=True, torsion_primes=(2, 3)):
    """Prop. B: every lune relation holds at chain level; Gamma/Lune has
    dimension |mu(L(A))|; rho is onto H~(L-bar(A))."""
    lunes = arr.lunes()
    rho = {i: arr.rho(C) for i, C in enumerate(arr.chambers)}
    nz = 0
    for L in lunes:
        s = {}
        for i in L:
            for k, v in rho[i].items():
                s[k] = s.get(k, 0) + v
        if any(s.values()):
            nz += 1
    check(nz == 0, f"{arr.name}: {nz} lunes with nonzero chamber-cycle sum")
    K = SupportComplex(arr, arr.faces)
    mu = K.m
    rows = [{i: 1 for i in L} for L in lunes]
    rk = rank_exact(rows) if exact else rank_mod(rows)
    check(len(arr.chambers) - rk == mu, f"{arr.name}: dim Gamma/Lune {len(arr.chambers) - rk} != |mu| {mu}")
    tors = {p: rank_mod(rows, p) for p in torsion_primes}
    for p, r in tors.items():
        check(r == rk, f"{arr.name}: Lune rank mod {p} = {r} != {rk}")
    rr = rank_mod(index_rows(list(rho.values())))
    check(rr == mu, f"{arr.name}: chamber cycles span rank {rr} != {mu}")
    log(f"  [propB] {arr.name}: {len(lunes)} non-singleton lunes, all chain sums zero: {nz == 0}; "
        f"#chambers {len(arr.chambers)} - rank Lune {rk} = {len(arr.chambers) - rk} = |mu| {mu}; "
        f"rank mod {list(tors)} = {list(tors.values())}; rank span rho = {rr}")
    return lunes


def q_check(arr, lunes, cones, exact, log=print, label=""):
    """Theorem C(ii),(iii): q(V) = m(V), and Gamma_V cap Lune = span{lunes in V}."""
    rk = rank_exact if exact else rank_mod
    Lrows = [{i: 1 for i in L} for L in lunes]
    rL = rk(Lrows)
    bad = 0
    for V in cones:
        idx = {arr.cidx[C] for C in V}
        K = SupportComplex(arr, arr.cone_faces(V))
        q = rk(Lrows + [{i: 1} for i in idx]) - rL
        inside = [{i: 1 for i in L} for L in lunes if L <= idx]
        g1 = len(V) - rk(inside) if inside else len(V)
        if not (q == K.m == g1):
            bad += 1
            check(False, f"{arr.name}: q={q} m={K.m} #V-rank(lunes in V)={g1}")
    log(f"  [q=m{'-exact' if exact else ''}] {arr.name}{label}: {len(cones)} cones, failures {bad}")
    return bad


def perm_matrix_action(arr, g):
    """Action of a linear map g (matrix) on faces, via interior points."""
    def app(x):
        return tuple(sum(g[i][j] * x[j] for j in range(arr.d)) for i in range(arr.d))
    fmap = {}
    for F in arr.faces:
        fmap[F] = arr.sign(app(arr.bary[F]))
    zmap = {arr.zero[F]: arr.zero[fmap[F]] for F in arr.faces}
    return fmap, zmap


def equivariance(arr, gs, chambers, twist=True):
    """g . rho_C = det(g) rho_{gC} at chain level; returns number of failures."""
    bad = 0
    for g in gs:
        dg = det(g) if twist else 1
        fmap, zmap = perm_matrix_action(arr, g)
        for C in chambers:
            lhs = {tuple(zmap[z] for z in k): v for k, v in arr.rho(C).items()}
            rhs = {k: dg * v for k, v in arr.rho(fmap[C]).items()}
            if lhs != rhs:
                bad += 1
    return bad


def signed_perms(n, rng, count):
    out = []
    for _ in range(count):
        p = list(range(n))
        rng.shuffle(p)
        s = [rng.choice((1, -1)) for _ in range(n)]
        g = [[0] * n for _ in range(n)]
        for i in range(n):
            g[p[i]][i] = s[i]
        out.append(g)
    return out


# ---- braid sign comparison with Prop. Phi (Wachs normalization)

def perm_sign(w):
    s = 1
    w = list(w)
    for i in range(len(w)):
        for j in range(i + 1, len(w)):
            if w[i] > w[j]:
                s = -s
    return s


def braid_setup(n):
    N, pairs = A_ess(n)
    arr = Arr(f"A{n - 1}", N)

    def word(C):
        # x_i < x_j iff sign of (x_i - x_j) is -1; order letters by x
        less = {(i, j): C[k] < 0 for k, (i, j) in enumerate(pairs)}
        key = lambda i: sum(1 for j in range(n) if j != i and
                            (less[(j, i)] if j < i else not less[(i, j)]))
        return tuple(sorted(range(n), key=key))

    def partition(z):
        parent = list(range(n))

        def find(a):
            while parent[a] != a:
                a = parent[a]
            return a
        for k in z:
            i, j = pairs[k]
            parent[find(i)] = find(j)
        blocks = {}
        for i in range(n):
            blocks.setdefault(find(i), []).append(i)
        return frozenset(frozenset(b) for b in blocks.values())

    return arr, word, partition


def braid_sign(n, twist=True, log=print):
    """Compare rho^B_{C_w} (Prop. B) with Wachs's rho_w (Prop. Phi):
    returns the set of values c(w) * sgn(w) (twist) or c(w) (no twist)."""
    arr, word, partition = braid_setup(n)
    vals = set()
    for C in arr.chambers:
        w = word(C)
        r = arr.rho(C)
        # support must be exactly the chains of interval partitions of w
        for k in r:
            for z in k:
                pi = partition(z)
                pos = {x: i for i, x in enumerate(w)}
                check(all(max(pos[x] for x in b) - min(pos[x] for x in b) == len(b) - 1 for b in pi),
                      f"A{n - 1}: rho_C has a non-interval partition")
        # Wachs chain: k-block partition w_1|...|w_{k-1}|rest, k = 2..n-1.
        # Our chains list flats by increasing dimension, i.e. coarsest partition
        # first (2 blocks first). Wachs lists the chain in refinement order,
        # finest first, so his oriented simplex is ours reversed: factor rev.
        wch = []
        for k in range(2, n):
            pi = frozenset([frozenset([w[i]]) for i in range(k - 1)] + [frozenset(w[k - 1:])])
            wch.append(pi)
        ours = tuple(wch)
        coeff = None
        for key, v in r.items():
            if tuple(partition(z) for z in key) == ours:
                coeff = v
        L = len(ours)
        rev = perm_sign(list(reversed(range(L))))
        c = coeff * rev
        vals.add(c * perm_sign(w) if twist else c)
    return vals


def braid_det(n):
    """det of each transposition on the essentialized coordinates is -1."""
    out = set()
    for i, j in itertools.combinations(range(n), 2):
        # x -> x with i,j swapped; y_k = x_k - x_{n-1}
        g = [[0] * (n - 1) for _ in range(n - 1)]
        for k in range(n - 1):
            # image of basis vector e_k of y-space under the swap, in y-coords:
            # pick x = e_k (x_{n-1} = 0), swap, then subtract last coordinate
            x = [0] * n
            x[k] = 1
            x[i], x[j] = x[j], x[i]
            y = [x[t] - x[n - 1] for t in range(n - 1)]
            for t in range(n - 1):
                g[t][k] = y[t]
        out.add(det(g))
    return out


def braid_gs(n):
    """All permutation matrices of S_n on the essentialized coordinates."""
    gs = []
    for p in itertools.permutations(range(n)):
        g = [[0] * (n - 1) for _ in range(n - 1)]
        for k in range(n - 1):
            x = [0] * n
            x[p[k]] = 1
            y = [x[t] - x[n - 1] for t in range(n - 1)]
            for t in range(n - 1):
                g[t][k] = y[t]
        gs.append((p, g))
    return gs


# ---------------------------------------------------------------- controls

def controls(log=print):
    ok = True
    # exact vs modular rank are different instruments
    c1 = rank_exact([{0: P}]) == 1 and rank_mod([{0: P}]) == 0
    # torsion detector
    c2 = rank_mod([{0: 2}], 2) == 0 and rank_exact([{0: 2}]) == 1
    log(f"  [ctl] exact rank sees [[p]] (1) where mod-p rank does not (0): {c1}")
    log(f"  [ctl] mod-2 rank detects the torsion of Z/[[2]]: {c2}")
    ok &= c1 and c2
    A3 = Arr("A3", A_ess(4)[0])
    B3 = Arr("B3", B(3))
    # face counts and Euler characteristic of the sphere
    c3 = (len(A3.chambers), len(A3.faces), len(B3.chambers), len(B3.faces)) == (24, 75, 48, 147)
    log(f"  [ctl] face counts A3 24/75, B3 48/147: {c3}")
    ok &= c3
    # Folkman/|mu| values: A3 6, B3 15
    KA, KB = SupportComplex(A3, A3.faces), SupportComplex(B3, B3.faces)
    c4 = (KA.m, KA.dimker(), KB.m, KB.dimker()) == (6, 6, 15, 15)
    log(f"  [ctl] |mu| and dim H~ for A3 (6) and B3 (15): {c4}")
    ok &= c4
    # orientation: with det signs Sum [C] is a cycle; with all +1 it is not
    c5 = orientation_check(B3, True) and not orientation_check(B3, False)
    log(f"  [ctl] Sum_C [C] is a cycle with det orientation, not with +1: {c5}")
    ok &= c5
    # spanning instrument can fail: non-convex chamber sets
    rng = random.Random(5)
    found = None
    for _ in range(400):
        U = rng.sample(B3.chambers, rng.randint(2, 6))
        Ufaces = [F for F in B3.faces if any(B3.leq(F, C) for C in U)]
        K = SupportComplex(B3, Ufaces)
        rows = index_rows([B3.rho(C) for C in U])
        rk, dk = rank_mod(rows), K.dimker()
        if rk < dk:
            found = (len(U), rk, dk)
            break
    log(f"  [ctl] a non-convex set U of B3 chambers whose cycles do not span: {found}")
    ok &= found is not None
    # lune relation fails if one chamber's sign is flipped
    lunes = B3.lunes()
    L = max(lunes, key=len)
    s = {}
    for t, i in enumerate(sorted(L)):
        for k, v in B3.rho(B3.chambers[i]).items():
            s[k] = s.get(k, 0) + (-v if t == 0 else v)
    c6 = any(s.values())
    log(f"  [ctl] lune relation with one sign flipped fails: {c6}")
    ok &= c6
    # det twist detected on B3
    gs = signed_perms(3, random.Random(2), 20)
    c7 = equivariance(B3, gs, B3.chambers[:6], twist=False) > 0
    log(f"  [ctl] equivariance without det fails: {c7}")
    ok &= c7
    # braid sign without sgn(w) not constant
    c8 = len(braid_sign(4, twist=False)) > 1
    log(f"  [ctl] braid: c(w) alone is not constant (sgn needed): {c8}")
    ok &= c8
    # simplicial certificate: B3 is simplicial
    c9 = B3.simplicial()
    log(f"  [ctl] B3 is simplicial (non-Coxeter certificate does not fire): {c9}")
    ok &= c9
    # Theorem 1 sum over all of Lambda would give a different m: q vs m differs
    # on a non-top-cone union; covered by the non-convex control above.
    check(ok, "a positive control did not fire")
    return ok


# ---------------------------------------------------------------- main

def euler_ok(arr):
    chi = sum((-1) ** (arr.fdim[F] - 1) for F in arr.faces if arr.fdim[F] > 0)
    return chi == 1 + (-1) ** (arr.d - 1)


def main(quick=False, log=print):
    log("Audit of Theorem C / Props. A, B (independent code)")
    log("Positive controls:")
    controls(log)

    log("Arrangements:")
    R4 = Arr("R4", random_arr(4, 9, seed=11))
    R5 = Arr("R5", random_arr(5, 8, seed=7))
    B4 = Arr("B4", B(4))
    A5 = Arr("A5", A_ess(6)[0]) if not quick else None
    for arr in [R4, R5, B4] + ([A5] if A5 else []):
        nonsimp = sum(1 for c in arr.chambers if len(arr.walls(c)) > arr.d)
        ok = euler_ok(arr)
        check(ok, f"{arr.name}: Euler characteristic of the sphere fails")
        log(f"  {arr.name}: d={arr.d}, {arr.n} hyperplanes, {len(arr.chambers)} chambers, "
            f"{len(arr.faces)} faces, Euler char ok {ok}, non-simplicial chambers {nonsimp}")
        if arr.name.startswith("R"):
            check(nonsimp > 0, f"{arr.name}: no non-simplicial chamber; not certified non-Coxeter")
    check(len(B4.chambers) == 384, "B4 chamber count")
    if A5:
        check((len(A5.chambers), len(A5.faces)) == (720, 4683), "A5 face count")
    log(f"  normals R4: {R4.N}")
    log(f"  normals R5: {R5.N}")

    log("Orientation coherence (Sum_C [C] is a cycle):")
    for arr in (R4, R5):
        ok = orientation_check(arr)
        check(ok, f"{arr.name}: orientation incoherent")
        log(f"  {arr.name}: {ok}")

    log("Theorem C(i): chamber cycles span H~_{d-2}(Lambda-bar(V)) (rank mod p; rigorous, see note):")
    nR = 40 if quick else 400
    check_cones(R4, sample_cones(R4, nR, 1), log=log)
    check_cones(R4, sample_cones(R4, nR // 4, 2, nonpointed=True), log=log, label=" non-pointed")
    check_cones(R5, sample_cones(R5, nR, 3), log=log)
    check_cones(R5, sample_cones(R5, nR // 4, 4, nonpointed=True), log=log, label=" non-pointed")
    check_cones(B4, sample_cones(B4, 15 if quick else 150, 5, nonpointed=True), log=log, label=" non-pointed")
    if A5:
        check_cones(A5, sample_cones(A5, 60, 6, nonpointed=True), log=log, label=" non-pointed")
    log("Theorem C(i), exact rank over Q (sample):")
    check_cones(R4, sample_cones(R4, 10 if quick else 40, 7, nonpointed=True), exact=True, log=log, label=" non-pointed")
    check_cones(R5, sample_cones(R5, 10 if quick else 40, 8, nonpointed=True), exact=True, log=log, label=" non-pointed")
    check_cones(B4, sample_cones(B4, 4 if quick else 20, 9, nonpointed=True, maxsize=200), exact=True, log=log,
                label=" non-pointed")
    if A5:
        check_cones(A5, sample_cones(A5, 10, 10, nonpointed=True, maxsize=240), exact=True, log=log,
                    label=" non-pointed")

    log("Prop. B (lune relations at chain level; dim Gamma/Lune = |mu|; no small torsion):")
    lunesR4 = lune_checks(R4, log, exact=True)
    lunesR5 = lune_checks(R5, log, exact=True)
    lunesB4 = lune_checks(B4, log, exact=not quick)

    log("Theorem C(ii)-(iii): q(V) = m(V) = #V - dim span{lunes in V}:")
    q_check(R4, lunesR4, sample_cones(R4, 10 if quick else 60, 12, nonpointed=True), exact=True, log=log,
            label=" non-pointed")
    q_check(R5, lunesR5, sample_cones(R5, 10 if quick else 60, 13, nonpointed=True), exact=True, log=log,
            label=" non-pointed")
    q_check(B4, lunesB4, sample_cones(B4, 5 if quick else 40, 14, nonpointed=True), exact=False, log=log,
            label=" non-pointed")

    log("Theorem C(iv): g.rho_C = det(g) rho_{gC} at chain level:")
    rng = random.Random(15)
    gs = signed_perms(4, rng, 10 if quick else 60)
    Cs = rng.sample(B4.chambers, 8 if quick else 40)
    bad = equivariance(B4, gs, Cs)
    check(bad == 0, f"B4 equivariance: {bad} failures")
    badu = equivariance(B4, gs, Cs, twist=False)
    log(f"  B4: {len(gs)} signed permutations x {len(Cs)} chambers: failures {bad}; "
        f"without det: {badu} failures (control)")
    check(badu > 0, "B4: det-free equivariance control did not fire")

    log("Braid case vs Prop. Phi (Wachs normalization):")
    for n in ((3, 4) if quick else (3, 4, 5, 6)):
        vals = braid_sign(n)
        dets = braid_det(n)
        check(len(vals) == 1, f"A{n - 1}: c(w) sgn(w) not constant: {vals}")
        check(dets == {-1}, f"A{n - 1}: det of a transposition {dets}")
        log(f"  n={n}: c(w)*sgn(w) over all w in S_n = {sorted(vals)}; det(transposition) = {sorted(dets)}")
    n = 4 if quick else 5
    arr, word, _ = braid_setup(n)
    gm = braid_gs(n)
    bad = 0
    for p, g in gm:
        check(det(g) == perm_sign(p), f"A{n - 1}: det != sgn")
    bad = equivariance(arr, [g for _, g in gm], arr.chambers[:10])
    check(bad == 0, f"A{n - 1}: equivariance failures {bad}")
    log(f"  A{n - 1}: det(g) = sgn(g) for all g in S_{n}; g.rho_C = sgn(g) rho_gC for all g, "
        f"10 chambers: failures {bad}")

    log("")
    if FAIL:
        log("FAILURES:")
        for f in FAIL:
            log("  " + f)
        log("RESULT: FAIL")
        return 1
    log("RESULT: ALL CHECKS PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(quick="--quick" in sys.argv))
