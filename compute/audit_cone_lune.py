#!/usr/bin/env python3
"""Independent audit of the cone/lune note (mg-52a16).

Companion to notes/audit_cone_lune_lie_theory.md.  Audits
notes/cone_lune_lie_theory.md WITHOUT importing compute/cone_lie.py or any
other module of this repository.  Plain Python 3, no dependencies.

Method (deliberately different from cone_lie.py, which closes cocircuits
under the Tits product):
  * arithmetic is exact, over Q or over Q(sqrt5) (for H_3);
  * rays = the 1-dimensional flats, as exact kernels of (d-1)-subsets;
  * covectors = sign vectors of sums of k signed rays, k = 0..d.  This is
    complete for an essential central arrangement: every face of dimension
    k >= 1 is a pointed cone spanned by extreme rays lying on 1-flats, and it
    contains a simplicial subcone on k of them, whose ray sum lies in the
    face's relative interior.  Completeness is re-checked against the exact
    face count sum_{X <= Y} |mu(X, Y)| of the flat lattice (Zaslavsky);
  * Lune = span of L(H, D) = {C : HC = D} over faces H != O, built from the
    Tits product itself (not from flat classes);
  * Lie := Lune^perp, an exact rational nullspace (no Ree / Aguiar-Mahajan
    input).  Membership in Lune is tested exactly as orthogonality to Lie.

Checks (one line each; exit status 0 iff all pass):
  [faces]   #topes and #covectors equal the Zaslavsky counts.
  [class]   every class {C : C|_Z = D|_Z} (Z a flat != A) is some L(H, D).
  [L]       Lemma L for every lune and every top-cone (or a sample).
  [E]       Lemma E: E_h(lune) is 0 or in Lune[A^h], exactly, every h.
  [5.2]     Theorem 5.2: pointed V => rank(Lie|_V) = |V| (rank mod p,
            which is a lower bound for the rational rank).
  [7.1a]    chamber sum of V lies in Lune (exactly) iff V is not pointed.
  [7.1b]    "non-singleton top-cone" (printed Ex. 10.9) is strictly stronger
            than "non-pointed": some pointed non-singleton V has its
            chamber sum outside Lune.
  [G1]      (extra evidence for Conjecture G1) dim(Gamma_V cap Lune) =
            rank(lunes inside V).
  [int]     Lie^int(V) = 0 for proper V, by a DIRECT rank computation of the
            constraints Hz = 0 (H in F(V), H != O), not via Brown's theorem.
  [CTL]     positive controls.

Run (from compute/):
  python3 audit_cone_lune.py > output/audit_cone_lune.txt
"""

import itertools
import random
import sys
from fractions import Fraction

P = 2 ** 31 - 1


# ---------------------------------------------------------------- fields

class Q5:
    """a + b*sqrt(5), a, b rational."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, o):
        o = _q5(o)
        return Q5(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __sub__(self, o):
        o = _q5(o)
        return Q5(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        return _q5(o) - self

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __mul__(self, o):
        o = _q5(o)
        return Q5(self.a * o.a + 5 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = _q5(o)
        n = o.a * o.a - 5 * o.b * o.b
        return self * Q5(o.a / n, -o.b / n)

    def __eq__(self, o):
        o = _q5(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def __repr__(self):
        return "(%s+%s*r5)" % (self.a, self.b)


def _q5(x):
    return x if isinstance(x, Q5) else Q5(x)


def sign(x):
    if isinstance(x, Q5):
        return sign_pair(x.a, x.b)
    return (x > 0) - (x < 0)


def sign_pair(a, b):
    """sign of a + b sqrt5 (a, b rational or int)."""
    sa, sb = (a > 0) - (a < 0), (b > 0) - (b < 0)
    if sa == sb or sb == 0:
        return sa
    if sa == 0:
        return sb
    c = a * a - 5 * b * b
    return sa if c > 0 else (sb if c < 0 else 0)


# ------------------------------------------------------- exact linear algebra

def rref(rows, ncols):
    """Exact RREF over a field.  Returns (pivot rows, pivot columns)."""
    rows = [list(r) for r in rows]
    piv = []
    out = []
    for r in rows:
        for (pr, pc) in zip(out, piv):
            if r[pc] != 0:
                f = r[pc]
                r = [x - f * y for x, y in zip(r, pr)]
        c = next((j for j in range(ncols) if r[j] != 0), None)
        if c is None:
            continue
        f = r[c]
        r = [x / f for x in r]
        for i, pr in enumerate(out):
            if pr[c] != 0:
                g = pr[c]
                out[i] = [x - g * y for x, y in zip(pr, r)]
        out.append(r)
        piv.append(c)
    return out, piv


def rank_exact(rows, ncols):
    return len(rref(rows, ncols)[0])


def nullspace(rows, ncols, zero, one):
    out, piv = rref(rows, ncols)
    free = [j for j in range(ncols) if j not in piv]
    basis = []
    for f in free:
        v = [zero] * ncols
        v[f] = one
        for pr, pc in zip(out, piv):
            v[pc] = -pr[f]
        basis.append(v)
    return basis


def rank_mod_p(rows):
    """Rank over GF(P) of integer rows (lists).  <= rational rank."""
    basis = {}          # pivot col -> row (normalised to 1 at pivot)
    r = 0
    for row in rows:
        row = [x % P for x in row]
        for c in sorted(basis):
            if row[c]:
                f = row[c]
                br = basis[c]
                row = [(x - f * y) % P for x, y in zip(row, br)]
        c = next((j for j, x in enumerate(row) if x), None)
        if c is None:
            continue
        inv = pow(row[c], P - 2, P)
        basis[c] = [(x * inv) % P for x in row]
        r += 1
    return r


# ------------------------------------------------------------ arrangements

class Arr:
    def __init__(self, name, normals, field="Q"):
        self.name = name
        if field == "Q":
            self.N = [[Fraction(x) for x in n] for n in normals]
            self.zero, self.one = Fraction(0), Fraction(1)
        else:
            self.N = [[_q5(x) for x in n] for n in normals]
            self.zero, self.one = Q5(0), Q5(1)
        self.m = len(self.N)
        self.d = len(self.N[0])
        assert rank_exact(self.N, self.d) == self.d, "not essential"
        self._flats()
        self._rays()
        self._covectors()

    # flats as frozensets of hyperplane indices
    def closure(self, S):
        S = list(S)
        r = rank_exact([self.N[i] for i in S], self.d) if S else 0
        return frozenset(e for e in range(self.m)
                         if e in S or rank_exact([self.N[i] for i in S] + [self.N[e]], self.d) == r)

    def rk(self, S):
        return rank_exact([self.N[i] for i in S], self.d) if S else 0

    def _flats(self):
        fl = {frozenset()}
        frontier = [frozenset()]
        while frontier:
            new = []
            for F in frontier:
                for e in range(self.m):
                    if e not in F:
                        G = self.closure(F | {e})
                        if G not in fl:
                            fl.add(G)
                            new.append(G)
            frontier = new
        self.flats = sorted(fl, key=lambda F: (len(F), sorted(F)))
        self.flat_rank = {F: self.rk(F) for F in self.flats}

    def mobius_from(self, X):
        """mu(X, Y) for flats Y >= X (Y contains X as hyperplane sets)."""
        up = [Y for Y in self.flats if X <= Y]
        up.sort(key=lambda Y: len(Y))
        mu = {}
        for Y in up:
            if Y == X:
                mu[Y] = 1
            else:
                mu[Y] = -sum(mu[Z] for Z in up if Z in mu and X <= Z and Z < Y)
        return mu

    def _rays(self):
        lines = []
        seen = set()
        for S in itertools.combinations(range(self.m), self.d - 1):
            if self.d > 1 and self.rk(S) != self.d - 1:
                continue
            ns = nullspace([self.N[i] for i in S], self.d, self.zero, self.one)
            assert len(ns) == 1
            v = ns[0]
            k = next(j for j in range(self.d) if v[j] != 0)
            v = tuple(x / v[k] for x in v)
            if v not in seen:
                seen.add(v)
                lines.append(v)
        self.lines = lines
        # integer-scaled dot vectors of the signed rays, as (a, b) pairs
        dots = []
        for v in lines:
            row = []
            for n in self.N:
                s = sum((x * y for x, y in zip(n, v)), self.zero)
                row.append(_q5(s))
            den = 1
            for z in row:
                for q in (z.a, z.b):
                    den = den * q.denominator // _gcd(den, q.denominator)
            row = [(int(z.a * den), int(z.b * den)) for z in row]
            dots.append(row)
            dots.append([(-a, -b) for (a, b) in row])
        self.ray_dots = dots

    def _covectors(self):
        cov = {tuple([0] * self.m)}
        R = self.ray_dots
        for k in range(1, self.d + 1):
            for comb in itertools.combinations(range(len(R)), k):
                sv = []
                for e in range(self.m):
                    a = b = 0
                    for i in comb:
                        a += R[i][e][0]
                        b += R[i][e][1]
                    sv.append(sign_pair(a, b))
                cov.add(tuple(sv))
        self.cov = cov
        self.topes = sorted(c for c in cov if 0 not in c)
        self.tidx = {c: i for i, c in enumerate(self.topes)}
        self.O = tuple([0] * self.m)

    def zaslavsky(self):
        bottom = frozenset()
        ntopes = sum(abs(x) for x in self.mobius_from(bottom).values())
        nfaces = sum(sum(abs(x) for x in self.mobius_from(X).values())
                     for X in self.flats)
        return ntopes, nfaces


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def tits(X, Y):
    return tuple(x if x else y for x, y in zip(X, Y))


def zeroset(X):
    return frozenset(e for e, x in enumerate(X) if x == 0)


# --------------------------------------------------------------- lune theory

def lunes(A):
    """dict (z(H), D|_{z(H)}) -> frozenset of tope indices, for H != O."""
    L = {}
    for H in A.cov:
        if H == A.O:
            continue
        Z = zeroset(H)
        for D in A.topes:
            if tits(H, D) != D:
                continue
            key = (Z, tuple(D[e] for e in sorted(Z)))
            if key in L:
                continue
            L[key] = frozenset(A.tidx[C] for C in A.topes if tits(H, C) == D)
    return L


def lie_basis(vectors, n):
    """Integer basis of the orthogonal complement of the given 0/1 sets."""
    rows = [[Fraction(1) if j in S else Fraction(0) for j in range(n)] for S in vectors]
    ns = nullspace(rows, n, Fraction(0), Fraction(1))
    out = []
    for v in ns:
        den = 1
        for x in v:
            den = den * x.denominator // _gcd(den, x.denominator)
        out.append([int(x * den) for x in v])
    return out


def top_cones(A):
    """All distinct nonempty sets {C : C_e = s_e for e in S}."""
    full = frozenset(range(len(A.topes)))
    seen = {full}
    frontier = [full]
    while frontier:
        new = []
        for V in frontier:
            for e in range(A.m):
                for s in (1, -1):
                    W = frozenset(i for i in V if A.topes[i][e] == s)
                    if W and W != V and W not in seen:
                        seen.add(W)
                        new.append(W)
        frontier = new
    return sorted(seen, key=lambda V: (len(V), sorted(V)))


def smax(A, V):
    return frozenset(e for e in range(A.m)
                     if len({A.topes[i][e] for i in V}) == 1)


def is_pointed(A, V):
    return A.rk(smax(A, V)) == A.d


def cone_faces(A, V):
    S = smax(A, V)
    s = {e: A.topes[next(iter(V))][e] for e in S}
    return [X for X in A.cov if all(X[e] in (0, s[e]) for e in S)]


# ---------------------------------------------------------------- checks

def check_classes(A, L):
    sets = set(L.values())
    ok = True
    for Z in A.flats:
        if len(Z) == A.m:
            continue
        zs = sorted(Z)
        cls = {}
        for i, C in enumerate(A.topes):
            cls.setdefault(tuple(C[e] for e in zs), set()).add(i)
        for c in cls.values():
            if frozenset(c) not in sets or len(c) < 2:
                ok = False
    return ok


def check_lemma_L(A, L, cones):
    for V in cones:
        S = smax(A, V)
        for (Z, Dz), Ls in L.items():
            # any D in L(H,D) with the given D|_Z; L depends only on (Z, D|_Z)
            inV = Ls <= V
            # Lemma L: L(H, D) in V iff (D in V and S_max(V) in z(H)); every
            # D in the lune gives the same lune, so test each of them.
            for i in Ls:
                if ((i in V) and (S <= Z)) != inV:
                    return False
    return True


def restriction_data(A, h):
    """Chambers of A^h (faces F with z(F) = {h}) and Lie[A^h] basis."""
    ch = sorted(F for F in A.cov if zeroset(F) == {h})
    idx = {F: i for i, F in enumerate(ch)}
    sets = set()
    for G in A.cov:
        if G[h] != 0 or G == A.O:
            continue
        for Dp in ch:
            if tits(G, Dp) != Dp:
                continue
            sets.add(frozenset(idx[F] for F in ch if tits(G, F) == Dp))
    return ch, idx, lie_basis(sorted(sets, key=sorted), len(ch))


def E_h(A, h, idx, S):
    v = [0] * len(idx)
    for i in S:
        C = A.topes[i]
        F = C[:h] + (0,) + C[h + 1:]
        if F in idx:
            v[idx[F]] += C[h]
    return v


def check_lemma_E(A, L):
    ok = True
    nonzero = 0
    for h in range(A.m):
        ch, idx, lie_h = restriction_data(A, h)
        for (Z, Dz), S in L.items():
            v = E_h(A, h, idx, S)
            if any(v):
                nonzero += 1
                if h not in Z:
                    ok = False      # Lemma E: must vanish when h not in z(H)
            if any(sum(x * y for x, y in zip(v, b)) for b in lie_h):
                ok = False
    return ok, nonzero


def lie_int_dim_upper(A, V):
    """|V| - rank_p of the constraints Hz = 0; an UPPER bound on dim_Q."""
    Vl = sorted(V)
    pos = {i: k for k, i in enumerate(Vl)}
    rows = set()
    for H in cone_faces(A, V):
        if H == A.O:
            continue
        cls = {}
        for i in Vl:
            cls.setdefault(tits(H, A.topes[i]), []).append(pos[i])
        for c in cls.values():
            rows.add(tuple(1 if k in c else 0 for k in range(len(Vl))))
    return len(Vl) - rank_mod_p([list(r) for r in rows])


def audit(A, max_cones=None, lemma_L_cones=300, int_cones=None, seed=1):
    print("[%s] m=%d d=%d lines=%d covectors=%d topes=%d flats=%d"
          % (A.name, A.m, A.d, len(A.lines), len(A.cov), len(A.topes), len(A.flats)))
    ok = True
    zt, zf = A.zaslavsky()
    good = (zt == len(A.topes) and zf == len(A.cov))
    print("  [faces] topes %d = Zaslavsky %d; covectors %d = sum |mu(X,Y)| %d: %s"
          % (len(A.topes), zt, len(A.cov), zf, good))
    ok &= good
    L = lunes(A)
    n = len(A.topes)
    lie = lie_basis(sorted(L.values(), key=sorted), n)
    mu_top = abs(A.mobius_from(frozenset())[frozenset(range(A.m))])
    good = len(lie) == mu_top
    print("  [lie]   dim Lune^perp = %d, |mu(flat lattice)| = %d: %s (reported)"
          % (len(lie), mu_top, good))
    good = check_classes(A, L)
    print("  [class] every flat class is a non-singleton L(H,D): %s" % good)
    ok &= good
    good, nz = check_lemma_E(A, L)
    print("  [E]     E_h(L) in Lune[A^h] exactly, and 0 unless h in z(H): %s (%d nonzero images)"
          % (good, nz))
    ok &= good
    cones = top_cones(A)
    rng = random.Random(seed)
    tested = cones if (max_cones is None or len(cones) <= max_cones) else rng.sample(cones, max_cones)
    print("  cones: %d total, %d tested" % (len(cones), len(tested)))
    lc = tested if len(tested) <= lemma_L_cones else rng.sample(tested, lemma_L_cones)
    good = check_lemma_L(A, L, lc)
    print("  [L]     Lemma L on %d cones x %d lunes: %s" % (len(lc), len(L), good))
    ok &= good
    n_point = n_point_ok = n_np = n_sum_ok = g1_ok = 0
    witness = None
    for V in tested:
        Vl = sorted(V)
        pointed = is_pointed(A, V)
        r = rank_mod_p([[b[i] for i in Vl] for b in lie])
        in_lune = all(sum(b[i] for i in Vl) == 0 for b in lie)
        if pointed:
            n_point += 1
            n_point_ok += (r == len(Vl))
            if len(Vl) > 1 and not in_lune and witness is None:
                witness = Vl
        else:
            n_np += 1
        n_sum_ok += (in_lune == (not pointed))
        inside = [S for S in L.values() if S <= V]
        rin = rank_mod_p([[1 if i in S else 0 for i in Vl] for S in inside]) if inside else 0
        g1_ok += (rin == len(Vl) - r)
    print("  [5.2]   pointed cones: %d; rank(Lie|_V) = |V|: %d/%d" % (n_point, n_point_ok, n_point))
    ok &= n_point_ok == n_point
    print("  [7.1a]  chamber sum in Lune <=> not pointed: %d/%d (non-pointed: %d)"
          % (n_sum_ok, len(tested), n_np))
    ok &= n_sum_ok == len(tested)
    print("  [7.1b]  pointed non-singleton cone with sum outside Lune: %s"
          % (witness is not None))
    ok &= witness is not None
    print("  [G1]    dim(Gamma_V cap Lune) = rank(lunes in V): %d/%d (Conjecture G1, reported)"
          % (g1_ok, len(tested)))
    if int_cones != 0:
        ic = [V for V in tested if len(V) < n]
        if int_cones is not None and len(ic) > int_cones:
            ic = rng.sample(ic, int_cones)
        zero = sum(1 for V in ic if lie_int_dim_upper(A, V) == 0)
        print("  [int]   Lie^int(V) = 0 (direct rank) for proper V: %d/%d" % (zero, len(ic)))
        full = lie_int_dim_upper(A, frozenset(range(n)))
        print("  [int]   full V: dim Lie^int <= %d, dim Lune^perp = %d (reported)" % (full, len(lie)))
    print("  => %s" % ("PASS" if ok else "FAIL"))
    return ok


# ------------------------------------------------------------- the arrangements

def h3():
    """The 15 reflecting planes of H_3 (positive roots up to scale)."""
    phi = Q5(Fraction(1, 2), Fraction(1, 2))
    iphi = phi - 1
    roots = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    base = (Q5(1), phi, iphi)
    for k in range(3):          # cyclic (even) permutations
        p = base[k:] + base[:k]
        for s1, s2 in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            roots.append((p[0], s1 * p[1], s2 * p[2]))
    return roots


ARRANGEMENTS = [
    ("A1xA2 (reducible, R^3)", [(1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 1)], "Q", {}),
    ("resonance R^3 (all 0/1 normals)",
     [v for v in itertools.product((0, 1), repeat=3) if any(v)], "Q", {}),
    ("A2xA2 (reducible, R^4)",
     [(1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 1, 1)], "Q",
     {}),
    ("generic 6 in R^5",
     [(1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (0, 0, 1, 0, 0), (0, 0, 0, 1, 0), (0, 0, 0, 0, 1),
      (1, 2, 3, 5, 7)], "Q", {}),
    ("non-generic 7 in R^4",
     [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (1, 1, 0, 0), (0, 1, 1, 1),
      (1, 0, 1, -1)], "Q", {}),
    ("H3 (non-crystallographic, Q(sqrt5))", h3(), "Q5",
     {"lemma_L_cones": 300, "int_cones": 1500}),
]


def controls():
    ok = True
    # (1) the ray-sum covector method must FAIL Zaslavsky if a ray is dropped.
    A = Arr("B2", [(1, 0), (0, 1), (1, 1), (1, -1)])
    A.ray_dots = A.ray_dots[:-2]
    A._covectors()
    c1 = A.zaslavsky()[0] != len(A.topes)
    print("[CTL] dropping one line breaks the Zaslavsky tope count: %s" % c1)
    # (2) the pointed test must fail on a non-pointed cone (a half-plane of A_2).
    A = Arr("A2", [(1, 0), (0, 1), (1, 1)])
    L = lunes(A)
    lie = lie_basis(sorted(L.values(), key=sorted), len(A.topes))
    V = [i for i, C in enumerate(A.topes) if C[0] == 1]
    r = rank_mod_p([[b[i] for i in V] for b in lie])
    c2 = (not is_pointed(A, frozenset(V))) and r < len(V)
    print("[CTL] half-plane of A_2: not pointed and dependent mod Lune: %s" % c2)
    # (3) Lemma E check must fire on a corrupted lune (one chamber removed).
    S = max(L.values(), key=len)
    S2 = frozenset(list(S)[1:])
    fired = False
    for h in range(A.m):
        ch, idx, lie_h = restriction_data(A, h)
        v = E_h(A, h, idx, S2)
        if any(sum(x * y for x, y in zip(v, b)) for b in lie_h):
            fired = True
    print("[CTL] corrupted lune is caught by the exact E_h membership test: %s" % fired)
    # (4) Lie^int is not identically zero: the full arrangement has it = Lie.
    c4 = lie_int_dim_upper(A, frozenset(range(len(A.topes)))) == len(lie) == 2
    print("[CTL] full A_2: dim Lie^int = dim Lie = 2: %s" % c4)
    return ok and c1 and c2 and fired and c4


def main():
    ok = controls()
    for name, normals, field, kw in ARRANGEMENTS:
        A = Arr(name, normals, field)
        ok &= audit(A, **kw)
        sys.stdout.flush()
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
