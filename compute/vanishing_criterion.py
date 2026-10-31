"""When does the cone Lie character chi_V(g) vanish?

Companion script of notes/vanishing_criterion.md.  Plain Python 3, exact
arithmetic (Fractions; Q(sqrt 5) for H3).  No imports from the other scripts.

For a finite reflection arrangement A (types A_n, B_n, D_4, F_4, H_3), a
top-cone V and a finite-order symmetry g of A with gV = V, it computes

  chi_V(g) = (-1)^d det(g) mu(Lambda(V)^g)

directly from the definition (the support lattice of V and its g-stable
part), and compares it with

  [CF]  sum_{Y in L^g} mu_{L^g}(0, Y) c(Y, g)                (closed formula)
  [Z]   sum_{X in Z*(V,g)} mu_{L(A)^g}(0, X) m(V_X^{Fix g})   (Formula Z)

where Z*(V, g) is the set of g-stable flats X inside lin V with
X cap Fix(g) = 0 and X + Fix(g) in no hyperplane, and m(V_X^{Fix g}) is the
bottom multiplicity of the restricted cone, computed from its own support
lattice.  It then tests

  [S]   "chi_V(g) != 0 for some cone V" iff some X in Z*(g) (lin V = R^d) has
        mu_{L(A)^g}(0, X) != 0, and the witness cone (a g-fixed chamber of the
        localization A_X) has chi = mu(0, X);
  [P]   pointed V: chi_V(g) = number of g-fixed chambers of V;
  [E]   Fix(g) = 0: chi_V(g) = 0 unless V is all chambers;
  [I]   g an involution: every X in Z*(g) has mu(0, X) != 0;
  [CR]  for X in Z*(g): mu(0, X) = 0 iff some g-stable flat strictly inside X
        has no g-stable complement in [0, X] (Crapo);
  [SC]  sign coherence: for fixed g, the nonzero mu(0, X), X in Z*(g), have
        one sign (reported, it fails);
  [PC]  cancellation count: pairs where some X in Z*(V, g) has mu(0, X) != 0
        but chi_V(g) = 0 (reported);
  [A+], [A-]  the type-A rule for +-w (see type_A_rule), against [S], on the
        root-system arrangements A2-A5 and by set partitions for n <= 8.
Springer regularity of each class is reported next to [S].

Usage (from compute/):
  python3 vanishing_criterion.py                  all types, F4 sampled
  python3 vanishing_criterion.py --types A3,B2    a subset
  python3 vanishing_criterion.py --quick          A2, A3, B2, B3; type A n <= 6
  python3 vanishing_criterion.py --n9             also five classes -w at n = 9
"""

import random
import sys
from fractions import Fraction
from itertools import combinations


# ---------------------------------------------------------------- fields

class Q5:
    """a + b sqrt(5), a and b rational."""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    @staticmethod
    def lift(x):
        return x if isinstance(x, Q5) else Q5(x)

    def __add__(self, o):
        o = Q5.lift(o)
        return Q5(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-Q5.lift(o))

    def __rsub__(self, o):
        return Q5.lift(o) - self

    def __mul__(self, o):
        o = Q5.lift(o)
        return Q5(self.a * o.a + 5 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = Q5.lift(o)
        n = o.a * o.a - 5 * o.b * o.b
        return self * Q5(o.a / n, -o.b / n)

    def __eq__(self, o):
        o = Q5.lift(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def sign(self):
        a, b = self.a, self.b
        sa, sb = (a > 0) - (a < 0), (b > 0) - (b < 0)
        if sb == 0:
            return sa
        if sa == 0 or sa == sb:
            return sb
        return sa if a * a > 5 * b * b else sb

    def __repr__(self):
        return f"({self.a}+{self.b}r5)"


def sgn(x):
    if isinstance(x, Q5):
        return x.sign()
    return (x > 0) - (x < 0)


# ---------------------------------------------------------------- linear algebra

class Span:
    """Row-echelon basis of a subspace of K^d (vectors are tuples)."""

    def __init__(self, d):
        self.d = d
        self.rows = []          # (pivot, vector with 1 at pivot)

    def reduce(self, v):
        v = list(v)
        for p, r in self.rows:
            c = v[p]
            if c != 0:
                v = [x - c * y for x, y in zip(v, r)]
        return v

    def add(self, v):
        v = self.reduce(v)
        for p, c in enumerate(v):
            if c != 0:
                v = [x / c for x in v]
                # keep fully reduced
                self.rows = [(q, [x - r[p] * y for x, y in zip(r, v)])
                             for q, r in self.rows]
                self.rows.append((p, v))
                return True
        return False

    def contains(self, v):
        return all(c == 0 for c in self.reduce(v))

    def rank(self):
        return len(self.rows)


def rank_of(vecs, d):
    s = Span(d)
    for v in vecs:
        s.add(v)
    return s.rank()


def det(M):
    """Determinant of a square matrix (list of rows)."""
    M = [list(r) for r in M]
    n = len(M)
    out = 1
    for i in range(n):
        p = next((k for k in range(i, n) if M[k][i] != 0), None)
        if p is None:
            return 0
        if p != i:
            M[i], M[p] = M[p], M[i]
            out = -out
        out = out * M[i][i]
        for k in range(i + 1, n):
            c = M[k][i] / M[i][i]
            if c != 0:
                M[k] = [x - c * y for x, y in zip(M[k], M[i])]
    return out


# ---------------------------------------------------------------- Moebius

def mobius_from_bottom(elems, leq):
    """mu(bottom, x) for every x of a finite poset with a unique bottom.
    elems must be sorted so that x <= y implies index(x) <= index(y)."""
    mu = {}
    for i, x in enumerate(elems):
        if i == 0:
            mu[x] = 1
            continue
        mu[x] = -sum(mu[y] for y in elems[:i] if leq(y, x))
    return mu


def popcount(x):
    return bin(x).count("1")


# ---------------------------------------------------------------- root systems

def gram(typ, n):
    """Gram matrix of the simple roots, and the field."""
    G = [[Fraction(0)] * n for _ in range(n)]
    field = Fraction
    if typ in "AD":
        for i in range(n):
            G[i][i] = Fraction(2)
        edges = [(i, i + 1) for i in range(n - 1)]
        if typ == "D":
            edges = [(i, i + 1) for i in range(n - 2)] + [(n - 3, n - 1)]
        for i, j in edges:
            G[i][j] = G[j][i] = Fraction(-1)
    elif typ == "B":
        for i in range(n):
            G[i][i] = Fraction(2)
        G[n - 1][n - 1] = Fraction(1)
        for i in range(n - 1):
            G[i][i + 1] = G[i + 1][i] = Fraction(-1)
    elif typ == "F":
        G = [[Fraction(x) for x in r] for r in
             [[2, -1, 0, 0], [-1, 2, -1, 0], [0, -1, 1, Fraction(-1, 2)],
              [0, 0, Fraction(-1, 2), 1]]]
    elif typ == "H":
        field = Q5
        half = Q5(Fraction(1, 2))
        tau2 = Q5(Fraction(1, 4), Fraction(1, 4))          # cos(pi/5)
        G = [[Q5(1), -tau2, Q5(0)], [-tau2, Q5(1), -half], [Q5(0), -half, Q5(1)]]
    return G, field


class RootSystem:
    def __init__(self, name):
        self.name = name
        typ, n = name[0], int(name[1:])
        self.typ, self.d = typ, n
        G, field = gram(typ, n)
        self.G = G
        zero = field(0)
        one = field(1)
        simple = [tuple(one if j == i else zero for j in range(n)) for i in range(n)]
        self.zero, self.one = zero, one

        def form(u, v):
            s = zero
            for i in range(n):
                if u[i] != 0:
                    for j in range(n):
                        if v[j] != 0:
                            s = s + u[i] * G[i][j] * v[j]
            return s

        self.form = form

        def refl(i, v):
            c = 2 * form(v, simple[i]) / G[i][i]
            return tuple(x - c * y for x, y in zip(v, simple[i]))

        roots = list(simple)
        seen = set(roots)
        k = 0
        while k < len(roots):
            for i in range(n):
                r = refl(i, roots[k])
                if r not in seen:
                    seen.add(r)
                    roots.append(r)
            k += 1
        pos = [r for r in roots if sgn(next(x for x in r if x != 0)) > 0]
        # order positive roots by height for readability
        pos.sort(key=lambda r: (sum(sgn(x) for x in r), r.__repr__()))
        self.m = len(pos)
        self.pos = pos
        self.roots = pos + [tuple(-x for x in r) for r in pos]   # index e, e+m = -e
        self.index = {r: i for i, r in enumerate(self.roots)}
        self.simple_idx = [self.index[s] for s in simple]

        def perm_of_linear(f):
            return tuple(self.index[f(r)] for r in self.roots)

        self.sref = [perm_of_linear(lambda v, i=i: refl(i, v)) for i in range(n)]
        self.neg = tuple((i + self.m) % (2 * self.m) for i in range(2 * self.m))
        self.extra = self._extra_symmetries()

    def _extra_symmetries(self):
        """Generators of Aut(root system) beyond W (diagram automorphisms and -1)."""
        n = self.d
        ex = []
        if self.typ == "A" and n >= 2:
            ex.append(self.neg)
        if self.typ == "D" and n == 4:
            for p in [(2, 1, 0, 3), (3, 1, 2, 0)]:   # generate S3 on the legs 0,2,3
                ex.append(tuple(self.index[tuple(r[p[j]] for j in range(n))]
                                for r in self.roots))
        return ex


# ---------------------------------------------------------------- the arrangement

def compose(p, q):
    """(p o q)(i) = p[q[i]]."""
    return tuple(p[i] for i in q)


def inverse(p):
    out = [0] * len(p)
    for i, x in enumerate(p):
        out[x] = i
    return tuple(out)


def closure_group(gens, ident):
    elems = [ident]
    seen = {ident}
    k = 0
    while k < len(elems):
        for s in gens:
            h = compose(s, elems[k])
            if h not in seen:
                seen.add(h)
                elems.append(h)
        k += 1
    return elems


class Arrangement:
    def __init__(self, name, with_extra=True):
        R = RootSystem(name)
        self.R = R
        self.name = name
        self.d = d = R.d
        self.m = m = R.m
        ident = tuple(range(2 * m))
        self.W = closure_group(R.sref, ident)
        Wset = set(self.W)
        self.G = closure_group(R.sref + (R.extra if with_extra else []), ident)
        self.inW = {g: (g in Wset) for g in self.G}
        self.full = (1 << m) - 1
        # chambers: sign vector of w C_0 at positive root e is + iff w^{-1}(e) > 0
        self.chambers = []
        self.chamber_index = {}
        for w in self.W:
            wi = inverse(w)
            pmask = 0
            for e in range(m):
                if wi[e] < m:
                    pmask |= 1 << e
            self.chamber_index[pmask] = len(self.chambers)
            self.chambers.append(pmask)
        self.nch = len(self.chambers)
        self._build_faces()
        self._build_flats()
        self.gdata = {}

    # signed hyperplane action: g maps hyperplane e to e' with sign s
    def hyp_action(self, g):
        m = self.m
        out = []
        for e in range(m):
            t = g[e]
            out.append((t % m, 1 if t < m else -1))
        return out

    def act_mask(self, g, mask):
        """Image of a set of hyperplanes (bitmask) under g."""
        m = self.m
        out = 0
        while mask:
            low = mask & -mask
            e = low.bit_length() - 1
            out |= 1 << (g[e] % m)
            mask ^= low
        return out

    def act_signvec(self, g, pos, neg):
        """g acts on a sign vector (pos, neg masks over hyperplanes):
        (gF)(g.e) = s * F(e) when g(alpha_e) = s alpha_{g.e}."""
        m = self.m
        npos = nneg = 0
        for e in range(m):
            t = g[e]
            f, s = t % m, (1 if t < m else -1)
            v = 1 if (pos >> e) & 1 else (-1 if (neg >> e) & 1 else 0)
            v *= s
            if v > 0:
                npos |= 1 << f
            elif v < 0:
                nneg |= 1 << f
        return npos, nneg

    def chamber_perm(self, g):
        full = self.full
        out = []
        for pm in self.chambers:
            p, _ = self.act_signvec(g, pm, full ^ pm)
            out.append(self.chamber_index[p])
        return tuple(out)

    def _build_faces(self):
        """All faces of A as (pos, neg) masks: w F_J, signs from heights."""
        R = self.R
        m, d = self.m, self.d
        faces = set()
        for J in range(1 << d):
            # height outside J of a root (in simple coords) decides the sign
            sig = []
            for r in R.roots:
                h = sum((r[i] for i in range(d) if not (J >> i) & 1), R.zero)
                sig.append(sgn(h))
            for w in self.W:
                wi = inverse(w)
                pos = neg = 0
                for e in range(m):
                    s = sig[wi[e]]
                    if s > 0:
                        pos |= 1 << e
                    elif s < 0:
                        neg |= 1 << e
                faces.add((pos, neg))
        self.faces = sorted(faces)

    def _build_flats(self):
        R = self.R
        m, d = self.m, self.d

        def closure(mask):
            s = Span(d)
            for e in range(m):
                if (mask >> e) & 1:
                    s.add(R.pos[e])
            out = 0
            for e in range(m):
                if s.contains(R.pos[e]):
                    out |= 1 << e
            return out, s.rank()

        flats = {0: 0}          # hyp mask -> rank of the annihilator
        frontier = [0]
        while frontier:
            new = []
            for F in frontier:
                for e in range(m):
                    if not (F >> e) & 1:
                        c, r = closure(F | (1 << e))
                        if c not in flats:
                            flats[c] = r
                            new.append(c)
            frontier = new
        self.flats = flats      # flat X <-> hyp(X); dim X = d - flats[hyp]
        self.closure = lambda mask: closure(mask)[0]

    def dim(self, hypmask):
        return self.d - self.flats[hypmask]

    # ------------------------------------------------ per-element data
    def data(self, g):
        if g in self.gdata:
            return self.gdata[g]
        R = self.R
        d, m = self.d, self.m
        cols = [R.roots[g[R.simple_idx[j]]] for j in range(d)]
        M = [[cols[j][i] for j in range(d)] for i in range(d)]   # matrix of g
        U0 = Span(d)                                             # annihilator of Fix g
        for j in range(d):
            U0.add(tuple(cols[j][i] - (R.one if i == j else R.zero) for i in range(d)))
        # hyperplanes containing Fix(g): roots in U0
        hypU = 0
        for e in range(m):
            if U0.contains(R.pos[e]):
                hypU |= 1 << e
        order = 1
        h = g
        ident = tuple(range(2 * m))
        while h != ident:
            h = compose(g, h)
            order += 1
        dfix = []
        h = ident
        for k in range(1, order + 1):
            h = compose(g, h)
            cols_k = [R.roots[h[R.simple_idx[j]]] for j in range(d)]
            Uk = Span(d)
            for j in range(d):
                Uk.add(tuple(cols_k[j][i] - (R.one if i == j else R.zero) for i in range(d)))
            dfix.append(d - Uk.rank())
        D = det(M)
        dd = {
            "det": int(sgn(D)),
            "U0": U0,
            "dimU": d - U0.rank(),
            "hypU": hypU,          # hyperplanes containing Fix(g)
            "order": order,
            "dfix": tuple(dfix),
            "chperm": self.chamber_perm(g),
        }
        self.gdata[g] = dd
        return dd

    def stable_flats(self, g):
        return [X for X in self.flats if self.act_mask(g, X) == X]

    def meets_U_trivially(self, X, gd):
        """X cap Fix(g) = 0  iff  span(hyp X) + U0 = everything."""
        s = Span(self.d)
        for r in gd["U0"].rows:
            s.add(r[1])
        for e in range(self.m):
            if (X >> e) & 1:
                s.add(self.R.pos[e])
        return s.rank() == self.d

    def sum_in_no_hyperplane(self, X, gd):
        """X + Fix(g) lies in no hyperplane: no hyperplane contains both."""
        return (X & gd["hypU"]) == 0


# ---------------------------------------------------------------- cones

def all_cones(A):
    """All top-cones as chamber bitmasks (BFS by adding sign constraints)."""
    m = A.m
    half = []
    for e in range(m):
        p = n = 0
        for i, pm in enumerate(A.chambers):
            if (pm >> e) & 1:
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
    return seen


def cone_constraints(A, V):
    """(P, N): hyperplanes on which every chamber of V is + resp. -."""
    full = A.full
    P, N = full, full
    x = V
    while x:
        low = x & -x
        i = low.bit_length() - 1
        pm = A.chambers[i]
        P &= pm
        N &= full ^ pm
        x ^= low
    return P, N


def chamber_set(A, P, N):
    out = 0
    for i, pm in enumerate(A.chambers):
        if (pm & P) == P and (pm & N) == 0:
            out |= 1 << i
    return out


def signed_roots_of(A, P, N):
    """The cone as the set of root indices s_e alpha_e (s_e = side)."""
    m = A.m
    out = []
    for e in range(m):
        if (P >> e) & 1:
            out.append(e)
        elif (N >> e) & 1:
            out.append(e + m)
    return frozenset(out)


def orbit_reps(A, cones, group):
    reps = []
    seen = set()
    for V in sorted(cones):
        P, N = cone_constraints(A, V)
        T = signed_roots_of(A, P, N)
        if T in seen:
            continue
        for g in group:
            seen.add(frozenset(g[i] for i in T))
        reps.append(V)
    return reps


def stabilizer(A, P, N):
    T = signed_roots_of(A, P, N)
    return [g for g in A.G if frozenset(g[i] for i in T) == T]


def classes_in(group_elems):
    """Conjugacy classes of a finite permutation group given by its elements."""
    S = set(group_elems)
    inv = {g: inverse(g) for g in group_elems}
    done = set()
    out = []
    for g in group_elems:
        if g in done:
            continue
        cl = {compose(compose(h, g), inv[h]) for h in group_elems}
        done |= cl
        out.append((g, len(cl)))
    assert sum(c for _, c in out) == len(S)
    return out


# ---------------------------------------------------------------- the three sides

class ConeCtx:
    """Everything about one cone V that does not depend on g."""

    def __init__(self, A, V):
        self.A = A
        self.V = V
        self.P, self.N = cone_constraints(A, V)
        self.smax = self.P | self.N
        self.Lhyp = A.closure(self.smax)        # hyp(lin V)
        P, N = self.P, self.N
        self.faces = [(p, n) for p, n in A.faces if (n & P) == 0 and (p & N) == 0]
        self.lam = sorted({A.full ^ (p | n) for p, n in self.faces},
                          key=lambda z: -popcount(z))   # zero sets, bottom (all) first
        self.chambers = [i for i in range(A.nch) if (V >> i) & 1]


def chi_direct(C, g, gd):
    """(-1)^d det(g) mu(Lambda(V)^g) from the support lattice."""
    A = C.A
    lamg = [Z for Z in C.lam if A.act_mask(g, Z) == Z]
    # order: Z1 <= Z2 (as flats) iff zero-set Z1 contains Z2
    mu = mobius_from_bottom(lamg, lambda a, b: (a & b) == b)
    return (-1) ** A.d * gd["det"] * mu[0]


def c_count(C, g, gd, Y):
    """Number of g-fixed chambers of A_Y inside |V|."""
    perm = gd["chperm"]
    A = C.A
    fixed = set()
    for i in C.chambers:
        r = A.chambers[i] & Y
        if (A.chambers[perm[i]] & Y) == r:
            fixed.add(r)
    return len(fixed)


def chi_cf(C, g, gd, Lg_mu):
    """Theorem CF: sum over g-stable flats inside lin V."""
    tot = 0
    for Y, mu in Lg_mu.items():
        if mu and (Y & C.Lhyp) == C.Lhyp:
            tot += mu * c_count(C, g, gd, Y)
    return tot


def m_restricted(C, g, gd, X):
    """m(V_X^{Fix g}) from the support lattice of the restricted cone:
    zero sets (inside hyp X) of the g-stable faces of V."""
    A = C.A
    elems = set()
    for p, n in C.faces:
        if A.act_signvec(g, p, n) == (p, n):
            elems.add(X & (A.full ^ (p | n)))
    elems = sorted(elems, key=lambda z: -popcount(z))
    assert elems[0] == X and 0 in elems
    mu = mobius_from_bottom(elems, lambda a, b: (a & b) == b)
    return (-1) ** gd["dimU"] * mu[0]


def zstar(A, g, gd, Lg):
    """Z*(g): g-stable flats X with X cap Fix g = 0 and X + Fix g in no hyperplane."""
    return [X for X in Lg
            if A.sum_in_no_hyperplane(X, gd) and A.meets_U_trivially(X, gd)]


class GCtx:
    """Everything about g that does not depend on V."""

    def __init__(self, A, g):
        self.g = g
        self.gd = gd = A.data(g)
        Lg = sorted(A.stable_flats(g), key=lambda z: -popcount(z))
        self.mu = mobius_from_bottom(Lg, lambda a, b: (a & b) == b)   # mu_{L^g}(0, .)
        self.zs = zstar(A, g, gd, Lg)
        self.zmu = {X: self.mu[X] for X in self.zs}
        nz = [v for v in self.zmu.values() if v]
        self.crit = bool(nz)                       # [S] prediction
        self.signs = {sgn(v) for v in nz}


def chi_z(C, G):
    tot = 0
    for X, mu in G.zmu.items():
        if mu and (X & C.Lhyp) == C.Lhyp:
            tot += mu * m_restricted(C, G.g, G.gd, X)
    return tot


def witness_cone(A, G, X):
    """A g-stable top-cone with lineality X: the chambers of A inside a
    g-fixed chamber of the localization A_X."""
    perm = G.gd["chperm"]
    for i, pm in enumerate(A.chambers):
        if (A.chambers[perm[i]] & X) == (pm & X):
            P, N = pm & X, (A.full ^ pm) & X
            return chamber_set(A, P, N)
    return None


# ---------------------------------------------------------------- labels

def class_label(A, g):
    gd = A.data(g)
    o = gd["order"]
    divs = [k for k in range(1, o + 1) if o % k == 0]
    fx = ",".join(str(gd["dfix"][k - 1]) for k in divs)
    lab = f"o={o} Fix(g^k),k|o=[{fx}] det={gd['det']:+d}"
    if A.R.typ == "A":
        lab = cycle_type_A(A, g) + "  " + lab
    if A.R.typ == "B":
        lab = signed_cycle_type_B(A, g) + "  " + lab
    return lab


def cycle_type_A(A, g):
    """Cycle type of the underlying permutation of [n+1] (and the sign -1)."""
    R = A.R
    n = A.d
    # root e_i - e_j (i < j) = alpha_i + ... + alpha_{j-1}
    def ij(r):
        sup = [k for k in range(n) if r[k] != 0]
        i, j = sup[0], sup[-1] + 1
        return (i, j) if r[sup[0]] > 0 else (j, i)
    neg = not A.inW[g]
    pts = n + 1
    # image of e_i - e_{i+1}: decide pi from roots e_0 - e_j
    img = {}
    for j in range(1, pts):
        r = tuple(Fraction(1) if 0 <= k < j else Fraction(0) for k in range(n))
        a, b = ij(R.roots[g[R.index[r]]])
        if neg:
            a, b = b, a
        img[(0, j)] = (a, b)
    pi0 = img[(0, 1)][0]
    pi = [pi0] + [img[(0, j)][1] for j in range(1, pts)]
    seen = [False] * pts
    cyc = []
    for i in range(pts):
        if not seen[i]:
            L = 0
            k = i
            while not seen[k]:
                seen[k] = True
                k = pi[k]
                L += 1
            cyc.append(L)
    cyc.sort(reverse=True)
    return ("-" if neg else "") + "(" + ",".join(map(str, cyc)) + ")"


def signed_cycle_type_B(A, g):
    R = A.R
    n = A.d
    # short roots e_i = alpha_i + ... + alpha_n (0-based i)
    e = [tuple(Fraction(1) if k >= i else Fraction(0) for k in range(n)) for i in range(n)]
    idx = {R.index[v]: (i, 1) for i, v in enumerate(e)}
    idx.update({R.index[tuple(-x for x in v)]: (i, -1) for i, v in enumerate(e)})
    pi, sg = [0] * n, [1] * n
    for i in range(n):
        j, s = idx[g[R.index[e[i]]]]
        pi[i], sg[i] = j, s
    seen = [False] * n
    cyc = []
    for i in range(n):
        if not seen[i]:
            L, s, k = 0, 1, i
            while not seen[k]:
                seen[k] = True
                s *= sg[k]
                k = pi[k]
                L += 1
            cyc.append(f"{L}{'+' if s > 0 else '-'}")
    cyc.sort(reverse=True)
    return "[" + " ".join(cyc) + "]"


def lineality_label(A, Lhyp):
    """dim L and the W-orbit of the flat L (by its sorted orbit minimum)."""
    key = min(A.act_mask(w, Lhyp) for w in A.W)
    return (A.dim(Lhyp), key)


# ---------------------------------------------------------------- Springer regularity

def to_float(x):
    if isinstance(x, Q5):
        return float(x.a) + float(x.b) * 5 ** 0.5
    return float(x)


def springer_regular(A, g, seed=7):
    """True iff g has an eigenvector (over C) on no reflecting hyperplane.
    Floating point; eigenvalues are o-th roots of unity, o = order of g."""
    import cmath
    R = A.R
    d = A.d
    o = A.data(g)["order"]
    cols = [R.roots[g[R.simple_idx[j]]] for j in range(d)]
    M = [[to_float(cols[j][i]) for j in range(d)] for i in range(d)]
    Gf = [[to_float(x) for x in r] for r in R.G]
    posf = [[to_float(x) for x in r] for r in R.pos]
    rng = random.Random(seed)
    for k in range(o):
        z = cmath.exp(2j * cmath.pi * k / o)
        B = [[M[i][j] - (z if i == j else 0) for j in range(d)] for i in range(d)]
        # kernel by Gaussian elimination with partial pivoting
        piv, r = [], 0
        B = [row[:] for row in B]
        for c in range(d):
            p = max(range(r, d), key=lambda i: abs(B[i][c]), default=None)
            if p is None or abs(B[p][c]) < 1e-9:
                continue
            B[r], B[p] = B[p], B[r]
            pv = B[r][c]
            B[r] = [x / pv for x in B[r]]
            for i in range(d):
                if i != r and abs(B[i][c]) > 0:
                    f = B[i][c]
                    B[i] = [a - f * b for a, b in zip(B[i], B[r])]
            piv.append(c)
            r += 1
            if r == d:
                break
        free = [c for c in range(d) if c not in piv]
        if not free:
            continue
        basis = []
        for f in free:
            v = [0j] * d
            v[f] = 1
            for i, c in enumerate(piv):
                v[c] = -B[i][f]
            basis.append(v)
        coef = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in basis]
        v = [sum(c * b[i] for c, b in zip(coef, basis)) for i in range(d)]
        vals = [abs(sum(a[i] * Gf[i][j] * v[j] for i in range(d) for j in range(d)))
                for a in posf]
        if min(vals) > 1e-7:
            return True
    return False


# ---------------------------------------------------------------- the run

def crapo_uncomplemented(A, G, X):
    """Some g-stable flat strictly between 0 and X has no g-stable complement
    in [0, X] (meet = intersection, join = smallest flat containing both)."""
    iv = [Y for Y in G.mu if (Y & X) == X]
    for y in iv:
        if y == X or y == A.full:
            continue
        if not any((y & z) == X and A.closure(y | z) == A.full for z in iv):
            return True
    return False


def check_pairs(A, pairs, gctx, out, stats, cls_stats, lin_stats, direct=True):
    """pairs: list of (V, g, class key).  Records every check."""
    ok = True
    ident = tuple(range(2 * A.m))
    allch = (1 << A.nch) - 1
    for V, g, ck in pairs:
        C = ConeCtx(A, V)
        if g not in gctx:
            gctx[g] = GCtx(A, g)
        G = gctx[g]
        gd = G.gd
        lhs = chi_direct(C, g, gd) if direct else None
        cf = chi_cf(C, g, gd, G.mu)
        z = chi_z(C, G)
        if direct and lhs != cf:
            ok = False
            out.write(f"  FAIL [CF] V={V:x} g={class_label(A, ck)}: direct={lhs} CF={cf}\n")
        if z != cf:
            ok = False
            out.write(f"  FAIL [Z] V={V:x} g={class_label(A, ck)}: CF={cf} Z={z}\n")
        chi = cf
        # [P] pointed cones: chi = number of g-fixed chambers of V
        if C.Lhyp == A.full:
            nfix = sum(1 for i in C.chambers if gd["chperm"][i] == i)
            if chi != nfix:
                ok = False
                out.write(f"  FAIL [P] V={V:x}\n")
        # [E] elliptic g: chi = 0 on every cone other than all chambers
        if gd["dimU"] == 0 and V != allch and chi != 0:
            ok = False
            out.write(f"  FAIL [E] V={V:x} g={class_label(A, ck)}\n")
        zsV = [X for X, mu in G.zmu.items() if mu and (X & C.Lhyp) == C.Lhyp]
        pc = bool(zsV)
        if pc != (chi != 0):
            stats["PC_fail"] += 1
            lab = class_label(A, ck)
            stats["PC_classes"][lab] = stats["PC_classes"].get(lab, 0) + 1
            if stats["PC_fail"] <= 6:
                terms = sorted((A.dim(X), G.zmu[X], m_restricted(C, g, gd, X)) for X in zsV)
                out.write(f"  [PC] cancellation: g={class_label(A, ck)}, dim L={A.dim(C.Lhyp)}, "
                          f"#V={len(C.chambers)}, chi=0, terms (dim X, mu, m)={terms}\n")
        stats["pairs"] += 1
        cs = cls_stats.setdefault(ck, {"pairs": 0, "nonzero": 0, "full": None})
        cs["pairs"] += 1
        if V == allch:
            cs["full"] = chi
        if chi:
            cs["nonzero"] += 1
        lab = lineality_label(A, C.Lhyp)
        ls = lin_stats.setdefault(lab, {"pairs": 0, "nonzero": 0, "corV": 0,
                                        "empty": 0, "other": 0, "g1": 0})
        ls["pairs"] += 1
        if g == ident:
            ls["g1"] += 1
        if chi:
            ls["nonzero"] += 1
        else:
            if (C.Lhyp & gd["hypU"]) != 0:
                ls["corV"] += 1           # Cor. V: a hyperplane contains L and Fix g
            elif not zsV:
                ls["empty"] += 1          # Z*(V) carries no X with mu != 0
            else:
                ls["other"] += 1          # cancellation
    return ok


def sample_pairs(A, Gcl, nsamp, seed):
    """g-stable cones for every class: sign constraints taken from a g-stable
    face, closed under <g>."""
    rng = random.Random(seed)
    pairs, seen = [], set()
    allch = (1 << A.nch) - 1
    for rep, _ in Gcl:
        gd = A.data(rep)
        stable_faces = [(p, n) for p, n in A.faces if A.act_signvec(rep, p, n) == (p, n)]
        for V in [allch] + [None] * nsamp:
            if V is None:
                p, n = rng.choice(stable_faces)
                supp = [e for e in range(A.m) if ((p | n) >> e) & 1]
                S = rng.sample(supp, rng.randint(0, len(supp)))
                P = N = 0
                for e in S:
                    if (p >> e) & 1:
                        P |= 1 << e
                    else:
                        N |= 1 << e
                h = rep
                for _ in range(gd["order"]):
                    P2, N2 = A.act_signvec(h, P, N)
                    P, N = P | P2, N | N2
                V = chamber_set(A, P, N)
                assert V
            if (V, rep) not in seen:
                seen.add((V, rep))
                pairs.append((V, rep, rep))
    return pairs


def run_type(name, out, sample=None, seed=1):
    A = Arrangement(name)
    out.write(f"\n=== {name}: d={A.d}, hyperplanes={A.m}, |W|={len(A.W)}, "
              f"|G|={len(A.G)}, chambers={A.nch}, faces={len(A.faces)}, "
              f"flats={len(A.flats)} ===\n")
    ok = True
    Gcl = classes_in(A.G)
    keyof = {}
    gctx = {}
    inv = {h: inverse(h) for h in A.G}
    for rep, size in Gcl:
        for x in {compose(compose(h, rep), inv[h]) for h in A.G}:
            keyof[x] = rep
        gctx[rep] = GCtx(A, rep)
    stats = {"pairs": 0, "PC_fail": 0, "PC_classes": {}}
    cls_stats, lin_stats = {}, {}
    pairs = []
    if sample is None:
        cones = all_cones(A)
        reps = orbit_reps(A, cones, A.W)
        out.write(f"top-cones={len(cones)}, W-orbits={len(reps)}; pairs = (W-orbit "
                  f"representative V, class of Stab_G(V))\n")
        for V in reps:
            P, N = cone_constraints(A, V)
            for g, _ in classes_in(stabilizer(A, P, N)):
                pairs.append((V, g, keyof[g]))
    else:
        out.write(f"sampled: all chambers and {sample} random g-stable cones per class "
                  f"of G (seed {seed}), plus the witness cones\n")
        pairs = sample_pairs(A, Gcl, sample, seed)
    # witness cones for [S]: a g-fixed chamber of A_X, X minimal in Z*(g) with mu != 0
    nwit = 0
    for rep, _ in Gcl:
        G = gctx[rep]
        nz = [X for X, mu in G.zmu.items() if mu]
        mins = [X for X in nz if not any(Y != X and (Y & X) == X for Y in nz)]
        for X in mins:
            V = witness_cone(A, G, X)
            C = ConeCtx(A, V)
            if C.Lhyp != X or chi_direct(C, rep, G.gd) != G.mu[X]:
                ok = False
                out.write(f"  FAIL [S] witness for {class_label(A, rep)}\n")
            nwit += 1
            pairs.append((V, rep, rep))
    ok &= check_pairs(A, pairs, gctx, out, stats, cls_stats, lin_stats)
    out.write(f"pairs (V, g) checked: {stats['pairs']} (incl. {nwit} witness cones); "
              f"[CF], [Z], [P], [E] and the witnesses hold on all: {ok}\n")
    out.write(f"[PC] pairs where Z*(V, g) carries a nonzero mu but chi_V(g) = 0 "
              f"(cancellation): {stats['PC_fail']}"
              f"{', by class: ' + str(stats['PC_classes']) if stats['PC_fail'] else ''}\n")
    out.write("classes of G:  label | |class| | in W | Springer-regular | pairs | "
              "chi != 0 | chi(all chambers) | [S] predicts | mu(0,X), X in Z*(g) | "
              "dims of those X\n")
    S_ok = SC_ok = CR_ok = I_ok = True
    nCR = nCR0 = 0
    rows = []
    for rep, size in Gcl:
        G = gctx[rep]
        cs = cls_stats.get(rep, {"pairs": 0, "nonzero": 0, "full": None})
        observed = cs["nonzero"] > 0
        if observed != G.crit:
            S_ok = False      # with sampling the witnesses make crit => observed
        if len(G.signs) > 1:
            SC_ok = False
        for X in G.zs:
            nCR += 1
            nCR0 += G.mu[X] == 0
            if (G.mu[X] == 0) != crapo_uncomplemented(A, G, X):
                CR_ok = False
                out.write(f"  [CR] fails at {class_label(A, rep)}, dim X={A.dim(X)}\n")
        if G.gd["order"] == 2 and any(v == 0 for v in G.zmu.values()):
            I_ok = False
        reg = springer_regular(A, rep)
        zv = sorted(G.zmu.values())
        dims = sorted(A.dim(X) for X in G.zs)
        rows.append((A.inW[rep], reg, G.crit))
        out.write(f"  {class_label(A, rep)} | {size} | {int(A.inW[rep])} | {int(reg)} | "
                  f"{cs['pairs']} | {cs['nonzero']} | {cs['full']} | {int(G.crit)} | "
                  f"{zv} | {dims}\n")
    regW = [(r, c) for w, r, c in rows if w]
    out.write(f"[S] 'nonzero on some cone' = [S] prediction on every class: {S_ok}\n")
    out.write(f"[SC] sign coherence on every class: {SC_ok}\n")
    out.write(f"[CR] mu(0,X) = 0 iff [0,X]^g has an uncomplemented element, all "
              f"{nCR} X in Z*(g) ({nCR0} with mu = 0): {CR_ok}\n")
    out.write(f"[I] involutions: mu(0,X) != 0 for every X in Z*(g): {I_ok}\n")
    out.write(f"Springer regularity vs [S] on classes of W: regular & vanishing "
              f"{sum(1 for r, c in regW if r and not c)}, non-regular & nonvanishing "
              f"{sum(1 for r, c in regW if not r and c)}, of {len(regW)}\n")
    out.write("by lineality type (dim L, orbit key of L): pairs | g = 1 | chi != 0 | "
              "zero by Cor. V | zero: Z*(V) carries no nonzero mu | zero by cancellation\n")
    for lab in sorted(lin_stats):
        ls = lin_stats[lab]
        out.write(f"  dimL={lab[0]} key={lab[1]:x}: {ls['pairs']} | {ls['g1']} | "
                  f"{ls['nonzero']} | {ls['corV']} | {ls['empty']} | {ls['other']}\n")
    ok = ok and S_ok and CR_ok and I_ok
    return ok, {"S": S_ok, "SC": SC_ok, "CR": CR_ok, "PC_fail": stats["PC_fail"],
                "pairs": stats["pairs"]}


def mobius_nt(k):
    r, p, x = 1, 2, k
    while p * p <= x:
        if x % p == 0:
            x //= p
            if x % p == 0:
                return 0
            r = -r
        p += 1
    return -r if x > 1 else r


def lcm(a, b):
    from math import gcd
    return a * b // gcd(a, b)


def type_A_rule(ct, neg):
    """+w: all cycles of one length o and mu(o) != 0.  -w (n >= 3): <g> acts
    freely on {+-e_i}, i.e. lcm(2, k) is the same for every cycle length k,
    and mu(o) != 0 for o = ord(-w) = lcm(2, ord w)."""
    if not neg:
        return len(set(ct)) == 1 and mobius_nt(ct[0]) != 0
    ls = {lcm(2, k) for k in ct}
    return len(ls) == 1 and mobius_nt(ls.pop()) != 0


def braid_control(out):
    """[A+] positive control and [A-]: the type-A rule against [S] on the
    arrangements A2-A5 (root-system code)."""
    ok = True
    for name in ["A2", "A3", "A4", "A5"]:
        A = Arrangement(name)
        for rep, _ in classes_in(A.G):
            G = GCtx(A, rep)
            lab = cycle_type_A(A, rep)
            neg = lab.startswith("-")
            ct = [int(c) for c in lab.lstrip("-").strip("()").split(",")]
            if type_A_rule(ct, neg) != G.crit:
                ok = False
                out.write(f"  FAIL type-A rule {name} {lab}\n")
    out.write(f"[A+]/[A-] type-A rule = [S] on every class of +-S_n, A2-A5: {ok}\n")
    return ok


# ---------------------------------------------------------------- type A by set partitions

def set_partitions(items):
    if not items:
        yield []
        return
    f = items[0]
    for p in set_partitions(items[1:]):
        for i in range(len(p)):
            yield p[:i] + [[f] + p[i]] + p[i + 1:]
        yield [[f]] + p


def int_partitions(n, m=None):
    m = n if m is None else m
    if n == 0:
        yield ()
        return
    for k in range(min(n, m), 0, -1):
        for r in int_partitions(n - k, k):
            yield (k,) + r


def typeA_zstar(n, ct, neg):
    """Z*(g) with mu(0, X) for g = +-w on R^n / R1, w of cycle type ct.
    Flats X_pi = functions constant on the blocks of pi; X_pi <= X_rho iff pi is
    coarser than rho; mu_{L^g}(0, X_pi) = mu_{Pi^w}(pi, 1).  Returns a list of
    (dim X, mu)."""
    w, s = [], 0
    for L in ct:
        w += [s + (i + 1) % L for i in range(L)]
        s += L
    eps = -1 if neg else 1
    # Fix(g) inside the sum-zero space: x_{w(i)} = eps x_i, sum x = 0
    eqs = []
    for i in range(n):
        e = [Fraction(0)] * n
        e[w[i]] += 1
        e[i] -= eps
        eqs.append(e)
    eqs.append([Fraction(1)] * n)
    rows = Span(n)
    for e in eqs:
        rows.add(e)
    piv = {p: r for p, r in rows.rows}
    free = [c for c in range(n) if c not in piv]
    U = []
    for f in free:
        v = [Fraction(0)] * n
        v[f] = Fraction(1)
        for p, r in piv.items():
            v[p] = -r[f]
        U.append(v)
    tight = {(i, j) for i in range(n) for j in range(i + 1, n)
             if all(u[i] == u[j] for u in U)}        # hyperplanes x_i = x_j containing Fix g
    canon = lambda p: tuple(sorted(tuple(sorted(b)) for b in p))
    st = [q for q in (canon(p) for p in set_partitions(list(range(n))))
          if canon([[w[i] for i in b] for b in q]) == q]
    st.sort(key=len)
    blk = {q: [set(b) for b in q] for q in st}
    coarser = lambda p, q: all(any(b <= B for B in blk[p]) for b in blk[q])
    mu = {}
    for i, q in enumerate(st):
        mu[q] = 1 if len(q) == 1 else -sum(mu[r] for r in st[:i] if r != q and coarser(r, q))
    out = []
    for q in st:
        Xb = []
        for b in q[1:]:
            v = [Fraction(0)] * n
            for i in b:
                v[i] = Fraction(1)
            for i in q[0]:
                v[i] -= Fraction(len(b), len(q[0]))
            Xb.append(v)
        if rank_of(U + Xb, n) != len(U) + len(Xb):
            continue                                  # X cap Fix g != 0
        if any((i, j) in tight for b in q for i in b for j in b if i < j):
            continue                                  # X + Fix g in a hyperplane
        out.append((len(q) - 1, mu[q]))
    return out


def typeA_partition_check(out, nmax, extra=()):
    ok = True
    cnt = 0
    for n in range(3, nmax + 1):
        for ct in int_partitions(n):
            for neg in (False, True):
                zs = typeA_zstar(n, ct, neg)
                crit = any(m for _, m in zs)
                cnt += 1
                if crit != type_A_rule(ct, neg):
                    ok = False
                    out.write(f"  FAIL type-A rule n={n} {'-' if neg else '+'}{ct}: {zs}\n")
    for n, ct, neg in extra:
        zs = typeA_zstar(n, ct, neg)
        crit = any(m for _, m in zs)
        cnt += 1
        out.write(f"  n={n} {'-' if neg else '+'}{ct}: [S]={int(crit)} rule="
                  f"{int(type_A_rule(ct, neg))} (dim X, mu) = {sorted(set(zs))}\n")
        ok &= crit == type_A_rule(ct, neg)
    out.write(f"[A+]/[A-] type-A rule = [S] by set partitions, all +-w for 3 <= n <= "
              f"{nmax}{' and the listed n = 9 classes' if extra else ''} ({cnt} classes): {ok}\n")
    return ok


def main(argv):
    types = ["A2", "A3", "A4", "A5", "B2", "B3", "B4", "D4", "H3", "F4"]
    nA = 8
    if "--quick" in argv:
        types = ["A2", "A3", "B2", "B3"]
        nA = 6
    if "--types" in argv:
        types = argv[argv.index("--types") + 1].split(",")
    nsamp = 12
    if "--samples" in argv:
        nsamp = int(argv[argv.index("--samples") + 1])
    out = sys.stdout
    allok = True
    summary = []
    for t in types:
        sample = nsamp if t == "F4" else None
        ok, info = run_type(t, out, sample=sample)
        allok &= ok
        summary.append((t, info["pairs"], info["S"], info["SC"], info["CR"], info["PC_fail"]))
        out.flush()
    out.write("\n=== type A: +-w ===\n")
    allok &= braid_control(out)
    extra = ()
    if "--n9" in argv:
        extra = [(9, ct, True) for ct in [(6, 3), (3, 3, 3), (9,), (6, 2, 1), (6, 1, 1, 1)]]
    allok &= typeA_partition_check(out, nA, extra)
    out.write("\nsummary: type | pairs | [S] | [SC] | [CR] | [PC] cancellations\n")
    for row in summary:
        out.write("  " + " | ".join(map(str, row)) + "\n")
    out.write("ALL CHECKS PASSED\n" if allok else "SOME CHECK FAILED\n")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
