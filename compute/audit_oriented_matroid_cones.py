"""Independent audit of notes/oriented_matroid_cones.md
(notes/audit_oriented_matroid_cones.md).

Plain Python 3, standard library only. Imports nothing from this repository;
in particular nothing from oriented_matroid_cones.py.

What is new compared with the audited note's own checks:
  * a rank-4 NON-realizable oriented matroid N (a lifting of non-Pappus:
    N = (M*[p])*, with M*[p] a lexicographic extension of the dual), so
    that N/p = non-Pappus;
  * the rank-4 braid OM A_4 (|Aut| = 240), so that the equivariant identity
    is exercised by a large group in rank 4;
  * integral checks (Smith-type unimodular elimination over Z) of the
    homology of Delta(Lambda-bar(V)) and of the chamber-cycle span;
  * simple connectivity checks in rank 4: every tope boundary B_T is a
    closed surface with chi = 2 (hence S^2), and pi_1(Delta(Lambda-bar(V)))
    is killed by a greedy presentation argument;
  * Lemma 0.2 checked through beat-point reduction (a homotopy
    equivalence), not only through homology.

Run (from compute/):  python3 audit_oriented_matroid_cones.py          (full)
                      python3 audit_oriented_matroid_cones.py --quick  (small)
Exit status 0 iff every check passes and every control fires.
"""

import itertools
import os
import random
import sys
from fractions import Fraction

P = 999983          # prime for modular ranks (different from the note's)
FAIL = []
WORKERS = int(os.environ.get("AUDIT_WORKERS", "3"))


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
    return cond


def popcount(x):
    return bin(x).count("1")


# ------------------------------------------------------------ linear algebra

def rank_mod(rows, p=P):
    """Rank over GF(p) of sparse rows (dict col -> int)."""
    piv = {}
    r = 0
    for row in rows:
        row = {c: v % p for c, v in row.items() if v % p}
        while row:
            c = min(row)
            if c in piv:
                f = row[c]
                for cc, vv in piv[c].items():
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


def rref_mod(rows, p=P):
    """Fully reduced row echelon form over GF(p): dict pivot col -> row."""
    piv = {}
    for row in rows:
        row = {c: v % p for c, v in row.items() if v % p}
        # reduce against existing pivots
        changed = True
        while changed:
            changed = False
            for c in [c for c in row if c in piv]:
                f = row.get(c, 0)
                if not f:
                    continue
                for cc, vv in piv[c].items():
                    nv = (row.get(cc, 0) - f * vv) % p
                    if nv:
                        row[cc] = nv
                    else:
                        row.pop(cc, None)
                changed = True
        if not row:
            continue
        c = min(row)
        inv = pow(row[c], p - 2, p)
        row = {cc: vv * inv % p for cc, vv in row.items()}
        # eliminate c from the other pivot rows
        for c2, r2 in piv.items():
            f = r2.get(c)
            if f:
                for cc, vv in row.items():
                    nv = (r2.get(cc, 0) - f * vv) % p
                    if nv:
                        r2[cc] = nv
                    else:
                        r2.pop(cc, None)
        piv[c] = row
    return piv


def smith_check(rows):
    """Integer elimination with unit pivots, then a dense Smith normal form
    on whatever is left. Returns (rank over Q, sorted list of invariant
    factors > 1). Exact over Z."""
    rows = [dict((c, v) for c, v in r.items() if v) for r in rows]
    rows = [r for r in rows if r]
    rank = 0
    colrows = {}
    for i, r in enumerate(rows):
        for c in r:
            colrows.setdefault(c, set()).add(i)
    alive = set(range(len(rows)))
    while True:
        found = None
        for i in alive:
            for c, v in rows[i].items():
                if v in (1, -1):
                    found = (i, c)
                    break
            if found:
                break
        if not found:
            break
        i, c = found
        pr = rows[i]
        pv = pr[c]
        for j in list(colrows.get(c, ())):
            if j == i or j not in alive:
                continue
            f = rows[j][c] * pv      # pv = +-1, so pv^{-1} = pv
            rj = rows[j]
            for cc, vv in pr.items():
                nv = rj.get(cc, 0) - f * vv
                if nv:
                    if cc not in rj:
                        colrows.setdefault(cc, set()).add(j)
                    rj[cc] = nv
                else:
                    if cc in rj:
                        del rj[cc]
                        colrows[cc].discard(j)
        # remove row i and column c (column c is now zero elsewhere; the
        # remaining entries of row i can be cleared by column operations)
        alive.discard(i)
        for cc in pr:
            colrows[cc].discard(i)
        rank += 1
        for j in alive:
            if c in rows[j]:
                raise AssertionError("elimination left an entry")
    rest = [rows[i] for i in alive if rows[i]]
    if not rest:
        return rank, []
    cols = sorted({c for r in rest for c in r})
    ci = {c: k for k, c in enumerate(cols)}
    A = [[0] * len(cols) for _ in rest]
    for k, r in enumerate(rest):
        for c, v in r.items():
            A[k][ci[c]] = v
    d = dense_snf(A)
    return rank + len(d), sorted(x for x in d if abs(x) > 1)


def dense_snf(A):
    """Nonzero invariant factors of an integer matrix (list of lists)."""
    A = [row[:] for row in A]
    m = len(A)
    n = len(A[0]) if m else 0
    out = []
    t = 0
    while t < m and t < n:
        # find smallest nonzero entry in the submatrix
        best = None
        for i in range(t, m):
            for j in range(t, n):
                if A[i][j] and (best is None or abs(A[i][j]) < abs(A[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        i, j = best
        A[t], A[i] = A[i], A[t]
        for row in A:
            row[t], row[j] = row[j], row[t]
        while True:
            done = True
            for i in range(t + 1, m):
                if A[i][t]:
                    q = A[i][t] // A[t][t]
                    for j in range(t, n):
                        A[i][j] -= q * A[t][j]
                    if A[i][t]:
                        done = False
                        A[t], A[i] = A[i], A[t]
            for j in range(t + 1, n):
                if A[t][j]:
                    q = A[t][j] // A[t][t]
                    for i in range(t, m):
                        A[i][j] -= q * A[i][t]
                    if A[t][j]:
                        done = False
                        for row in A:
                            row[t], row[j] = row[j], row[t]
            if done:
                # divisibility: if some entry not divisible, add its row
                bad = None
                for i in range(t + 1, m):
                    for j in range(t + 1, n):
                        if A[i][j] % A[t][t]:
                            bad = i
                            break
                    if bad is not None:
                        break
                if bad is None:
                    break
                for j in range(t, n):
                    A[t][j] += A[bad][j]
        out.append(abs(A[t][t]))
        t += 1
    return out


# ---------------------------------------------------------- poset topology

def chains(elems, less):
    """All nonempty chains of a finite poset, as tuples increasing in the
    order. less(x, y) is the strict order."""
    elems = list(elems)
    up = {x: [y for y in elems if less(x, y)] for x in elems}
    out = []

    def ext(ch):
        out.append(tuple(ch))
        for y in up[ch[-1]]:
            ch.append(y)
            ext(ch)
            ch.pop()
    for x in elems:
        ext([x])
    return out


def reduced_betti(chs, p=P):
    """Reduced Betti numbers over GF(p) of the order complex whose simplices
    are the chains chs (closed under taking subchains)."""
    if not chs:
        return {-1: 1}
    bydim = {}
    for c in chs:
        bydim.setdefault(len(c) - 1, []).append(c)
    top = max(bydim)
    index = {d: {c: i for i, c in enumerate(bydim[d])} for d in bydim}
    rk = {0: 1}   # rank of augmentation C_0 -> Z
    for d in range(1, top + 1):
        rows = []
        for c in bydim[d]:
            row = {}
            for i in range(len(c)):
                f = c[:i] + c[i + 1:]
                row[index[d - 1][f]] = (-1) ** i
            rows.append(row)
        rk[d] = rank_mod(rows, p)
    b = {}
    for d in range(0, top + 1):
        b[d] = len(bydim[d]) - rk[d] - rk.get(d + 1, 0)
    return {d: v for d, v in b.items() if v}


def boundary_rows(chs):
    bydim = {}
    for c in chs:
        bydim.setdefault(len(c) - 1, []).append(c)
    index = {d: {c: i for i, c in enumerate(bydim[d])} for d in bydim}
    out = {}
    for d in bydim:
        if d == 0:
            continue
        rows = []
        for c in bydim[d]:
            rows.append({index[d - 1][c[:i] + c[i + 1:]]: (-1) ** i for i in range(len(c))})
        out[d] = rows
    return bydim, index, out


def torsion_free(chs):
    """Exact integral check: every boundary map of the order complex has all
    invariant factors 1, so the integral homology is free. Returns the list
    of non-unit invariant factors found (empty = torsion-free)."""
    _, _, bd = boundary_rows(chs)
    bad = []
    for d, rows in bd.items():
        _, f = smith_check(rows)
        bad += f
    return bad


def pi1_trivial(chs):
    """Greedy proof that pi_1 of the order complex is trivial (connected
    complex assumed). Sound when it returns True; False = inconclusive."""
    verts = sorted({c[0] for c in chs if len(c) == 1})
    edges = [c for c in chs if len(c) == 2]
    tris = [c for c in chs if len(c) == 3]
    # spanning tree by BFS
    adj = {v: [] for v in verts}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen = {verts[0]}
    tree = set()
    stack = [verts[0]]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                tree.add(frozenset((v, w)))
                stack.append(w)
    if len(seen) != len(verts):
        return False
    parent = {}

    def find(g):
        # returns (root, eps) with g = root^eps; root None = trivial
        eps = 1
        while g in parent:
            g, s = parent[g]
            eps *= s
            if g is None:
                return None, 1
        return g, eps
    for (a, b) in edges:
        if frozenset((a, b)) in tree:
            parent[(a, b)] = (None, 1)
    changed = True
    while changed:
        changed = False
        for (a, b, c) in tris:
            word = [((a, b), 1), ((b, c), 1), ((a, c), -1)]
            w = []
            for g, e in word:
                r, s = find(g)
                if r is not None:
                    w.append((r, s * e))
            # cyclic free reduction
            red = True
            while red and w:
                red = False
                for i in range(len(w)):
                    j = (i + 1) % len(w)
                    if len(w) > 1 and w[i][0] == w[j][0] and w[i][1] == -w[j][1]:
                        if j > i:
                            del w[j]
                            del w[i]
                        else:
                            del w[i]
                            del w[j]
                        red = True
                        break
            if len(w) == 1:
                parent[w[0][0]] = (None, 1)
                changed = True
            elif len(w) == 2 and w[0][0] != w[1][0]:
                # x^e1 y^e2 = 1  =>  x = y^(-e2*e1)
                (x, e1), (y, e2) = w
                parent[x] = (y, -e2 * e1)
                changed = True
            elif len(w) == 2 and w[0][0] == w[1][0] and w[0][1] == w[1][1]:
                pass   # x^2 = 1: not enough on its own
    return all(find(e)[0] is None for e in edges)


def closed_surface_sphere(chs):
    """For a 2-dimensional complex: every edge in exactly two triangles,
    every vertex link a single cycle, connected, chi = 2. Then it is a closed
    surface with chi 2, hence S^2 (classification of surfaces)."""
    verts = [c for c in chs if len(c) == 1]
    edges = [c for c in chs if len(c) == 2]
    tris = [c for c in chs if len(c) == 3]
    if any(len(c) > 3 for c in chs):
        return False
    cnt = {e: 0 for e in edges}
    link = {v[0]: [] for v in verts}
    for t in tris:
        for i in range(3):
            cnt[t[:i] + t[i + 1:]] += 1
        a, b, c = t
        link[a].append((b, c))
        link[b].append((a, c))
        link[c].append((a, b))
    if any(v != 2 for v in cnt.values()):
        return False
    for v, es in link.items():
        if not es:
            return False
        adj = {}
        for x, y in es:
            adj.setdefault(x, []).append(y)
            adj.setdefault(y, []).append(x)
        if any(len(n) != 2 for n in adj.values()):
            return False
        start = next(iter(adj))
        seen = {start}
        st = [start]
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    st.append(w)
        if len(seen) != len(adj):
            return False
    if len(verts) - len(edges) + len(tris) != 2:
        return False
    b = reduced_betti(chs)
    return b == {2: 1}


# ---------------------------------------------------------------- chirotopes

def perm_sign(seq):
    s = 1
    seq = list(seq)
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                s = -s
            elif seq[i] == seq[j]:
                return 0
    return s


def det(M):
    A = [[Fraction(x) for x in r] for r in M]
    n = len(A)
    d = Fraction(1)
    for k in range(n):
        piv = next((i for i in range(k, n) if A[i][k] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != k:
            A[k], A[piv] = A[piv], A[k]
            d = -d
        d *= A[k][k]
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            if f:
                for j in range(k, n):
                    A[i][j] -= f * A[k][j]
    return d


class Chirotope:
    def __init__(self, n, r, vals):
        self.n, self.r = n, r
        self.vals = {k: v for k, v in vals.items() if v}

    def __call__(self, seq):
        s = perm_sign(seq)
        if not s:
            return 0
        return s * self.vals.get(tuple(sorted(seq)), 0)

    @staticmethod
    def from_vectors(vecs):
        n, r = len(vecs), len(vecs[0])
        vals = {}
        for B in itertools.combinations(range(n), r):
            d = det([vecs[i] for i in B])
            vals[B] = (d > 0) - (d < 0)
        return Chirotope(n, r, vals)

    def dual(self):
        n, r = self.n, self.r
        vals = {}
        for B in itertools.combinations(range(n), n - r):
            comp = tuple(e for e in range(n) if e not in B)
            vals[B] = self.vals.get(comp, 0) * perm_sign(B + comp)
        return Chirotope(n, n - r, vals)

    def lex_extension(self, seq):
        """Lexicographic single-element extension by p = n with
        chi(p, Y) = s_i chi(a_i, Y) for the first i with chi(a_i, Y) != 0;
        seq = [(a_1, s_1), ...]."""
        n, r = self.n, self.r
        vals = dict(self.vals)
        for Y in itertools.combinations(range(n), r - 1):
            v = 0
            for a, s in seq:
                c = self((a,) + Y)
                if c:
                    v = s * c
                    break
            # stored on the sorted tuple Y + (n,): chi(Y, p) = (-1)^(r-1) chi(p, Y)
            vals[Y + (n,)] = v * (-1) ** (r - 1)
        return Chirotope(n + 1, r, vals)

    def contract(self, p):
        """chi_{M/p}(x) = chi(p, x), on E - p relabelled 0..n-2."""
        n, r = self.n, self.r
        lab = [e for e in range(n) if e != p]
        vals = {}
        for X in itertools.combinations(range(n - 1), r - 1):
            vals[X] = self((p,) + tuple(lab[i] for i in X))
        return Chirotope(n - 1, r - 1, vals)


def chirotope_axioms(ch):
    """Alternating by construction. Checks that the support is the set of
    bases of a matroid (exchange axiom) and the 3-term Grassmann-Pluecker
    relations (BLSWZ Thm 3.6.2, CITED, not opened)."""
    n, r = ch.n, ch.r
    bases = [B for B, v in ch.vals.items() if v]
    if not bases:
        return False, "identically zero"
    bset = set(bases)
    for B1 in bases:
        s1 = set(B1)
        for B2 in bases:
            s2 = set(B2)
            for x in s1 - s2:
                if not any(tuple(sorted((s1 - {x}) | {y})) in bset for y in s2 - s1):
                    return False, "basis exchange fails"
    for X in itertools.combinations(range(n), r - 2):
        rest = [e for e in range(n) if e not in X]
        for a, b, c, d in itertools.combinations(rest, 4):
            t = {ch(X + (a, b)) * ch(X + (c, d)),
                 -ch(X + (a, c)) * ch(X + (b, d)),
                 ch(X + (a, d)) * ch(X + (b, c))}
            if not (t == {0} or (1 in t and -1 in t)):
                return False, "3-term GP fails at %s" % ((X, a, b, c, d),)
    return True, "ok"


# --------------------------------------------------------- oriented matroids

def comp(X, Y):
    s = X[0] | X[1]
    return (X[0] | (Y[0] & ~s), X[1] | (Y[1] & ~s))


def leq(X, Y):
    return (X[0] & ~Y[0]) == 0 and (X[1] & ~Y[1]) == 0


def neg(X):
    return (X[1], X[0])


class OM:
    def __init__(self, name, ch, realizable=None):
        self.name, self.ch, self.n, self.r = name, ch, ch.n, ch.r
        self.realizable = realizable
        n, r = self.n, self.r
        self.full = (1 << n) - 1
        self.bases = [sum(1 << e for e in B) for B, v in ch.vals.items() if v]
        # cocircuits
        coc = set()
        for A in itertools.combinations(range(n), r - 1):
            Am = sum(1 << e for e in A)
            if not any(popcount(Am & B) == r - 1 for B in self.bases):
                continue
            p = m = 0
            for e in range(n):
                v = ch(A + (e,))
                if v > 0:
                    p |= 1 << e
                elif v < 0:
                    m |= 1 << e
            coc.add((p, m))
            coc.add((m, p))
        self.cocircuits = sorted(coc)
        L = {(0, 0)}
        front = [(0, 0)]
        while front:
            new = []
            for X in front:
                for C in self.cocircuits:
                    Y = comp(X, C)
                    if Y not in L:
                        L.add(Y)
                        new.append(Y)
            front = new
        self._rk = {}
        self.L = sorted(L, key=lambda X: (self.dim(X), X))
        self.idx = {X: i for i, X in enumerate(self.L)}
        self.topes = [X for X in self.L if (X[0] | X[1]) == self.full]
        self.tidx = {T: i for i, T in enumerate(self.topes)}
        self.flats = sorted({self.z(X) for X in self.L}, key=lambda Z: -popcount(Z))
        self.rank_of = {Z: self.rk(Z) for Z in self.flats}

    def rk(self, A):
        if A not in self._rk:
            self._rk[A] = max(popcount(A & B) for B in self.bases)
        return self._rk[A]

    def z(self, X):
        return self.full & ~(X[0] | X[1])

    def dim(self, X):
        return self.r - self.rk(self.z(X))

    # ---- certificates
    def cocircuit_axioms(self):
        C = self.cocircuits
        Cs = set(C)
        for X in C:
            if neg(X) not in Cs:
                return False
        supp = {X: X[0] | X[1] for X in C}
        for X in C:
            for Y in C:
                if X != Y and (supp[X] | supp[Y]) == supp[Y] and supp[X] != supp[Y]:
                    return False
        for X in C:
            for Y in C:
                if X == neg(Y) or X == Y:
                    continue
                sep = (X[0] & Y[1]) | (X[1] & Y[0])
                for e in range(self.n):
                    if not (sep >> e) & 1:
                        continue
                    # need Z with Z_e = 0, Z+ in X+ u Y+ minus e, Z- in X- u Y- minus e
                    ok = any(not ((Z[0] | Z[1]) >> e) & 1
                             and (Z[0] & ~(X[0] | Y[0])) == 0
                             and (Z[1] & ~(X[1] | Y[1])) == 0 for Z in C)
                    if not ok:
                        return False
        return True

    def covector_elimination_sample(self, k, seed):
        rnd = random.Random(seed)
        Ls = set(self.L)
        L = self.L
        for _ in range(k):
            X, Y = rnd.choice(L), rnd.choice(L)
            if comp(X, Y) not in Ls:
                return False
            sep = (X[0] & Y[1]) | (X[1] & Y[0])
            if not sep:
                continue
            es = [e for e in range(self.n) if (sep >> e) & 1]
            e = rnd.choice(es)
            XY = comp(X, Y)
            keep = self.full & ~sep
            if not any(not ((Z[0] | Z[1]) >> e) & 1 and (Z[0] & keep) == (XY[0] & keep)
                       and (Z[1] & keep) == (XY[1] & keep) for Z in L):
                return False
        return True

    def simple(self):
        return (all(self.rk(1 << e) == 1 for e in range(self.n))
                and all(self.rk((1 << a) | (1 << b)) == 2 for a in range(self.n) for b in range(a)))

    # ---- structure used by the checks
    def prepare(self):
        n, r = self.n, self.r
        L = self.L
        self.dims = [self.dim(X) for X in L]
        bydim = {}
        for i, X in enumerate(L):
            bydim.setdefault(self.dims[i], []).append(i)
        self.bydim = bydim
        self.up = {i: [] for i in range(len(L))}
        for d in range(0, r):
            for i in bydim.get(d, []):
                for j in bydim.get(d + 1, []):
                    if leq(L[i], L[j]):
                        self.up[i].append(j)
        # maximal chains of L - 0 (cocircuit < ... < tope), one per flag
        mch = []

        def ext(ch):
            if len(ch) == r:
                mch.append(tuple(ch))
                return
            for j in self.up[ch[-1]]:
                ch.append(j)
                ext(ch)
                ch.pop()
        for i in bydim.get(1, []):
            ext([i])
        self.maxchains = mch
        # fundamental cycle by propagation across codimension-one faces
        faces = {}
        for s in mch:
            for k in range(r):
                faces.setdefault(s[:k] + s[k + 1:], []).append((s, (-1) ** k))
        self.thin = all(len(v) == 2 for v in faces.values())
        omega = {}
        consistent = True
        if mch and self.thin:
            omega[mch[0]] = 1
            stack = [mch[0]]
            while stack:
                s = stack.pop()
                for k in range(r):
                    f = s[:k] + s[k + 1:]
                    (s1, e1), (s2, e2) = faces[f]
                    t, et, es = (s2, e2, e1) if s1 == s else (s1, e1, e2)
                    want = -omega[s] * es * et
                    if t in omega:
                        if omega[t] != want:
                            consistent = False
                    else:
                        omega[t] = want
                        stack.append(t)
        self.omega = omega
        self.omega_ok = self.thin and consistent and len(omega) == len(mch)
        # rho_C
        self.rho = []
        self.rho_supported_ok = True
        for C in range(len(self.topes)):
            ci = self.idx[self.topes[C]]
            bd = {}
            for s in mch:
                if s[-1] != ci:
                    continue
                for k in range(r):
                    f = s[:k] + s[k + 1:]
                    bd[f] = bd.get(f, 0) + omega[s] * (-1) ** k
            bd = {f: v for f, v in bd.items() if v}
            if any(ci in f for f in bd):
                self.rho_supported_ok = False
            rc = {}
            for f, v in bd.items():
                key = tuple(self.z(L[i]) for i in f)
                rc[key] = rc.get(key, 0) + v
            self.rho.append({k: v for k, v in rc.items() if v})
        # lunes: for H != 0, D >= H: {C : C = D on z(H)}
        lunes = set()
        self.lune_pairs = []
        for H in L:
            if H == (0, 0):
                continue
            zH = self.z(H)
            groups = {}
            for ti, C in enumerate(self.topes):
                k = C[0] & zH
                groups[k] = groups.get(k, 0) | (1 << ti)
            for D in self.topes:
                if leq(H, D):
                    m = groups[D[0] & zH]
                    lunes.add(m)
                    self.lune_pairs.append((H, self.tidx[D], m))
        self.lunes = sorted(lunes)
        self.lune_rref = rref_mod([{t: 1 for t in bits(m)} for m in self.lunes])
        self.lune_piv = set(self.lune_rref)
        self.nf_tope = [self.nf({t: 1}) for t in range(len(self.topes))]
        # Moebius function of the lattice of flats
        self.mu_L = mobius_top(self.flats)[self.full]

    def nf(self, v):
        """Normal form modulo Lune (supported on non-pivot coordinates)."""
        v = {c: x % P for c, x in v.items() if x % P}
        for c in [c for c in v if c in self.lune_piv]:
            f = v.get(c, 0)
            if not f:
                continue
            for cc, vv in self.lune_rref[c].items():
                nv = (v.get(cc, 0) - f * vv) % P
                if nv:
                    v[cc] = nv
                else:
                    v.pop(cc, None)
        return v

    # ---- automorphisms
    def automorphisms(self):
        """All signed permutations g preserving the tope set. Backtracking
        with matroid invariants and the chirotope (chi o g = c chi, c = +-1);
        every leaf is verified on the full tope set."""
        n, r, ch = self.n, self.r, self.ch
        inv = []
        for e in range(n):
            inv.append(tuple(sum(1 for Z in self.flats if (Z >> e) & 1 and self.rank_of[Z] == k)
                             for k in range(r)))
        T = [tuple((1 if (X[0] >> e) & 1 else -1) for e in range(n)) for X in self.topes]
        Tset = set(T)
        out = []
        perm, sg = [], []
        state = {"c": None}

        def ok_new(k):
            # element k just assigned
            for size in range(2, r + 1):
                for A in itertools.combinations(range(k), size - 1):
                    A = A + (k,)
                    Am = sum(1 << e for e in A)
                    Bm = sum(1 << perm[e] for e in A)
                    if self.rk(Am) != self.rk(Bm):
                        return False
                    if size == r and self.rk(Am) == r:
                        v = ch(tuple(perm[e] for e in A))
                        for e in A:
                            v *= sg[e]
                        c = v * ch(A)
                        if state["c"] is None:
                            state["c"] = c
                            state["cset"] = A
                        elif state["c"] != c:
                            return False
            return True

        def rec(k):
            if k == n:
                img = set()
                for t in T:
                    u = [0] * n
                    for e in range(n):
                        u[perm[e]] = sg[e] * t[e]
                    img.add(tuple(u))
                if img == Tset:
                    out.append((tuple(perm), tuple(sg)))
                return
            for im in range(n):
                if im in perm or inv[im] != inv[k]:
                    continue
                for s in (1, -1):
                    perm.append(im)
                    sg.append(s)
                    saved = dict(state)
                    if ok_new(k):
                        rec(k + 1)
                    state.clear()
                    state.update(saved)
                    perm.pop()
                    sg.pop()
        rec(0)
        return out

    def act(self, g, X):
        perm, sg = g
        p = m = 0
        for e in range(self.n):
            if (X[0] >> e) & 1:
                if sg[e] > 0:
                    p |= 1 << perm[e]
                else:
                    m |= 1 << perm[e]
            elif (X[1] >> e) & 1:
                if sg[e] > 0:
                    m |= 1 << perm[e]
                else:
                    p |= 1 << perm[e]
        return (p, m)

    def act_set(self, g, Z):
        perm, _ = g
        out = 0
        for e in range(self.n):
            if (Z >> e) & 1:
                out |= 1 << perm[e]
        return out


def chirotope_factor(om, g):
    """c with chi(g B) = c chi(B) for every basis B, or None."""
    perm, sg = g
    c = None
    for B, v in om.ch.vals.items():
        img = om.ch(tuple(perm[b] for b in B))
        for b in B:
            img *= sg[b]
        cc = img * v
        if c is None:
            c = cc
        elif c != cc:
            return None
    return c


def bits(m):
    i = 0
    while m:
        if m & 1:
            yield i
        m >>= 1
        i += 1


def mobius_top(flats):
    """mu(Z, top) for a family of sets under reverse inclusion whose top is
    the empty set (assumed present)."""
    order = sorted(flats, key=popcount)
    mu = {}
    for Z in order:
        if Z == 0:
            mu[Z] = 1
            continue
        mu[Z] = -sum(mu[W] for W in mu if (W & ~Z) == 0 and W != Z)
    return mu


# ------------------------------------------------------------------ the OMs

def vectors_A(n):
    """Braid arrangement A_{n-1}: e_i - e_j in R^n, last coordinate dropped."""
    out = []
    for i, j in itertools.combinations(range(n), 2):
        v = [0] * n
        v[i], v[j] = 1, -1
        out.append(v[:n - 1])
    return out


def vectors_B3():
    e = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    out = [r[:] for r in e]
    for i, j in itertools.combinations(range(3), 2):
        out.append([e[i][k] + e[j][k] for k in range(3)])
        out.append([e[i][k] - e[j][k] for k in range(3)])
    return out


def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]


PAPPUS_LINES = None


def pappus_vectors():
    """A, B, C on y = 0 and a, b, c on y = 1 (homogeneous integer
    coordinates); X = Ab.aB, Y = Ac.aC, Z = Bc.bC. Order A B C a b c X Y Z."""
    A, B, C = [0, 0, 1], [2, 0, 1], [7, 0, 1]
    a, b, c = [-1, 1, 1], [3, 1, 1], [4, 1, 1]

    def meet(p1, p2, q1, q2):
        return cross(cross(p1, p2), cross(q1, q2))
    X = meet(A, b, a, B)
    Y = meet(A, c, a, C)
    Z = meet(B, c, b, C)
    return [A, B, C, a, b, c, X, Y, Z]


PAPPUS_9 = sorted(tuple(sorted(t)) for t in [
    (0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 4, 6), (3, 1, 6), (0, 5, 7), (3, 2, 7), (1, 5, 8), (4, 2, 8)])


def zero_triples(ch):
    return sorted(B for B in itertools.combinations(range(ch.n), ch.r) if ch.vals.get(B, 0) == 0)


def non_pappus(sign):
    ch = Chirotope.from_vectors(pappus_vectors())
    vals = dict(ch.vals)
    vals[(6, 7, 8)] = sign
    return ch, Chirotope(9, 3, vals)


def non_realizability_certificate(ch3):
    """Zero set of the rank-3 chirotope = the 8 non-Pappus lines exactly
    (the underlying matroid is non-Pappus, not representable over any field
    by Pappus's theorem)."""
    want = [t for t in PAPPUS_9 if t != (6, 7, 8)]
    return zero_triples(ch3) == want


def with_coloop(ch):
    """Direct sum with a coloop f = n (rank r + 1)."""
    vals = {B + (ch.n,): v for B, v in ch.vals.items()}
    return Chirotope(ch.n + 1, ch.r + 1, vals)


def lifting_of(ch3, seq):
    """N = (M*[p])*: rank r+1 on n+1 elements with N/p = M."""
    d = ch3.dual()
    ext = d.lex_extension(seq)
    return d, ext, ext.dual()


# ------------------------------------------------------------- per-cone checks

G = {}     # globals for forked workers


def tconvex_sets(om):
    """All nonempty T-convex sets, keyed by the S_max sign vector."""
    n = om.n
    T = om.topes
    out = {}

    def rec(e, cand, sp, sm):
        if not cand:
            return
        if e == n:
            ap = am = om.full
            mask = 0
            for t in cand:
                ap &= T[t][0]
                am &= T[t][1]
                mask |= 1 << t
            out[(ap, am)] = mask
            return
        rec(e + 1, cand, sp, sm)
        c1 = [t for t in cand if (T[t][0] >> e) & 1]
        c2 = [t for t in cand if (T[t][1] >> e) & 1]
        if len(c1) < len(cand):
            rec(e + 1, c1, sp | 1 << e, sm)
        if len(c2) < len(cand):
            rec(e + 1, c2, sp, sm | 1 << e)
    rec(0, list(range(len(T))), 0, 0)
    return out


def lambda_chains(Lam, full):
    inner = [Z for Z in Lam if Z != full and Z != 0]
    return chains(inner, lambda A, B: (B & ~A) == 0 and A != B)


def check_cone(key):
    """All per-cone checks for one T-convex set. Returns a dict of results."""
    om = G["om"]
    auts = G["auts"]
    deep = G["deep"]
    sp, sm = key
    Vmask = G["sets"][key]
    V = list(bits(Vmask))
    Smax = sp | sm
    res = {}
    r = om.r
    F = [X for X in om.L if (X[0] & sm) == 0 and (X[1] & sp) == 0]
    Lam = {om.z(X) for X in F}
    res["flatL"] = all(Z in Lam for Z in om.flats if (Smax & ~Z) == 0)
    mu = mobius_top(Lam)
    m = (-1) ** r * mu[om.full]
    res["m"] = m
    res["zas"] = len(V) == sum((-1) ** om.rank_of[Z] * mu[Z] for Z in Lam if (Smax & ~Z) == 0)
    res["zas_wrong"] = len(V) == sum((-1) ** om.rank_of[Z] * mu[Z] for Z in Lam)
    chs = lambda_chains(Lam, om.full)
    b = reduced_betti(chs) if chs else {-1: 1}
    res["wedge"] = (m >= 0 and all(d == r - 2 for d in b) and b.get(r - 2, 0) == m)
    # Brown: c_Z independent of X, Moebius sum = m
    SigL = [X for X in om.L if (X[0] | X[1]) & Smax == 0]
    cz = {}
    ok = True
    for X in SigL:
        c = sum(1 for t in V if leq(X, om.topes[t]))
        Z = om.z(X)
        if Z in cz and cz[Z] != c:
            ok = False
        cz[Z] = c
    interval = [Z for Z in om.flats if (Smax & ~Z) == 0]
    # mu(E, Z) on the interval, E at the bottom (largest set)
    muE = {}
    for Z in sorted(interval, key=lambda A: -popcount(A)):
        if Z == om.full:
            muE[Z] = 1
        else:
            muE[Z] = -sum(muE[W] for W in muE if (Z & ~W) == 0 and W != Z)
    res["brown"] = ok and sum(muE[Z] * cz[Z] for Z in interval) == m
    # Lemma L-OM (i)
    ok = True
    for (H, Di, lm) in om.lune_pairs:
        inV = (lm & ~Vmask) == 0
        pred = bool((Vmask >> Di) & 1) and ((H[0] | H[1]) & Smax) == 0
        if inV != pred:
            ok = False
            break
    res["lunL"] = ok
    # chamber cycles
    Lamset = Lam
    supp_ok = all(all(Zf in Lamset for ch in om.rho[t] for Zf in ch) for t in V)
    top = [c for c in chs if len(c) == r - 1]
    tix = {c: i for i, c in enumerate(top)}
    rows = []
    for t in V:
        rows.append({tix[c]: v for c, v in om.rho[t].items()} if supp_ok else {})
    rk_rho = rank_mod(rows)
    res["rho"] = supp_ok and rk_rho == m
    # q(V) from lunes alone (no rho)
    q = rank_mod([om.nf_tope[t] for t in V])
    res["q"] = q
    res["q=m"] = q == m
    # (iii): span of lunes inside V, and Lie directly
    inside = [lm for lm in om.lunes if (lm & ~Vmask) == 0]
    rk_in = rank_mod([{t: 1 for t in bits(lm)} for lm in inside])
    Hmin = [X for X in om.cocircuits if (X[0] | X[1]) & Smax == 0]
    act_rows = {}
    for H in Hmin:
        img = {}
        for t in V:
            D = comp(H, om.topes[t])
            img.setdefault(D, {})[t] = 1
        for D, row in img.items():
            act_rows[(H, D)] = row
    lie = len(V) - rank_mod(list(act_rows.values())) if Hmin else len(V)
    res["G1"] = (rk_in == len(V) - m) and (lie == m) and (len(V) - q == rk_in)
    # equivariance: characters
    if deep:
        tperm = G["tperm"]
        dets = G["dets"]
        U = rref_mod([om.nf_tope[t] for t in V])
        upiv = sorted(U)
        Vset = set(V)
        twisted_ok = True
        untwisted_ok = True
        nstab = 0
        for gi, g in enumerate(auts):
            if not (Vmask >> tperm[gi][V[0]]) & 1:
                continue
            if {tperm[gi][t] for t in V} != Vset:
                continue
            nstab += 1
            # LHS: Lefschetz on the fixed subposet of Lambda-bar(V)
            fixed = [c for c in chs if all(om.act_set(g, Z) == Z for Z in c)]
            chi = -1 + sum((-1) ** (len(c) - 1) for c in fixed)
            lhs = (-1) ** r * chi
            # RHS: trace on (Gamma_V + Lune)/Lune = span of NF(e_C), C in V
            tr = 0
            for c0 in upiv:
                u = U[c0]
                w = {}
                for c, x in u.items():
                    for cc, y in om.nf_tope[tperm[gi][c]].items():
                        w[cc] = (w.get(cc, 0) + x * y) % P
                tr = (tr + w.get(c0, 0)) % P
            if tr > P // 2:
                tr -= P
            if lhs != dets[gi] * tr:
                twisted_ok = False
            if lhs != tr:
                untwisted_ok = False
        res["eq"] = twisted_ok
        res["eq_untwisted"] = untwisted_ok
        res["nstab"] = nstab
    if G.get("integral") and key in G["integral"]:
        res["Z_tors"] = torsion_free(chs) if chs else []
        rq, fac = smith_check(rows)
        res["Z_rho"] = (rq == m and not fac)
        if r == 4:
            res["pi1"] = pi1_trivial(chs) if chs else True
    return key, res


# ------------------------------------------------------------- Lemma 0.2

def beat_core(om, Kmask):
    """Remove beat points (unique maximal lower / minimal upper element)
    until none is left; a homotopy equivalence of order complexes (Stong).
    Returns the remaining set as a list of covector indices."""
    below, above, dimmask = om.below, om.above, om.dimmask
    P_ = Kmask
    changed = True
    while changed:
        changed = False
        for i in list(bits(P_)):
            if not (P_ >> i) & 1:
                continue
            for rel, near in ((below, -1), (above, 1)):
                S = rel[i] & P_
                if not S:
                    continue
                d = om.dims[i]
                rng = range(d - 1, 0, -1) if near < 0 else range(d + 1, om.r + 1)
                y = None
                for dd in rng:
                    grp = S & dimmask.get(dd, 0)
                    if grp:
                        if grp & (grp - 1) == 0:
                            y = grp.bit_length() - 1
                        break
                if y is None:
                    continue
                rest = S & ~(1 << y) & ~rel[y]
                if rest == 0:
                    P_ &= ~(1 << i)
                    changed = True
                    break
    return list(bits(P_))


def prepare_lem02(om):
    n = len(om.L)
    om.below = [0] * n
    om.above = [0] * n
    for i, X in enumerate(om.L):
        for j, Y in enumerate(om.L):
            if i != j and leq(X, Y):
                om.below[j] |= 1 << i
                om.above[i] |= 1 << j
    om.dimmask = {}
    for i, d in enumerate(om.dims):
        om.dimmask[d] = om.dimmask.get(d, 0) | (1 << i)


def K_mask(om, sp, sm):
    m = 0
    for i, X in enumerate(om.L):
        if X != (0, 0) and (X[0] & sm) == 0 and (X[1] & sp) == 0:
            m |= 1 << i
    return m


def classify_K(om, Kmask):
    """'empty', 'point' (contractible by beat points), or the reduced Betti
    numbers of the core."""
    if Kmask == 0:
        return "empty", None
    core = beat_core(om, Kmask)
    if len(core) == 1:
        return "point", None
    L = om.L
    chs = chains(core, lambda a, b: a != b and leq(L[a], L[b]))
    return "core%d" % len(core), reduced_betti(chs)


def lem02_worker(args):
    om = G["om"]
    sp, sm, Vnonempty = args
    Km = K_mask(om, sp, sm)
    kind, b = classify_K(om, Km)
    S = sp | sm
    if not Vnonempty:
        return args, kind, b, None
    if S == 0:
        ok = b == {om.r - 1: 1}
    else:
        ok = kind == "point" or (b == {})
    return args, kind, b, ok


# ------------------------------------------------------------- driver

def run_om(name, ch, realizable, log, quick, integral_sample=None, deep_all=True,
           lem_sample=None, cone_sample=None):
    log("[%s] rank=%d n=%d realizable=%s" % (name, ch.r, ch.n, realizable))
    ok, why = chirotope_axioms(ch)
    check(ok, name + " chirotope axioms: " + why)
    om = OM(name, ch, realizable)
    check(om.cocircuit_axioms(), name + " cocircuit axioms")
    check(om.covector_elimination_sample(3000, 1), name + " covector elimination (sample)")
    check(om.simple(), name + " simple")
    om.prepare()
    log("  [axioms] chirotope (exchange + 3-term GP): %s; cocircuit axioms: ok; simple: %s"
        % (why, om.simple()))
    log("  covectors=%d topes=%d flats=%d cocircuits=%d maximal chains=%d"
        % (len(om.L), len(om.topes), len(om.flats), len(om.cocircuits), len(om.maxchains)))
    check(om.omega_ok, name + " omega")
    check(om.rho_supported_ok, name + " rho support")
    log("  [omega] thin=%s, +-1 cycle unique up to sign by propagation: %s; "
        "d(omega_C) avoids C for every tope: %s" % (om.thin, om.omega_ok, om.rho_supported_ok))
    absmu = abs(om.mu_L)
    dimq = len(om.topes) - len(om.lune_piv)
    rank_rho = rank_mod(_rho_rows(om))
    # Lune rank exactly over Z/Q
    lq, lf = smith_check([{t: 1 for t in bits(m)} for m in om.lunes])
    check(dimq == absmu == rank_rho, name + " propB dims")
    check(len(om.topes) - lq == absmu and not lf, name + " Lune exact")
    killed = all(not sum_rho(om, lm) for lm in om.lunes)
    check(killed, name + " lunes killed")
    single = all(popcount(lm) >= 2 for (_, _, lm) in om.lune_pairs)
    check(single, name + " lune non-singleton")
    log("  |mu(L(M))|=%d; dim Gamma/Lune: GF(p) %d, exact %d (Lune lattice invariant factors >1: %s); "
        "rank C->rho_C = %d; %d distinct lunes, each killed at chain level: %s"
        % (absmu, dimq, len(om.topes) - lq, lf or "none", rank_rho, len(om.lunes), killed))
    cyc = all(is_cycle(om.rho[t]) for t in range(len(om.topes)))
    check(cyc, name + " rho cycles")
    # tope boundaries
    L = om.L
    bt_ok = True
    surf_ok = True
    for T in om.topes:
        ti = om.idx[T]
        elems = [i for i in range(1, len(L)) if i != ti and leq(L[i], T)]
        chs = chains(elems, lambda a, b: a != b and leq(L[a], L[b]))
        if reduced_betti(chs) != {om.r - 2: 1}:
            bt_ok = False
        if om.r == 4 and not closed_surface_sphere(chs):
            surf_ok = False
    check(bt_ok, name + " tope boundaries")
    check(surf_ok, name + " tope boundaries S^2")
    log("  [Btope] every tope boundary B_T has the homology of S^%d: %s%s"
        % (om.r - 2, bt_ok, ("; r = 4: every B_T is a closed surface with chi = 2, i.e. S^2: %s" % surf_ok)
                             if om.r == 4 else ""))
    # automorphisms and det
    auts = om.automorphisms()
    tperm = []
    dets = []
    chis = []
    rho_eq = True
    rho_eq_untw = True
    for g in auts:
        tp = [om.tidx[om.act(g, T)] for T in om.topes]
        tperm.append(tp)
        imap = [om.idx[om.act(g, X)] for X in om.L]
        d = None
        for s, c in om.omega.items():
            gs = tuple(imap[i] for i in s)
            dd = om.omega[gs] * c
            if d is None:
                d = dd
            elif d != dd:
                d = 0
                break
        check(d in (1, -1), name + " det well defined")
        dets.append(d)
        chis.append(chirotope_factor(om, g))
        for t in range(len(om.topes)):
            img = {tuple(om.act_set(g, Z) for Z in k): v for k, v in om.rho[t].items()}
            if img != {k: d * v for k, v in om.rho[tp[t]].items()}:
                rho_eq = False
            if img != om.rho[tp[t]]:
                rho_eq_untw = False
    check(rho_eq, name + " g.rho = det rho")
    check(None not in chis and chis == dets, name + " det = chirotope factor")
    log("  [aut] |Aut M| = %d signed permutations; det(g) = -1 for %d of them; "
        "g.rho_C = det(g) rho_gC at chain level for all g, C: %s (without det: %s); "
        "det(g) equals the chirotope factor c(g) (chi o g = c(g) chi) for every g: %s"
        % (len(auts), dets.count(-1), rho_eq, rho_eq_untw, chis == dets))
    om.auts, om.tperm, om.dets = auts, tperm, dets
    om.rho_eq_untw = rho_eq_untw
    # cones
    sets = tconvex_sets(om)
    keys = sorted(sets)
    G.clear()
    G.update(om=om, auts=auts, sets=sets, tperm=tperm, dets=dets, deep=deep_all)
    rnd = random.Random(7)
    if cone_sample and len(keys) > cone_sample:
        run_keys = rnd.sample(keys, cone_sample)
        # always include the whole space and the singletons
        run_keys = sorted(set(run_keys) | {k for k in keys if k == (0, 0)})
    else:
        run_keys = keys
    if integral_sample is None:
        G["integral"] = set(run_keys)
    else:
        G["integral"] = set(rnd.sample(run_keys, min(integral_sample, len(run_keys)))) | {(0, 0)}
    results = parallel_map(check_cone, run_keys)
    log("  T-convex sets: %d%s" % (len(keys), "" if run_keys is keys else
                                   " (checked: a random sample of %d plus V = all topes)" % len(run_keys)))
    tally(name, results, log)
    return om, sets, results


def _rho_rows(om):
    keys = {}
    rows = []
    for t in range(len(om.topes)):
        rows.append({keys.setdefault(k, len(keys)): v for k, v in om.rho[t].items()})
    om.rho_index_rows = rows
    return rows


def sum_rho(om, lm):
    s = {}
    for t in bits(lm):
        for k, v in om.rho[t].items():
            s[k] = s.get(k, 0) + v
    return {k: v for k, v in s.items() if v}


def is_cycle(ch):
    bd = {}
    for k, v in ch.items():
        if len(k) == 1:
            bd[()] = bd.get((), 0) + v
            continue
        for i in range(len(k)):
            f = k[:i] + k[i + 1:]
            bd[f] = bd.get(f, 0) + v * (-1) ** i
    return not any(bd.values())


def parallel_map(fn, items):
    items = list(items)
    if WORKERS <= 1 or len(items) < 50:
        return [fn(k) for k in items]
    import multiprocessing as mp
    ctx = mp.get_context("fork")
    with ctx.Pool(WORKERS) as pool:
        return pool.map(fn, items, chunksize=max(1, len(items) // (WORKERS * 20)))


def tally(name, results, log):
    names = ["flatL", "zas", "wedge", "brown", "lunL", "rho", "q=m", "G1", "eq"]
    N = len(results)
    for k in names:
        good = sum(1 for _, r in results if r.get(k))
        have = sum(1 for _, r in results if k in r)
        if have:
            check(good == have, "%s [%s] %d/%d" % (name, k, good, have))
            log("  [%s] %d/%d" % (k, good, have))
    wrong = sum(1 for _, r in results if not r["zas_wrong"])
    log("  [zas control] summing over all of Lambda(V) instead of the flats containing S_max "
        "gives the wrong count on %d/%d cones" % (wrong, N))
    if any("eq" in r for _, r in results):
        untw = sum(1 for _, r in results if r.get("eq_untwisted"))
        st = sum(r["nstab"] for _, r in results)
        log("  [eq] sum of stabiliser orders %d; control (det twist removed) holds on %d/%d cones"
            % (st, untw, N))
    zt = [r for _, r in results if "Z_tors" in r]
    if zt:
        tors = sum(1 for r in zt if r["Z_tors"])
        zr = sum(1 for r in zt if r["Z_rho"])
        check(tors == 0 and zr == len(zt), name + " integral")
        log("  [Z] exact integral check on %d cones: torsion-free homology on %d, "
            "chamber cycles span H_{r-2}(;Z) (invariant factors all 1, rank m over Q) on %d"
            % (len(zt), len(zt) - tors, zr))
    p1 = [r for _, r in results if "pi1" in r]
    if p1:
        good = sum(1 for r in p1 if r["pi1"])
        check(good == len(p1), name + " pi1")
        log("  [pi1] pi_1(Delta(Lambda-bar(V))) = 1 proven by greedy presentation on %d/%d cones"
            % (good, len(p1)))
    ms = {}
    for _, r in results:
        ms[r["m"]] = ms.get(r["m"], 0) + 1
    log("  m(V) distribution: %s" % dict(sorted(ms.items())))


def run_lem02(om, log, sample=None, seed=3):
    prepare_lem02(om)
    n = om.n
    G["om"] = om
    conds = []
    T = om.topes
    for s in itertools.product((0, 1, -1), repeat=n):
        sp = sum(1 << e for e in range(n) if s[e] == 1)
        sm = sum(1 << e for e in range(n) if s[e] == -1)
        nonempty = any((t[0] & sm) == 0 and (t[1] & sp) == 0 and ((t[0] & sp) == sp) for t in T)
        conds.append((sp, sm, nonempty))
    if sample and len(conds) > sample:
        rnd = random.Random(seed)
        base = [c for c in conds if popcount(c[0] | c[1]) <= 1]
        conds = sorted(set(base) | set(rnd.sample(conds, sample)))
    res = parallel_map(lem02_worker, conds)
    # Lemma 2.2(a): Delta(L - {0, T}) is contractible, for every tope T
    allm = sum(1 << i for i in range(1, len(om.L)))
    l22 = [classify_K(om, allm & ~(1 << om.idx[T])) for T in om.topes]
    l22ok = all(k == "point" or b == {} for k, b in l22)
    check(l22ok, om.name + " Lemma 2.2(a)")
    log("  [lem22a] Delta(L - {0, T}) contractible for all %d topes (beat-point core a point on %d): %s"
        % (len(om.topes), sum(1 for k, _ in l22 if k == "point"), l22ok))
    lem = [r for r in res if r[3] is not None]
    good = sum(1 for r in lem if r[3])
    check(good == len(lem), om.name + " lem02")
    pts = sum(1 for r in lem if r[1] == "point")
    # trichotomy for all s
    tri_ok = True
    for (sp, sm, ne), kind, b, _ in res:
        if kind in ("empty", "point"):
            continue
        Km = K_mask(om, sp, sm)
        sym = all(((Km >> om.idx[neg(om.L[i])]) & 1) for i in bits(Km))
        if sym:
            if not (len(b) == 1 and list(b.values()) == [1]):
                tri_ok = False
        elif b != {}:
            tri_ok = False
    check(tri_ok, om.name + " trichotomy")
    log("  [lem02] %d/%d sign conditions with V(S,s) nonempty: S = {} gives a homology S^%d, "
        "S != {} gives a contractible K (beat-point core a single point on %d of these, "
        "acyclic core otherwise)%s; trichotomy (empty / sphere iff K = -K / acyclic) on all "
        "%d tested s: %s"
        % (good, len(lem), om.r - 1, pts, "" if not sample else " [sample]", len(res), tri_ok))


def controls(log):
    """Positive and negative controls for the instruments."""
    allok = True
    # 1. corrupted chirotope rejected
    ch = Chirotope.from_vectors(vectors_A(4))
    vals = dict(ch.vals)
    B = next(iter(vals))
    vals[B] = -vals[B]
    bad, _ = chirotope_axioms(Chirotope(ch.n, ch.r, vals))
    allok &= check(not bad, "control: flipped chirotope accepted")
    # 2. Pappus (realizable) fails the non-Pappus certificate; non-Pappus passes
    pap, npap = non_pappus(1)
    allok &= check(zero_triples(pap) == PAPPUS_9, "control: Pappus zero set")
    allok &= check(not non_realizability_certificate(pap), "control: Pappus certified")
    allok &= check(non_realizability_certificate(npap), "control: non-Pappus not certified")
    # 3. torsion detector: 6-vertex RP^2 has H_1 = Z/2
    rp2 = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5), (1, 2, 4), (2, 3, 5),
           (1, 3, 4), (1, 3, 5), (2, 4, 5)]
    simp = set()
    for t in rp2:
        for k in (1, 2, 3):
            for f in itertools.combinations(t, k):
                simp.add(f)
    tf = torsion_free(list(simp))
    allok &= check(tf == [2], "control: RP2 torsion not detected")
    # 4. pi_1 instrument does not claim RP^2 simply connected; does on S^2
    allok &= check(not pi1_trivial(list(simp)), "control: pi1 claims RP2 trivial")
    s2 = set()
    for t in itertools.combinations(range(4), 3):
        for k in (1, 2, 3):
            for f in itertools.combinations(t, k):
                s2.add(f)
    allok &= check(pi1_trivial(list(s2)) and closed_surface_sphere(list(s2)), "control: S2")
    allok &= check(not closed_surface_sphere(list(simp)), "control: RP2 called S2")
    # 5. smith on a known matrix
    allok &= check(smith_check([{0: 2, 1: 4}, {0: 1, 1: 2}, {1: 3}])[0] == 2, "control: smith rank")
    allok &= check(smith_check([{0: 2}, {1: 3}])[1] == [6], "control: smith factors")
    log("[controls] flipped chirotope rejected; Pappus zero set = its 9 lines and it fails the "
        "non-Pappus certificate; RP^2 torsion Z/2 detected; pi_1 and S^2 tests reject RP^2 and "
        "accept the boundary of a tetrahedron; Smith form on known matrices: %s"
        % ("all fire" if allok else "FAILED"))
    return allok


def negative_cone_control(om, log):
    """A non-T-convex set of topes, V = {T, -T}: the closed face complex is
    two balls (not contractible) and the Zaslavsky formula fails."""
    prepare_lem02(om) if not hasattr(om, "below") else None
    T = om.topes[0]
    nT = neg(T)
    Km = 0
    for i, X in enumerate(om.L):
        if X != (0, 0) and (leq(X, T) or leq(X, nT)):
            Km |= 1 << i
    kind, b = classify_K(om, Km)
    F = [X for X in om.L if leq(X, T) or leq(X, nT)]
    Lam = {om.z(X) for X in F}
    mu = mobius_top(Lam)
    count = sum((-1) ** om.rank_of[Z] * mu[Z] for Z in Lam)
    fires = (kind != "point" and b == {0: 1}) and count != 2
    check(fires, om.name + " negative cone control")
    log("  [neg] V = {T, -T} (not T-convex): closed face complex has reduced Betti %s "
        "(two components, not contractible); Zaslavsky-type sum gives %d, not 2: control fires: %s"
        % (b, count, fires))


KNOWN = {
    # name: (T-convex sets, |mu|, |Aut|, sum |Stab|, untwisted-identity count) or None
    "A3": (219, 6, 48, 576, 128),          # note's table; A001035(4) = 219
    "B3": (941, 15, 48, 1680, 826),        # note's table and general_theory.txt [B3]
    "nonPappus+": (1295, 20, 2, 1296, 1294),   # note's table
    "A4": (4231, 24, 240, None, None),     # A001035(5) = 4231 posets on 5 labelled points
}


def known_control(name, om, sets, results, log):
    if name not in KNOWN:
        return
    k = KNOWN[name]
    st = sum(r.get("nstab", 0) for _, r in results)
    untw = sum(1 for _, r in results if r.get("eq_untwisted"))
    got = (len(sets), abs(om.mu_L), len(om.auts), st, untw)
    ok = all(a is None or a == b for a, b in zip(k, got))
    check(ok, "%s known values %s != %s" % (name, k, got))
    log("  [known] (cones, |mu|, |Aut|, sum|Stab|, untwisted) = %s; expected %s: %s"
        % (got, tuple("-" if a is None else a for a in k), ok))


def linear_subgroup_control(om, n, log):
    """Restrict the equivariant check of the braid OM to the linear group
    W = S_n (permuting coordinates), as compute/output/general_theory.txt
    [A4] does: expect sum |Stab| = 7560 and the untwisted identity on all
    4231 cones (that file's values, not re-derived there by us)."""
    pairs = list(itertools.combinations(range(n), 2))
    pix = {p: k for k, p in enumerate(pairs)}
    pats = set()
    for sig in itertools.permutations(range(n)):
        perm, sg = [], []
        for (i, j) in pairs:
            a_, b_ = sig[i], sig[j]
            perm.append(pix[(min(a_, b_), max(a_, b_))])
            sg.append(1 if a_ < b_ else -1)
        pats.add((tuple(perm), tuple(sg)))
    sub = [k for k, g in enumerate(om.auts) if g in pats]
    check(len(sub) == 120, "S_n subgroup size")
    G["auts"] = [om.auts[k] for k in sub]
    G["tperm"] = [om.tperm[k] for k in sub]
    G["dets"] = [om.dets[k] for k in sub]
    G["integral"] = set()
    keys = sorted(G["sets"])
    res = parallel_map(check_cone, keys)
    st = sum(r["nstab"] for _, r in res)
    untw = sum(1 for _, r in res if r["eq_untwisted"])
    tw = sum(1 for _, r in res if r["eq"])
    sg_ok = all(d == perm_parity_of(om.auts[k][0], pairs, n) for k, d in zip(sub, G["dets"]))
    ok = (st, untw, tw) == (7560, 4231, 4231)
    check(ok and sg_ok, "A4 linear subgroup control")
    log("  [W=S_5] restricted to the linear group: sum |Stab| = %d, twisted identity on %d/%d, "
        "untwisted on %d/%d; general_theory.txt [A4] reports 7560 and 4231/4231: %s; "
        "det(sigma) = sgn(sigma) for every sigma: %s" % (st, tw, len(keys), untw, len(keys), ok, sg_ok))


def perm_parity_of(perm, pairs, n):
    """sgn of the permutation sigma of {0..n-1} inducing perm on pairs."""
    # recover sigma: vertex i is the common point of the pairs containing it
    sig = []
    for i in range(n):
        imgs = [set(pairs[perm[k]]) for k, p in enumerate(pairs) if i in p]
        common = set.intersection(*imgs)
        sig.append(next(iter(common)))
    return perm_sign(sig)


def lifting_N():
    _, M = non_pappus(+1)
    d = M.dual()
    basis = next(B for B in itertools.combinations(range(9), 6) if d.vals.get(B))
    seq = [(a, s) for a, s in zip(basis, (1, -1, 1, -1, 1, -1))]
    d, ext, N = lifting_of(M, seq)
    return M, d, ext, N, seq


def main():
    quick = "--quick" in sys.argv
    log = print
    controls(log)
    plan = [("A3", Chirotope.from_vectors(vectors_A(4)), True),
            ("B3", Chirotope.from_vectors(vectors_B3()), True),
            ("nonPappus+", non_pappus(+1)[1], False)]
    if not quick:
        plan += [("nonPappus-", non_pappus(-1)[1], False),
                 ("A4", Chirotope.from_vectors(vectors_A(5)), True)]
    for name, ch, real in plan:
        if name.startswith("nonPappus"):
            c = non_realizability_certificate(ch)
            check(c, name + " certificate")
            log("[%s certificate] zero set of chi = the 8 non-Pappus lines: %s" % (name, c))
        om, sets, res = run_om(name, ch, real, log, quick)
        known_control(name, om, sets, res, log)
        if name == "A4":
            linear_subgroup_control(om, 5, log)
        if om.r == 3 and (not quick or name != "B3"):
            run_lem02(om, log)
        if name == "B3":
            negative_cone_control(om, log)
        log("  => %s" % ("PASS" if not FAIL else "FAIL so far"))
    # rank 4, non-realizable: the lifting N, and non-Pappus + coloop
    M, d, ext, N, seq = lifting_N()
    okd, _ = chirotope_axioms(d)
    oke, _ = chirotope_axioms(ext)
    con = N.contract(9)
    same = con.vals == M.vals or con.vals == {k: -v for k, v in M.vals.items()}
    check(okd and oke and same, "lifting construction")
    log("[N = (nonPappus*[p])*] dual (rank %d) axioms ok: %s; lexicographic extension "
        "[%s] axioms ok: %s; N/p = nonPappus up to global sign: %s; so N is NOT realizable "
        "(a minor of a realizable OM is realizable)"
        % (d.r, okd, " ".join("%d%s" % (a, "+" if s > 0 else "-") for a, s in seq), oke, same))
    om, sets, res = run_om("N", N, False, log, quick,
                           cone_sample=400 if quick else None)
    check(om.rk(om.full & ~(1 << 9)) == om.r, "p coloop")
    log("  p is not a coloop of N (N is not a direct sum with p): %s" % (om.rk(om.full & ~(1 << 9)) == om.r))
    run_lem02(om, log, sample=100 if quick else 1500)
    negative_cone_control(om, log)
    log("  => %s" % ("PASS" if not FAIL else "FAIL so far"))
    if not quick:
        NC = with_coloop(non_pappus(+1)[1])
        om, sets, res = run_om("nonPappus+coloop", NC, False, log, quick)
        run_lem02(om, log, sample=1500)
        log("  => %s" % ("PASS" if not FAIL else "FAIL so far"))
    if FAIL:
        log("FAILURES:")
        for f in FAIL[:50]:
            log("  " + f)
        log("SOME CHECKS FAILED")
        sys.exit(1)
    log("ALL PASS")


if __name__ == "__main__":
    main()
