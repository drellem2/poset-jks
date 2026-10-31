"""Independent check of (S4) for e_H = 3 (notes/audit_s4_eh3.md).

Theorem S consequence (S4), case e_H = dim Fix(H) = 3:  T^H ~ wedge of m_H circles,
where T = Delta(proper part of Lambda(V)) and m_H = #chambers of V fixed by H.

New code. It imports nothing from the repository.

For every (V, H) with e_H = 3 in the families below, it computes:
  * T^H = Delta(Lambda-bar(V)^H): the Stong core of the poset of H-stable flats, then
    (if the core has height >= 2) elementary simplicial collapses of its order complex.
    PASS means: the result is a connected graph with first Betti number m_H
    (a connected graph with b_1 = m is homotopy equivalent to a wedge of m circles).
  * X^H = Delta(Q'^H): the maximal chain length of Q'^H (H-stable non-chamber faces != O).
    The dimension claim of notes/audit_s4_eh3.md is: m_H >= 1  ==>  X^H is a graph.

Families:
  [B3]  every pointed top-cone of the B_3 arrangement, G = its stabilizer in W(B_3);
        e_H = 3 forces H = 1.
  [B4]  every pointed top-cone of the B_4 arrangement, G = its stabilizer in W(B_4);
        e_H = 3 forces H = <reflection>, hence m_H = 0.
  [A]   every connected poset P with 3 <= n <= NMAX (up to isomorphism),
        V = {x_i <= x_j for i <_P j} in R^n / R1, G = full stabilizer of V in
        S_n x {+-1}, every subgroup H with e_H = 3.
  [CTL] controls that must fail / must fire.
"""

import argparse
import itertools
import sys
import time
from collections import defaultdict

# ---------------------------------------------------------------- linear algebra


def rank_q(rows):
    """Rank over Q of an integer matrix (list of lists), fraction-free elimination."""
    m = [list(r) for r in rows if any(r)]
    rk = 0
    ncols = len(m[0]) if m else 0
    for c in range(ncols):
        piv = None
        for i in range(rk, len(m)):
            if m[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        p = m[rk]
        for i in range(len(m)):
            if i != rk and m[i][c] != 0:
                f = m[i][c]
                m[i] = [f * p[j] - p[c] * m[i][j] for j in range(ncols)]
        rk += 1
    return rk


def matvec(M, x):
    return tuple(sum(M[i][j] * x[j] for j in range(len(x))) for i in range(len(M)))


def matmul(A, B):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)) for i in range(n))


def ident(n):
    return tuple(tuple(1 if i == j else 0 for j in range(n)) for i in range(n))


def fix_dim(H, n, quotient_by_ones=False):
    """dim of the H-fixed subspace, by the character formula (1/|H|) sum tr(h).

    With quotient_by_ones, the representation is R^n / R(1,...,1); each h is a signed
    permutation matrix eps*P, which acts on R1 by eps, so tr_quotient = tr - eps."""
    s = 0
    for h in H:
        tr = sum(h[i][i] for i in range(n))
        if quotient_by_ones:
            eps = sum(h[0])  # row sum of eps*P is eps
            tr -= eps
        s += tr
    assert s % len(H) == 0
    return s // len(H)


# ---------------------------------------------------------------- groups


def closure(gens, n):
    e = ident(n)
    G = {e}
    frontier = [e]
    while frontier:
        new = []
        for a in frontier:
            for g in gens:
                b = matmul(a, g)
                if b not in G:
                    G.add(b)
                    new.append(b)
        frontier = new
    return frozenset(G)


def subgroups(G, n):
    """All subgroups: start from cyclic subgroups, close under pairwise joins."""
    cyc = {closure([g], n) for g in G}
    subs = set(cyc)
    frontier = set(cyc)
    while frontier:
        new = set()
        for A in frontier:
            for C in cyc:
                if C <= A:
                    continue
                J = closure(list(A) + list(C), n)
                if J not in subs:
                    new.add(J)
        subs |= new
        frontier = new
    return subs


# ---------------------------------------------------------------- arrangements


class Arrangement:
    """Central arrangement given by integer normals; faces given by sample points.

    A face is keyed by its sign vector (tuple in {-1,0,1}). `pt[key]` is a point of it."""

    def __init__(self, normals, points, dim, quotient_by_ones=False):
        self.normals = [tuple(v) for v in normals]
        self.n = dim
        self.qo = quotient_by_ones
        self.pt = {}
        for x in points:
            k = self.sign(x)
            if k not in self.pt:
                self.pt[k] = tuple(x)
        self.faces = list(self.pt)
        self.chambers = [f for f in self.faces if 0 not in f]
        self.zero = tuple(0 for _ in self.normals)
        assert self.zero in self.pt

    def sign(self, x):
        out = []
        for v in self.normals:
            s = sum(a * b for a, b in zip(v, x))
            out.append((s > 0) - (s < 0))
        return tuple(out)

    def act(self, g, f):
        return self.sign(matvec(g, self.pt[f]))

    def fdim(self, f):
        """Dimension of the face f (of its span), modulo R1 when quotienting."""
        Z = [self.normals[i] for i, s in enumerate(f) if s == 0]
        d = self.n - (rank_q(Z) if Z else 0)
        return d - 1 if self.qo else d


def braid(n):
    normals = []
    for i in range(n):
        for j in range(i + 1, n):
            v = [0] * n
            v[i], v[j] = 1, -1
            normals.append(v)
    pts = itertools.product(range(n), repeat=n)
    return Arrangement(normals, pts, n, quotient_by_ones=True)


def typeB(n):
    normals = []
    for i in range(n):
        v = [0] * n
        v[i] = 1
        normals.append(v)
    for i in range(n):
        for j in range(i + 1, n):
            for s in (1, -1):
                v = [0] * n
                v[i], v[j] = 1, s
                normals.append(v)
    pts = itertools.product(range(-n, n + 1), repeat=n)
    return Arrangement(normals, pts, n)


def signed_perms(n, signs=True):
    out = []
    for p in itertools.permutations(range(n)):
        for eps in (itertools.product((1, -1), repeat=n) if signs else [(1,) * n]):
            M = [[0] * n for _ in range(n)]
            for i in range(n):
                M[p[i]][i] = eps[i]
            out.append(tuple(tuple(r) for r in M))
    return out


# ---------------------------------------------------------------- cones


def conformal(f, c):
    """Face f lies in the closure of the face c."""
    return all(a == 0 or a == b for a, b in zip(f, c))


class Cone:
    """Top-cone V given by its set of chambers; |V| = union of closed chambers."""

    def __init__(self, Ar, chambers, common=None):
        self.Ar = Ar
        self.ch = frozenset(chambers)
        if common is None:
            # the faces of V: faces in the closure of some chamber of V (|V| is convex, so
            # this is the same as F subset |V|)
            self.faces = [f for f in Ar.faces if any(conformal(f, c) for c in self.ch)]
        else:
            # |V| = {x : sign_i(x) in {0, s_i} for (i, s_i) in common}
            self.faces = [f for f in Ar.faces if all(f[i] in (0, s) for i, s in common)]
        fs = set(self.faces)
        neg = lambda f: tuple(-a for a in f)
        self.pointed = all(f == Ar.zero or neg(f) not in fs for f in self.faces)
        self.fset = fs

    def stabilizer(self, group):
        return [g for g in group if all(self.Ar.act(g, c) in self.ch for c in self.ch)]


def convex_hull_chambers(Ar, S):
    """Chambers lying in the intersection of the closed halfspaces common to S."""
    S = list(S)
    common = [i for i in range(len(Ar.normals)) if len({c[i] for c in S}) == 1]
    return frozenset(c for c in Ar.chambers if all(c[i] == S[0][i] for i in common))


def all_top_cones(Ar):
    """All convex unions of chambers (intersections of closed halfspaces of A).

    Every such cone K is gallery connected, so starting from one of its chambers and
    adjoining an adjacent chamber of K then taking the hull stays inside K; BFS over
    'adjoin an adjacent chamber, take the hull' reaches every K."""
    adj = defaultdict(list)
    chs = Ar.chambers
    idx = {c: i for i, c in enumerate(chs)}
    for c in chs:
        for i in range(len(c)):
            d = list(c)
            d[i] = -d[i]
            d = tuple(d)
            if d in idx:
                adj[c].append(d)
    seen = set()
    frontier = []
    for c in chs:
        K = frozenset([c])
        seen.add(K)
        frontier.append(K)
    while frontier:
        new = []
        for K in frontier:
            nb = {d for c in K for d in adj[c]} - K
            for d in nb:
                K2 = convex_hull_chambers(Ar, K | {d})
                if K2 not in seen and len(K2) < len(chs):
                    seen.add(K2)
                    new.append(K2)
        frontier = new
    return seen


# ---------------------------------------------------------------- posets and homotopy


def stong_core(elems, lt):
    """Remove beat points until none is left. Returns (elements, lt-relation as dict)."""
    E = set(elems)
    up = {x: {y for y in E if lt(x, y)} for x in E}
    down = {x: {y for y in E if lt(y, x)} for x in E}
    changed = True
    while changed:
        changed = False
        for x in list(E):
            U = up[x] & E
            D = down[x] & E
            beat = False
            if U:
                mins = [y for y in U if not any(z in U and z in down[y] for z in U)]
                if len(mins) == 1:
                    beat = True
            if not beat and D:
                maxs = [y for y in D if not any(z in D and z in up[y] for z in D)]
                if len(maxs) == 1:
                    beat = True
            if beat:
                E.discard(x)
                changed = True
    rel = {x: up[x] & E for x in E}
    return E, rel


def chains(E, rel):
    """All nonempty chains (as frozensets) of the poset (E, rel: x -> set of y > x)."""
    out = []

    def ext(ch, top):
        out.append(frozenset(ch))
        for y in rel[top]:
            ext(ch + [y], y)

    for x in E:
        ext([x], x)
    return out


def height(E, rel):
    """Maximal number of elements in a chain (0 for the empty poset)."""
    memo = {}

    def h(x):
        if x not in memo:
            memo[x] = 1 + max((h(y) for y in rel[x]), default=0)
        return memo[x]

    return max((h(x) for x in E), default=0)


def collapse_to_low_dim(simplices):
    """Elementary collapses (free faces) on a simplicial complex given by all its simplices.

    Repeatedly removes a pair (s, t) with s a codim-1 face of t, t maximal, and t the only
    simplex properly containing s. Returns the remaining simplices."""
    S = set(simplices)
    cof = defaultdict(set)
    for t in S:
        if len(t) >= 2:
            for v in t:
                cof[t - {v}].add(t)
    changed = True
    while changed:
        changed = False
        for s in list(S):
            if s not in S or len(s) == 0:
                continue
            co = cof[s] & S
            if len(co) == 1:
                (t,) = co
                if not (cof[t] & S):  # t maximal
                    S.discard(t)
                    S.discard(s)
                    changed = True
    return S


def graph_type(E, rel):
    """Homotopy certificate for Delta(E, rel).

    Returns (status, b0, b1): status 'graph' if (after Stong core, plus collapses when
    needed) the complex is <= 1-dimensional, else 'not-certified'."""
    E, rel = stong_core(E, rel if callable(rel) else (lambda x, y: y in rel[x]))
    if height(E, rel) <= 2:
        verts = list(E)
        edges = [(x, y) for x in E for y in rel[x]]
    else:
        simp = collapse_to_low_dim(chains(E, rel))
        if any(len(s) >= 3 for s in simp):
            return "not-certified", None, None
        verts = [next(iter(s)) for s in simp if len(s) == 1]
        edges = [tuple(s) for s in simp if len(s) == 2]
    # components by union-find
    par = {v: v for v in verts}

    def find(v):
        while par[v] != v:
            par[v] = par[par[v]]
            v = par[v]
        return v

    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra != rb:
            par[ra] = rb
    b0 = len({find(v) for v in verts})
    b1 = len(edges) - len(verts) + b0
    return "graph", b0, b1


# ---------------------------------------------------------------- the (S4) check


def zero_set(f):
    return frozenset(i for i, s in enumerate(f) if s == 0)


def analyse_pair(V, H):
    """Data for one (V, H): m_H, the T^H certificate, and the height of Q'^H."""
    Ar = V.Ar
    stable = [f for f in V.faces if f != Ar.zero and all(Ar.act(h, f) == f for h in H)]
    m = sum(1 for f in stable if 0 not in f)
    Qp = [f for f in stable if 0 in f]
    # Q'^H, ordered by f < f' iff f in closure(f')
    relQ = {f: {g for g in Qp if g != f and conformal(f, g)} for f in Qp}
    hQ = height(Qp, relQ)
    # Lambda-bar(V)^H. A flat is keyed by its zero set (the set of hyperplanes containing
    # it). span F has zero set Z(F). 0 has zero set 'all hyperplanes'; R^d has the empty set.
    full = frozenset(range(len(Ar.normals)))
    flats = {zero_set(f) for f in V.faces} - {full, frozenset()}
    # action of h on flats: via the action on a face spanning the flat
    rep = {}
    for f in V.faces:
        z = zero_set(f)
        if z in flats and z not in rep:
            rep[z] = f
    stable_flats = [z for z in flats if all(zero_set(Ar.act(h, rep[z])) == z for h in H)]
    relT = {z: {w for w in stable_flats if w < z} for z in stable_flats}  # Y < Y' iff Z(Y) > Z(Y')
    if not stable_flats:
        st, b0, b1 = "empty", 0, 0
    else:
        st, b0, b1 = graph_type(stable_flats, relT)
    ok = st == "graph" and b0 == 1 and b1 == m
    return dict(m=m, hQ=hQ, status=st, b0=b0, b1=b1, ok=ok, nflats=len(stable_flats))


def run_family(tag, items, out, quotient=False):
    """items: iterable of (label, V, G, n). Checks every H <= G with e_H = 3."""
    stats = defaultdict(int)
    hist = defaultdict(int)
    for label, V, G, n in items:
        for H in subgroups(G, n):
            e = fix_dim(H, n, quotient_by_ones=quotient)
            if e != 3:
                continue
            r = analyse_pair(V, H)
            stats["pairs"] += 1
            stats["pass" if r["ok"] else "FAIL"] += 1
            stats["m>=1" if r["m"] >= 1 else "m=0"] += 1
            hist[(r["m"] >= 1, r["hQ"])] += 1
            if r["m"] >= 1 and r["hQ"] > 2:
                stats["DIM-CLAIM-FAIL"] += 1
            if len(H) > 1 and r["m"] >= 1:
                stats["H!=1,m>=1"] += 1
            if not r["ok"]:
                print(f"[{tag}] FAIL {label} |H|={len(H)} {r}", file=out)
    print(f"[{tag}] e_H=3 pairs: {stats['pairs']}  pass: {stats['pass']}  FAIL: {stats['FAIL']}  "
          f"(m_H>=1: {stats['m>=1']}, of which H!=1: {stats['H!=1,m>=1']}; m_H=0: {stats['m=0']})", file=out)
    for (mpos, h), c in sorted(hist.items()):
        print(f"[{tag}]   m_H{'>=1' if mpos else '=0 '}  max chain length of Q'^H = {h}"
              f"  (dim X^H = {h - 1}): {c} pairs", file=out)
    print(f"[{tag}] dimension claim (m_H>=1 => X^H a graph) failures: {stats['DIM-CLAIM-FAIL']}", file=out)
    return stats


# ---------------------------------------------------------------- posets (type A)


def down_sets(n, less):
    """All down-closed subsets of the poset on range(n) (less: set of pairs (a,b), a<b)."""
    out = []
    for mask in range(1 << n):
        ok = True
        for (a, b) in less:
            if (mask >> b) & 1 and not (mask >> a) & 1:
                ok = False
                break
        if ok:
            out.append(mask)
    return out


def naturally_labelled_posets(n):
    """All posets on range(n) whose order extends 0 < 1 < ... < n-1 (as relation sets)."""
    res = [frozenset()]
    for k in range(1, n):
        new = []
        for less in res:
            for D in down_sets(k, less):
                new.append(less | {(a, k) for a in range(k) if (D >> a) & 1})
        res = new
    return res


def connected(n, less):
    par = list(range(n))

    def find(v):
        while par[v] != v:
            v = par[v]
        return v

    for a, b in less:
        par[find(a)] = find(b)
    return len({find(v) for v in range(n)}) == 1


def canon(n, less):
    best = None
    for p in itertools.permutations(range(n)):
        k = tuple(sorted((p[a], p[b]) for a, b in less))
        if best is None or k < best:
            best = k
    return best


def connected_posets(n):
    seen = {}
    for less in naturally_labelled_posets(n):
        if not connected(n, less):
            continue
        # cheap invariant before the expensive canonical form
        c = canon(n, less)
        if c not in seen:
            seen[c] = frozenset(less)
    return list(seen.values())


def poset_cone(Ar, n, less):
    ch = [c for c in Ar.chambers if all(Ar.pt[c][a] < Ar.pt[c][b] for a, b in less)]
    return Cone(Ar, ch)


def typeA_items(nmax, out):
    for n in range(3, nmax + 1):
        t = time.time()
        Ar = braid(n)
        allg = signed_perms(n, signs=False)
        allg = allg + [tuple(tuple(-a for a in r) for r in g) for g in allg]  # S_n x {+-1}
        Ps = connected_posets(n)
        cnt = 0
        for less in Ps:
            V = poset_cone(Ar, n, less)
            assert V.pointed
            G = V.stabilizer(allg)
            cnt += 1
            yield (f"n={n} P={sorted(less)}", V, G, n)
        print(f"[A] n={n}: {cnt} connected posets, {time.time() - t:.1f}s", file=out)


def common_signs(Ar, K):
    S = list(K)
    return [(i, S[0][i]) for i in range(len(Ar.normals)) if len({c[i] for c in S}) == 1]


def typeB4_items(out):
    """B_4: an orthogonal H with dim Fix(H) = 3 fixes a hyperplane pointwise, so
    H = {1, s} with s the reflection in it. So only pairs (V, <s>) with s in W(B_4) a
    reflection preserving V are needed; one item per pair, with G = <s>."""
    n = 4
    Ar = typeB(n)
    W = signed_perms(n)
    e = ident(n)
    refl = [g for g in W if g != e and matmul(g, g) == e and fix_dim([e, g], n) == 3]
    assert len(refl) == 16
    # signed permutation of hyperplanes induced by each reflection
    hidx = {v: i for i, v in enumerate(Ar.normals)}
    hp = {}
    for s in refl:
        m = []
        for v in Ar.normals:
            w = matvec(s, v)
            if w in hidx:
                m.append((hidx[w], 1))
            else:
                m.append((hidx[tuple(-a for a in w)], -1))
        hp[s] = m
    cones = all_top_cones(Ar)
    pointed = 0
    npairs = 0
    for K in cones:
        com = common_signs(Ar, K)
        if rank_q([Ar.normals[i] for i, _ in com]) < n:
            continue  # |V| contains the line cut out by the common hyperplanes
        pointed += 1
        cs = set(com)
        good = [s for s in refl if {(hp[s][i][0], hp[s][i][1] * si) for i, si in com} == cs]
        if not good:
            continue
        V = Cone(Ar, K, common=com)
        assert V.pointed
        for s in good:
            npairs += 1
            yield (f"B4 cone #{pointed} ({len(K)} chambers)", V, [e, s], n)
    print(f"[B4] {len(cones)} proper top-cones, {pointed} pointed, "
          f"{npairs} (cone, reflection) pairs with s(V) = V", file=out)


def typeB_items(n, out):
    Ar = typeB(n)
    W = signed_perms(n)
    cones = all_top_cones(Ar)
    pointed = 0
    for K in cones:
        V = Cone(Ar, K)
        if not V.pointed:
            continue
        pointed += 1
        G = V.stabilizer(W)
        yield (f"B{n} cone #{pointed} ({len(K)} chambers)", V, G, n)
    print(f"[B{n}] {len(cones)} proper top-cones, {pointed} pointed", file=out)


# ---------------------------------------------------------------- controls


def controls(out):
    ok = True
    # (1) a non-pointed cone: the half-space {x_1 >= 0} in B_3, H = 1. T is the proper part
    #     of the whole intersection lattice of B_3: a wedge of 15 circles, but m = 24.
    Ar = typeB(3)
    half = [c for c in Ar.chambers if c[0] == 1]
    V = Cone(Ar, half)
    r = analyse_pair(V, [ident(3)])
    fired = (not V.pointed) and r["status"] == "graph" and r["b1"] == 15 and r["m"] == 24 and not r["ok"]
    print(f"[CTL] non-pointed half-space of B_3, H=1: pointed={V.pointed} m={r['m']} "
          f"b1(T)={r['b1']} -> (S4) prediction must FAIL: {'fails, as it must' if fired else 'DID NOT FAIL'}", file=out)
    ok &= fired
    # (2) the certifier must refuse a 2-sphere: face poset of the octahedron boundary
    verts = [(i, s) for i in range(3) for s in (1, -1)]
    faces = []
    for k in (1, 2, 3):
        for idx in itertools.combinations(range(3), k):
            for sg in itertools.product((1, -1), repeat=k):
                faces.append(frozenset(zip(idx, sg)))
    rel = {f: {g for g in faces if f < g} for f in faces}
    st, _, _ = graph_type(faces, rel)
    print(f"[CTL] octahedral 2-sphere: certifier says {st!r} (must not be 'graph')", file=out)
    ok &= st != "graph"
    # (3) the certifier must accept a contractible 2-dim complex that is not a graph
    #     (Delta of a poset with a top element collapses to a point via Stong) and a
    #     triangulated disc given without a top (face poset of a 2-simplex minus nothing)
    tri = [frozenset(s) for k in (1, 2, 3) for s in itertools.combinations(range(3), k)]
    rel = {f: {g for g in tri if f < g} for f in tri}
    st, b0, b1 = graph_type(tri, rel)
    print(f"[CTL] 2-simplex face poset: {st} b0={b0} b1={b1} (must be graph, 1, 0)", file=out)
    ok &= (st, b0, b1) == ("graph", 1, 0)
    # (4) Stong-irreducible but collapsible-to-graph: the face poset of a hexagon with all
    #     its 6 triangles from a centre removed... use the crown (minimal non-contractible
    #     height-2 Stong core): S^1, must give graph with b1 = 1
    crown = ["a0", "a1", "b0", "b1"]
    rel = {"a0": {"b0", "b1"}, "a1": {"b0", "b1"}, "b0": set(), "b1": set()}
    st, b0, b1 = graph_type(crown, rel)
    print(f"[CTL] crown: {st} b0={b0} b1={b1} (must be graph, 1, 1)", file=out)
    ok &= (st, b0, b1) == ("graph", 1, 1)
    # (5) the subgroup enumerator: S_3 has 6 subgroups, W(B_3) has 98, S_4 has 30
    s3 = closure([g for g in signed_perms(3, signs=False)], 3)
    s4 = closure([g for g in signed_perms(4, signs=False)], 4)
    wb3 = closure(signed_perms(3), 3)
    c = (len(subgroups(s3, 3)), len(subgroups(s4, 4)), len(subgroups(wb3, 3)))
    print(f"[CTL] subgroup counts S_3, S_4, W(B_3): {c} (must be (6, 30, 98))", file=out)
    ok &= c == (6, 30, 98)
    # (6) the dimension detector must fire: B_4 reflection pairs have m_H = 0 and the
    #     reflecting hyperplane lies in A, so Q'^H has 3-chains (checked in the B4 run).
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--skip-b4", action="store_true")
    args = ap.parse_args()
    out = sys.stdout
    t0 = time.time()
    allok = controls(out)
    s = run_family("B3", typeB_items(3, out), out)
    allok &= s["FAIL"] == 0 and s["DIM-CLAIM-FAIL"] == 0
    if not args.skip_b4:
        s = run_family("B4", typeB4_items(out), out)
        allok &= s["FAIL"] == 0 and s["DIM-CLAIM-FAIL"] == 0
    s = run_family("A", typeA_items(args.nmax, out), out, quotient=True)
    allok &= s["FAIL"] == 0 and s["DIM-CLAIM-FAIL"] == 0
    print(f"total {time.time() - t0:.1f}s", file=out)
    print(f"ALL CHECKS PASS: {allok}", file=out)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
