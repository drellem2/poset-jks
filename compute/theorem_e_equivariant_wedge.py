#!/usr/bin/env python3
"""Checks for notes/theorem_e_equivariant_wedge.md (Theorem E: equivariant wedge).

Setting. A is a finite real central arrangement, V a top-cone (a set of chambers cut out
by sign conditions), G a finite group of signed permutations of the hyperplanes induced
by linear maps preserving A and V. Lambda(V) is the set of spans of faces of V, i.e. of
zero sets z(F) of the faces F of V. T = Delta(proper part of Lambda(V)).

For every subgroup H <= G we compute the fixed subcomplex T^H = Delta(Lambda-bar(V)^H)
and test it against the prediction of the note:

  (S)  H~_*(T^H) = Z^{m_H} concentrated in degree e_H - 2,
       m_H = number of chambers of V fixed by H, e_H = dim Fix(H) (essential space),
       for pointed V and EVERY H (consequence of Theorem S of the note).
  (E)  in particular, if H != 1 fixes no chamber, T^H is acyclic, and we also certify
       contractibility by a Stong core of one point (beat-point deletion; Stong 1966,
       cited).

Homology: reduced Betti numbers modulo each prime in PRIMES. Equality of all of them
with the prediction is what "COMPUTED" means in the note (no integral Smith form).

Parts:
  [CTL]  instrument controls: Boolean B_3 proper part (S^1), a crown (S^1, no beat
         point), a chain (contractible).
  [POS]  type A, connected P, 4 <= n <= NMAX, |Aut P| > 1, G = Aut(P): every subgroup.
         Positive control for Theorem E (free action, pointed cone).
  [GEN]  general arrangements: every pointed top-cone of the Boolean arrangement in R^3,
         R^4 and of the B_3 arrangement, G = full stabilizer in the signed-permutation
         group, every subgroup; tests (S) (free and non-free cases).
  [NEG]  negative controls:
         - non-free: orthant of R^3 / R^4 with the symmetric group: T^G is EMPTY, and the
           "trivial-action permutation wedge" prediction (Z^{m_H} in degree d-2) fails;
         - non-pointed, free on chambers: all chambers of A_3 (Pi_4) with S_4 and its
           subgroups, and P = two 2-chains with the swap: some T^H, H != 1, not acyclic;
         - a deliberately wrong prediction (degree e_H - 1) must fail somewhere.

Run:  python3 theorem_e_equivariant_wedge.py [--nmax N]    (default N = 6)
Self-contained: imports nothing from this repository.
"""
import itertools
import sys
from fractions import Fraction

PRIMES = (2, 3, 5, 7, 2 ** 31 - 1)

# ------------------------------------------------------------------ linear algebra


def rank_mod(rows, p):
    """Rank of a sparse matrix over F_p. rows: list of dicts col->int."""
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
                pivots[c] = {cc: (vv * inv) % p for cc, vv in row.items()}
                r += 1
                break
    return r


def rank_frac(mat):
    m = [[Fraction(x) for x in row] for row in mat]
    rk, col = 0, 0
    ncol = len(m[0]) if m else 0
    while rk < len(m) and col < ncol:
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
        col += 1
    return rk


def nullspace_frac(mat, d):
    """Basis of {x in Q^d : mat x = 0}."""
    m = [[Fraction(x) for x in row] for row in mat]
    piv_cols, rk = [], 0
    for col in range(d):
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        pv = m[rk][col]
        m[rk] = [a / pv for a in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        piv_cols.append(col)
        rk += 1
    free = [c for c in range(d) if c not in piv_cols]
    basis = []
    for fc in free:
        x = [Fraction(0)] * d
        x[fc] = Fraction(1)
        for i, pc in enumerate(piv_cols):
            x[pc] = -m[i][fc]
        basis.append(x)
    return basis


# ------------------------------------------------------------------ order complexes


def chains_of(elems, lt):
    E = list(elems)
    up = {a: [b for b in E if lt(a, b)] for a in E}
    out = [[()]]
    while out[-1]:
        nxt = []
        for c in out[-1]:
            for b in (E if not c else up[c[-1]]):
                nxt.append(c + (b,))
        out.append(nxt)
    out.pop()
    return out  # out[k] = chains with k elements


def reduced_betti(elems, lt, p):
    """Reduced Betti numbers mod p; list indexed by degree -1, 0, 1, ..."""
    ch = chains_of(elems, lt)
    idx = [{c: i for i, c in enumerate(cs)} for cs in ch]
    # boundary from k-element chains to (k-1)-element chains (augmented: k=1 -> empty)
    ranks = [0] * (len(ch) + 1)
    for k in range(1, len(ch)):
        rows = []
        for c in ch[k]:
            row = {}
            for i in range(k):
                face = c[:i] + c[i + 1:]
                row[idx[k - 1][face]] = (-1) ** i
            rows.append(row)
        ranks[k] = rank_mod(rows, p)
    betti = []
    for k in range(len(ch)):  # degree k-1
        betti.append(len(ch[k]) - ranks[k] - ranks[k + 1])
    return betti


def betti_all(elems, lt):
    res = {p: reduced_betti(elems, lt, p) for p in PRIMES}
    vals = list(res.values())
    same = all(v == vals[0] for v in vals)
    return vals[0], same


def stong_core_size(elems, lt):
    E = set(elems)
    changed = True
    while changed and E:
        changed = False
        for x in sorted(E, key=repr):
            below = [y for y in E if lt(y, x)]
            above = [y for y in E if lt(x, y)]
            def has_max(S):
                return any(all(y == m or lt(y, m) for y in S) for m in S)
            def has_min(S):
                return any(all(y == m or lt(m, y) for y in S) for m in S)
            if (below and has_max(below)) or (above and has_min(above)):
                E.remove(x)
                changed = True
                break
    return len(E)


def predicted(m, deg):
    """Reduced Betti vector (index = degree+1) for Z^m in degree deg."""
    if m == 0:
        return None  # acyclic (all zeros, any length)
    v = [0] * (deg + 2)
    v[deg + 1] = m
    return v


def matches(betti, m, deg):
    if m == 0:
        return all(b == 0 for b in betti)
    b = list(betti) + [0] * max(0, deg + 2 - len(betti))
    return all((b[i] == (m if i == deg + 1 else 0)) for i in range(len(b)))


# ------------------------------------------------------------------ groups


def compose(a, b):
    """Signed permutations of hyperplanes as tuples of (target, sign); (a*b)(e) = a(b(e))."""
    return tuple((a[t][0], a[t][1] * s) for (t, s) in b)


def closure(gens, ident):
    G = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = compose(g, x)
                if y not in G:
                    G.add(y)
                    new.append(y)
        frontier = new
    return G


def all_subgroups(G, ident):
    G = list(G)
    cyc = set()
    for g in G:
        cyc.add(frozenset(closure([g], ident)))
    subs = set(cyc)
    frontier = set(cyc)
    while frontier:
        new = set()
        for A in frontier:
            for C in cyc:
                if not C <= A:
                    J = frozenset(closure(list(A | C), ident))
                    if J not in subs:
                        new.add(J)
        subs |= new
        frontier = new
    return subs


def act(g, sigma):
    out = [0] * len(sigma)
    for e, s in enumerate(sigma):
        t, eps = g[e]
        out[t] = eps * s
    return tuple(out)


# ------------------------------------------------------------------ cones


def compose_cov(a, b):
    return tuple(x if x != 0 else y for x, y in zip(a, b))


def conformal_le(f, c):
    return all(x == 0 or x == y for x, y in zip(f, c))


class Cone:
    """A top-cone V given by its chambers, inside the set of all covectors."""

    def __init__(self, covectors, chambers_V):
        self.chambers = set(chambers_V)
        self.faces = {f for f in covectors if any(conformal_le(f, c) for c in self.chambers)}
        m = len(next(iter(self.chambers)))
        self.m = m
        zs = {frozenset(e for e in range(m) if f[e] == 0) for f in self.faces}
        full = frozenset(range(m))
        self.flats = [z for z in zs if z != full and len(z) > 0]  # proper part

    def pointed(self):
        neg = {tuple(-x for x in f) for f in self.faces}
        return all(all(x == 0 for x in f) for f in self.faces & neg)

    @staticmethod
    def lt(a, b):  # flat a < flat b  iff  zero set a strictly contains zero set b
        return a > b


def zact(g, z):
    return frozenset(g[e][0] for e in z)


def analyse(cone, G, ident, fixdim, label, report, want_core=True, check_full=True):
    """For every subgroup H of G compare T^H with prediction (S). Returns list of rows."""
    rows = []
    subs = all_subgroups(G, ident)
    for H in sorted(subs, key=len):
        Hl = list(H)
        elems = [z for z in cone.flats if all(zact(h, z) == z for h in Hl)]
        mH = sum(1 for c in cone.chambers if all(act(h, c) == c for h in Hl))
        eH = fixdim(Hl)
        if len(H) == 1 and not check_full:
            rows.append((len(H), mH, eH, None, None, None, None))
            continue
        b, same = betti_all(elems, Cone.lt)
        ok = same and matches(b, mH, eH - 2)
        core = None
        if want_core and mH == 0 and len(H) > 1:
            core = stong_core_size(elems, Cone.lt)
        rows.append((len(H), mH, eH, b, ok, core, len(elems)))
    return rows


# ------------------------------------------------------------------ arrangements


def covectors_from_normals(normals):
    d = len(normals[0])
    m = len(normals)
    rays = set()
    for S in itertools.combinations(range(m), d - 1):
        mat = [normals[i] for i in S]
        if rank_frac(mat) != d - 1:
            continue
        (v,) = nullspace_frac(mat, d)
        for sgn in (1, -1):
            x = [sgn * t for t in v]
            sv = tuple((lambda s: (s > 0) - (s < 0))(sum(a * b for a, b in zip(n, x))) for n in normals)
            rays.add(sv)
    cov = {tuple([0] * m)} | rays
    frontier = set(rays)
    while frontier:
        new = set()
        for a in frontier:
            for r in rays:
                c = compose_cov(a, r)
                if c not in cov:
                    new.add(c)
        cov |= new
        frontier = new
    return cov


def signed_perm_matrices(d):
    for perm in itertools.permutations(range(d)):
        for signs in itertools.product((1, -1), repeat=d):
            M = [[0] * d for _ in range(d)]
            for i in range(d):
                M[perm[i]][i] = signs[i]
            yield M


def matvec(M, x):
    return [sum(M[i][j] * x[j] for j in range(len(x))) for i in range(len(M))]


def hyperplane_action(M, normals):
    """Signed permutation of hyperplanes induced by x -> Mx (normal n -> n M^{-1}).
    For signed permutation matrices M^{-1} = M^T."""
    MT = [list(r) for r in zip(*M)]
    out = []
    for n in normals:
        nn = matvec(M, n)  # (n M^T)^T = M n  since M^{-1} = M^T
        found = None
        for t, q in enumerate(normals):
            if list(q) == nn:
                found = (t, 1)
            elif [-a for a in q] == nn:
                found = (t, -1)
        if found is None:
            return None
        out.append(found)
    return tuple(out)


def general_case(name, normals, d, report, max_cones=None, only_pointed=True):
    cov = covectors_from_normals(normals)
    m = len(normals)
    chambers = [c for c in cov if 0 not in c]
    # linear group: signed permutation matrices preserving A
    mats = {}
    for M in signed_perm_matrices(d):
        g = hyperplane_action(M, normals)
        if g is not None:
            mats[g] = M
    ident = tuple((e, 1) for e in range(m))

    def fixdim_of(Hl):
        rows = []
        for h in Hl:
            M = mats[h]
            rows += [[M[i][j] - (1 if i == j else 0) for j in range(d)] for i in range(d)]
        return d - rank_frac(rows)

    # top-cones: sign conditions on a subset S of hyperplanes
    cones = {}
    for c in chambers:
        for k in range(m + 1):
            for S in itertools.combinations(range(m), k):
                key = frozenset((e, c[e]) for e in S)
                if key in cones:
                    continue
                V = frozenset(cc for cc in chambers if all(cc[e] == s for e, s in key))
                cones[key] = V
    distinct = set(cones.values())
    stats = dict(cones=0, pairs=0, ok=0, free_nontriv=0, core_ok=0, nonfree=0, emptyG=0)
    for V in sorted(distinct, key=lambda v: (len(v), sorted(v))):
        cone = Cone(cov, V)
        if only_pointed and not cone.pointed():
            continue
        stab = [g for g in mats if frozenset(act(g, c) for c in V) == V]
        if len(stab) == 1:
            continue
        stats["cones"] += 1
        rows = analyse(cone, set(stab), ident, fixdim_of, name, report)
        for (order, mH, eH, b, ok, core, ne) in rows:
            stats["pairs"] += 1
            stats["ok"] += ok
            if order > 1 and mH == 0:
                stats["free_nontriv"] += 1
                stats["core_ok"] += (core == 1)
            if order > 1 and mH > 0:
                stats["nonfree"] += 1
                if ne == 0:
                    stats["emptyG"] += 1
        if max_cones and stats["cones"] >= max_cones:
            break
    report(f"[GEN] {name}: pointed cones with nontrivial stabilizer = {stats['cones']}, "
           f"(cone, subgroup) pairs = {stats['pairs']}, prediction (S) holds on {stats['ok']}; "
           f"H != 1 fixing no chamber: {stats['free_nontriv']} pairs, Stong core = 1 point on "
           f"{stats['core_ok']}; H != 1 fixing a chamber: {stats['nonfree']} pairs, "
           f"of which T^H empty: {stats['emptyG']}")
    return stats["ok"] == stats["pairs"] and stats["core_ok"] == stats["free_nontriv"], stats


# ------------------------------------------------------------------ type A


def ordered_set_partitions(n):
    def rec(rest):
        if not rest:
            yield []
            return
        rest = list(rest)
        first_choices = []
        for k in range(1, len(rest) + 1):
            for B in itertools.combinations(rest, k):
                rem = [x for x in rest if x not in B]
                for tail in rec(rem):
                    yield [frozenset(B)] + tail
    yield from rec(range(n))


def braid_data(n):
    pairs = list(itertools.combinations(range(n), 2))
    pidx = {p: i for i, p in enumerate(pairs)}
    cov = set()
    for op in ordered_set_partitions(n):
        pos = {}
        for b, B in enumerate(op):
            for x in B:
                pos[x] = b
        cov.add(tuple((pos[j] > pos[i]) - (pos[j] < pos[i]) for (i, j) in pairs))
    return pairs, pidx, cov


def perm_action(w, pairs, pidx):
    out = []
    for (i, j) in pairs:
        a, b = w[i], w[j]
        if a < b:
            out.append((pidx[(a, b)], 1))
        else:
            out.append((pidx[(b, a)], -1))
    return tuple(out)


def posets_up_to_iso(n):
    """All posets on n points up to isomorphism, as sets of strict relations (i,j), i<_P j."""
    res = [frozenset()] if n == 0 else None
    if n == 0:
        return res
    prev = posets_up_to_iso(n - 1)
    out = []
    seen = {}
    for R in prev:
        # add new maximal element n-1 above an order ideal (down-set) D of R
        elems = range(n - 1)
        for k in range(n):
            for D in itertools.combinations(elems, k):
                Ds = set(D)
                if any((a, b) in R and b in Ds and a not in Ds for a in elems for b in elems):
                    continue
                newR = frozenset(R | {(a, n - 1) for a in Ds})
                key = invariant(newR, n)
                bucket = seen.setdefault(key, [])
                if any(isomorphic(newR, S, n) for S in bucket):
                    continue
                bucket.append(newR)
                out.append(newR)
    return out


def invariant(R, n):
    down = [sum(1 for a in range(n) if (a, x) in R) for x in range(n)]
    up = [sum(1 for b in range(n) if (x, b) in R) for x in range(n)]
    return tuple(sorted(zip(down, up)))


def isomorphic(R, S, n):
    for w in itertools.permutations(range(n)):
        if all(((w[a], w[b]) in S) for (a, b) in R) and len(R) == len(S):
            return True
    return False


def automorphisms(R, n):
    return [w for w in itertools.permutations(range(n))
            if all(((w[a], w[b]) in R) for (a, b) in R)]


def connected(R, n):
    adj = {x: set() for x in range(n)}
    for a, b in R:
        adj[a].add(b)
        adj[b].add(a)
    seen, st = {0}, [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == n


def poset_cone(R, n, braid):
    pairs, pidx, cov = braid
    chambers = [c for c in cov if 0 not in c]
    V = []
    for c in chambers:
        # c[pidx(i,j)] = sign(x_j - x_i); need x_a < x_b for a <_P b
        if all((c[pidx[(a, b)]] == 1) if a < b else (c[pidx[(b, a)]] == -1) for (a, b) in R):
            V.append(c)
    return Cone(cov, V)


def braid_fixdim(Hperms, n):
    # dim Fix(H) in R^n / R1 = (#orbits of H on [n]) - 1
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for w in Hperms:
        for i in range(n):
            a, b = find(i), find(w[i])
            if a != b:
                parent[a] = b
    return len({find(i) for i in range(n)}) - 1


def type_a(nmax, report):
    allok = True
    tot = dict(posets=0, pairs=0, ok=0, core=0, nontriv=0, skipped=0)
    for n in range(4, nmax + 1):
        braid = braid_data(n)
        pairs, pidx, _ = braid
        ident = tuple((e, 1) for e in range(len(pairs)))
        cnt = 0
        for R in posets_up_to_iso(n):
            if not connected(R, n):
                continue
            auts = automorphisms(R, n)
            if len(auts) == 1:
                continue
            cone = poset_cone(R, n, braid)
            assert cone.pointed()
            g_of = {perm_action(w, pairs, pidx): w for w in auts}
            G = set(g_of)
            # free action on chambers (Lin P): check directly
            free = all(all(act(g, c) != c for c in cone.chambers) for g in G if g != ident)
            assert free
            fd = lambda Hl: braid_fixdim([g_of[h] for h in Hl], n)
            big = n >= 6 and len(cone.chambers) > 40
            rows = analyse(cone, G, ident, fd, "A", report, check_full=not big)
            cnt += 1
            for (order, mH, eH, b, ok, core, ne) in rows:
                if ok is None:
                    tot["skipped"] += 1
                    continue
                tot["pairs"] += 1
                tot["ok"] += ok
                if order > 1:
                    tot["nontriv"] += 1
                    tot["core"] += (core == 1)
            rel = sorted(R)
            report(f"[POS] n={n} P={rel} |Aut|={len(auts)} |Lin P|={len(cone.chambers)} "
                   f"subgroups={len(rows)} all-match={all(r[4] for r in rows if r[4] is not None)} "
                   f"cores={[r[5] for r in rows if r[0] > 1]}"
                   + (" (H=1 not recomputed: Theorem 1)" if big else ""))
        tot["posets"] += cnt
    allok = tot["ok"] == tot["pairs"] and tot["core"] == tot["nontriv"]
    report(f"[POS] summary: connected posets with |Aut|>1, 4<=n<={nmax}: {tot['posets']}; "
           f"(P, H) pairs computed {tot['pairs']}, prediction holds on {tot['ok']} "
           f"(H = 1 skipped on {tot['skipped']} large cases); H != 1: "
           f"{tot['nontriv']} pairs, all acyclic over the test fields, Stong core one point "
           f"on {tot['core']}")
    return allok


# ------------------------------------------------------------------ controls


def controls(report):
    ok = True
    # Boolean B_3 proper part: hexagon
    B3 = [frozenset(s) for k in (1, 2) for s in itertools.combinations(range(3), k)]
    b, _ = betti_all(B3, lambda a, c: a < c)
    ok &= b == [0, 0, 1]
    crown = ["a", "b", "c", "x", "y", "z"]
    rel = {("a", "x"), ("a", "y"), ("b", "y"), ("b", "z"), ("c", "z"), ("c", "x")}
    lt = lambda u, v: (u, v) in rel
    b2, _ = betti_all(crown, lt)
    ok &= b2 == [0, 0, 1] and stong_core_size(crown, lt) == 6
    chain = [0, 1, 2, 3]
    b3, _ = betti_all(chain, lambda u, v: u < v)
    ok &= all(x == 0 for x in b3) and stong_core_size(chain, lambda u, v: u < v) == 1
    report(f"[CTL] B_3 proper part betti {b}, crown betti {b2} core 6, chain acyclic core 1: {ok}")
    return ok


def negatives(report):
    ok = True
    # (1) orthant of R^d, symmetric group S_d (one chamber, fixed by all of G).
    for d in (3, 4):
        normals = [[1 if j == i else 0 for j in range(d)] for i in range(d)]
        cov = covectors_from_normals(normals)
        V = [tuple([1] * d)]
        cone = Cone(cov, V)
        ident = tuple((e, 1) for e in range(d))
        G = set()
        mats = {}
        for w in itertools.permutations(range(d)):
            g = tuple((w[e], 1) for e in range(d))
            G.add(g)
            mats[g] = w
        TG = [z for z in cone.flats if all(zact(h, z) == z for h in G)]
        ok &= len(TG) == 0
        # trivial-action permutation-wedge prediction: Z^{m_H} in degree d-2
        fails = 0
        for H in all_subgroups(G, ident):
            elems = [z for z in cone.flats if all(zact(h, z) == z for h in H)]
            mH = 1
            b, _ = betti_all(elems, Cone.lt)
            if not matches(b, mH, d - 2):
                fails += 1
        ok &= fails > 0
        tH = None
        if d == 3:
            H2 = frozenset(closure([((1, 1), (0, 1), (2, 1))], ident))
            elems = [z for z in cone.flats if all(zact(h, z) == z for h in H2)]
            tH, _ = betti_all(elems, Cone.lt)
            ok &= tH == [0, 1]   # S^0
        report(f"[NEG] orthant of R^{d}, G=S_{d}: T^G empty = {len(TG) == 0}; trivial-action "
               f"wedge prediction fails on {fails} subgroups"
               + (f"; T^<(12)> betti {tH} (= S^0)" if tH is not None else ""))
    # (2) non-pointed, free on chambers: Pi_4 with S_4
    n = 4
    pairs, pidx, cov = braid_data(n)
    chambers = [c for c in cov if 0 not in c]
    cone = Cone(cov, chambers)
    ident = tuple((e, 1) for e in range(len(pairs)))
    G = {perm_action(w, pairs, pidx) for w in itertools.permutations(range(n))}
    bad = []
    for H in sorted(all_subgroups(G, ident), key=len):
        if len(H) == 1:
            continue
        elems = [z for z in cone.flats if all(zact(h, z) == z for h in H)]
        b, _ = betti_all(elems, Cone.lt)
        if any(b):
            bad.append((len(H), b))
    ok &= len(bad) > 0
    report(f"[NEG] Pi_4 (all chambers of A_3, not pointed), G=S_4 free on chambers: "
           f"{len(bad)} subgroups H != 1 with T^H not acyclic, e.g. {bad[:3]}")
    # (3) P = two 2-chains, swap: free on Lin P, cone not pointed
    R = frozenset({(0, 1), (2, 3)})
    pairs, pidx, cov = braid_data(4)
    cone = poset_cone(R, 4, (pairs, pidx, cov))
    sw = perm_action((2, 3, 0, 1), pairs, pidx)
    ident = tuple((e, 1) for e in range(len(pairs)))
    free = all(act(sw, c) != c for c in cone.chambers)
    elems = [z for z in cone.flats if zact(sw, z) == z]
    b, _ = betti_all(elems, Cone.lt)
    ball, _ = betti_all(cone.flats, Cone.lt)
    ok &= free and (not cone.pointed()) and any(b)
    report(f"[NEG] P = 2-chain + 2-chain, swap: free on Lin P = {free}, pointed = {cone.pointed()}, "
           f"|Lin P| = {len(cone.chambers)}, T betti {ball}, T^swap betti {b} (not acyclic)")
    return ok


def wrong_prediction_fails(report):
    """Degree e_H - 1 instead of e_H - 2 must fail somewhere (instrument sanity)."""
    d = 3
    normals = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    cov = covectors_from_normals(normals)
    cone = Cone(cov, [(1, 1, 1)])
    b, _ = betti_all(cone.flats, Cone.lt)
    r = not matches(b, 1, d - 1) and matches(b, 1, d - 2)
    report(f"[NEG] wrong degree (e_H - 1) rejected on the orthant of R^3: {r}")
    return r


def main():
    nmax = 6
    if "--nmax" in sys.argv:
        nmax = int(sys.argv[sys.argv.index("--nmax") + 1])
    out = []
    def report(s):
        print(s, flush=True)
        out.append(s)
    ok = controls(report)
    ok &= wrong_prediction_fails(report)
    ok &= negatives(report)
    for d in (3, 4):
        normals = [[1 if j == i else 0 for j in range(d)] for i in range(d)]
        r, _ = general_case(f"Boolean R^{d}", normals, d, report)
        ok &= r
    B3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, -1, 0], [1, 0, 1], [1, 0, -1],
          [0, 1, 1], [0, 1, -1]]
    r, _ = general_case("B_3", B3, 3, report)
    ok &= r
    ok &= type_a(nmax, report)
    report(f"ALL CHECKS PASS: {ok}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
