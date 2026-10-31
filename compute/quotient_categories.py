#!/usr/bin/env python3
"""Checks for notes/quotient_categories.md (quotient categories and wedges of spheres).

Parts (each prints lines tagged as below; the run ends "ALL CHECKS PASS: True"):
  [CTL]  instrument controls: Boolean B_3 proper part = S^1, a chain is acyclic,
         and the torsion detector fires on a known torsion complex (RP^2, 6 vertices).
  [MIX]  mixed graphs (graph G with some edges oriented, acyclically). The cone V of the
         graphic arrangement A_G cut out by the oriented edges. Lambda(V) computed
         geometrically (spans of faces, from weak orders = value patterns) equals the
         combinatorial set "connected partitions whose quotient digraph is acyclic";
         reduced homology of its proper part is concentrated in degree rank-2 with rank
         m(V) = |mu|; and for pointed V, m(V) = #V = number of acyclic orientations of G
         extending the given orientation.
  [FIX]  posets, cyclic H = <g> <= Aut(P): the H-stable faces of the order cone C_P are
         in bijection with the faces of the cone of the orbit quotient P//H (pullback).
  [DDIV] d-divisible partition lattices: the support map from the rank-selected Coxeter
         complex K (ordered partitions with all blocks of size divisible by d) to the
         proper part Q of Pi_n^{(d)} + 0. Checks: Q and K have homology concentrated in
         degree n/d - 2; rank H(K) = beta_n(S), rank H(Q) = beta_{n-1}(S) (descent
         counts); the fiber-theorem Euler identity holds.
  [NEG]  negative control: the lattice of "at most 2-to-1" quotients of a 7-set
         (matchings + top) has 3-torsion in H_1 of its proper part, so it is not a wedge
         of spheres; and it fails the upper-interval (composition) axiom.
  [GSET] G-sets: quotient lattices of G/1 = subgroup lattices, for A_4, S_4, A_5:
         Betti numbers of the proper part (A_4: homology in degree 0 of a 1-dim complex,
         so not Cohen-Macaulay).
  [NC]   noncrossing partitions: for n = 4, 5, 6, is NC(n) equal to OP(P) as a set of
         partitions, for some labeled poset P on [n]? And does any OP(P) share
         NC(n)'s size, rank sizes and Moebius number (a necessary condition for
         isomorphism)?

Homology: reduced Betti numbers modulo primes (no integral Smith form). A difference
between the mod-2 and mod-3 Betti numbers certifies torsion.

Run:  python3 quotient_categories.py [--quick]
Plain Python 3, single process, imports nothing from this repository.
"""
import itertools
import random
import sys

P_BIG = 2 ** 31 - 1

# ------------------------------------------------------------------ linear algebra


def rank_mod(rows, p):
    """Rank over F_p of a sparse matrix given as a list of dicts col -> int."""
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


def reduced_betti(simplices, p):
    """Reduced Betti numbers mod p of a simplicial complex.

    simplices: iterable of tuples (vertices sorted), closed under faces, nonempty
    faces only. Returns dict degree -> betti, degree -1 included (empty complex)."""
    by_dim = {}
    for s in simplices:
        by_dim.setdefault(len(s) - 1, []).append(s)
    if not by_dim:
        return {-1: 1}
    top = max(by_dim)
    index = {d: {s: i for i, s in enumerate(sorted(by_dim.get(d, [])))}
             for d in range(-1, top + 1)}
    index[-1] = {(): 0}
    ranks = {}
    for d in range(0, top + 1):
        rows = []
        for s in by_dim.get(d, []):
            row = {}
            for i in range(len(s)):
                f = s[:i] + s[i + 1:]
                row[index[d - 1][f]] = (-1) ** i
            rows.append(row)
        ranks[d] = rank_mod(rows, p)
    betti = {}
    for d in range(-1, top + 1):
        n_d = len(index[d])
        betti[d] = n_d - ranks.get(d, 0) - ranks.get(d + 1, 0)
    return {d: b for d, b in betti.items() if b}


def order_complex(elems, lt):
    """All nonempty chains (as sorted index tuples) of the poset (elems, lt)."""
    n = len(elems)
    up = [[j for j in range(n) if lt(elems[i], elems[j])] for i in range(n)]
    out = []

    def ext(chain):
        out.append(tuple(sorted(chain)))
        for j in up[chain[-1]]:
            ext(chain + [j])
    for i in range(n):
        ext([i])
    return out


def mobius_bottom_top(elems, lt, bot, top):
    """mu(bot, top) in the poset elems (bot, top in elems)."""
    order = sorted(elems, key=lambda e: sum(1 for f in elems if lt(f, e)))
    mu = {}
    for e in order:
        if e == bot:
            mu[e] = 1
        elif lt(bot, e):
            mu[e] = -sum(mu[f] for f in order if f in mu and (f == bot or lt(bot, f))
                         and lt(f, e))
    return mu[top]


def betti_of_poset(elems, lt, primes=(2, P_BIG)):
    cx = order_complex(elems, lt)
    return {p: reduced_betti(cx, p) for p in primes}


# ------------------------------------------------------------------ partitions


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


def canon(p):
    return frozenset(frozenset(b) for b in p)


def refines(a, b):
    """a finer than or equal to b (every block of a inside a block of b)."""
    return all(any(x <= y for y in b) for x in a)


def has_cycle(nodes, arcs):
    adj = {v: set() for v in nodes}
    for u, v in arcs:
        if u == v:
            continue
        adj[u].add(v)
    color = {v: 0 for v in nodes}

    def dfs(u):
        color[u] = 1
        for w in adj[u]:
            if color[w] == 1:
                return True
            if color[w] == 0 and dfs(w):
                return True
        color[u] = 2
        return False
    return any(color[v] == 0 and dfs(v) for v in nodes)


def components(n, edges):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for u, v in edges:
        parent[find(u)] = find(v)
    comp = {}
    for x in range(n):
        comp.setdefault(find(x), set()).add(x)
    return canon(comp.values())


def weak_orders(n):
    """All surjections [n] -> {0..k-1} (ordered set partitions), as tuples."""
    for k in range(1, n + 1):
        for f in itertools.product(range(k), repeat=n):
            if len(set(f)) == k:
                yield f


# ------------------------------------------------------------------ [CTL]


def part_ctl(out):
    ok = True
    # Boolean B_3 proper part: 6 nonempty proper subsets, a hexagon = S^1.
    subs = [frozenset(s) for r in (1, 2) for s in itertools.combinations(range(3), r)]
    b = betti_of_poset(subs, lambda a, c: a < c)
    good = all(v == {1: 1} for v in b.values())
    out.append(f"[CTL] B_3 proper part Betti {b[2]} (expect {{1: 1}}): {good}")
    ok &= good
    chain = [1, 2, 3]
    b = betti_of_poset(chain, lambda a, c: a < c)
    good = all(v == {} for v in b.values())
    out.append(f"[CTL] 3-chain acyclic: {good}")
    ok &= good
    # RP^2 (6-vertex triangulation): H_1 = Z/2, so mod 2 and mod 3 differ.
    faces = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5), (1, 2, 4),
             (2, 3, 5), (1, 3, 4), (1, 3, 5), (2, 4, 5)]
    cx = set()
    for f in faces:
        for r in range(1, 4):
            for s in itertools.combinations(f, r):
                cx.add(s)
    b2, b3 = reduced_betti(cx, 2), reduced_betti(cx, 3)
    good = b2 == {1: 1, 2: 1} and b3 == {}
    out.append(f"[CTL] RP^2 torsion detector: mod2 {b2}, mod3 {b3}: {good}")
    ok &= good
    return ok


# ------------------------------------------------------------------ [MIX]


def mixed_lambda_geometric(n, edges, arcs):
    """Spans of faces of the closed cone {x_i <= x_j for arcs (i,j)} in A_G."""
    flats = set()
    for x in weak_orders(n):
        if all(x[i] <= x[j] for i, j in arcs):
            eq = [(i, j) for i, j in edges if x[i] == x[j]]
            flats.add(components(n, eq))
    return flats


def mixed_lambda_combinatorial(n, edges, arcs):
    res = set()
    for p in set_partitions(range(n)):
        p = canon(p)
        # blocks connected in G
        if any(components(n, [(i, j) for i, j in edges if i in B and j in B])
               != canon([B] + [{x} for x in range(n) if x not in B])
               for B in p):
            continue
        blk = {x: B for B in p for x in B}
        if has_cycle(list(p), [(blk[i], blk[j]) for i, j in arcs if blk[i] != blk[j]]):
            continue
        res.add(p)
    return res


def chambers_extending(n, edges, arcs):
    """Acyclic orientations of G extending the arcs; returns list of arc-sets."""
    und = [e for e in edges if e not in arcs and (e[1], e[0]) not in arcs]
    res = []
    for bits in itertools.product((0, 1), repeat=len(und)):
        o = list(arcs) + [(i, j) if b == 0 else (j, i) for (i, j), b in zip(und, bits)]
        if not has_cycle(range(n), o):
            res.append(frozenset(o))
    return res


def check_mixed(n, edges, arcs):
    geo = mixed_lambda_geometric(n, edges, arcs)
    comb = mixed_lambda_combinatorial(n, edges, arcs)
    if geo != comb:
        return False, "lambda mismatch", None
    bot = components(n, edges)
    top = canon([{x} for x in range(n)])
    d = n - len(bot)
    lt = lambda a, b: a != b and refines(b, a)   # coarser < finer
    elems = sorted(geo, key=lambda p: (len(p), sorted(map(sorted, p))))
    mu = mobius_bottom_top(elems, lt, bot, top) if bot != top else 1
    m = (-1) ** d * mu
    proper = [e for e in elems if e not in (bot, top)]
    if d >= 2:
        bet = betti_of_poset(proper, lt)
        want = {d - 2: m} if m else {}
        if any(b != want for b in bet.values()):
            return False, f"homology {bet} want {want}", None
    if m < 1:
        return False, f"m = {m} < 1", None
    ch = chambers_extending(n, edges, arcs)
    smax = [e for e in edges
            if len({(e in c) for c in ch}) == 1]  # orientation constant on V
    pointed = components(n, smax) == bot
    if pointed and len(ch) != m:
        return False, f"pointed but #V={len(ch)} != m={m}", None
    return True, "", (pointed, m, len(ch))


def part_mix(out, quick):
    ok = True
    stats = {"configs": 0, "pointed": 0, "nonpointed_strict": 0}
    rng = random.Random(20261031)
    for n in (2, 3, 4, 5):
        pairs = list(itertools.combinations(range(n), 2))
        configs = []
        if n <= 4:
            for mask in range(1 << len(pairs)):
                edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
                for st in itertools.product((0, 1, 2), repeat=len(edges)):
                    arcs = [e if s == 1 else (e[1], e[0])
                            for e, s in zip(edges, st) if s]
                    configs.append((edges, arcs))
        else:
            for _ in range(60 if quick else 250):
                edges = [e for e in pairs if rng.random() < 0.6]
                arcs = [e if rng.random() < 0.5 else (e[1], e[0])
                        for e in edges if rng.random() < 0.5]
                configs.append((edges, arcs))
        for edges, arcs in configs:
            if has_cycle(range(n), arcs):
                continue
            good, why, info = check_mixed(n, edges, arcs)
            stats["configs"] += 1
            if not good:
                ok = False
                out.append(f"[MIX] FAIL n={n} edges={edges} arcs={arcs}: {why}")
                continue
            pointed, m, nv = info
            stats["pointed"] += pointed
            stats["nonpointed_strict"] += (not pointed and m < nv)
    out.append(f"[MIX] {stats['configs']} mixed graphs (n<=4 exhaustive, n=5 seeded "
               f"sample): Lambda_geo = Lambda_comb, homology concentrated, rank m>=1; "
               f"{stats['pointed']} pointed with #V = m; {stats['nonpointed_strict']} "
               f"non-pointed with m < #V: {ok}")
    # control: drop the connectivity requirement -> some mismatch must appear
    n, edges, arcs = 3, [(0, 1)], []
    loose = set(canon(p) for p in set_partitions(range(n)))
    ctl = loose != mixed_lambda_geometric(n, edges, arcs)
    out.append(f"[MIX] control: all partitions != Lambda for G = one edge on 3 vertices: "
               f"{ctl}")
    return ok and ctl


# ------------------------------------------------------------------ posets


def natural_posets(n):
    """Naturally labeled posets on [n] as sets of strict relations (i, j), i < j."""
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        rel = {pairs[i] for i in range(len(pairs)) if mask >> i & 1}
        if all((a, c) in rel for (a, b) in rel for (b2, c) in rel if b == b2):
            yield frozenset(rel)


def all_labeled_posets(n):
    seen = set()
    for rel in natural_posets(n):
        for perm in itertools.permutations(range(n)):
            r = frozenset((perm[a], perm[b]) for a, b in rel)
            if r not in seen:
                seen.add(r)
                yield r


def op_lattice(n, rel):
    res = []
    for p in set_partitions(range(n)):
        blk = {x: i for i, B in enumerate(p) for x in B}
        if not has_cycle(range(len(p)), [(blk[a], blk[b]) for a, b in rel
                                          if blk[a] != blk[b]]):
            res.append(canon(p))
    return res


def automorphisms(n, rel):
    return [g for g in itertools.permutations(range(n))
            if frozenset((g[a], g[b]) for a, b in rel) == rel]


def cone_faces(n, rel):
    """Faces of the closed order cone: weak orders f with a<b => f(a) <= f(b)."""
    return [f for f in weak_orders(n) if all(f[a] <= f[b] for a, b in rel)]


def orbit_quotient_classes(n, rel, g):
    """Classes of P//<g>: orbits, then strongly connected components of the orbit
    preorder. Returns (list of classes, relation on class indices)."""
    orb = components(n, [(x, g[x]) for x in range(n)])
    orb = list(orb)
    oi = {x: i for i, O in enumerate(orb) for x in O}
    arcs = {(oi[a], oi[b]) for a, b in rel if oi[a] != oi[b]}
    k = len(orb)
    reach = [[i == j for j in range(k)] for i in range(k)]
    for a, b in arcs:
        reach[a][b] = True
    for m in range(k):
        for i in range(k):
            for j in range(k):
                if reach[i][m] and reach[m][j]:
                    reach[i][j] = True
    scc = components(k, [(i, j) for i in range(k) for j in range(k)
                         if reach[i][j] and reach[j][i] and i != j])
    scc = list(scc)
    si = {i: c for c, S in enumerate(scc) for i in S}
    classes = [frozenset(x for i in S for x in orb[i]) for S in scc]
    crel = {(si[a], si[b]) for a, b in arcs if si[a] != si[b]}
    return classes, crel


def part_fix(out, nmax):
    ok = True
    pairs_checked = merged = ctl_fired = ctl_tried = 0
    for n in range(2, nmax + 1):
        for rel in natural_posets(n):
            faces = cone_faces(n, rel)
            for g in automorphisms(n, rel):
                if all(g[x] == x for x in range(n)):
                    continue
                stable = [f for f in faces if all(f[g[x]] == f[x] for x in range(n))]
                classes, crel = orbit_quotient_classes(n, rel, g)
                qf = cone_faces(len(classes), crel)
                pulled = set()
                for h in qf:
                    f = [None] * n
                    for c, C in enumerate(classes):
                        for x in C:
                            f[x] = h[c]
                    pulled.add(tuple(f))
                pairs_checked += 1
                if pulled != set(stable):
                    ok = False
                    out.append(f"[FIX] FAIL n={n} rel={sorted(rel)} g={g}")
                n_orbits = len(components(n, [(x, g[x]) for x in range(n)]))
                merged += len(classes) != n_orbits
                # control: a wrong quotient (orbits of g^2 instead of g) must fail
                # whenever g^2 has strictly more orbits than g
                g2 = tuple(g[g[x]] for x in range(n))
                if len(components(n, [(x, g2[x]) for x in range(n)])) > n_orbits:
                    c2, r2 = orbit_quotient_classes(n, rel, g2)
                    wrong = set()
                    for h in cone_faces(len(c2), r2):
                        f = [None] * n
                        for c, C in enumerate(c2):
                            for x in C:
                                f[x] = h[c]
                        wrong.add(tuple(f))
                    ctl_fired += wrong != set(stable)
                    ctl_tried += 1
    out.append(f"[FIX] {pairs_checked} (P, g != 1) pairs, n <= {nmax}: H-stable faces of "
               f"C_P = pullbacks of faces of C_(P/H): {ok}; orbit preorder ever cyclic: "
               f"{merged} times (expect 0)")
    ctl = ctl_tried > 0 and ctl_fired == ctl_tried
    out.append(f"[FIX] control: quotient by <g^2> instead of <g> rejected on "
               f"{ctl_fired}/{ctl_tried} pairs: {ctl}")
    return ok and ctl and merged == 0


# ------------------------------------------------------------------ [DDIV]


def beta_descent(n, S):
    S = set(S)
    c = 0
    for w in itertools.permutations(range(n)):
        if {i + 1 for i in range(n - 1) if w[i] > w[i + 1]} == S:
            c += 1
    return c


def part_ddiv(out, cases):
    ok = True
    for n, d in cases:
        S = list(range(d, n, d))
        top_deg = n // d - 2
        # Q: d-divisible partitions with >= 2 blocks; order coarser < finer
        Q = [canon(p) for p in set_partitions(range(n))
             if all(len(B) % d == 0 for B in p) and len(p) >= 2]
        lt = lambda a, b: a != b and refines(b, a)
        bQ = betti_of_poset(Q, lt)
        # K: rank-selected Boolean lattice at ranks S (= rank-selected Coxeter complex)
        Kv = [frozenset(s) for r in S for s in itertools.combinations(range(n), r)]
        bK = betti_of_poset(Kv, lambda a, b: a < b)
        bn, bn1 = beta_descent(n, S), beta_descent(n - 1, S)
        cQ = all(v == {top_deg: bn1} for v in bQ.values())
        cK = all(v == {top_deg: bn} for v in bK.values())
        # Euler identity of the fiber theorem: chi(K) = chi(Q) + sum_pi -chi(S^{k-2})chi(Q>pi)
        chiQ = (-1) ** top_deg * bn1
        chiK = (-1) ** top_deg * bn
        tot = chiQ
        for pi in Q:
            k = len(pi)
            above = [s for s in Q if lt(pi, s)]
            if above:
                b = betti_of_poset(above, lt, primes=(P_BIG,))[P_BIG]
                chi_up = sum((-1) ** dd * v for dd, v in b.items())
            else:
                chi_up = -1  # empty complex
            tot += -((-1) ** (k - 2)) * chi_up
        cE = tot == chiK
        # Pointed version (dual claw T: n above everything; OP(T) = Pi_n). Faces of
        # C_T in the rank selection: ordered d-divisible partitions with n in the last
        # block, = chains in B_{n-1} with sizes in S. Its homology must be beta_{n-1}(S),
        # and every Quillen fiber (faces whose support is coarser than or equal to pi)
        # must be acyclic.
        Kp = [frozenset(s) for r in S for s in itertools.combinations(range(n - 1), r)]
        bKp = betti_of_poset(Kp, lambda a, b: a < b, primes=(P_BIG,))[P_BIG]
        cKp = bKp == {top_deg: bn1}
        faces_p = []
        for p in Q:
            for order in itertools.permutations(sorted(p, key=sorted)):
                if (n - 1) in order[-1]:
                    faces_p.append(order)
        def chain_of(F):
            return frozenset(frozenset().union(*F[:i]) for i in range(1, len(F)))
        face_lt = lambda a, b: chain_of(a) < chain_of(b)
        fib_ok = True
        for pi in Q:
            fib = [F for F in faces_p if refines(pi, canon(F))]
            b = betti_of_poset(fib, face_lt, primes=(P_BIG,))[P_BIG]
            fib_ok &= b == {}
        # control: without pointing (n anywhere), the fiber over a 2-block pi is S^0
        pi2 = next(p for p in Q if len(p) == 2)
        unp = [o for o in itertools.permutations(sorted(pi2, key=sorted))]
        b_unp = betti_of_poset(unp, face_lt, primes=(P_BIG,))[P_BIG]
        fib_ok &= b_unp == {0: 1}
        good = cQ and cK and cE and cKp and fib_ok
        ok &= good
        out.append(f"[DDIV] n={n} d={d}: |Q|={len(Q)} H(Q)={bQ[P_BIG]} "
                   f"beta_(n-1)(S)={bn1}; pointed companion H={bKp}, all {len(Q)} Quillen "
                   f"fibers acyclic: {fib_ok}; unpointed H(K)={bK[P_BIG]} beta_n(S)={bn}, "
                   f"fiber Euler identity {tot}=={chiK}: {good}")
    return ok


# ------------------------------------------------------------------ [NEG]


def part_neg(out):
    n = 7
    edges = list(itertools.combinations(range(n), 2))
    matchings = []
    for r in (1, 2, 3):
        for s in itertools.combinations(edges, r):
            if len({x for e in s for x in e}) == 2 * r:
                matchings.append(frozenset(s))
    lt = lambda a, b: a < b
    cx = order_complex(matchings, lt)
    b2, b3, bp = (reduced_betti(cx, p) for p in (2, 3, P_BIG))
    torsion = b2 != b3
    out.append(f"[NEG] at-most-2-to-1 quotients of a 7-set: proper part Betti mod 2 {b2}, "
               f"mod 3 {b3}, mod 2^31-1 {bp}; torsion detected: {torsion}")
    # upper-interval axiom: [pi, 1] vs Q(X/pi) for pi = one 2-block
    pi = frozenset({(0, 1)})
    up = sum(1 for m in matchings if pi <= m) + 1          # elements >= pi, plus top
    # quotients of the 6-point set X/pi with fibers of size <= 2 (as a set): all
    # matchings of K_6, the empty one, and a top
    k6 = 1 + sum(1 for r in (1, 2, 3)
                 for s in itertools.combinations(list(itertools.combinations(range(6), 2)), r)
                 if len({x for e in s for x in e}) == 2 * r) + 1
    fails = up != k6
    out.append(f"[NEG] upper interval [pi,1] has {up} elements, Q(X/pi) has {k6}: "
               f"axiom (Q2) fails: {fails}")
    return torsion and fails


# ------------------------------------------------------------------ [GSET]


def perm_mul(a, b):
    return tuple(a[b[i]] for i in range(len(b)))


def gen_group(gens, n):
    e = tuple(range(n))
    G = {e}
    frontier = [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = perm_mul(g, x)
                if y not in G:
                    G.add(y)
                    new.append(y)
        frontier = new
    return frozenset(G)


def subgroups(G, n):
    """All subgroups, as joins of cyclic subgroups (complete for finite groups)."""
    cyc = {gen_group([g], n) for g in G}
    subs = set(cyc)
    frontier = set(cyc)
    while frontier:
        new = set()
        for H in frontier:
            for C in cyc:
                if not C <= H:
                    J = gen_group(list(H | C), n)
                    if J not in subs:
                        new.add(J)
        subs |= new
        frontier = new
    return subs


def sign(p):
    s, seen = 1, set()
    for i in range(len(p)):
        if i in seen:
            continue
        j, L = i, 0
        while j not in seen:
            seen.add(j)
            j = p[j]
            L += 1
        s *= (-1) ** (L - 1)
    return s


def part_gset(out, quick):
    ok = True
    groups = [("A_4", 4, True), ("S_4", 4, False)]
    if not quick:
        groups.append(("A_5", 5, True))
    for name, n, alt in groups:
        G = frozenset(p for p in itertools.permutations(range(n))
                      if not alt or sign(p) == 1)
        subs = subgroups(G, n)
        proper = [H for H in subs if 1 < len(H) < len(G)]
        b = betti_of_poset(proper, lambda a, c: a < c)
        dim = max(len(c) for c in order_complex(proper, lambda a, c: a < c)) - 1
        out.append(f"[GSET] {name}: {len(subs)} subgroups; proper part dim {dim}, "
                   f"Betti mod 2 {b[2]}, mod 2^31-1 {b[P_BIG]}")
        if name == "A_4":
            ok &= b[P_BIG] == {0: 4} and dim == 1
    return ok


# ------------------------------------------------------------------ [NC]


def noncrossing(p):
    for A, B in itertools.combinations(p, 2):
        for a1, a2 in itertools.combinations(sorted(A), 2):
            for b in B:
                if a1 < b < a2 and any(c < a1 or c > a2 for c in B):
                    return False
    return True


def lattice_invariants(parts, n):
    lt = lambda a, b: a != b and refines(a, b)  # finer < coarser
    bot = canon([{x} for x in range(n)])
    top = canon([set(range(n))])
    rs = tuple(sum(1 for p in parts if len(p) == k) for k in range(n, 0, -1))
    mu = mobius_bottom_top(parts, lt, bot, top)
    return len(parts), rs, mu


def part_nc(out, nmax):
    ok = True
    for n in range(4, nmax + 1):
        nc = [canon(p) for p in set_partitions(range(n)) if noncrossing(canon(p))]
        inv_nc = lattice_invariants(nc, n)
        ncset = set(nc)
        equal_sets, inv_match = 0, 0
        seen_inv = {}
        for rel in all_labeled_posets(n):
            op = op_lattice(n, rel)
            if len(op) != len(nc):
                continue
            if set(op) == ncset:
                equal_sets += 1
            key = frozenset(op)
            if key not in seen_inv:
                seen_inv[key] = lattice_invariants(op, n)
            if seen_inv[key] == inv_nc:
                inv_match += 1
        good = (equal_sets > 0) if n == 4 else (inv_match == 0)
        ok &= good
        out.append(f"[NC] n={n}: NC(n) size/ranks/mu = {inv_nc}; labeled posets with "
                   f"OP(P) = NC(n) as sets: {equal_sets}; with matching invariants: "
                   f"{inv_match} (expect >0 sets at n=4, 0 invariant matches at n>=5): "
                   f"{good}")
    return ok


# ------------------------------------------------------------------ main


def main():
    quick = "--quick" in sys.argv
    out = []
    results = {}
    results["CTL"] = part_ctl(out)
    results["MIX"] = part_mix(out, quick)
    results["FIX"] = part_fix(out, 4 if quick else 5)
    results["DDIV"] = part_ddiv(out, [(4, 2), (6, 2), (6, 3)] if quick
                                else [(4, 2), (6, 2), (6, 3), (8, 2), (9, 3), (8, 4)])
    results["NEG"] = part_neg(out)
    results["GSET"] = part_gset(out, quick)
    results["NC"] = part_nc(out, 5 if quick else 6)
    for line in out:
        print(line)
    for k, v in results.items():
        print(f"[SUMMARY] {k}: {v}")
    allok = all(results.values())
    print(f"ALL CHECKS PASS: {allok}")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
