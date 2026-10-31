"""Independent check of the complementation-axiom claim (notes/audit_complementation_axiom.md).

Claim under audit (notes/quotient_categories.md §1.5): in a class satisfying (Q1), (Q2)
and axiom (C) -- for every X with Q-bar(X) nonempty there is t in Q-bar(X) whose
complements in Q(X) form an antichain of atoms a with [a, 1] = Q(X/a) -- every Q-bar(X)
is a wedge of spheres, pure when all the X/a have the same length.

New code. It imports nothing from the repository.

Instruments
  * finite lattices from an explicit order; join/meet tables (lattice-ness is checked);
  * reduced Betti numbers of the order complex of an open interval over GF(p),
    p in PRIMES (sparse elimination); agreement across p = no p-torsion seen;
  * BW(L, z): the Bjorner-Walker prediction  L-bar ~ V_{y in Co(z)} Susp(D(0,y) * D(y,1))
    turned into reduced Betti numbers by Kunneth over a field;
  * cert(L): recursive (C)-certificate on upper intervals, and the sphere multiset it
    predicts; the dual certificate (complements = coatoms, recursion on lower intervals).

Sections
  [BW]   the formula against direct homology, for every z with antichain Co(z), on every
         interval of every lattice in the corpus (partition lattices, OP(P), subgroup
         lattices, random closure-system lattices).
  [CERT] (C)-certified lattices: predicted sphere multiset vs. direct homology.
  [PURE] the purity clause: an explicit lattice whose upper intervals all satisfy (C),
         with a t whose atom complements a all have l([a,1]) equal, but a non-pure wedge;
         and (in [CERT]) graded + certified => homology in the single degree l - 2.
  [GRP]  subgroup lattices: (C) at the top, on every upper interval, on every interval,
         the dual (coatom) form and the mixed certificate; homology of every interval.
  [GRP+] S5, PSL(2,7): certificate census on every interval; antichain census at the top.
  [CTL]  controls that must fail / must fire.
"""

import argparse
import itertools
import random
import sys
from functools import lru_cache

PRIMES = (2, 3, 5, 2147483647)

# ------------------------------------------------------------------ lattices


class Lattice:
    """Finite bounded poset on 0..N-1 given by a reflexive order; checks it is a lattice."""

    def __init__(self, n, leq, name=""):
        self.n = n
        self.name = name
        self.leq = leq  # leq[i][j] bool
        self.up = [frozenset(j for j in range(n) if leq[i][j]) for i in range(n)]
        self.down = [frozenset(j for j in range(n) if leq[j][i]) for i in range(n)]
        bots = [i for i in range(n) if len(self.up[i]) == n]
        tops = [i for i in range(n) if len(self.down[i]) == n]
        assert len(bots) == 1 and len(tops) == 1, f"{name}: not bounded"
        self.bot, self.top = bots[0], tops[0]
        self.join = [[None] * n for _ in range(n)]
        self.meet = [[None] * n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                ub = self.up[i] & self.up[j]
                lub = [u for u in ub if self.down[u] >= ub & self.down[u] and all(leq[u][v] for v in ub)]
                lb = self.down[i] & self.down[j]
                glb = [d for d in lb if all(leq[v][d] for v in lb)]
                assert len(lub) == 1 and len(glb) == 1, f"{name}: not a lattice"
                self.join[i][j] = self.join[j][i] = lub[0]
                self.meet[i][j] = self.meet[j][i] = glb[0]

    def lt(self, i, j):
        return i != j and self.leq[i][j]

    def open_interval(self, x, y):
        return [e for e in range(self.n) if self.lt(x, e) and self.lt(e, y)]

    def closed(self, x, y):
        return [e for e in range(self.n) if self.leq[x][e] and self.leq[e][y]]

    def length(self, x, y):
        """Length of the longest chain from x to y (x <= y)."""
        return _length(self, x, y)

    def complements(self, z, x=None, y=None):
        """Complements of z inside the interval [x, y] (default [0,1])."""
        x = self.bot if x is None else x
        y = self.top if y is None else y
        return [e for e in self.closed(x, y) if self.meet[e][z] == x and self.join[e][z] == y]

    def atoms(self, x, y):
        return [e for e in self.open_interval(x, y)
                if not any(self.lt(x, f) and self.lt(f, e) for f in range(self.n))]

    def coatoms(self, x, y):
        return [e for e in self.open_interval(x, y)
                if not any(self.lt(e, f) and self.lt(f, y) for f in range(self.n))]


def _length(L, x, y):
    """Longest-chain length, cached on the lattice object itself (an id()-keyed global
    cache is unsound: ids are reused after garbage collection)."""
    cache = L.__dict__.setdefault("_len_cache", {})
    key = (x, y)
    if key in cache:
        return cache[key]
    if x == y:
        r = 0
    else:
        r = 1 + max((_length(L, e, y) for e in L.up[x] if e != x and L.leq[e][y]), default=-1)
    cache[key] = r
    return r


def is_graded(L):
    """All maximal chains of L have the same length."""
    memo = {}

    def lens(x):
        if x in memo:
            return memo[x]
        if x == L.top:
            r = {0}
        else:
            covers = [e for e in L.up[x] if e != x and not any(L.lt(x, f) and L.lt(f, e) for f in range(L.n))]
            r = {1 + k for e in covers for k in lens(e)}
        memo[x] = r
        return r

    return len(lens(L.bot)) == 1


def lattice_from_sets(family, name=""):
    """Lattice of a family of frozensets ordered by inclusion (must be a lattice)."""
    fam = list(family)
    n = len(fam)
    leq = [[fam[i] <= fam[j] for j in range(n)] for i in range(n)]
    L = Lattice(n, leq, name)
    L.labels = fam
    return L


# ------------------------------------------------------------------ homology


def chains(elems, lt):
    """All nonempty chains (as sorted tuples by a linear extension) of the poset elems."""
    el = list(elems)
    # linear extension by number of elements below
    el.sort(key=lambda e: sum(1 for f in el if lt(f, e)))
    idx = {e: k for k, e in enumerate(el)}
    above = {e: [f for f in el if lt(e, f)] for e in el}
    out = []

    def rec(ch):
        out.append(tuple(ch))
        for f in above[ch[-1]]:
            rec(ch + [f])

    for e in el:
        rec([e])
    return out, idx


def rank_mod_p(rows, p):
    """Rank of a sparse matrix (list of dict col->val) over GF(p)."""
    pivots = {}
    rk = 0
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            c = min(r)
            if c in pivots:
                prow = pivots[c]
                f = r[c]
                for cc, vv in prow.items():
                    nv = (r.get(cc, 0) - f * vv) % p
                    if nv:
                        r[cc] = nv
                    else:
                        r.pop(cc, None)
            else:
                inv = pow(r[c], p - 2, p)
                r = {cc: (vv * inv) % p for cc, vv in r.items()}
                pivots[c] = r
                rk += 1
                break
    return rk


def reduced_betti(elems, lt, p):
    """Reduced Betti numbers {d: b} of Delta(elems) over GF(p). Empty poset -> {-1: 1}."""
    el = list(elems)
    if not el:
        return {-1: 1}
    chs, _ = chains(el, lt)
    bydim = {}
    for c in chs:
        bydim.setdefault(len(c) - 1, []).append(c)
    top = max(bydim)
    index = {d: {c: k for k, c in enumerate(bydim[d])} for d in bydim}
    ranks = {}
    for d in range(1, top + 1):
        rows = []
        for c in bydim[d]:
            row = {}
            for k in range(len(c)):
                f = c[:k] + c[k + 1:]
                row[index[d - 1][f]] = (-1) ** k
            rows.append(row)
        ranks[d] = rank_mod_p(rows, p)
    b = {}
    for d in range(0, top + 1):
        cd = len(bydim[d])
        z = cd - (ranks.get(d, 0))
        bnd = ranks.get(d + 1, 0)
        v = z - bnd - (1 if d == 0 else 0)
        if v:
            b[d] = v
    return b


def interval_betti(L, x, y, p):
    cache = L.__dict__.setdefault("_betti_cache", {})
    key = (x, y, p)
    if key not in cache:
        cache[key] = reduced_betti(L.open_interval(x, y), L.lt, p)
    return dict(cache[key])


def join_betti(a, b):
    """Reduced Betti of A*B from those of A, B (field coefficients). {-1:1} = empty set."""
    out = {}
    for i, u in a.items():
        for j, v in b.items():
            out[i + j + 1] = out.get(i + j + 1, 0) + u * v
    return {k: v for k, v in out.items() if v}


def susp(a):
    return {k + 1: v for k, v in a.items()}


def bw_prediction(L, z, x, y, p):
    """Bjorner-Walker prediction for the open interval (x,y) and z in it, or None if Co(z)
    is not an antichain."""
    co = L.complements(z, x, y)
    if any(L.lt(u, v) for u in co for v in co):
        return None
    tot = {}
    for c in co:
        s = susp(join_betti(interval_betti(L, x, c, p), interval_betti(L, c, y, p)))
        for k, v in s.items():
            tot[k] = tot.get(k, 0) + v
    return {k: v for k, v in tot.items() if v}


# ------------------------------------------------------------------ (C)-certificates


def cert(L, x, y, dual=False, memo=None, require_all=False):
    """Recursive (C)-certificate for the interval [x, y].

    Returns (ok, spheres) where spheres = {dim: count} is the predicted wedge, or (False, None).
    Primal: some z in (x,y) has all complements atoms; recurse on [a, y].
    Dual:   some z has all complements coatoms; recurse on [x, c].
    The length-1 interval has proper part empty = S^-1.
    """
    if memo is None:
        memo = {}
    key = (x, y, dual)
    if key in memo:
        return memo[key]
    if L.length(x, y) <= 1:
        memo[key] = (True, {-1: 1})
        return memo[key]
    res = (False, None)
    small = set(L.coatoms(x, y) if dual else L.atoms(x, y))
    for z in L.open_interval(x, y):
        co = L.complements(z, x, y)
        if not set(co) <= small:
            continue
        sph = {}
        good = True
        for a in co:
            ok, s = cert(L, a if not dual else x, y if not dual else a, dual, memo)
            if not ok:
                good = False
                break
            for k, v in s.items():
                sph[k + 1] = sph.get(k + 1, 0) + v
        if good:
            res = (True, sph)
            break
    memo[key] = res
    return res


def cert_mixed(L, x, y, memo=None):
    """Mixed certificate: at each interval use either (C) (atom complements, recurse on
    [a, y]) or its dual (coatom complements, recurse on [x, c]).  Intervals of intervals
    are intervals, so the Bjorner-Walker induction runs the same way."""
    if memo is None:
        memo = {}
    if (x, y) in memo:
        return memo[(x, y)]
    if L.length(x, y) <= 1:
        memo[(x, y)] = (True, {-1: 1})
        return memo[(x, y)]
    memo[(x, y)] = (False, None)
    atoms, coatoms = set(L.atoms(x, y)), set(L.coatoms(x, y))
    for z in L.open_interval(x, y):
        co = L.complements(z, x, y)
        for kind, small in (("C", atoms), ("Cop", coatoms)):
            if not set(co) <= small:
                continue
            sph, good = {}, True
            for a in co:
                ok, s = cert_mixed(L, a, y, memo) if kind == "C" else cert_mixed(L, x, a, memo)
                if not ok:
                    good = False
                    break
                for k, v in s.items():
                    sph[k + 1] = sph.get(k + 1, 0) + v
            if good:
                memo[(x, y)] = (True, sph)
                return memo[(x, y)]
    return memo[(x, y)]


def has_C(L, x, y, dual=False):
    """(C) at the top of [x,y] only: some z whose complements are all atoms (coatoms)."""
    if L.length(x, y) <= 1:
        return True
    small = set(L.coatoms(x, y) if dual else L.atoms(x, y))
    return any(set(L.complements(z, x, y)) <= small for z in L.open_interval(x, y))


# ------------------------------------------------------------------ corpus


def partition_lattice(n):
    parts = []

    def rec(i, blocks):
        if i == n:
            parts.append(frozenset(frozenset(b) for b in blocks))
            return
        for b in blocks:
            b.add(i)
            rec(i + 1, blocks)
            b.remove(i)
        blocks.append({i})
        rec(i + 1, blocks)
        blocks.pop()

    rec(0, [])
    N = len(parts)

    def finer(a, b):
        return all(any(x <= y for y in b) for x in a)

    leq = [[finer(parts[i], parts[j]) for j in range(N)] for i in range(N)]
    L = Lattice(N, leq, f"Pi_{n}")
    L.labels = parts
    return L


def op_lattice(n, less):
    """OP(P): partitions of [n] whose quotient of P (arcs between distinct blocks) is acyclic."""
    P = partition_lattice(n)
    keep = []
    for k, pi in enumerate(P.labels):
        blk = {i: b for b in pi for i in b}
        arcs = {(blk[i], blk[j]) for (i, j) in less if blk[i] != blk[j]}
        nodes = list(pi)
        indeg = {b: 0 for b in nodes}
        for (_, v) in arcs:
            indeg[v] += 1
        q = [b for b in nodes if indeg[b] == 0]
        seen = 0
        while q:
            b = q.pop()
            seen += 1
            for (u, v) in arcs:
                if u == b:
                    indeg[v] -= 1
                    if indeg[v] == 0:
                        q.append(v)
        if seen == len(nodes):
            keep.append(k)
    N = len(keep)
    leq = [[P.leq[keep[i]][keep[j]] for j in range(N)] for i in range(N)]
    L = Lattice(N, leq, f"OP({sorted(less)})")
    L.labels = [P.labels[k] for k in keep]
    return L


def posets_up_to(n):
    """All strict partial orders on range(n), naturally labelled (i<j whenever i<_P j),
    deduplicated up to isomorphism by brute-force canonical form."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    seen = set()
    out = []
    for mask in range(1 << len(pairs)):
        rel = {pairs[k] for k in range(len(pairs)) if mask >> k & 1}
        if any((i, j) in rel and (j, k) in rel and (i, k) not in rel
               for i in range(n) for j in range(n) for k in range(n)):
            continue
        canon = min(tuple(sorted((perm[i], perm[j]) for (i, j) in rel))
                    for perm in itertools.permutations(range(n)))
        if canon in seen:
            continue
        seen.add(canon)
        out.append(frozenset(rel))
    return out


# --- permutation groups


def pmul(a, b):  # (a*b)(i) = a(b(i))
    return tuple(a[i] for i in b)


def gen_group(gens, deg):
    e = tuple(range(deg))
    G = {e}
    frontier = [e]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = pmul(g, s)
                if h not in G:
                    G.add(h)
                    nxt.append(h)
        frontier = nxt
    return frozenset(G)


def subgroup_lattice(gens, deg, name):
    G = gen_group(gens, deg)
    e = tuple(range(deg))
    subs = {frozenset({e})}
    frontier = list(subs)
    while frontier:
        nxt = []
        for H in frontier:
            for g in G:
                if g in H:
                    continue
                K = gen_group(list(H) + [g], deg) if len(H) < 40 else gen_group(_gens_of(H, deg) + [g], deg)
                if K not in subs:
                    subs.add(K)
                    nxt.append(K)
        frontier = nxt
    L = lattice_from_sets(sorted(subs, key=len), name)
    L.group_order = len(G)
    return L


def _gens_of(H, deg):
    gens = []
    cur = gen_group([], deg)
    for h in sorted(H):
        if h not in cur:
            gens.append(h)
            cur = gen_group(gens, deg)
    return gens


def cyc(deg, *cycles):
    p = list(range(deg))
    for c in cycles:
        for k in range(len(c)):
            p[c[k]] = c[(k + 1) % len(c)]
    return tuple(p)


def groups():
    """(name, gens, degree, solvable)."""
    return [
        ("C2xC2", [cyc(4, (0, 1)), cyc(4, (2, 3))], 4, True),
        ("S3", [cyc(3, (0, 1)), cyc(3, (0, 1, 2))], 3, True),
        ("D8", [cyc(4, (0, 1, 2, 3)), cyc(4, (0, 2))], 4, True),
        ("Q8", [cyc(8, (0, 1, 2, 3), (4, 5, 6, 7)), cyc(8, (0, 4, 2, 6), (1, 7, 3, 5))], 8, True),
        ("C2^3", [cyc(6, (0, 1)), cyc(6, (2, 3)), cyc(6, (4, 5))], 6, True),
        ("A4", [cyc(4, (0, 1, 2)), cyc(4, (0, 1), (2, 3))], 4, True),
        ("D12", [cyc(6, (0, 1, 2, 3, 4, 5)), cyc(6, (1, 5), (2, 4))], 6, True),
        ("S4", [cyc(4, (0, 1)), cyc(4, (0, 1, 2, 3))], 4, True),
        ("A5", [cyc(5, (0, 1, 2)), cyc(5, (0, 1, 2, 3, 4))], 5, False),
    ]


def big_groups():
    """Larger groups, used for the (C)-on-every-interval census only."""
    psl27 = [cyc(7, (0, 1, 2, 3, 4, 5, 6)), cyc(7, (1, 2, 4), (3, 6, 5)), cyc(7, (2, 3), (4, 6))]
    return [
        ("S5", [cyc(5, (0, 1)), cyc(5, (0, 1, 2, 3, 4))], 5, False),
        ("PSL(2,7)", psl27, 7, False),
    ]


def random_closure_lattice(rng, m, k):
    """Lattice of all intersections of k random subsets of [m], plus [m] (Moore family)."""
    ground = frozenset(range(m))
    fam = {ground}
    for _ in range(k):
        fam.add(frozenset(i for i in range(m) if rng.random() < 0.5))
    changed = True
    while changed:
        changed = False
        for a in list(fam):
            for b in list(fam):
                c = a & b
                if c not in fam:
                    fam.add(c)
                    changed = True
    return lattice_from_sets(sorted(fam, key=len), "rand")


def face_lattice_rp2():
    """Face lattice of the 6-vertex RP^2 with 0-hat and 1-hat (torsion control)."""
    tris = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 5, 1),
            (1, 2, 4), (2, 3, 5), (3, 4, 1), (4, 5, 2), (5, 1, 3)]
    faces = {frozenset()}
    for t in tris:
        for r in range(1, 4):
            for s in itertools.combinations(t, r):
                faces.add(frozenset(s))
    faces.add(frozenset(range(7)))  # 1-hat
    return lattice_from_sets(sorted(faces, key=len), "RP2")


# ------------------------------------------------------------------ checks

FAILS = []


def check(tag, ok, msg, out):
    print(f"[{tag}] {'PASS' if ok else 'FAIL'}: {msg}", file=out)
    if not ok:
        FAILS.append((tag, msg))
    return ok


def betti_all(L, x, y):
    return {p: interval_betti(L, x, y, p) for p in PRIMES}


def section_bw(lattices, out, max_intervals=None):
    """[BW] the formula vs direct homology on every interval and every z with antichain Co(z)."""
    tested = mismatches = nonanti = 0
    for L in lattices:
        ivs = [(x, y) for x in range(L.n) for y in range(L.n) if L.leq[x][y] and L.length(x, y) >= 2]
        if max_intervals:
            ivs = ivs[:max_intervals]
        for (x, y) in ivs:
            actual = {p: interval_betti(L, x, y, p) for p in (2, 3)}
            for z in L.open_interval(x, y):
                for p in (2, 3):
                    pred = bw_prediction(L, z, x, y, p)
                    if pred is None:
                        nonanti += 1
                        break
                    tested += 1
                    if pred != actual[p]:
                        mismatches += 1
    check("BW", tested > 0 and mismatches == 0,
          f"{tested} (interval, z, p) cases with Co(z) an antichain: prediction = direct homology "
          f"in all but {mismatches}; {nonanti} (interval, z) skipped (Co(z) not an antichain)", out)
    return tested, mismatches


def section_cert(lattices, out):
    """[CERT] certified lattices: predicted sphere multiset vs direct homology at all primes."""
    rows = []
    for L in lattices:
        ok, sph = cert(L, L.bot, L.top)
        okd, sphd = cert(L, L.bot, L.top, dual=True)
        b = betti_all(L, L.bot, L.top)
        agree_p = all(b[p] == b[2] for p in PRIMES)
        line = f"{L.name}: |L|={L.n} l={L.length(L.bot, L.top)} betti={b[2]} torsion-free(seen)={agree_p}"
        if ok:
            check("CERT", sph == b[2] and agree_p, line + f"; (C)-certificate predicts {sph}", out)
        if okd:
            check("CERT", sphd == b[2] and agree_p, line + f"; dual (C)-certificate predicts {sphd}", out)
        if not ok and not okd:
            print(f"[CERT] info: {line}; no certificate (primal or dual)", file=out)
        if ok and is_graded(L):
            ell = L.length(L.bot, L.top)
            check("CERT", set(b[2]) <= {ell - 2},
                  f"{L.name}: graded and certified -> homology only in degree l-2 = {ell - 2}", _Quiet(out))
        rows.append((L.name, ok, okd))
    return rows


def upper_hereditary_C(L):
    """(C) holds on every upper interval [x,1] of length >= 2 (needed once (Q2) makes every
    upper interval an object of the class)."""
    return all(has_C(L, x, L.top) for x in range(L.n))


def purity_example():
    """L = M x 2 with M = B_3 plus one extra element p (0 < p < 1, p incomparable to the rest).

    M-bar = hexagon + isolated point ~ S^1 v S^0.  In L, t = (1_M, 0) has exactly one
    complement, the atom a = (0_M, 1), and [a, 1] = M.  So "all X/a have the same length"
    holds vacuously at the top, yet L-bar ~ Susp(M-bar) ~ S^2 v S^1 is not pure.
    """
    B3 = [frozenset(s) for r in range(4) for s in itertools.combinations((1, 2, 3), r)]
    M = B3[:-1] + [frozenset({"p"}), frozenset({1, 2, 3, "p"})]  # top of M = {1,2,3,p}
    fam = [m | ({"s"} if k else set()) for m in M for k in (0, 1)]
    return lattice_from_sets(sorted(fam, key=lambda f: (len(f), sorted(map(str, f)))), "(B3+p)x2")


def section_pure(out):
    """[PURE] the purity clause as stated (top level only) fails; hereditary version holds."""
    L = purity_example()
    labels = L.labels
    t = labels.index(frozenset({1, 2, 3, "p"}))
    co = L.complements(t)
    atoms = set(L.atoms(L.bot, L.top))
    b = {p: interval_betti(L, L.bot, L.top, p) for p in PRIMES}
    ok, sph = cert(L, L.bot, L.top)
    uh = upper_hereditary_C(L)
    check("PURE", len(co) == 1 and set(co) <= atoms and uh and ok and sph == b[2]
          and all(b[p] == b[2] for p in PRIMES) and len(b[2]) == 2,
          f"(B3 + point) x 2, |L|={L.n}: every upper interval satisfies (C); t=(1,0) has the single "
          f"atom complement (0,1), so 'all X/a have the same length' holds; yet L-bar has Betti "
          f"{b[2]} (= certificate {sph}): a non-pure wedge S^1 v S^2", out)
    # inside M (= [a,1]): the witnesses of (C) have complements of different upper lengths
    a = co[0]
    lens = []
    for z in L.open_interval(a, L.top):
        cz = L.complements(z, a, L.top)
        if set(cz) <= set(L.atoms(a, L.top)) and cz:
            lens.append(sorted(L.length(c, L.top) for c in cz))
    check("PURE", all(len(set(x)) > 1 for x in lens) and lens,
          f"in [a,1] = M every (C)-witness t' has complements of unequal upper length {lens}: the "
          f"hereditary hypothesis fails one level down, exactly where the non-purity enters", out)
    # hereditary-equal-length lattices are pure: check on the certified corpus elsewhere
    return L


class _Quiet:
    """Sink that only lets FAIL lines through (bulk per-interval checks)."""

    def __init__(self, out):
        self.out = out

    def write(self, s):
        if "FAIL" in s:
            self.out.write(s)

    def flush(self):
        pass


def section_groups_big(out):
    """[GRP+] census of (C), dual (C) and mixed certificates on every interval; no homology
    except where a certificate makes a prediction for the whole lattice."""
    res = {}
    for (name, gens, deg, solv) in big_groups():
        L = subgroup_lattice(gens, deg, f"L({name})")
        ivs = [(x, y) for x in range(L.n) for y in range(L.n) if L.leq[x][y] and L.length(x, y) >= 2]
        fC = [(x, y) for (x, y) in ivs if not has_C(L, x, y)]
        fD = [(x, y) for (x, y) in ivs if not has_C(L, x, y, dual=True)]
        mmemo = {}
        fM = [(x, y) for (x, y) in ivs if not cert_mixed(L, x, y, mmemo)[0]]
        okc, sph = cert(L, L.bot, L.top)
        okm, sphm = cert_mixed(L, L.bot, L.top, mmemo)
        okc, sph = cert(L, L.bot, L.top)
        anti_top = [z for z in L.open_interval(L.bot, L.top)
                    if not any(L.lt(u, v) for u in L.complements(z) for v in L.complements(z))]
        bt = {p: interval_betti(L, L.bot, L.top, p) for p in PRIMES + (7,)}
        print(f"[GRP+] {name}: L-bar(G) reduced Betti over GF(p), p in {PRIMES + (7,)}: "
              f"{[bt[p] for p in PRIMES + (7,)]}", file=out)
        if okc:
            check("GRP+", sph == bt[2] and all(bt[p] == bt[2] for p in bt),
                  f"{name}: (C)-certificate prediction {sph} = direct homology", out)
        print(f"[GRP+] {name}: elements z of L-bar(G) with Co(z) an antichain: {len(anti_top)} "
              f"(|z| in {sorted({len(L.labels[z]) for z in anti_top})})", file=out)

        def desc(xs):
            return sorted({(len(L.labels[x]), len(L.labels[y])) for (x, y) in xs})
        print(f"[GRP+] {name} (|G|={L.group_order}, {L.n} subgroups): intervals of length>=2: {len(ivs)}; "
              f"failing (C): {len(fC)}; failing dual: {len(fD)}; no mixed certificate: {len(fM)} "
              f"(|H|,|K| types {desc(fM)[:12]}); top: (C) cert {okc} {sph if okc else ''}, "
              f"mixed cert {okm} {sphm if okm else ''}", file=out)
        res[name] = dict(L=L, fC=len(fC), fD=len(fD), fM=len(fM), okc=okc, sph=sph, okm=okm, sphm=sphm,
                         fM_types=desc(fM), anti_top=len(anti_top))
    return res


def section_groups(out):
    """[GRP] subgroup lattices."""
    res = {}
    for (name, gens, deg, solv) in groups():
        L = subgroup_lattice(gens, deg, f"L({name})")
        ivs = [(x, y) for x in range(L.n) for y in range(L.n) if L.leq[x][y] and L.length(x, y) >= 2]
        top_C = has_C(L, L.bot, L.top)
        at = set(L.atoms(L.bot, L.top))
        wit = sorted({len(L.labels[z]) for z in L.open_interval(L.bot, L.top)
                      if set(L.complements(z)) <= at})
        top_D = has_C(L, L.bot, L.top, dual=True)
        upper = [x for x in range(L.n) if not has_C(L, x, L.top)]
        lower_dual = [y for y in range(L.n) if not has_C(L, L.bot, y, dual=True)]
        all_C = [(x, y) for (x, y) in ivs if not has_C(L, x, y)]
        all_D = [(x, y) for (x, y) in ivs if not has_C(L, x, y, dual=True)]
        all_CD = [(x, y) for (x, y) in all_C if (x, y) in set(all_D)]
        okc, sph = cert(L, L.bot, L.top)
        okd, sphd = cert(L, L.bot, L.top, dual=True)
        mmemo = {}
        mixed_fail = [(x, y) for (x, y) in ivs if not cert_mixed(L, x, y, mmemo)[0]]
        torsion_ivs = []
        betti_top = None
        for (x, y) in ivs:
            b = {p: interval_betti(L, x, y, p) for p in (2, 3, 5)}
            if not (b[2] == b[3] == b[5]):
                torsion_ivs.append((x, y))
            if (x, y) == (L.bot, L.top):
                betti_top = b[2]
        sizes = lambda xs: sorted({len(L.labels[x]) for x in xs})
        print(f"[GRP] {name} (|G|={L.group_order}, {L.n} subgroups, solvable={solv}): "
              f"L-bar Betti {betti_top}; (C) at top {top_C} (|t| in {wit}), dual at top {top_D}; "
              f"recursive cert {okc} {sph if okc else ''}, dual cert {okd} {sphd if okd else ''}; "
              f"upper intervals [H,G] failing (C): {len(upper)} (|H| in {sizes(upper)}); "
              f"lower intervals [1,K] failing dual (C): {len(lower_dual)} (|K| in {sizes(lower_dual)}); "
              f"intervals failing (C): {len(all_C)}/{len(ivs)}, failing dual: {len(all_D)}, failing both: "
              f"{len(all_CD)}; intervals with no mixed certificate: {len(mixed_fail)}; "
              f"intervals with p-torsion (p=2,3,5): {len(torsion_ivs)}", file=out)
        for (x, y) in ivs:
            okm, sm = cert_mixed(L, x, y, mmemo)
            if okm:
                check("GRP", sm == interval_betti(L, x, y, 2) == interval_betti(L, x, y, 3),
                      f"{name}: interval [{len(L.labels[x])},{len(L.labels[y])}] mixed certificate "
                      f"predicts {sm}", _Quiet(out))
        res[name] = dict(top_C=top_C, top_D=top_D, upper_fail=len(upper), lower_dual_fail=len(lower_dual),
                         cert=okc, dcert=okd, sph=sph, dsph=sphd, betti=betti_top,
                         fail_both=len(all_CD), mixed_fail=len(mixed_fail), torsion=len(torsion_ivs), L=L, solv=solv)
        if solv:
            check("GRP", okd and sphd == betti_top,
                  f"{name}: dual (coatom) certificate exists and predicts the homology "
                  f"(Kratzer-Thevenaz mechanism)", out)
    return res


def controls(out):
    ok = True
    # 1. non-antichain complements: BW formula must mispredict.
    # 0 < a < b < 1, 0 < t < 1 ; Co(t) = {a, b}
    fam = [frozenset(), frozenset({1}), frozenset({1, 2}), frozenset({3}), frozenset({1, 2, 3})]
    L = lattice_from_sets(fam, "N5")
    t = fam.index(frozenset({3}))
    co = L.complements(t)
    actual = interval_betti(L, L.bot, L.top, 2)
    tot = {}
    for c in co:
        s = susp(join_betti(interval_betti(L, L.bot, c, 2), interval_betti(L, c, L.top, 2)))
        for k, v in s.items():
            tot[k] = tot.get(k, 0) + v
    tot = {k: v for k, v in tot.items() if v}
    ok &= check("CTL", len(co) == 2 and tot != actual and bw_prediction(L, t, L.bot, L.top, 2) is None,
                f"N5 with Co(t) = {{a<b}} (not an antichain): naive BW sum {tot} != actual {actual}; "
                f"the instrument refuses the case", out)
    # 2. Pi_4, t = 01|23: complements are not atoms, (C) witness check must reject it
    P4 = partition_lattice(4)
    t = P4.labels.index(frozenset({frozenset({0, 1}), frozenset({2, 3})}))
    co = P4.complements(t)
    atoms = set(P4.atoms(P4.bot, P4.top))
    ok &= check("CTL", not set(co) <= atoms,
                f"Pi_4, t=01|23: complements {[sorted(map(sorted, P4.labels[c])) for c in co]} include non-atoms", out)
    # 3. torsion detector: RP^2 face lattice, mod 2 vs mod 3 must differ
    R = face_lattice_rp2()
    b2 = interval_betti(R, R.bot, R.top, 2)
    b3 = interval_betti(R, R.bot, R.top, 3)
    ok &= check("CTL", b2 != b3, f"RP^2 face lattice: mod 2 {b2}, mod 3 {b3} differ (torsion detected)", out)
    # 4. RP^2 has no (C)-certificate (it cannot: it is not a wedge)
    okc, _ = cert(R, R.bot, R.top)
    okd, _ = cert(R, R.bot, R.top, dual=True)
    ok &= check("CTL", not okc and not okd, "RP^2 face lattice: no (C)-certificate, primal or dual", out)
    # 5. heredity is needed: L = R-hat x 2 has (C) at the top (t = (1,0), unique complement
    #    the atom (0,1), [a,1] = R-hat), but L-bar = Susp(R-bar) has torsion.
    Rl = R.labels
    fam = [frozenset(f) | ({"s"} if k else set()) for f in Rl for k in (0, 1)]
    L2 = lattice_from_sets(sorted(fam, key=len), "RP2x2")
    tz = L2.labels.index(frozenset(range(7)))
    co = L2.complements(tz)
    atoms = set(L2.atoms(L2.bot, L2.top))
    b2 = interval_betti(L2, L2.bot, L2.top, 2)
    b3 = interval_betti(L2, L2.bot, L2.top, 3)
    ok &= check("CTL", has_C(L2, L2.bot, L2.top) and set(co) <= atoms and len(co) == 1 and b2 != b3
                and not cert(L2, L2.bot, L2.top)[0],
                f"RP^2-hat x 2: (C) holds at the top (t=(1,0), Co(t) = one atom) but not hereditarily; "
                f"L-bar has mod 2 {b2}, mod 3 {b3} -> torsion, not a wedge", out)
    # 6. Pi_n positive: certificate with t = {n}|rest gives (n-1)! spheres S^{n-3}
    for n in (3, 4, 5):
        Pn = partition_lattice(n)
        okc, sph = cert(Pn, Pn.bot, Pn.top)
        ok &= check("CTL", okc and sph == {n - 3: _fact(n - 1)}, f"Pi_{n}: certificate predicts {sph}", out)
    return ok


def _fact(k):
    r = 1
    for i in range(2, k + 1):
        r *= i
    return r


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=4, help="max n for OP(P) corpus")
    ap.add_argument("--random", type=int, default=150, help="random lattices in the BW corpus")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--no-big", action="store_true", help="skip S5 and PSL(2,7)")
    args = ap.parse_args(argv)
    out = sys.stdout
    rng = random.Random(args.seed)

    print("== controls", file=out)
    controls(out)

    print("== corpus", file=out)
    corpus = [partition_lattice(n) for n in (3, 4, 5)]
    ops = []
    for n in range(3, args.nmax + 1):
        for rel in posets_up_to(n):
            ops.append(op_lattice(n, rel))
    print(f"OP(P): {len(ops)} posets with 3 <= n <= {args.nmax}", file=out)
    rand = []
    while len(rand) < args.random:
        L = random_closure_lattice(rng, rng.randint(3, 6), rng.randint(2, 7))
        if L.length(L.bot, L.top) >= 2:
            rand.append(L)

    print("== [BW] formula vs direct homology", file=out)
    section_bw(corpus + ops + rand, out)

    print("== [CERT] (C)-certified lattices", file=out)
    section_cert(corpus + ops, out)
    nc = sum(1 for L in rand if cert(L, L.bot, L.top)[0])
    print(f"[CERT] info: {nc}/{len(rand)} random lattices carry a primal certificate", file=out)
    section_cert([L for L in rand if cert(L, L.bot, L.top)[0]], out)

    print("== [PURE] purity clause", file=out)
    section_pure(out)

    print("== [GRP] subgroup lattices", file=out)
    res = section_groups(out)
    gl = [r["L"] for r in res.values()]
    section_bw(gl, out)
    if not args.no_big:
        print("== [GRP+] larger groups: certificate census", file=out)
        section_groups_big(out)

    print(f"== done: {len(FAILS)} failure(s)", file=out)
    for f in FAILS:
        print("FAIL", f, file=out)
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
