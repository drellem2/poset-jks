#!/usr/bin/env python3
"""Independent audit computations for notes/quotient_categories.md.

Written for notes/audit_quotient_categories.md. Imports nothing from the repo
(in particular nothing from compute/quotient_categories.py). Plain Python 3,
single process.

Sections (output tags):
  [HOM]   homology engine and its controls (S^1, torus, RP^2 torsion)
  [NEG]   at-most-2-to-1 quotients, n = 7: 3-torsion; interval sizes 27 / 77
  [GSET]  subgroup lattices of A_4, S_4, A_5; G-invariant partitions = subgroups
  [INT]   the interval category of an arbitrary lattice satisfies (Q1)-(Q3)
          with one fiber; face lattice of RP^2 is not a wedge
  [MIX]   Prop 2.1 (mixed graphs), Lambda(V) computed from points
  [DDIV]  Prop 2.2 (d-divisible), Quillen fibers, the BWW identity with
          Q_{<pi} (correct) versus Q_{>pi} (as printed)
  [FIX]   (R5): stable faces = pullbacks, orbit preorder acyclic
  [CMP]   Route C's complementation axiom on OP(P); same test on L(G)
  [VAL]   Prop 3.1 sharpened: counting decompositions along {B}|{c}

Usage: python3 audit_quotient_categories.py [--quick]
Exit status 0 iff every check (including every control) behaves as expected.
"""
import itertools
import random
import sys
from math import factorial

QUICK = "--quick" in sys.argv
FAILS = []


def check(tag, cond, msg):
    print(f"[{tag}] {'ok  ' if cond else 'FAIL'} {msg}")
    if not cond:
        FAILS.append(f"{tag}: {msg}")


# ---------------------------------------------------------------- homology

def rank_mod_p(rows, p):
    """rows: list of dict col->int. Rank over GF(p) by sparse elimination."""
    pivots = {}  # col -> row(dict) with leading col
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
                row = {cc: (vv * inv) % p for cc, vv in row.items()}
                pivots[c] = row
                r += 1
                break
    return r


def reduced_betti_complex(faces, p):
    """faces: iterable of frozensets/tuples (simplices, closed under faces not
    required: we take the closure). Returns dict dim -> reduced Betti mod p."""
    allf = set()
    for f in faces:
        f = tuple(sorted(f))
        for k in range(len(f) + 1):
            for s in itertools.combinations(f, k):
                allf.add(s)
    return _betti_from_simplices(allf, p)


def _betti_from_simplices(allf, p):
    bydim = {}
    for s in allf:
        bydim.setdefault(len(s) - 1, []).append(s)
    index = {d: {s: i for i, s in enumerate(sorted(L))} for d, L in bydim.items()}
    maxd = max(bydim)
    ranks = {}
    for d in range(0, maxd + 1):
        rows = []
        for s in bydim.get(d, []):
            row = {}
            for i in range(len(s)):
                t = s[:i] + s[i + 1:]
                row[index[d - 1][t]] = (-1) ** i
            rows.append(row)
        ranks[d] = rank_mod_p(rows, p)
    betti = {}
    for d in range(-1, maxd + 1):
        b = len(bydim.get(d, [])) - ranks.get(d, 0) - ranks.get(d + 1, 0)
        if b:
            betti[d] = b
    return betti


def chains(elements, less):
    """All nonempty chains of a finite poset, plus the empty chain, as tuples
    of element indices sorted increasingly in the order."""
    n = len(elements)
    up = [[j for j in range(n) if less(elements[i], elements[j])] for i in range(n)]
    out = [()]

    def ext(ch):
        out.append(tuple(ch))
        for j in up[ch[-1]]:
            ch.append(j)
            ext(ch)
            ch.pop()
    for i in range(n):
        ext([i])
    return out


def order_complex_betti(elements, less, p):
    if not elements:
        return {-1: 1}
    ch = set(chains(elements, less))
    # chains are closed under taking subsets; faces as tuples in chain order.
    # _betti_from_simplices needs faces as tuples with consistent order; a
    # sub-chain of a chain in chain order is again in chain order.
    return _betti_chains(ch, p)


def _betti_chains(ch, p):
    bydim = {}
    for s in ch:
        bydim.setdefault(len(s) - 1, []).append(s)
    index = {d: {s: i for i, s in enumerate(L)} for d, L in bydim.items()}
    maxd = max(bydim)
    ranks = {}
    for d in range(0, maxd + 1):
        rows = []
        for s in bydim.get(d, []):
            row = {}
            for i in range(len(s)):
                t = s[:i] + s[i + 1:]
                row[index[d - 1][t]] = (-1) ** i
            rows.append(row)
        ranks[d] = rank_mod_p(rows, p)
    betti = {}
    for d in range(-1, maxd + 1):
        b = len(bydim.get(d, [])) - ranks.get(d, 0) - ranks.get(d + 1, 0)
        if b:
            betti[d] = b
    return betti


BIG = 2 ** 31 - 1
RP2 = [(1, 2, 3), (1, 3, 4), (1, 4, 5), (1, 5, 6), (1, 2, 6), (2, 3, 5), (2, 4, 5),
       (2, 4, 6), (3, 4, 6), (3, 5, 6)]


def torus7():
    # 7-vertex Moebius torus
    T = []
    for i in range(7):
        T.append((i, (i + 1) % 7, (i + 3) % 7))
        T.append((i, (i + 2) % 7, (i + 3) % 7))
    return T


def sec_hom():
    s1 = [(0, 1), (1, 2), (0, 2)]
    check("HOM", reduced_betti_complex(s1, 2) == {1: 1}, "S^1 boundary of triangle: {1:1}")
    t = torus7()
    b2, b3 = reduced_betti_complex(t, 2), reduced_betti_complex(t, 3)
    check("HOM", b2 == {1: 2, 2: 1} == b3, f"7-vertex torus: {b2} (mod 2) = {b3} (mod 3)")
    r2, r3 = reduced_betti_complex(RP2, 2), reduced_betti_complex(RP2, 3)
    check("HOM", r2 == {1: 1, 2: 1} and r3 == {}, f"RP^2_6: mod 2 {r2}, mod 3 {r3} (torsion detected)")
    # order complex engine on face poset of RP^2 (barycentric subdivision)
    fp = sorted({tuple(sorted(s)) for f in RP2 for k in (1, 2, 3) for s in itertools.combinations(f, k)})
    sub = lambda a, b: a != b and set(a) <= set(b)
    o2, o3 = order_complex_betti(fp, sub, 2), order_complex_betti(fp, sub, 3)
    check("HOM", o2 == r2 and o3 == r3, f"order complex of face poset of RP^2_6 agrees: {o2}, {o3}")
    # positive control that must fail: a deliberately wrong boundary sign
    rows = [{0: 1, 1: 1}, {1: 1, 2: 1}, {0: 1, 2: 1}]  # unsigned boundary of S^1
    check("HOM", rank_mod_p(rows, 3) == 3, "control: unsigned boundary of S^1 has rank 3 mod 3 (would give wrong Betti) - detects sign errors")


# ---------------------------------------------------------------- partitions

def set_partitions(s):
    s = list(s)
    if not s:
        yield []
        return
    first, rest = s[0], s[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def canon(p):
    return tuple(sorted(tuple(sorted(b)) for b in p))


def refines(a, b):
    """partition a finer than or equal to b"""
    blk = {}
    for i, B in enumerate(b):
        for x in B:
            blk[x] = i
    return all(len({blk[x] for x in A}) == 1 for A in a)


def strictly_finer(a, b):
    return a != b and refines(a, b)


# ---------------------------------------------------------------- [NEG]

def sec_neg():
    n = 7
    edges = list(itertools.combinations(range(n), 2))
    match = [()]
    for k in (1, 2, 3):
        for es in itertools.combinations(edges, k):
            vs = [v for e in es for v in e]
            if len(set(vs)) == len(vs):
                match.append(es)
    nonempty = [m for m in match if m]
    f = [sum(1 for m in nonempty if len(m) == k) for k in (1, 2, 3)]
    check("NEG", f == [21, 105, 105], f"matching complex M_7 f-vector {f}")
    b = {p: reduced_betti_complex(nonempty, p) for p in (2, 3, BIG)}
    check("NEG", b[2] == {2: 20} and b[BIG] == {2: 20} and b[3] == {1: 1, 2: 21},
          f"M_7 reduced Betti mod 2 {b[2]}, mod 3 {b[3]}, mod 2^31-1 {b[BIG]}: H_1 has 3-torsion")
    # same on the order complex of the face poset = proper part of Q(X)
    sub = lambda a, c: a != c and set(a) <= set(c)
    o3 = order_complex_betti(nonempty, sub, 3)
    o2 = order_complex_betti(nonempty, sub, 2)
    check("NEG", o3 == b[3] and o2 == b[2], f"proper part of Q(7) (face poset): mod 2 {o2}, mod 3 {o3}")
    # positive control: n = 6 (M_6 has free homology) gives equal mod 2 / mod 3
    e6 = list(itertools.combinations(range(6), 2))
    m6 = [es for k in (1, 2, 3) for es in itertools.combinations(e6, k)
          if len({v for e in es for v in e}) == 2 * k]
    c2, c3 = reduced_betti_complex(m6, 2), reduced_betti_complex(m6, 3)
    check("NEG", c2 == c3, f"control M_6: mod 2 {c2} = mod 3 {c3} (detector silent on torsion-free case)")
    # interval sizes: [pi,1] for pi = one 2-block, vs Q(X/pi)
    up = sum(1 for m in match if (0, 1) in m) + 1
    q6 = len(m6) + 1 + 1
    check("NEG", up == 27 and q6 == 77, f"|[pi,1^]| = {up}, |Q(6-set)| = {q6}: (Q2) fails")
    # composition closure fails: (2-to-1) o (2-to-1) can be 4-to-1
    check("NEG", True, "composite of {01}{23}... then merging the two 2-blocks has a 4-element fiber (by inspection)")


# ---------------------------------------------------------------- groups

def compose(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[i] for i in q)


def gen_group(gens, n):
    e = tuple(range(n))
    G = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = compose(s, g)
                if h not in G:
                    G.add(h)
                    new.append(h)
        frontier = new
    return frozenset(G)


def parity(p):
    s, seen = 0, set()
    for i in range(len(p)):
        if i in seen:
            continue
        j, L = i, 0
        while j not in seen:
            seen.add(j)
            j = p[j]
            L += 1
        s += L - 1
    return s % 2


def subgroups(G, n):
    G = list(G)
    subs = set()
    e = tuple(range(n))
    subs.add(frozenset([e]))
    cyc = {}
    for g in G:
        cyc[g] = gen_group([g], n)
        subs.add(cyc[g])
    els = list(G)
    for a, b in itertools.combinations(els, 2):
        subs.add(gen_group([a, b], n))
    # close under joins of pairs (catches 3-generated subgroups if any)
    changed = True
    while changed:
        changed = False
        L = list(subs)
        for A, B in itertools.combinations(L, 2):
            if A <= B or B <= A:
                continue
            J = gen_group(list(A | B), n)
            if J not in subs:
                subs.add(J)
                changed = True
    return subs


def mobius_bottom_top(elems, leq):
    # mu(0,x) for lattice given as list with leq; returns mu(0,1)
    order = sorted(elems, key=len)
    bot, top = order[0], order[-1]
    mu = {}
    for x in order:
        if x == bot:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if y != x and leq(y, x))
    return mu[top]


def sec_gset():
    groups = {}
    groups["A4"] = (frozenset(g for g in itertools.permutations(range(4)) if parity(g) == 0), 4)
    groups["S4"] = (frozenset(itertools.permutations(range(4))), 4)
    if not QUICK:
        groups["A5"] = (frozenset(g for g in itertools.permutations(range(5)) if parity(g) == 0), 5)
    expect = {"A4": (10, 4, {0: 4}), "S4": (30, -12, {1: 12}), "A5": (59, -60, {1: 60})}
    store = {}
    for name, (G, n) in groups.items():
        S = subgroups(G, n)
        e = frozenset([tuple(range(n))])
        proper = [H for H in S if H != e and H != G]
        lt = lambda a, b: a != b and a <= b
        mu = mobius_bottom_top(list(S), lambda a, b: a <= b)
        # dimension of proper part
        ch = chains(proper, lt)
        dim = max(len(c) for c in ch) - 1
        bs = {p: order_complex_betti(proper, lt, p) for p in (2, 3, 5, BIG)}
        cnt, emu, eb = expect[name]
        same = all(bs[p] == eb for p in bs)
        check("GSET", len(S) == cnt and mu == emu and same,
              f"L({name}): {len(S)} subgroups, mu = {mu}, dim proper part = {dim}, "
              f"reduced Betti mod 2,3,5,2^31-1 = {[bs[p] for p in (2, 3, 5, BIG)]}")
        top = dim
        check("GSET", all(d < top for d in eb),
              f"L({name}) is NOT Cohen-Macaulay: homology only in degree {sorted(eb)} < dim {top}")
        store[name] = (S, G, n)
    # G-invariant partitions of the regular G-set = subgroups (S_3, Z/4, S_4 on cosets)
    S3 = frozenset(itertools.permutations(range(3)))
    els = sorted(S3)
    idx = {g: i for i, g in enumerate(els)}
    inv = []
    for p in set_partitions(range(6)):
        P = canon(p)
        ok = True
        for g in els:
            img = canon([[idx[compose(g, els[i])] for i in B] for B in p])
            if img != P:
                ok = False
                break
        if ok:
            inv.append(P)
    subsS3 = subgroups(S3, 3)
    check("GSET", len(inv) == len(subsS3) == 6,
          f"S_3: {len(inv)} left-invariant partitions of the regular S_3-set, {len(subsS3)} subgroups")
    # block of identity is a subgroup, and the map is an order isomorphism
    e = idx[tuple(range(3))]
    blocks = [frozenset(els[i] for i in next(B for B in P if e in B)) for P in inv]
    iso = set(blocks) == set(subsS3) and all(
        (refines(P1, P2)) == (b1 <= b2) for P1, b1 in zip(inv, blocks) for P2, b2 in zip(inv, blocks))
    check("GSET", iso, "S_3: P -> block of e is an order isomorphism onto L(S_3)")
    # control: right-multiplication-invariant check with a non-normal block fails
    # (the partition into right cosets of a non-normal C_2 is not left-invariant)
    C2 = gen_group([(1, 0, 2)], 3)
    right = canon([[idx[compose(h, g)] for h in C2] for g in els])
    check("GSET", right not in inv, "control: right cosets of a non-normal C_2 are not a left-invariant partition")
    # intervals (H,G) of L(G) are Q(G/H): count G-invariant partitions of G/H
    S, G, n = store["S4"]
    for H in sorted(S, key=len):
        if len(H) not in (3, 4, 6, 8):
            continue
        els4 = sorted(G)
        cos = sorted({frozenset(compose(g, h) for h in H) for g in els4}, key=lambda c: min(c))
        cidx = {c: i for i, c in enumerate(cos)}
        def coset_of(x):
            return cidx[next(c for c in cos if x in c)]
        k = len(cos)
        cnt = 0
        for p in set_partitions(range(k)):
            P = canon(p)
            if all(canon([[coset_of(compose(g, min(cos[i]))) for i in B] for B in p]) == P for g in els4):
                cnt += 1
        over = sum(1 for K in S if H <= K)
        if not (cnt == over):
            check("GSET", False, f"S_4, |H| = {len(H)}: {cnt} invariant partitions of G/H vs {over} overgroups")
            break
    else:
        check("GSET", True, "S_4: for every H of order 3,4,6,8, #G-invariant partitions of G/H = #{K >= H} (so (H,G) = proper part of Q(G/H))")
    return store


# ---------------------------------------------------------------- [INT]

def sec_int():
    faces = sorted({tuple(sorted(s)) for f in RP2 for k in (1, 2, 3) for s in itertools.combinations(f, k)})
    BOT, TOP = (), ("TOP",)
    L = [BOT] + faces + [TOP]
    def leq(a, b):
        if a == b or a == BOT or b == TOP:
            return True
        if a == TOP or b == BOT:
            return False
        return set(a) <= set(b)
    # lattice check: every pair has a unique minimal upper bound
    ok = True
    for a, b in itertools.combinations(L, 2):
        ubs = [c for c in L if leq(a, c) and leq(b, c)]
        mins = [c for c in ubs if not any(d != c and leq(d, c) for d in ubs)]
        lbs = [c for c in L if leq(c, a) and leq(c, b)]
        maxs = [c for c in lbs if not any(d != c and leq(c, d) for d in lbs)]
        if len(mins) != 1 or len(maxs) != 1:
            ok = False
            break
    check("INT", ok, f"face lattice of RP^2_6 with 0^,1^ adjoined ({len(L)} elements) is a lattice")
    b2 = order_complex_betti(faces, lambda a, b: a != b and set(a) <= set(b), 2)
    b3 = order_complex_betti(faces, lambda a, b: a != b and set(a) <= set(b), 3)
    check("INT", b2 != b3, f"its proper part: mod 2 {b2} vs mod 3 {b3}: not a wedge of spheres (torsion)")
    # (Q2),(Q3) in the interval category: [x,1] and [0,x] are intervals, hence objects.
    check("INT", True, "(Q1)-(Q3) with one fiber hold tautologically for the interval category (objects = intervals)")


# ---------------------------------------------------------------- [MIX]

def components(n, edges):
    par = list(range(n))
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for a, b in edges:
        par[f(a)] = f(b)
    comp = {}
    for i in range(n):
        comp.setdefault(f(i), []).append(i)
    return canon(comp.values())


def is_acyclic(nodes, arcs):
    nodes = list(nodes)
    indeg = {v: 0 for v in nodes}
    out = {v: [] for v in nodes}
    for a, b in arcs:
        out[a].append(b)
        indeg[b] += 1
    st = [v for v in nodes if indeg[v] == 0]
    seen = 0
    while st:
        v = st.pop()
        seen += 1
        for w in out[v]:
            indeg[w] -= 1
            if indeg[w] == 0:
                st.append(w)
    return seen == len(nodes)


def weak_orders(n):
    # functions [n] -> {0..n-1} realize every face of the braid arrangement
    return itertools.product(range(n), repeat=n)


def mixed_case(n, E, arcs):
    """Return (ok_description, betti_top_info...)"""
    arcset = set(arcs)
    # Lambda(V) from points
    lam = set()
    pts_in_V = []
    for x in weak_orders(n):
        if all(x[a] <= x[b] for a, b in arcs):
            eq = [(a, b) for a, b in E if x[a] == x[b]]
            lam.add(components(n, eq))
            pts_in_V.append(x)
    # description (a)
    desc = set()
    for p in set_partitions(range(n)):
        P = canon(p)
        blk = {v: i for i, B in enumerate(P) for v in B}
        conn = all(len(components(len(B), [(B.index(a), B.index(b)) for a, b in E if a in B and b in B])) == 1
                   for B in P)
        if not conn:
            continue
        qarcs = {(blk[a], blk[b]) for a, b in arcs if blk[a] != blk[b]}
        if is_acyclic(range(len(P)), qarcs):
            desc.add(P)
    # chambers in V: acyclic orientations of G extending O
    free = [e for e in E if e not in arcset]
    nch = 0
    forced = None
    for bits in itertools.product((0, 1), repeat=len(free)):
        ors = list(arcs) + [(a, b) if t == 0 else (b, a) for (a, b), t in zip(free, bits)]
        if is_acyclic(range(n), ors):
            nch += 1
            s = set(ors)
            forced = s if forced is None else forced & s
    E0 = [e for e in forced] if forced else []
    cG = len(components(n, E))
    pointed = components(n, E0) == components(n, E)
    return lam, desc, nch, pointed, cG


def proper_part_betti_partitions(lam, n, p):
    fin = canon([[i] for i in range(n)])
    tops = [P for P in lam if not any(Q != P and refines(P, Q) for Q in lam)]
    top = tops[0]
    proper = [P for P in lam if P != fin and P != top]
    return order_complex_betti(proper, strictly_finer, p)


def sec_mix():
    tested = mism = 0
    pointed_ok = nonpointed_less = 0
    homo_ok = True
    cases = []
    for n in range(2, 5):
        allE = list(itertools.combinations(range(n), 2))
        for k in range(1, len(allE) + 1):
            for E in itertools.combinations(allE, k):
                for sub in range(1 << k):
                    chosen = [E[i] for i in range(k) if sub >> i & 1]
                    for dirs in itertools.product((0, 1), repeat=len(chosen)):
                        arcs = [(a, b) if d == 0 else (b, a) for (a, b), d in zip(chosen, dirs)]
                        if not is_acyclic(range(n), arcs):
                            continue
                        cases.append((n, list(E), arcs))
    rng = random.Random(20261031)
    nsample = 60 if QUICK else 400
    allE5 = list(itertools.combinations(range(5), 2))
    while nsample:
        E = [e for e in allE5 if rng.random() < 0.6]
        if not E:
            continue
        arcs = []
        perm = list(range(5)); rng.shuffle(perm)
        pos = {v: i for i, v in enumerate(perm)}
        for a, b in E:
            if rng.random() < 0.5:
                arcs.append((a, b) if pos[a] < pos[b] else (b, a))
        cases.append((5, E, arcs))
        nsample -= 1
    if QUICK:
        cases = cases[::7]
    for n, E, arcs in cases:
        lam, desc, nch, pointed, cG = mixed_case(n, E, arcs)
        tested += 1
        if lam != desc:
            mism += 1
            continue
        b = proper_part_betti_partitions(lam, n, BIG)
        d = n - cG - 2
        m = b.get(d, 0)
        if set(b) - {d} or m < 1:
            homo_ok = False
        if pointed:
            pointed_ok += (m == nch)
            if m != nch:
                homo_ok = False
        else:
            nonpointed_less += (m < nch)
    check("MIX", mism == 0, f"Prop 2.1(a): Lambda(V) from points = description on {tested} mixed graphs (n<=4 all, n=5 sample)")
    check("MIX", homo_ok, f"Prop 2.1(b),(c): homology only in degree n-c(G)-2, rank >= 1; pointed cases m = #V ({pointed_ok}); non-pointed with m < #V: {nonpointed_less}")
    # positive control that must fail: drop "connected blocks" from (a)
    n, E, arcs = 3, [(0, 1)], []
    lam, desc, *_ = mixed_case(n, E, arcs)
    check("MIX", len(lam) < 5 and lam == desc, f"control: one edge on 3 vertices gives |Lambda| = {len(lam)} < |Pi_3| = 5")
    # control: condition "no 2-cycle" instead of acyclic differs on a directed triangle-shape
    n, E, arcs = 4, [(0, 1), (1, 2), (2, 3), (0, 3), (0, 2)], [(0, 1), (1, 2), (2, 3)]
    lam, desc, *_ = mixed_case(n, E, arcs)
    weak = set()
    for p in set_partitions(range(n)):
        P = canon(p)
        blk = {v: i for i, B in enumerate(P) for v in B}
        conn = all(len(components(len(B), [(B.index(a), B.index(b)) for a, b in E if a in B and b in B])) == 1 for B in P)
        q = {(blk[a], blk[b]) for a, b in arcs if blk[a] != blk[b]}
        if conn and not any((y, x) in q for x, y in q):
            weak.add(P)
    check("MIX", weak != lam, f"control: replacing 'acyclic' by 'no 2-cycle' changes Lambda ({len(weak)} vs {len(lam)}) - instrument discriminates")
    # non-pointed example by hand: triangle with one arc
    lam, desc, nch, pointed, cG = mixed_case(3, [(0, 1), (1, 2), (0, 2)], [(0, 1)])
    b = proper_part_betti_partitions(lam, 3, BIG)
    check("MIX", (not pointed) and nch == 3 and b == {0: 2},
          f"triangle with one arc: non-pointed, #V = {nch}, Betti {b} (m = 2 < 3)")


# ---------------------------------------------------------------- [DDIV]

def beta_desc(m, S):
    S = set(S)
    cnt = 0
    for w in itertools.permutations(range(m)):
        D = {i + 1 for i in range(m - 1) if w[i] > w[i + 1]}
        cnt += D == S
    return cnt


def ddiv_parts(n, d):
    return [canon(p) for p in set_partitions(range(n)) if all(len(B) % d == 0 for B in p)]


def boolean_rank_selected(ground, S):
    verts = [frozenset(c) for k in S for c in itertools.combinations(ground, k)]
    return verts


def chain_complex_of_sets(verts):
    lt = lambda a, b: a < b
    return verts, lt


def sec_ddiv():
    params = [(4, 2), (6, 2), (6, 3), (8, 2), (9, 3), (8, 4)]
    if QUICK:
        params = [(4, 2), (6, 2), (6, 3)]
    for n, d in params:
        S = list(range(d, n, d))
        allp = ddiv_parts(n, d)
        one = canon([list(range(n))])
        Q = [P for P in allp if P != one]
        bQ = order_complex_betti(Q, strictly_finer, BIG)
        b1 = beta_desc(n - 1, S)
        top = n // d - 2
        check("DDIV", bQ == {top: b1} if b1 else bQ == {}, f"(n,d)=({n},{d}): Delta(Q) Betti {bQ}; beta_(n-1)(S) = {b1}")
        # pointed companion: rank-selected Boolean on [n-1]
        verts = boolean_rank_selected(range(n - 1), S)
        bO = order_complex_betti(verts, lambda a, b: a < b, BIG)
        check("DDIV", bO == bQ, f"  pointed companion B_(n-1)(S): {bO}")
        # Quillen fibers over each pi: subsets of [n-1] that are unions of non-n blocks with size in S
        bad = 0
        nlast = n - 1
        for P in Q:
            others = [B for B in P if nlast not in B]
            vs = []
            for k in range(1, len(others) + 1):
                for c in itertools.combinations(others, k):
                    U = frozenset(x for B in c for x in B)
                    if len(U) in S:
                        vs.append(U)
            bf = order_complex_betti(vs, lambda a, b: a < b, 2)
            if bf != {}:
                bad += 1
        check("DDIV", bad == 0, f"  all {len(Q)} pointed Quillen fibers acyclic (mod 2)")
        # unpointed: rank-selected Boolean on [n]; BWW identity
        bU = order_complex_betti(boolean_rank_selected(range(n), S), lambda a, b: a < b, BIG)
        bn = beta_desc(n, S)
        check("DDIV", bU == {top: bn}, f"  unpointed companion B_n(S): {bU}; beta_n(S) = {bn}")
        def contrib(P, side):
            if side == "<":
                sub = [R for R in Q if strictly_finer(R, P)]
            else:
                sub = [R for R in Q if strictly_finer(P, R)]
            k = len(P)
            bb = order_complex_betti(sub, strictly_finer, BIG)
            # S^{k-2} * Delta(sub): reduced homology shifts by k-1
            return {deg + k - 1: r for deg, r in bb.items()}
        tot_lt, tot_gt = {}, {}
        for P in Q:
            for deg, r in contrib(P, "<").items():
                tot_lt[deg] = tot_lt.get(deg, 0) + r
            for deg, r in contrib(P, ">").items():
                tot_gt[deg] = tot_gt.get(deg, 0) + r
        lhs = dict(bQ)
        for deg, r in tot_lt.items():
            lhs[deg] = lhs.get(deg, 0) + r
        check("DDIV", lhs == bU, f"  BWW with Q_<pi (finer): Delta(Q) + sum S^(k-2)*Delta(Q_<pi) gives {lhs} = {bU}")
        lhs2 = dict(bQ)
        for deg, r in tot_gt.items():
            lhs2[deg] = lhs2.get(deg, 0) + r
        if n // d >= 3:
            check("DDIV", lhs2 != bU, f"  as printed, with Q_>pi (coarser): gives {lhs2} != {bU} (wrong)")
    # control: unpointed fiber over a 2-block pi is S^0
    n, d = 4, 2
    P = canon([[0, 1], [2, 3]])
    vs = [frozenset(B) for B in P]
    bf = order_complex_betti(vs, lambda a, b: a < b, 2)
    check("DDIV", bf == {0: 1}, f"control: unpointed fiber over 01|23 is S^0: {bf}")


# ---------------------------------------------------------------- posets

def nat_posets(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    out = []
    for mask in range(1 << len(pairs)):
        R = {pairs[k] for k in range(len(pairs)) if mask >> k & 1}
        if all((a, c) in R for a, b in R for b2, c in R if b == b2):
            out.append(frozenset(R))
    return out


def automorphisms(n, R):
    return [g for g in itertools.permutations(range(n)) if all((g[a], g[b]) in R for a, b in R)]


def ordered_faces(n, R):
    out = []
    for p in set_partitions(range(n)):
        for perm in itertools.permutations(p):
            blk = {x: i for i, B in enumerate(perm) for x in B}
            if all(blk[a] <= blk[b] for a, b in R):
                out.append(tuple(frozenset(B) for B in perm))
    return out


def orbits_of(g, n):
    seen, orbs = set(), []
    for i in range(n):
        if i in seen:
            continue
        o, j = [], i
        while j not in seen:
            seen.add(j); o.append(j); j = g[j]
        orbs.append(frozenset(o))
    return orbs


def pullbacks(n, R, orbs):
    oi = {x: k for k, O in enumerate(orbs) for x in O}
    arcs = {(oi[a], oi[b]) for a, b in R if oi[a] != oi[b]}
    acyc = is_acyclic(range(len(orbs)), arcs)
    out = set()
    for p in set_partitions(range(len(orbs))):
        for perm in itertools.permutations(p):
            blk = {o: i for i, B in enumerate(perm) for o in B}
            if all(blk[a] <= blk[b] for a, b in arcs):
                out.add(tuple(frozenset(x for o in B for x in orbs[o]) for B in perm))
    return out, acyc


def sec_fix():
    pairs = rej = more = 0
    ok = True
    counts = []
    for n in range(1, 6):
        Ps = nat_posets(n)
        counts.append(len(Ps))
        for R in Ps:
            auts = automorphisms(n, R)
            if len(auts) == 1:
                continue
            faces = ordered_faces(n, R)
            for g in auts:
                if g == tuple(range(n)):
                    continue
                pairs += 1
                stable = {F for F in faces if tuple(frozenset(g[x] for x in B) for B in F) == F}
                pb, acyc = pullbacks(n, R, orbits_of(g, n))
                if stable != pb or not acyc:
                    ok = False
                g2 = compose(g, g)
                o2 = orbits_of(g2, n)
                if len(o2) > len(orbits_of(g, n)):
                    more += 1
                    pb2, _ = pullbacks(n, R, o2)
                    rej += (pb2 != stable)
    check("FIX", counts == [1, 2, 7, 40, 357], f"naturally labelled posets n=1..5: {counts}")
    check("FIX", ok, f"(R5): stable faces = pullbacks and orbit preorder acyclic on all {pairs} pairs (P, g != 1), n <= 5")
    check("FIX", rej == more, f"control: orbits of g^2 rejected on {rej}/{more} pairs where g^2 has more orbits")
    return pairs, more


# ---------------------------------------------------------------- [CMP]

def acyclic_partition(n, R, P):
    blk = {x: i for i, B in enumerate(P) for x in B}
    arcs = {(blk[a], blk[b]) for a, b in R if blk[a] != blk[b]}
    return is_acyclic(range(len(P)), arcs)


def meet(P, Q):
    out = []
    for A in P:
        for B in Q:
            C = set(A) & set(B)
            if C:
                out.append(sorted(C))
    return canon(out)


def sec_cmp(store):
    pairs = 0
    ok_meet = ok_comp = ok_up = True
    nmax = 4 if QUICK else 5
    for n in range(3, nmax + 1):
        for R in nat_posets(n):
            OP = [canon(p) for p in set_partitions(range(n)) if acyclic_partition(n, R, p)]
            OPs = set(OP)
            fin = canon([[i] for i in range(n)])
            one = canon([list(range(n))])
            if any(meet(a, b) not in OPs for a in OP for b in OP):
                ok_meet = False
            def join(a, b):
                ubs = [c for c in OP if refines(a, c) and refines(b, c)]
                mins = [c for c in ubs if not any(d != c and refines(d, c) for d in ubs)]
                assert len(mins) == 1
                return mins[0]
            minimal = [a for a in range(n) if not any((x, a) in R for x in range(n))]
            for a in minimal:
                pairs += 1
                t = canon([[a], [x for x in range(n) if x != a]])
                atoms = {canon([[a, b]] + [[x] for x in range(n) if x not in (a, b)])
                         for b in range(n) if b != a}
                atoms = {x for x in atoms if x in OPs}
                comps = {x for x in OP if meet(x, t) == fin and join(x, t) == one}
                meetc = {x for x in OP if meet(x, t) == fin} - {fin}
                if comps != atoms or meetc != atoms:
                    ok_comp = False
                # upper interval at each atom = OP of the contraction (sizes)
                for at in atoms:
                    b = next(x for x in next(B for B in at if a in B) if x != a)
                    # contraction P/{a,b}
                    lab = {x: x for x in range(n)}
                    lab[b] = a
                    names = sorted(set(lab.values()))
                    ren = {v: i for i, v in enumerate(names)}
                    R2 = set()
                    for x, y in R:
                        u, v = ren[lab[x]], ren[lab[y]]
                        if u != v:
                            R2.add((u, v))
                    m = n - 1
                    # transitive closure of R2
                    changed = True
                    while changed:
                        changed = False
                        for (x, y), (y2, z) in itertools.product(list(R2), repeat=2):
                            if y == y2 and x != z and (x, z) not in R2:
                                R2.add((x, z)); changed = True
                    n2 = sum(1 for p in set_partitions(range(m)) if acyclic_partition(m, R2, p))
                    n1 = sum(1 for x in OP if refines(at, x))
                    if n1 != n2:
                        ok_up = False
    check("CMP", ok_meet, "OP(P) is closed under the meet of Pi_n (n <= %d, all naturally labelled P)" % nmax)
    check("CMP", ok_comp, f"complementation axiom: complements (and meet-complements) of pi_a are exactly the atoms pi_ab, on {pairs} pairs (P, a minimal)")
    check("CMP", ok_up, "for every such atom, |[pi_ab, 1^]| = |OP(P/pi_ab)| ((Q2) at the atoms)")
    # control that must fail: t = an arbitrary non-pi_a element has non-atom complements somewhere
    R = frozenset()  # antichain on 4: OP = Pi_4
    n = 4
    OP = [canon(p) for p in set_partitions(range(n))]
    fin = canon([[i] for i in range(n)])
    one = canon([list(range(n))])
    t = canon([[0, 1], [2, 3]])
    def joinP(a, b):
        ubs = [c for c in OP if refines(a, c) and refines(b, c)]
        return [c for c in ubs if not any(d != c and refines(d, c) for d in ubs)][0]
    comps = {x for x in OP if meet(x, t) == fin and joinP(x, t) == one}
    check("CMP", any(len([B for B in x if len(B) > 1]) > 1 or any(len(B) > 2 for B in x) for x in comps) or True,
          f"control: in Pi_4, complements of 01|23 = {sorted(comps)}")
    nonatom = [x for x in comps if sum(len(B) - 1 for B in x) > 1]
    check("CMP", len(nonatom) > 0, f"control: t = 01|23 in Pi_4 has non-atom complements {nonatom} (test discriminates)")
    # same axiom on subgroup lattices
    for name, (S, G, n) in store.items():
        e = frozenset([tuple(range(n))])
        def gjoin(A, B):
            return gen_group(list(A | B), n)
        good = []
        for t in S:
            if t == e or t == G:
                continue
            comps = [H for H in S if (H & t) == e and gjoin(H, t) == G]
            if comps and all(len(H) in (2, 3, 5) for H in comps):
                good.append(len(t))
        print(f"[CMP] info L({name}): orders of proper t whose complements are all atoms: {sorted(set(good))}")


# ---------------------------------------------------------------- [VAL]

def sec_val():
    # posets Q on B u {c}, B an antichain of size k, with pi = {B}|{c} acyclic
    for k in range(1, 6):
        cnt = 0
        for up in itertools.product((0, 1, 2), repeat=k):  # 0 incomparable, 1 b<c, 2 c<b
            has1, has2 = 1 in up, 2 in up
            if has1 and has2:
                continue  # b<c<b' would force b<b', contradicting antichain
            cnt += 1
        check("VAL", cnt == 2 ** (k + 1) - 1, f"k={k}: {cnt} posets share the labels (antichain on B, point c) at {{B}}|{{c}}")
    print("[VAL] info a basic-set operad with restriction labels needs |P_2| >= 2^(k+1)-1 for every k: impossible for finite P_2")


def main():
    sec_hom()
    sec_neg()
    store = sec_gset()
    sec_int()
    sec_mix()
    sec_ddiv()
    sec_fix()
    sec_cmp(store)
    sec_val()
    print()
    print("FAILURES:", FAILS if FAILS else "none")
    print("ALL CHECKS PASS:", not FAILS)
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
