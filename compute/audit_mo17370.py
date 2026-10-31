"""Independent audit of notes/mo17370_wedges_of_spheres.md: claim (E1), the
integral reading of Route C, and the rank-4 tree of section 2.6.

Written from the definitions only. Imports nothing from the repository
(in particular not mo17370_homotopy_checks.py, cr_v_type_a.py or
conjecture_cr_v.py).

Model.
  P: a poset on [n], as a set of strict relations (i, j) meaning i <_P j.
  OP(P): the set partitions of [n] whose quotient digraph (B -> B' when some
    i in B, j in B' have i <_P j, B != B') is acyclic, ordered by refinement.
  g = +tau (tau in Aut P) or g = -tau (tau an anti-automorphism); g acts on
    the flats of the braid arrangement as tau acts on set partitions, so the
    fixed lattice of g is M = OP(P)^tau (dual to Lambda(C_P)^g; duality
    changes neither the order complex nor complementation).
  Lattice operations are NOT taken from any formula: complements are found
  from the definition (common lower bounds = {0}, common upper bounds = {1})
  and M is checked to be a lattice by brute force.

Parts:
  [CTL]  poset counts (OEIS A000112); Stong-core controls (chain, B_3,
         crown, Pi_4); mod-p Betti controls.
  [E1]   every poset with 3 <= n <= NMAX up to isomorphism, every g up to
         Aut(P)-conjugacy: mu(M); Stong core of the proper part of M; an
         uncomplemented element (Kozlov 1998, Thm 2.4 hypothesis); mod-p
         Betti numbers where the order complex is small enough.
         Assertions: mu = 0  =>  core is one point   (E1, computed)
                     mu != 0 =>  core is not a point (positive control:
                                 a nonzero reduced Euler characteristic
                                 rules out contractibility)
                     uncomplemented element => core is one point (Kozlov)
                     mu = 0 <=> uncomplemented element    (TA-CR, n <= NMAX)
  [ZZ]   tau = id: reduced Betti numbers of Delta(proper part of OP(P)) mod 2,
         mod 3 and mod a large prime agree and are concentrated in degree
         n - 3 (consistent with integral concentration and freeness).
  [R4]   the 9-element lattice of notes/conjecture_cr_v.md section 0.2, rebuilt
         from the coordinates given there by exact rank computations.
"""

import argparse
import itertools
import sys
from fractions import Fraction

BIGP = 2147483647


# ---------------------------------------------------------------- posets

def closure(n, rel):
    r = set(rel)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(r):
            for (c, d) in list(r):
                if b == c and (a, d) not in r:
                    r.add((a, d))
                    changed = True
    return frozenset(r)


def canon(n, rel):
    """Lexicographically least relation set over all relabelings, with the
    search restricted to permutations preserving (indegree, outdegree)."""
    indeg = [0] * n
    outdeg = [0] * n
    for (a, b) in rel:
        outdeg[a] += 1
        indeg[b] += 1
    key = [(indeg[i], outdeg[i]) for i in range(n)]
    order = sorted(range(n), key=lambda i: key[i])
    groups = []
    for k, grp in itertools.groupby(order, key=lambda i: key[i]):
        groups.append(list(grp))
    best = None
    for choice in itertools.product(*[itertools.permutations(g) for g in groups]):
        seq = [x for g in choice for x in g]   # new label t -> old element seq[t]
        pos = {old: t for t, old in enumerate(seq)}
        r = tuple(sorted((pos[a], pos[b]) for (a, b) in rel))
        if best is None or r < best:
            best = r
    return best


def posets_up_to_iso(nmax):
    """Natural labelings: element n-1 added on top of a down-closed set."""
    level = {0: [frozenset()]}
    out = {}
    for n in range(1, nmax + 1):
        seen = {}
        for rel in level[n - 1]:
            m = n - 1
            # down-closed subsets of the previous poset
            for mask in range(1 << m):
                S = [i for i in range(m) if mask >> i & 1]
                ok = all((mask >> a & 1) for (a, b) in rel if mask >> b & 1)
                if not ok:
                    continue
                r = set(rel) | {(i, m) for i in S}
                r = closure(n, r)
                c = canon(n, r)
                if c not in seen:
                    seen[c] = frozenset(c)
        level[n] = list(seen.values())
        out[n] = level[n]
    return out


def automorphisms(n, rel):
    auts, antis = [], []
    for p in itertools.permutations(range(n)):
        img = {(p[a], p[b]) for (a, b) in rel}
        if img == rel:
            auts.append(p)
        if {(b, a) for (a, b) in img} == rel:
            antis.append(p)
    return auts, antis


def compose(p, q):  # (p o q)(i) = p[q[i]]
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def conj_reps(maps, auts):
    reps, seen = [], set()
    for t in maps:
        if t in seen:
            continue
        reps.append(t)
        for s in auts:
            seen.add(compose(compose(s, t), inverse(s)))
    return reps


# ---------------------------------------------------------------- partitions

def set_partitions(n):
    def rec(i, cur, k):
        if i == n:
            yield tuple(cur)
            return
        for b in range(k + 1):
            cur.append(b)
            yield from rec(i + 1, cur, max(k, b + 1))
            cur.pop()
    yield from rec(0, [], 0)


def pairmask(n, part):
    m = 0
    for i in range(n):
        for j in range(i + 1, n):
            if part[i] == part[j]:
                m |= 1 << (i * n + j)
    return m


def acyclic_quotient(n, rel, part):
    k = max(part) + 1
    adj = [set() for _ in range(k)]
    for (a, b) in rel:
        if part[a] != part[b]:
            adj[part[a]].add(part[b])
    color = [0] * k

    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if color[v] == 1:
                return False
            if color[v] == 0 and not dfs(v):
                return False
        color[u] = 2
        return True
    return all(color[u] or dfs(u) for u in range(k))


def stable(part, tau):
    n = len(part)
    return all((part[i] == part[j]) == (part[tau[i]] == part[tau[j]])
               for i in range(n) for j in range(i + 1, n))


# ---------------------------------------------------------------- finite posets

class FinPoset:
    """Elements 0..N-1 with a leq matrix."""

    def __init__(self, leq):
        self.N = len(leq)
        self.leq = leq

    def lt(self, a, b):
        return a != b and self.leq[a][b]


def lattice_from_masks(masks):
    N = len(masks)
    leq = [[(masks[a] & ~masks[b]) == 0 for b in range(N)] for a in range(N)]
    return FinPoset(leq)


def bottom_top(L):
    bot = [a for a in range(L.N) if all(L.leq[a][b] for b in range(L.N))]
    top = [a for a in range(L.N) if all(L.leq[b][a] for b in range(L.N))]
    assert len(bot) == 1 and len(top) == 1
    return bot[0], top[0]


def is_lattice(L):
    for a in range(L.N):
        for b in range(a + 1, L.N):
            lb = [x for x in range(L.N) if L.leq[x][a] and L.leq[x][b]]
            if not any(all(L.leq[y][x] for y in lb) for x in lb):
                return False
            ub = [x for x in range(L.N) if L.leq[a][x] and L.leq[b][x]]
            if not any(all(L.leq[x][y] for y in ub) for x in ub):
                return False
    return True


def mobius(L):
    bot, top = bottom_top(L)
    order = sorted(range(L.N), key=lambda x: sum(L.leq[y][x] for y in range(L.N)))
    mu = {}
    for x in order:
        if x == bot:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in range(L.N) if L.lt(y, x) and y in mu)
    return mu[top]


def has_uncomplemented(L):
    bot, top = bottom_top(L)
    for x in range(L.N):
        if x in (bot, top):
            continue
        found = False
        for y in range(L.N):
            lb = [z for z in range(L.N) if L.leq[z][x] and L.leq[z][y]]
            ub = [z for z in range(L.N) if L.leq[x][z] and L.leq[y][z]]
            if lb == [bot] and ub == [top]:
                found = True
                break
        if not found:
            return True
    return False


def proper_part(L):
    bot, top = bottom_top(L)
    return [x for x in range(L.N) if x not in (bot, top)]


def stong_core(L, elems):
    """Repeatedly delete beat points of the subposet on `elems`."""
    S = list(elems)
    while True:
        removed = False
        for x in S:
            down = [y for y in S if L.lt(y, x)]
            up = [y for y in S if L.lt(x, y)]
            if down and any(all(L.leq[z][m] for z in down) for m in down):
                S.remove(x); removed = True; break
            if up and any(all(L.leq[m][z] for z in up) for m in up):
                S.remove(x); removed = True; break
        if not removed:
            return S


def chains(L, elems, cap):
    """All nonempty chains of the subposet, as sorted tuples; None if > cap."""
    elems = sorted(elems, key=lambda x: sum(L.leq[y][x] for y in elems))
    out = []
    def rec(ch, start):
        for i in range(start, len(elems)):
            x = elems[i]
            if all(L.lt(c, x) for c in ch):
                ch.append(x)
                out.append(tuple(ch))
                if len(out) > cap:
                    raise OverflowError
                rec(ch, i + 1)
                ch.pop()
    try:
        rec([], 0)
    except OverflowError:
        return None
    return out


def rank_mod_p(rows, p):
    """rows: list of dict col->val. Gaussian elimination mod p."""
    pivots = {}
    r = 0
    for row in rows:
        row = {k: v % p for k, v in row.items() if v % p}
        while row:
            c = min(row)
            if c in pivots:
                prow = pivots[c]
                f = row[c]
                for k, v in prow.items():
                    nv = (row.get(k, 0) - f * v) % p
                    if nv:
                        row[k] = nv
                    else:
                        row.pop(k, None)
            else:
                inv = pow(row[c], p - 2, p)
                row = {k: v * inv % p for k, v in row.items()}
                pivots[c] = row
                r += 1
                break
    return r


def reduced_betti(chs, p):
    """Reduced Betti numbers mod p of the order complex with these chains
    (the empty chain in degree -1)."""
    if not chs:
        return {-1: 1}
    bydim = {}
    for c in chs:
        bydim.setdefault(len(c) - 1, []).append(c)
    bydim[-1] = [()]
    index = {d: {c: i for i, c in enumerate(v)} for d, v in bydim.items()}
    top = max(bydim)
    rk = {}
    for d in range(0, top + 1):
        rows = []
        for c in bydim[d]:
            row = {}
            for i in range(len(c)):
                f = c[:i] + c[i + 1:]
                row[index[d - 1][f]] = (-1) ** i
            rows.append(row)
        rk[d] = rank_mod_p(rows, p)
    betti = {}
    for d in range(-1, top + 1):
        dimC = len(bydim[d])
        b = dimC - rk.get(d, 0) - rk.get(d + 1, 0)
        if b:
            betti[d] = b
    return betti


# ---------------------------------------------------------------- controls

def boolean(k):
    masks = list(range(1 << k))
    return lattice_from_masks(masks)


def from_cover(names, less):
    """Poset from strict relations given by name pairs (transitively closed)."""
    idx = {x: i for i, x in enumerate(names)}
    N = len(names)
    leq = [[i == j for j in range(N)] for i in range(N)]
    for (a, b) in less:
        leq[idx[a]][idx[b]] = True
    for k in range(N):
        for i in range(N):
            for j in range(N):
                if leq[i][k] and leq[k][j]:
                    leq[i][j] = True
    return FinPoset(leq), idx


def build_M(n, rel, tau, allparts):
    parts = [q for q in allparts if stable(q, tau) and acyclic_quotient(n, rel, q)]
    masks = [pairmask(n, q) for q in parts]
    return lattice_from_masks(masks), parts


def controls(out):
    ok = True
    # chain 0<1<2<3<4: proper part 3-chain, core one point
    C, _ = from_cover(list(range(5)), [(i, i + 1) for i in range(4)])
    core = stong_core(C, proper_part(C))
    out.append(f"[CTL] 5-chain proper part: core size {len(core)} (expect 1)")
    ok &= len(core) == 1
    # B_3: proper part is the boundary of a triangle = S^1; no beat point
    B3 = boolean(3)
    core = stong_core(B3, proper_part(B3))
    bt = reduced_betti(chains(B3, proper_part(B3), 10 ** 5), BIGP)
    out.append(f"[CTL] B_3 proper part: core size {len(core)} (expect 6), betti {bt} (expect {{1: 1}})")
    ok &= len(core) == 6 and bt == {1: 1}
    # crown a,b < c,d : S^1, core 4
    Cr, _ = from_cover(['0', 'a', 'b', 'c', 'd', '1'],
                       [('0', 'a'), ('0', 'b'), ('a', 'c'), ('a', 'd'), ('b', 'c'),
                        ('b', 'd'), ('c', '1'), ('d', '1')])
    core = stong_core(Cr, proper_part(Cr))
    out.append(f"[CTL] crown: core size {len(core)} (expect 4)")
    ok &= len(core) == 4
    # Pi_4 (P = antichain on 4, tau = id): mu = -6, not contractible
    allp = list(set_partitions(4))
    L, _ = build_M(4, frozenset(), (0, 1, 2, 3), allp)
    mu = mobius(L)
    core = stong_core(L, proper_part(L))
    bt = reduced_betti(chains(L, proper_part(L), 10 ** 5), 2)
    out.append(f"[CTL] Pi_4: |L| = {L.N} (15), mu = {mu} (-6), core size {len(core)} (>1), "
               f"betti mod 2 {bt} (expect {{1: 6}})")
    ok &= L.N == 15 and mu == -6 and len(core) > 1 and bt == {1: 6}
    # Pi_4^{(1234)}: chain 0 < 13|24 < 1, mu = 0, uncomplemented
    L, parts = build_M(4, frozenset(), (1, 2, 3, 0), allp)
    out.append(f"[CTL] Pi_4^(1234): |M| = {L.N} (3), mu = {mobius(L)} (0), "
               f"uncomplemented {has_uncomplemented(L)} (True)")
    ok &= L.N == 3 and mobius(L) == 0 and has_uncomplemented(L)
    # mod-p control that DOES see torsion: the 6-vertex RP^2, as the face poset
    # of its triangulation (order complex = barycentric subdivision of RP^2).
    tri = [(0,1,2),(0,2,3),(0,3,4),(0,4,5),(0,5,1),(1,2,4),(2,3,5),(3,4,1),(4,5,2),(5,1,3)]
    faces = set()
    for t in tri:
        for k in (1, 2, 3):
            for f in itertools.combinations(sorted(t), k):
                faces.add(f)
    faces = sorted(faces)
    leq = [[set(a) <= set(b) for b in faces] for a in faces]
    F = FinPoset(leq)
    ch = chains(F, range(F.N), 10 ** 5)
    b2, bp = reduced_betti(ch, 2), reduced_betti(ch, BIGP)
    out.append(f"[CTL] RP^2: betti mod 2 {b2} (expect {{1: 1, 2: 1}}), mod large p {bp} (expect {{}})")
    ok &= b2 == {1: 1, 2: 1} and bp == {}
    return ok


# ---------------------------------------------------------------- [R4]

def rank_Q(vecs):
    M = [list(map(Fraction, v)) for v in vecs]
    r = 0
    cols = len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
    return r


def r4(out):
    a = (-3, 1, 0, 0); v2 = (1, 2, 0, 0); v3 = (-2, 3, 0, 0)
    e3 = (0, 0, 1, 0); e4 = (0, 0, 0, 1)
    I = [(1, 0, 0, 0), (0, 1, 0, 0), e3, e4]
    sub = {'0': [], 'a': [a], 'b': [e3], 'c': [e4], 'L': [a, e3], 'B': [a, e4],
           'C': [v2, e4], 'D': [v3, e4], 'R4': I}
    names = list(sub)

    def contained(x, y):
        if not sub[x]:
            return True
        if not sub[y]:
            return False
        return rank_Q(sub[x] + sub[y]) == rank_Q(sub[y])
    leq = [[contained(x, y) for y in names] for x in names]
    L = FinPoset(leq)
    pp = proper_part(L)
    edges = sorted((names[x], names[y]) for x in pp for y in pp if L.lt(x, y))
    core = stong_core(L, pp)
    bt = reduced_betti(chains(L, pp, 10 ** 4), BIGP)
    lat = is_lattice(L)
    unc = has_uncomplemented(L)
    mu = mobius(L)
    out.append(f"[R4] proper part {len(pp)} elements, {len(edges)} edges: {edges}")
    out.append(f"[R4] lattice {lat}, mu {mu}, uncomplemented element {unc}, "
               f"reduced betti {bt or '{} (acyclic)'}, Stong core {[names[x] for x in core]}")
    expect = [('a', 'B'), ('a', 'L'), ('b', 'L'), ('c', 'B'), ('c', 'C'), ('c', 'D')]
    return lat and mu == 0 and not unc and edges == expect and len(core) == 1 and not bt


# ---------------------------------------------------------------- main sweep

def sweep(nmax, cap, out):
    ok = True
    ps = posets_up_to_iso(nmax)
    counts = {n: len(ps[n]) for n in ps}
    out.append(f"[CTL] posets up to iso n=1..{nmax}: {[counts[n] for n in range(1, nmax + 1)]} "
               f"(A000112: 1, 2, 5, 16, 63, 318)")
    ok &= [counts[n] for n in range(1, nmax + 1)] == [1, 2, 5, 16, 63, 318][:nmax]
    tot = dict(pairs=0, zeros=0, nonzeros=0, zero_core1=0, nonzero_core_not_point=0,
               unc=0, unc_core1=0, tacr_agree=0, not_lattice=0,
               zero_betti_checked=0, zero_acyclic=0, nz_betti_checked=0, nz_single_deg=0,
               id_checked=0, id_conc=0, id_skipped=0)
    for n in range(3, nmax + 1):
        allp = list(set_partitions(n))
        row = dict(pairs=0, plus=0, minus=0, zeros=0)
        for rel in ps[n]:
            auts, antis = automorphisms(n, rel)
            gs = [(+1, t) for t in conj_reps(auts, auts)] + \
                 [(-1, t) for t in conj_reps(antis, auts)]
            for sign, tau in gs:
                L, parts = build_M(n, rel, tau, allp)
                if not is_lattice(L):
                    tot['not_lattice'] += 1
                    ok = False
                mu = mobius(L)
                pp = proper_part(L)
                core = stong_core(L, pp)
                unc = has_uncomplemented(L)
                tot['pairs'] += 1; row['pairs'] += 1
                row['plus' if sign > 0 else 'minus'] += 1
                chs = chains(L, pp, cap)
                if mu == 0:
                    tot['zeros'] += 1; row['zeros'] += 1
                    if len(core) == 1:
                        tot['zero_core1'] += 1
                    else:
                        ok = False
                        out.append(f"  FAIL zero with core {len(core)}: n={n} rel={sorted(rel)} g={sign}{tau}")
                    if chs is not None:
                        tot['zero_betti_checked'] += 1
                        if not reduced_betti(chs, 2) and not reduced_betti(chs, BIGP):
                            tot['zero_acyclic'] += 1
                else:
                    tot['nonzeros'] += 1
                    if len(core) != 1:   # empty (S^-1) or >= 2 points
                        tot['nonzero_core_not_point'] += 1
                    else:
                        ok = False
                        out.append(f"  FAIL nonzero with point core: n={n} rel={sorted(rel)}")
                    if chs is not None:
                        tot['nz_betti_checked'] += 1
                        b = reduced_betti(chs, BIGP)
                        if len(b) == 1:
                            tot['nz_single_deg'] += 1
                if unc:
                    tot['unc'] += 1
                    if len(core) == 1:
                        tot['unc_core1'] += 1
                    else:
                        ok = False
                if unc == (mu == 0):
                    tot['tacr_agree'] += 1
                else:
                    ok = False
                    out.append(f"  TA-CR mismatch n={n} rel={sorted(rel)} g={sign}{tau}")
                # [ZZ] tau = id, sign +
                if sign > 0 and tau == tuple(range(n)):
                    if chs is None:
                        tot['id_skipped'] += 1
                    else:
                        tot['id_checked'] += 1
                        b2 = reduced_betti(chs, 2)
                        b3 = reduced_betti(chs, 3)
                        bp = reduced_betti(chs, BIGP)
                        conc = (b2 == b3 == bp and set(bp) <= {n - 3}
                                and bp.get(n - 3, 0) == abs(mu))
                        if conc:
                            tot['id_conc'] += 1
                        else:
                            ok = False
                            out.append(f"  ZZ FAIL n={n} rel={sorted(rel)} {b2} {b3} {bp}")
        out.append(f"[E1] n={n}: pairs {row['pairs']} (+w {row['plus']}, -tau {row['minus']}), zeros {row['zeros']}")
    for k, v in tot.items():
        out.append(f"[E1] {k}: {v}")
    ok &= tot['zero_core1'] == tot['zeros'] and tot['nonzero_core_not_point'] == tot['nonzeros']
    ok &= tot['unc_core1'] == tot['unc'] and tot['tacr_agree'] == tot['pairs']
    ok &= tot['zero_acyclic'] == tot['zero_betti_checked']
    ok &= tot['id_conc'] == tot['id_checked']
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=6)
    ap.add_argument('--cap', type=int, default=6000,
                    help='skip mod-p homology when the order complex has more chains')
    args = ap.parse_args()
    out = []
    ok = controls(out)
    ok &= r4(out)
    ok &= sweep(args.nmax, args.cap, out)
    out.append('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    print('\n'.join(out))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
