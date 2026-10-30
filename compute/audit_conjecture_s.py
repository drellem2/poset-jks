#!/usr/bin/env python3
"""Independent audit of the Conjecture S proof (mg-8c10c).

Companion to notes/audit_conjecture_s.md.  Audits
notes/conjecture_s_splitting_cycles_span.md WITHOUT importing
compute/conjecture_s.py, compute/splitting_cycles.py or any other module of
this repository: posets, shuffles, Lie combs, splitting cycles, order
complexes and ranks are all re-implemented here.  Plain Python 3.

Letters are 0..n-1; a word is a tuple of distinct letters; a linear
combination is a dict word -> int.  Ranks are over GF(p), p = 2^31 - 1, and
every rank conclusion is drawn in the direction that is rigorous over Q
(rank_p <= rank_Q; see the audit note).

Checks (each prints one line; exit status 0 iff all pass):
  [L1]   Lemma 1: E_{a,x}(u ш v) equals the predicted +-(u\\x) ш v or 0, for
         every ordered pair of complementary nonempty words and every
         ordered pair (a, x), n <= NE.  Also E_{a,x}(Sh) lies in Sh by a
         Ree-free rank test (n <= 5).
  [ADJ]  <E_{a,x} w, w'> = <w, w'[a->xa] - w'[a->ax]> for all words, and the
         substitution a -> [x,a] maps every right comb to an element
         orthogonal to all proper shuffles (n <= 5).
  [REE]  shuffle membership via comb coordinates agrees with the Ree-free
         generator test on every W_P (n <= NREE).
  [LEM]  Lemmas 2(a)(b), 3, 4, 5 and the (*) support claim, every poset and
         every adjacent pair, n <= NLEM.
  [AB]   Theorem A (B_P independent mod Sh), |B_P| = e_C(P) with e_C counted
         as C_n-orbits meeting Lin P, Lemma 6 (W_P = span B_P + R_P),
         Theorem B (K_P = R_P), every unlabeled poset with n <= NMAX and every
         choice of base component.
  [CHN]  chain level, no Prop. Phi and no Jenca-Sarkoci: Lemma D, rho_w is an
         integral cycle, rank{rho_w : w in B_P} = |B_P| = dim of the top cycle
         space of Delta(O^(P)), every R_P generator gives an exact chain
         relation, the explicit isomorphism of Cor. 5.5 holds at chain level
         (rho_w = sum_b sgn(w) sgn(b) N(w)_b rho_b), and g rho_w = rho_{gw}
         for g in Aut(P), n <= NCHN.
  [CTL]  positive controls: each instrument fires on a known-bad input.

Run (from compute/):
  python3 audit_conjecture_s.py --nmax 6 --ne 6 --nlem 6 --nchn 6 --nree 6
"""

import argparse
import heapq
import itertools
import sys
from collections import defaultdict
from math import factorial

PRIME = 2147483647

# ---------------------------------------------------------------------------
# Linear algebra over GF(p): incremental echelon on sparse dict vectors.


class Echelon:
    """Rows kept with pivot = least column; reduce() gives the normal form
    (no pivot column survives), a linear map whose kernel is the span."""

    def __init__(self):
        self.piv = {}

    def reduce(self, vec):
        v = {k: c % PRIME for k, c in vec.items() if c % PRIME}
        heap = [k for k in v if k in self.piv]
        heapq.heapify(heap)
        while heap:
            c = heapq.heappop(heap)
            if c not in v:
                continue
            f = v[c]
            for k, val in self.piv[c].items():
                nv = (v.get(k, 0) - f * val) % PRIME
                if nv:
                    if k not in v and k in self.piv:
                        heapq.heappush(heap, k)
                    v[k] = nv
                else:
                    v.pop(k, None)
        return v

    def add(self, vec):
        """Insert; return True iff vec was independent of the span."""
        v = self.reduce(vec)
        if not v:
            return False
        c = min(v)
        inv = pow(v[c], PRIME - 2, PRIME)
        self.piv[c] = {k: val * inv % PRIME for k, val in v.items()}
        return True

    def rank(self):
        return len(self.piv)


def rank(vecs):
    e = Echelon()
    for v in vecs:
        e.add(v)
    return e.rank()


# ---------------------------------------------------------------------------
# Words, shuffles, Lie combs


def sgn(w):
    s = 1
    for i in range(len(w)):
        for j in range(i + 1, len(w)):
            if w[i] > w[j]:
                s = -s
    return s


def shuffle_set(u, v):
    if not u:
        return [v]
    if not v:
        return [u]
    return [(u[0],) + z for z in shuffle_set(u[1:], v)] + \
           [(v[0],) + z for z in shuffle_set(u, v[1:])]


def proper_shuffle_pairs(letters):
    """All (u, v): nonempty words with complementary letter sets."""
    letters = tuple(letters)
    n = len(letters)
    for k in range(1, n):
        for S in itertools.combinations(letters, k):
            T = tuple(y for y in letters if y not in S)
            for u in itertools.permutations(S):
                for v in itertools.permutations(T):
                    yield u, v


def vec_of(words, coef=1):
    d = defaultdict(int)
    for z in words:
        d[z] += coef
    return dict(d)


def delete(w, x):
    return tuple(y for y in w if y != x)


def E(vec, a, x, sign=1):
    out = defaultdict(int)
    for w, c in vec.items():
        i = w.index(a)
        if i > 0 and w[i - 1] == x:
            out[delete(w, x)] += c
        elif i + 1 < len(w) and w[i + 1] == x:
            out[delete(w, x)] -= sign * c
    return {k: v for k, v in out.items() if v}


def substitute(w, a, x):
    """w[a -> xa] - w[a -> ax] (the adjoint of E_{a,x})."""
    i = w.index(a)
    return {w[:i] + (x, a) + w[i + 1:]: 1, w[:i] + (a, x) + w[i + 1:]: -1}


def bracket(p, q):
    out = defaultdict(int)
    for u, c in p.items():
        for v, d in q.items():
            out[u + v] += c * d
            out[v + u] -= c * d
    return {k: v for k, v in out.items() if v}


def right_comb(t):
    q = {(t[-1],): 1}
    for y in reversed(t[:-1]):
        q = bracket({(y,): 1}, q)
    return q


_COMB = {}


def comb_coords(n):
    """word -> {comb index: coefficient}; combs r_t, t(n) = n-1."""
    if n not in _COMB:
        coords = defaultdict(dict)
        for idx, t in enumerate(itertools.permutations(range(n - 1))):
            for w, c in right_comb(t + (n - 1,)).items():
                coords[w][idx] = c
        _COMB[n] = coords
    return _COMB[n]


def mod_sh_vec(vec, n):
    """Image of vec under the comb-coordinate map (kernel = Sh_n by Ree)."""
    co = comb_coords(n)
    out = defaultdict(int)
    for w, c in vec.items():
        for k, d in co.get(w, {}).items():
            out[k] += c * d
    return dict(out)


_SHECH = {}


def sh_echelon(n):
    """Ree-free: echelon basis of Sh_n from the shuffle generators."""
    if n not in _SHECH:
        e = Echelon()
        for u, v in proper_shuffle_pairs(range(n)):
            e.add({WID[n][z]: 1 for z in shuffle_set(u, v)})
        _SHECH[n] = e
    return _SHECH[n]


WID = {}


def word_ids(n):
    if n not in WID:
        WID[n] = {w: i for i, w in enumerate(itertools.permutations(range(n)))}
    return WID[n]


# ---------------------------------------------------------------------------
# Posets: up[i] = set of j with i < j (transitively closed).


class Poset:
    def __init__(self, n, rel):
        self.n = n
        self.rel = frozenset(rel)  # pairs (i, j) with i < j in P
        self.up = [set() for _ in range(n)]
        for i, j in self.rel:
            self.up[i].add(j)

    def less(self, i, j):
        return (i, j) in self.rel

    def comparable(self, i, j):
        return (i, j) in self.rel or (j, i) in self.rel

    def is_lin(self, w):
        pos = {y: k for k, y in enumerate(w)}
        return all(pos[i] < pos[j] for i, j in self.rel)

    def lin(self):
        res = []
        below = [set() for _ in range(self.n)]
        for i, j in self.rel:
            below[j].add(i)

        def rec(pref, used):
            if len(pref) == self.n:
                res.append(tuple(pref))
                return
            for y in range(self.n):
                if y not in used and below[y] <= used:
                    used.add(y)
                    pref.append(y)
                    rec(pref, used)
                    pref.pop()
                    used.discard(y)

        rec([], set())
        return res

    def components(self):
        comp = list(range(self.n))

        def find(a):
            while comp[a] != a:
                comp[a] = comp[comp[a]]
                a = comp[a]
            return a

        for i, j in self.rel:
            comp[find(i)] = find(j)
        groups = defaultdict(set)
        for y in range(self.n):
            groups[find(y)].add(y)
        return [frozenset(g) for g in groups.values()]

    def automorphisms(self):
        for g in itertools.permutations(range(self.n)):
            if all((g[i], g[j]) in self.rel for i, j in self.rel):
                yield g


def closure(n, pairs):
    """Transitive closure; None if it has a cycle."""
    up = [set() for _ in range(n)]
    for i, j in pairs:
        up[i].add(j)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            new = set()
            for j in up[i]:
                new |= up[j]
            if not new <= up[i]:
                up[i] |= new
                changed = True
    if any(i in up[i] for i in range(n)):
        return None
    return {(i, j) for i in range(n) for j in up[i]}


def canonical(n, rel):
    up = [0] * n
    dn = [0] * n
    for i, j in rel:
        up[i] += 1
        dn[j] += 1
    inv = [(dn[i], up[i], tuple(sorted((dn[j], up[j]) for j in range(n)
                                       if (i, j) in rel or (j, i) in rel)))
           for i in range(n)]
    classes = defaultdict(list)
    for i in range(n):
        classes[inv[i]].append(i)
    keys = sorted(classes)
    best = None
    for choice in itertools.product(*[itertools.permutations(classes[k])
                                      for k in keys]):
        order = [y for blk in choice for y in blk]
        pos = {y: k for k, y in enumerate(order)}
        code = tuple(sorted((pos[i], pos[j]) for i, j in rel))
        if best is None or code < best:
            best = code
    return best


def unlabeled_posets(nmax):
    """{n: [Poset]} up to isomorphism, n = 1..nmax, by adding a maximal
    element above a down-set; labels relabelled to a natural labeling."""
    out = {1: [Poset(1, [])]}
    for n in range(2, nmax + 1):
        seen = {}
        for P in out[n - 1]:
            m = n - 1
            below = [set() for _ in range(m)]
            for i, j in P.rel:
                below[j].add(i)
            for k in range(m + 1):
                for D in itertools.combinations(range(m), k):
                    D = set(D)
                    if any(not below[y] <= D for y in D):
                        continue
                    rel = set(P.rel) | {(y, m) for y in D}
                    c = canonical(n, rel)
                    if c not in seen:
                        seen[c] = Poset(n, c)
        out[n] = list(seen.values())
    return out


# ---------------------------------------------------------------------------
# Blocks, B_P, e_C, R_P


def union_prefix_lengths(P, w, comps=None):
    comps = comps or P.components()
    compof = {y: c for c in comps for y in c}
    lens = []
    pref = set()
    for k, y in enumerate(w):
        pref.add(y)
        if all(compof[z] <= pref for z in pref):
            lens.append(k + 1)
    return lens


def blocks(P, w, comps=None):
    lens = [0] + union_prefix_lengths(P, w, comps)
    return [w[lens[i]:lens[i + 1]] for i in range(len(lens) - 1)]


def good_words(P, base, lin=None, comps=None):
    lin = lin if lin is not None else P.lin()
    return [w for w in lin if base <= set(blocks(P, w, comps)[0])]


def e_cyclic(P, lin):
    """Number of C_n-orbits (rotation classes) meeting Lin P."""
    orbits = set()
    for w in lin:
        orbits.add(min(w[k:] + w[:k] for k in range(len(w))))
    return len(orbits)


def restrict_lin(P, S):
    S = sorted(S)
    idx = {y: k for k, y in enumerate(S)}
    Q = Poset(len(S), [(idx[i], idx[j]) for i, j in P.rel
                       if i in idx and j in idx])
    return [tuple(S[k] for k in w) for w in Q.lin()]


def R_generators(P, comps=None):
    comps = comps or P.components()
    k = len(comps)
    gens = []
    for r in range(1, k):
        for chosen in itertools.combinations(range(k), r):
            S = set().union(*[comps[i] for i in chosen])
            T = set(range(P.n)) - S
            for s in restrict_lin(P, S):
                for t in restrict_lin(P, T):
                    gens.append((s, t))
    return gens


def normal_form(P, base, comps, memo, w):
    """Lemma 6 reduction: w = N(w) mod R_P with N(w) supported on B_P."""
    if w in memo:
        return memo[w]
    bl = blocks(P, w, comps)
    j = next(i for i, b in enumerate(bl) if base <= set(b))
    if j == 0:
        memo[w] = {w: 1}
        return memo[w]
    s = tuple(y for b in bl[:j] for y in b)
    t = tuple(y for b in bl[j:] for y in b)
    mu = len(s)
    out = defaultdict(int)
    for z in shuffle_set(s, t):
        if z == w:
            continue
        # mu(z) < mu(w): the decrease the proof claims
        zb = blocks(P, z, comps)
        zj = next(i for i, b in enumerate(zb) if base <= set(b))
        assert sum(len(b) for b in zb[:zj]) < mu, (w, z)
        for b, c in normal_form(P, base, comps, memo, z).items():
            out[b] -= c
    memo[w] = {k: v for k, v in out.items() if v}
    return memo[w]


# ---------------------------------------------------------------------------
# Partitions and splitting cycles


def canon_part(blocks_):
    lab = {}
    for k, b in enumerate(sorted(tuple(sorted(b)) for b in blocks_)):
        for y in b:
            lab[y] = k
    return tuple(lab[y] for y in range(len(lab)))


def part_blocks(p):
    d = defaultdict(list)
    for y, k in enumerate(p):
        d[k].append(y)
    return list(d.values())


def order_preserving(P, p):
    """P/p acyclic."""
    nb = max(p) + 1
    pairs = {(p[i], p[j]) for i, j in P.rel if p[i] != p[j]}
    return closure(nb, pairs) is not None


def rho(w):
    """Splitting cycle: sum over orders pi of the n-1 cut positions of
    sgn(pi) * (chain with cuts {pi_1..pi_k}, k = n-2 .. 1, finest first)."""
    n = len(w)
    out = {}
    for pi in itertools.permutations(range(1, n)):
        chain = []
        for k in range(n - 2, 0, -1):
            cuts = sorted(pi[:k])
            segs, prev = [], 0
            for c in cuts + [n]:
                segs.append(w[prev:c])
                prev = c
            chain.append(canon_part(segs))
        out[tuple(chain)] = out.get(tuple(chain), 0) + sgn(pi)
    return out


def boundary(chainvec):
    out = defaultdict(int)
    for ch, c in chainvec.items():
        for i in range(len(ch)):
            out[ch[:i] + ch[i + 1:]] += (-1) ** i * c
    return {k: v for k, v in out.items() if v}


def top_simplices(P):
    """Chains pi_1 < ... < pi_{n-2} in O^(P), pi_k with n-k blocks."""
    n = P.n
    res = []

    def rec(p, chain):
        if len(chain) == n - 2:
            res.append(tuple(chain))
            return
        bl = part_blocks(p)
        for i in range(len(bl)):
            for j in range(i + 1, len(bl)):
                nb = [b for k, b in enumerate(bl) if k not in (i, j)]
                nb.append(bl[i] + bl[j])
                q = canon_part(nb)
                if order_preserving(P, q):
                    rec(q, chain + [q])

    rec(tuple(range(n)), [])
    return res


def act(g, w):
    return tuple(g[y] for y in w)


def act_part(g, p):
    return canon_part([[g[y] for y in b] for b in part_blocks(p)])


# ---------------------------------------------------------------------------
# Checks


def check_L1(ne):
    ok = True
    total = 0
    for n in range(2, ne + 1):
        for u, v in proper_shuffle_pairs(range(n)):
            X = vec_of(shuffle_set(u, v))
            for a in range(n):
                for x in range(n):
                    if a == x:
                        continue
                    pred = {}
                    for (p, q) in ((u, v), (v, u)):
                        if a in p and x in p:
                            i = p.index(a)
                            if i > 0 and p[i - 1] == x:
                                pred = vec_of(shuffle_set(delete(p, x), q))
                            elif i + 1 < len(p) and p[i + 1] == x:
                                pred = vec_of(shuffle_set(delete(p, x), q), -1)
                    total += 1
                    if E(X, a, x) != pred:
                        ok = False
    # Ree-free: E maps Sh_n into Sh_{n-1}, n <= 5
    for n in range(3, min(ne, 5) + 1):
        word_ids(n - 1)
        for a, x in itertools.permutations(range(n), 2):
            rest = [y for y in range(n) if y != x]
            relab = {y: k for k, y in enumerate(rest)}
            sh = sh_echelon(n - 1)
            for u, v in proper_shuffle_pairs(range(n)):
                img = E(vec_of(shuffle_set(u, v)), a, x)
                img = {WID[n - 1][tuple(relab[y] for y in z)]: c
                       for z, c in img.items()}
                if sh.reduce(img):
                    ok = False
    print(f"[L1]  Lemma 1 exact formula on {total} (shuffle, a, x) cases, "
          f"n <= {ne}; E(Sh) in Sh by Ree-free rank, n <= {min(ne, 5)}: {ok}")
    return ok


def check_ADJ(nmax=5):
    ok = True
    cnt = 0
    for n in range(3, nmax + 1):
        words = list(itertools.permutations(range(n)))
        for a, x in itertools.permutations(range(n), 2):
            rest = tuple(y for y in range(n) if y != x)
            for w in words:
                Ew = E({w: 1}, a, x)
                for wp in itertools.permutations(rest):
                    if Ew.get(wp, 0) != substitute(wp, a, x).get(w, 0):
                        ok = False
                    cnt += 1
        # substitution of [x,a] maps Lie into Lie: combs on rest -> _|_ Sh_n
        gens = [vec_of(shuffle_set(u, v)) for u, v in proper_shuffle_pairs(range(n))]
        for a, x in [(0, n - 1), (n - 1, 0), (1, 2)]:
            rest = [y for y in range(n) if y != x]
            for t in itertools.permutations(rest[:-1]):
                c = right_comb(t + (rest[-1],))
                s = defaultdict(int)
                for wp, co in c.items():
                    for w, d in substitute(wp, a, x).items():
                        s[w] += co * d
                for g in gens:
                    if sum(s.get(z, 0) for z in g) != 0:
                        ok = False
    print(f"[ADJ] <E w, w'> = <w, sub(w')> on {cnt} pairs; sub(comb) _|_ Sh, "
          f"n <= {nmax}: {ok}")
    return ok


def check_REE(posets, nree):
    ok = True
    cnt = 0
    for n in range(2, nree + 1):
        word_ids(n)
        sh = sh_echelon(n)
        # rank of comb coordinates on all words = (n-1)!
        r_all = rank(mod_sh_vec({w: 1}, n) for w in WID[n])
        ok &= (r_all == factorial(n - 1)) and (len(WID[n]) - sh.rank() == r_all)
        for P in posets[n]:
            lin = P.lin()
            r1 = rank(mod_sh_vec({w: 1}, n) for w in lin)
            r2 = rank(sh.reduce({WID[n][w]: 1}) for w in lin)
            cnt += 1
            if r1 != r2:
                ok = False
    print(f"[REE] comb-coordinate rank = Ree-free generator rank on Lin P for "
          f"{cnt} posets, rank Sh_n = n! - (n-1)!, n <= {nree}: {ok}")
    return ok


def quotient(P, a, x):
    """P/{a,x} on letters != x (relabelled 0..n-2); None if cyclic."""
    rest = [y for y in range(P.n) if y != x]
    idx = {y: k for k, y in enumerate(rest)}
    img = lambda y: idx[a] if y == x else idx[y]
    pairs = {(img(i), img(j)) for i, j in P.rel if img(i) != img(j)}
    rel = closure(P.n - 1, pairs)
    return (None if rel is None else Poset(P.n - 1, rel)), idx


def check_LEM(posets, nlem):
    ok = {"2a": True, "2b": True, "3": True, "4": True, "5": True, "star": True}
    cnt = 0
    for n in range(2, nlem + 1):
        for P in posets[n]:
            lin = P.lin()
            linset = set(lin)
            comps = P.components()
            # Lemma 3: adjacent incomparable swaps connect Lin P
            seen = {lin[0]}
            stack = [lin[0]]
            while stack:
                w = stack.pop()
                for i in range(n - 1):
                    if not P.comparable(w[i], w[i + 1]):
                        z = w[:i] + (w[i + 1], w[i]) + w[i + 2:]
                        if z not in seen:
                            seen.add(z)
                            stack.append(z)
            ok["3"] &= seen == linset
            # Lemma 4
            for w in lin:
                ul = set(union_prefix_lengths(P, w, comps))
                for j in range(1, n):
                    rot = w[j:] + w[:j]
                    ok["4"] &= (rot in linset) == (j in ul)
            for base in comps:
                B = good_words(P, base, lin, comps)
                classes = defaultdict(list)
                for w in lin:
                    classes[min(w[k:] + w[:k] for k in range(n))].append(w)
                Bs = set(B)
                ok["4"] &= all(sum(z in Bs for z in c) == 1
                               for c in classes.values())
            # Lemmas 2, 5, (*) for every pair adjacent in some extension
            pairs = {(w[i + 1], w[i]) for w in lin for i in range(n - 1)}
            pairs |= {(x, a) for a, x in pairs}
            for a, x in pairs:
                cnt += 1
                Q, idx = quotient(P, a, x)
                if Q is None:
                    ok["2a"] = False
                    continue
                lq = set(Q.lin())
                for w in lin:
                    i = w.index(a)
                    if (i > 0 and w[i - 1] == x) or (i + 1 < n and w[i + 1] == x):
                        ok["2a"] &= tuple(idx[y] for y in delete(w, x)) in lq
                inv = {k: y for y, k in idx.items()}
                for wq in lq:
                    wo = tuple(inv[k] for k in wq)
                    j = wo.index(a)
                    xa = wo[:j] + (x, a) + wo[j + 1:]
                    ax = wo[:j] + (a, x) + wo[j + 1:]
                    ok["2b"] &= (xa in linset) == (not P.less(a, x))
                    ok["2b"] &= (ax in linset) == (not P.less(x, a))
                qcomps = Q.components()
                for base in comps:
                    y0 = next(iter(base))
                    q0 = idx[a] if y0 == x else idx[y0]
                    qbase = next(c for c in qcomps if q0 in c)
                    BQ = set(good_words(Q, qbase, None, qcomps))
                    B = good_words(P, base, lin, comps)
                    for w in B:
                        i = w.index(a)
                        if (i > 0 and w[i - 1] == x) or (i + 1 < n and w[i + 1] == x):
                            ok["5"] &= tuple(idx[y] for y in delete(w, x)) in BQ
                    # (*): E_{a,x} of a generic combination on B_P lies on B_Q
                    X = {w: 1 + (hash(w) % 7) for w in B}
                    img = E(X, a, x)
                    ok["star"] &= all(tuple(idx[y] for y in z) in BQ for z in img)
    good = all(ok.values())
    print(f"[LEM] Lemmas 2(a),2(b),3,4,5,(*) on {cnt} (poset, adjacent pair) "
          f"cases, n <= {nlem}: {ok} -> {good}")
    return good


def check_AB(posets, nmax):
    ok = True
    stats = defaultdict(lambda: [0, 0])
    for n in range(2, nmax + 1):
        for P in posets[n]:
            lin = P.lin()
            comps = P.components()
            ec = e_cyclic(P, lin)
            vecs = {w: mod_sh_vec({w: 1}, n) for w in lin}
            rlin = rank(vecs.values())
            gens = R_generators(P, comps)
            rR = rank(vec_of(shuffle_set(s, t)) for s, t in gens)
            good = True
            # Conjecture S via Phi: rank(Lin P mod Sh) = e_C; K_P = R_P
            # (dim_p R <= dim_Q R <= dim_Q K <= |Lin| - rank_p(Lin mod Sh))
            good &= rlin == ec
            good &= rR == len(lin) - rlin
            if len(comps) == 1:
                good &= rlin == len(lin)
            for base in comps:
                B = good_words(P, base, lin, comps)
                good &= len(B) == ec
                good &= rank(vecs[w] for w in B) == len(B)       # Theorem A
                # Lemma 6 + Theorem B: span B (+) R_P = W_P, exactly
                memo = {}
                for w in lin:
                    N = normal_form(P, base, comps, memo, w)
                    good &= set(N) <= set(B)
                e = Echelon()
                for s, t in gens:
                    e.add(vec_of(shuffle_set(s, t)))
                good &= e.rank() + len(B) == len(lin)
                e2 = Echelon()
                for v in [vec_of(shuffle_set(s, t)) for s, t in gens] + [{w: 1} for w in B]:
                    e2.add(v)
                good &= e2.rank() == len(lin)
            stats[n][0] += 1
            stats[n][1] += good
            ok &= good
    desc = ", ".join(f"n={n}: {a}/{b}" for n, (b, a) in sorted(stats.items()))
    print(f"[AB]  Theorem A, |B_P| = e_C, Lemma 6, Theorem B (all base "
          f"components): {desc}: {ok}")
    return ok


def check_CHN(posets, nchn):
    ok = {"D": True, "cycle": True, "rankB": True, "Rrel": True,
          "iso": True, "equiv": True}
    cnt = 0
    for n in range(3, nchn + 1):
        for P in posets[n]:
            cnt += 1
            lin = P.lin()
            comps = P.components()
            ec = e_cyclic(P, lin)
            tops = top_simplices(P)
            topset = set(tops)
            tid = {t: i for i, t in enumerate(tops)}
            faces = {}
            e = Echelon()
            for t in tops:
                v = {}
                for i in range(len(t)):
                    f = t[:i] + t[i + 1:]
                    v[faces.setdefault(f, len(faces))] = (-1) ** i
                e.add(v)
            zdim = len(tops) - e.rank()      # dim_p Z >= dim_Q Z = dim H_P
            R = {w: rho(w) for w in lin}
            for w in lin:
                ok["D"] &= set(R[w]) <= topset
                ok["cycle"] &= not boundary(R[w])
            for base in comps:
                B = good_words(P, base, lin, comps)
                r = rank({tid[c]: v for c, v in R[w].items()} for w in B)
                ok["rankB"] &= r == len(B) == zdim == ec
                memo = {}
                for w in lin:
                    N = normal_form(P, base, comps, memo, w)
                    diff = defaultdict(int, R[w])
                    for b, c in N.items():
                        for ch, d in R[b].items():
                            diff[ch] -= sgn(w) * sgn(b) * c * d
                    ok["iso"] &= not any(diff.values())
            for s, t in R_generators(P, comps):
                tot = defaultdict(int)
                for z in shuffle_set(s, t):
                    for ch, d in R[z].items():
                        tot[ch] += sgn(z) * d
                ok["Rrel"] &= not any(tot.values())
            for g in P.automorphisms():
                for w in lin:
                    gw = act(g, w)
                    img = {tuple(act_part(g, p) for p in ch): c
                           for ch, c in R[w].items()}
                    ok["equiv"] &= gw in R and img == R[gw]
    good = all(ok.values())
    print(f"[CHN] chain level (no Phi, no J-S) for {cnt} posets, "
          f"3 <= n <= {nchn}: {ok} -> {good}")
    return good


def check_CTL(posets):
    ctl = []
    # E with the wrong sign breaks Lemma 1 / E(Sh) in Sh
    X = vec_of(shuffle_set((0, 1), (2,)))
    word_ids(2)
    bad = E(X, 0, 1, sign=-1)   # "ax" with a=0, x=1: sign must be -
    ctl.append(bool(bad != vec_of(shuffle_set((0,), (2,)), -1)))
    X2 = vec_of(shuffle_set((0,), (1, 2)))         # case 2: x in u, a in v
    ctl.append(bool(E(X2, 1, 0) == {} and E(X2, 1, 0, sign=-1) != {}))
    # Lin P for disconnected P is dependent mod Sh (two 2-chains)
    P = Poset(4, [(0, 1), (2, 3)])
    lin = P.lin()
    r = rank(mod_sh_vec({w: 1}, 4) for w in lin)
    ctl.append(bool(r < len(lin) and r == e_cyclic(P, lin) == 5))
    # "words beginning with a letter of P_1" is the WRONG variant of B_P
    alt = [w for w in lin if w[0] in (0, 1)]
    ctl.append(bool(len(alt) == 3 and len(good_words(P, frozenset({0, 1}), lin)) == 5))
    ctl.append(bool((2, 0, 3, 1) in good_words(P, frozenset({0, 1}), lin)))
    # Lin P of the 3-antichain is dependent mod Sh; B_P is not
    A = Poset(3, [])
    la = A.lin()
    ctl.append(bool(rank(mod_sh_vec({w: 1}, 3) for w in la) == 2))
    # a non-cycle is detected; a wrong-orientation rho fails the iso check
    ctl.append(bool(bool(boundary({next(iter(rho((0, 1, 2, 3)))): 1}))))
    # top cycle space of the 4-antichain has dim 3! = 6
    tops = top_simplices(Poset(4, []))
    e = Echelon()
    faces = {}
    for t in tops:
        e.add({faces.setdefault(t[:i] + t[i + 1:], len(faces)): (-1) ** i
               for i in range(len(t))})
    ctl.append(bool(len(tops) - e.rank() == 6))
    # unsigned splitting-cycle shuffle relation fails (sign twist is needed)
    tot = defaultdict(int)
    for z in shuffle_set((0, 1), (2, 3)):
        for ch, d in rho(z).items():
            tot[ch] += d
    ctl.append(bool(any(tot.values())))
    # Lemma 6 normal form omitting sgn in the iso check would fail
    P = Poset(4, [(0, 1), (2, 3)])
    w = (2, 3, 0, 1)
    N = normal_form(P, frozenset({0, 1}), P.components(), {}, w)
    diff = defaultdict(int, rho(w))
    for b, c in N.items():
        for ch, d in rho(b).items():
            diff[ch] -= c * d
    ctl.append(bool(any(diff.values())))
    # enumeration counts
    ctl.append(bool([len(posets[n]) for n in sorted(posets)][:6] == [1, 2, 5, 16, 63, 318][:len(posets)]))
    ok = all(ctl)
    print(f"[CTL] positive controls fire: {ctl} -> {ok}")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--ne", type=int, default=6)
    ap.add_argument("--nlem", type=int, default=6)
    ap.add_argument("--nchn", type=int, default=5)
    ap.add_argument("--nree", type=int, default=5)
    args = ap.parse_args()
    top = max(args.nmax, args.nlem, args.nchn, args.nree)
    posets = unlabeled_posets(top)
    print("posets:", {n: len(v) for n, v in sorted(posets.items())})
    res = [check_CTL(posets),
           check_L1(args.ne),
           check_ADJ(5),
           check_REE(posets, args.nree),
           check_LEM(posets, args.nlem),
           check_AB(posets, args.nmax),
           check_CHN(posets, args.nchn)]
    print("ALL CHECKS PASSED" if all(res) else "SOME CHECK FAILED")
    sys.exit(0 if all(res) else 1)


if __name__ == "__main__":
    main()
