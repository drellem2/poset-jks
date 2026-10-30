#!/usr/bin/env python3
"""Independent audit script for notes/general_theory.md, section 2
(framework (b): the Hopf monoid Q', Theorems 6, 7, 8 and "(b) = (a)").
Written for notes/audit_general_theory_hopf.md.

It does NOT import compute/general_theory.py nor any other module of this
repo.  Posets, linear extensions, components, cyclic classes, shuffles, combs,
the species operations of Q' and of the Hopf monoid Q of [Glob, 4.1], braid
lunes (from sign vectors) and the modular linear algebra are re-implemented.

Conventions.  A poset is (ground, rels): ground a frozenset of ints, rels a
frozenset of strict pairs (a, b) meaning a < b (transitively closed).  A word
is a tuple.  A basis element of Q'[I] (and of Q[I]) is (rels, word) with
set(word) = I and word a linear extension.  Right multiplication by gamma^k
rotates LEFT by k: w gamma^k = w[k:] + w[:k]; e_zeta = (1/n) sum zeta^-j gamma^j.

Arithmetic: exact integers where possible; ranks/kernels modulo primes
p = 1 (mod 60).  A full rank mod p certifies full rank over Q (a nonzero
minor stays nonzero mod p only if it was nonzero over Z); a nonzero
coordinate mod p certifies a nonzero rational.  Equalities of ranks that
need an upper bound are obtained from exact integer orthogonality.

Every check prints PASS/FAIL; every positive control is a deliberately
wrong variant that MUST fail, and prints CONTROL FIRED / CONTROL DID NOT FIRE.

Sections (claim audited in brackets):
  [enum]   poset counts 1,2,5,16,63,(318)
  [axioms] Lemma 2.1: every bimonoid axiom of Q' on all labelled posets,
           n <= 4, plus naturality.  Controls: down-set coproduct (must break
           cocommutativity), ordinal-sum product (must break compatibility).
  [prim]   Thm 7(a): Prim(Q')[n] computed over the whole of Q'[n] (n <= 4)
           is P-homogeneous, of dim sum_P e_C(P).  Control: same instrument
           on Q (restriction to every S) gives non-homogeneous primitives.
  [ree]    Ree, multilinear, n <= 6: combs orthogonal to proper shuffles,
           rank Lie_n = (n-1)!, rank Sh_n = n! - (n-1)!.  Control: Klyachko's
           W e_zeta is not orthogonal to Sh_n.
  [trunc]  Thm 7(b): pr_P(Lie_n) = R_P^perp, dim e_C(P), all posets n <= nmax (6).
           Control: annihilator of the DOWN-SET shuffles differs.
  [char]   Thm 7(c): character of p_P = sum_{gC=C} zeta^{r_g(C)} (Klyachko's
           Lie(P), no sign twist).  Control: the untwisted class count.
  [brkt]   Thm 7(a,d): [x, y] of truncated combs is primitive and equals the
           truncated free Lie bracket, exactly over Z.  Controls: [Glob 3.4]
           -- the concatenation commutator does NOT descend to W e_zeta;
           commutator with a non-primitive element is not primitive.
  [filt]   Thm 8: r(P|S)+r(P|T) <= r(P), equality iff S union of components
           (n <= 5); for Q[n], n <= 4: dim gr_r Prim(Q) = sum_{r(P)=r} e_C(P)
           for every r, and leading terms are Q'-primitive.  Control: leading
           terms are NOT primitive for Q's own coproduct.
  [pbw]    Thm 6: shuffle products over set partitions of components of bases
           of V_Q (two choices: V_Q = p_Q, and V_Q = span B_Q) are a basis of
           W_P; Lemma 1.3; equivariant character form.  Controls: drop
           partitions with >= 3 blocks; trivial character in place of p.
  [dual]   Sec. 2.3: dual product = disjoint union + shuffle, dual coproduct
           = deconcatenation at cuts (n <= 4); decomposables = R_P = span of
           braid top-lunes inside C_P computed from sign vectors (n <= 5).
           Control: lunes MEETING C_P (truncated) do not span R_P.

Run from compute/:
    python3 audit_general_theory_hopf.py > output/audit_general_theory_hopf.txt
Exit status 0 iff every check passes and every control fires.
"""

import argparse
import cmath
import itertools
import random
import sys
from math import comb, factorial

PRIMES = [2147483641, 1000000021]   # placeholders, replaced in _find_primes
FAILURES = []


def _is_prime(m):
    if m < 2:
        return False
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return True


def _find_primes():
    out, m = [], 2_000_000_000 - (2_000_000_000 % 60) + 1
    while len(out) < 2:
        if _is_prime(m):
            out.append(m)
        m -= 60
    return out


PRIMES = _find_primes()
P0 = PRIMES[0]


def report(tag, ok, msg):
    print(f"[{tag}] {'PASS' if ok else 'FAIL'}: {msg}")
    if not ok:
        FAILURES.append(f"{tag}: {msg}")


def control(tag, fired, msg):
    print(f"[{tag}] {'CONTROL FIRED' if fired else 'CONTROL DID NOT FIRE'}: {msg}")
    if not fired:
        FAILURES.append(f"{tag} control: {msg}")


# ---------------------------------------------------------------------------
# posets

def closure(rels):
    rels = set(rels)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(rels):
            for (c, d) in list(rels):
                if b == c and (a, d) not in rels:
                    rels.add((a, d))
                    changed = True
    return frozenset(rels)


def naturally_labelled(n):
    """All posets on {0..n-1} for which the identity is a linear extension."""
    out = [frozenset()]
    for k in range(n):
        new = []
        for rels in out:
            # predecessors of k: any down-set of the poset on 0..k-1
            for mask in range(1 << k):
                D = {i for i in range(k) if mask >> i & 1}
                if all(a in D for (a, b) in rels if b in D):
                    new.append(rels | frozenset((d, k) for d in D))
        out = new
    return out


def canon(rels, n):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((p[a], p[b]) for (a, b) in rels))
        if best is None or key < best:
            best = key
    return best


def enumerate_posets(nmax):
    """{n: list of rels}, one representative per isomorphism class."""
    res = {0: [frozenset()]}
    for n in range(1, nmax + 1):
        seen = {}
        for rels in naturally_labelled(n):
            c = canon(rels, n)
            if c not in seen:
                seen[c] = rels
        res[n] = list(seen.values())
    return res


def all_labelled(n):
    """All posets on {0..n-1} (labelled)."""
    out = set()
    for rels in naturally_labelled(n):
        for p in itertools.permutations(range(n)):
            out.add(frozenset((p[a], p[b]) for (a, b) in rels))
    return sorted(out, key=lambda r: sorted(r))


def restrict(rels, S):
    return frozenset((a, b) for (a, b) in rels if a in S and b in S)


def components(ground, rels):
    ground = set(ground)
    adj = {x: set() for x in ground}
    for (a, b) in rels:
        adj[a].add(b)
        adj[b].add(a)
    comps, seen = [], set()
    for x in sorted(ground):
        if x in seen:
            continue
        st, c = [x], set()
        while st:
            y = st.pop()
            if y in c:
                continue
            c.add(y)
            st.extend(adj[y] - c)
        seen |= c
        comps.append(frozenset(c))
    return comps


def is_union_of_components(ground, rels, S):
    return all((a in S) == (b in S) for (a, b) in rels)


def is_down_set(rels, S):
    return all(a in S for (a, b) in rels if b in S)


def lin_ext(ground, rels):
    ground = sorted(ground)
    preds = {x: {a for (a, b) in rels if b == x} for x in ground}
    out = []

    def rec(pref, left):
        if not left:
            out.append(tuple(pref))
            return
        for x in sorted(left):
            if preds[x] <= set(pref):
                pref.append(x)
                rec(pref, left - {x})
                pref.pop()
    rec([], set(ground))
    return out


def classes(words):
    """Cyclic classes: rotation orbits meeting the set `words` (of Lin P)."""
    W = set(words)
    seen, out = set(), []
    for w in words:
        if w in seen:
            continue
        cl = [w[k:] + w[:k] for k in range(len(w)) if w[k:] + w[:k] in W]
        seen |= set(cl)
        out.append(cl)
    return out


def e_C(ground, rels):
    if not ground:
        return 1
    return len(classes(lin_ext(ground, rels)))


def automorphisms(ground, rels):
    g = sorted(ground)
    out = []
    for p in itertools.permutations(g):
        m = dict(zip(g, p))
        if frozenset((m[a], m[b]) for (a, b) in rels) == rels:
            out.append(m)
    return out


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


# ---------------------------------------------------------------------------
# words / vectors (dict word -> int)

def shuffle_words(u, v):
    if not u:
        return [v]
    if not v:
        return [u]
    return [(u[0],) + w for w in shuffle_words(u[1:], v)] + \
           [(v[0],) + w for w in shuffle_words(u, v[1:])]


def vshuffle(x, y):
    out = {}
    for u, a in x.items():
        for v, b in y.items():
            for w in shuffle_words(u, v):
                out[w] = out.get(w, 0) + a * b
    return {k: c for k, c in out.items() if c}


def vconcat(x, y):
    out = {}
    for u, a in x.items():
        for v, b in y.items():
            out[u + v] = out.get(u + v, 0) + a * b
    return {k: c for k, c in out.items() if c}


def vsub(x, y):
    out = dict(x)
    for k, c in y.items():
        out[k] = out.get(k, 0) - c
    return {k: c for k, c in out.items() if c}


def vbracket(x, y):
    return vsub(vconcat(x, y), vconcat(y, x))


def right_comb(word):
    """[w1,[w2,[...,[w_{n-1},w_n]]]] as dict of words."""
    if len(word) == 1:
        return {tuple(word): 1}
    rest = right_comb(word[1:])
    return vbracket({(word[0],): 1}, rest)


def lie_spanning(ground):
    """(n-1)! right combs with fixed last letter max(ground): a basis of Lie."""
    g = sorted(ground)
    last = g[-1]
    return [right_comb(p + (last,)) for p in itertools.permutations(g[:-1])]


def truncate(x, Lset):
    return {w: c for w, c in x.items() if w in Lset}


def dot(x, y):
    if len(x) > len(y):
        x, y = y, x
    return sum(c * y.get(k, 0) for k, c in x.items())


def act(g, x):
    return {tuple(g[a] for a in w): c for w, c in x.items()}


def R_generators(ground, rels, downsets=False):
    """Generators s sh t of R_P (S a nonempty proper union of components);
    with downsets=True, S a nonempty proper down-set instead (control)."""
    ground = frozenset(ground)
    els = sorted(ground)
    out = []
    for k in range(1, len(els)):
        for S in itertools.combinations(els, k):
            S = frozenset(S)
            T = ground - S
            if downsets:
                if not is_down_set(rels, S):
                    continue
            elif not is_union_of_components(ground, rels, S):
                continue
            for s in lin_ext(S, restrict(rels, S)):
                for t in lin_ext(T, restrict(rels, T)):
                    out.append({w: 1 for w in shuffle_words(s, t)})
    return out


# ---------------------------------------------------------------------------
# modular RREF

class RREF:
    """Row space mod p, kept in reduced row echelon form (sparse rows)."""

    def __init__(self, p=P0):
        self.p = p
        self.rows = {}           # pivot key -> row dict (1 at pivot)
        self.order = None

    def reduce(self, v):
        p = self.p
        v = {k: c % p for k, c in v.items() if c % p}
        for piv in [k for k in v if k in self.rows]:
            c = v.get(piv, 0)
            if c:
                for k, a in self.rows[piv].items():
                    nv = (v.get(k, 0) - c * a) % p
                    if nv:
                        v[k] = nv
                    else:
                        v.pop(k, None)
        # pivots introduced by subtraction may now be present again
        while True:
            hits = [k for k in v if k in self.rows]
            if not hits:
                return v
            for piv in hits:
                c = v.get(piv, 0)
                if c:
                    for k, a in self.rows[piv].items():
                        nv = (v.get(k, 0) - c * a) % p
                        if nv:
                            v[k] = nv
                        else:
                            v.pop(k, None)

    def add(self, v):
        v = self.reduce(v)
        if not v:
            return False
        p = self.p
        piv = min(v)
        inv = pow(v[piv], p - 2, p)
        v = {k: c * inv % p for k, c in v.items()}
        for q, r in self.rows.items():
            c = r.get(piv, 0)
            if c:
                for k, a in v.items():
                    nv = (r.get(k, 0) - c * a) % p
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
        self.rows[piv] = v
        return True

    def rank(self):
        return len(self.rows)

    def contains(self, v):
        return not self.reduce(v)

    def trace(self, g):
        """Trace of the relabelling g on this (g-stable) row space."""
        p = self.p
        return sum(act(g, {k: c for k, c in r.items()}).get(piv, 0)
                   for piv, r in self.rows.items()) % p


def rank_of(vecs, p=P0):
    R = RREF(p)
    for v in vecs:
        R.add(v)
    return R.rank()


def signed(x, p):
    x %= p
    return x - p if x > p // 2 else x


# ---------------------------------------------------------------------------
# p_P = pr_P(Lie) with a cached RREF basis

_PCACHE = {}


def prim_space(ground, rels, p=P0):
    key = (frozenset(ground), rels, p)
    if key not in _PCACHE:
        L = set(lin_ext(ground, rels))
        R = RREF(p)
        ints = []
        for c in lie_spanning(ground) if ground else []:
            t = truncate(c, L)
            if R.add(t):
                ints.append(t)
        _PCACHE[key] = (R, ints)
    return _PCACHE[key]


# ---------------------------------------------------------------------------
# [axioms] Lemma 2.1

def coprod(x, S, T, mode):
    """Delta_{S,T} on a dict of (rels, word).  mode: 'Qp' (unions of
    components), 'Q' (every S), 'down' (down-sets; control)."""
    out = {}
    for (rels, w), c in x.items():
        I = frozenset(w)
        if mode == 'Qp' and not is_union_of_components(I, rels, S):
            continue
        if mode == 'down' and not is_down_set(rels, S):
            continue
        a = (restrict(rels, S), tuple(z for z in w if z in S))
        b = (restrict(rels, T), tuple(z for z in w if z in T))
        out[(a, b)] = out.get((a, b), 0) + c
    return {k: v for k, v in out.items() if v}


def prod(x, y, mode):
    """mu on dicts.  mode 'sum': disjoint union; 'ordinal' (control):
    ordinal sum P (+) P' (everything of P below everything of P')."""
    out = {}
    for (r1, u), a in x.items():
        for (r2, v), b in y.items():
            r = r1 | r2
            if mode == 'ordinal':
                r = r | frozenset((i, j) for i in u for j in v)
            k = (r, u + v)
            out[k] = out.get(k, 0) + a * b
    return out


def tensor_prod(xx, yy, pmode):
    """(mu (x) mu) after middle swap: (a(x)b) , (c(x)d) -> ac (x) bd."""
    out = {}
    for (a, b), s in xx.items():
        for (c, d), t in yy.items():
            for k1, u in prod({a: 1}, {c: 1}, pmode).items():
                for k2, v in prod({b: 1}, {d: 1}, pmode).items():
                    out[(k1, k2)] = out.get((k1, k2), 0) + s * t * u * v
    return {k: v for k, v in out.items() if v}


def species_basis(I):
    I = sorted(I)
    n = len(I)
    out = []
    for rels in all_labelled(n):
        m = dict(enumerate(I))
        r = frozenset((m[a], m[b]) for (a, b) in rels)
        for w in lin_ext(frozenset(I), r):
            out.append((r, w))
    return out


def check_axioms(nmax, cmode, pmode):
    """Return dict axiom -> bool for the structure (cmode, pmode)."""
    ok = {k: True for k in ['assoc', 'unit', 'counit', 'coassoc', 'cocomm',
                            'compat', 'natural', 'closed']}
    bases = {}
    for n in range(0, nmax + 1):
        bases[n] = species_basis(range(n))
    # relabel helper for subsets
    for n in range(0, nmax + 1):
        I = frozenset(range(n))
        B = bases[n]
        empty = (frozenset(), ())
        for b in B:
            x = {b: 1}
            # unit / counit
            if prod({empty: 1}, x, pmode) != x or prod(x, {empty: 1}, pmode) != x:
                ok['unit'] = False
            if coprod(x, frozenset(), I, cmode) != {(empty, b): 1} or \
               coprod(x, I, frozenset(), cmode) != {(b, empty): 1}:
                ok['counit'] = False
            for k in range(0, n + 1):
                for S in itertools.combinations(sorted(I), k):
                    S = frozenset(S)
                    T = I - S
                    d = coprod(x, S, T, cmode)
                    dT = coprod(x, T, S, cmode)
                    if {(bb, aa): c for (aa, bb), c in d.items()} != dT:
                        ok['cocomm'] = False
                    # closed: restrictions are basis elements
                    for (aa, bb) in d:
                        for (r, w) in (aa, bb):
                            if w not in set(lin_ext(frozenset(w), r)):
                                ok['closed'] = False
                    # coassociativity for every split of T into S2, S3
                    for k2 in range(0, len(T) + 1):
                        for S2 in itertools.combinations(sorted(T), k2):
                            S2 = frozenset(S2)
                            S3 = T - S2
                            lhs, rhs = {}, {}
                            # (id (x) Delta_{S2,S3}) Delta_{S1, S2+S3}
                            for (aa, bb), c in d.items():
                                for (b1, b2), e in coprod({bb: 1}, S2, S3, cmode).items():
                                    key = (aa, b1, b2)
                                    lhs[key] = lhs.get(key, 0) + c * e
                            # (Delta_{S1,S2} (x) id) Delta_{S1+S2, S3}
                            for (aa, bb), c in coprod(x, S | S2, S3, cmode).items():
                                for (a1, a2), e in coprod({aa: 1}, S, S2, cmode).items():
                                    key = (a1, a2, bb)
                                    rhs[key] = rhs.get(key, 0) + c * e
                            if lhs != rhs:
                                ok['coassoc'] = False
        # products and compatibility: x on S, y on T, S + T = I
        for k in range(0, n + 1):
            for S in itertools.combinations(sorted(I), k):
                S = frozenset(S)
                T = I - S
                mS = dict(enumerate(sorted(S)))
                mT = dict(enumerate(sorted(T)))
                BS = [(frozenset((mS[a], mS[b]) for (a, b) in r),
                       tuple(mS[z] for z in w)) for (r, w) in bases[len(S)]]
                BT = [(frozenset((mT[a], mT[b]) for (a, b) in r),
                       tuple(mT[z] for z in w)) for (r, w) in bases[len(T)]]
                for xa in BS:
                    for yb in BT:
                        xy = prod({xa: 1}, {yb: 1}, pmode)
                        for (r, w) in xy:
                            if w not in set(lin_ext(I, r)):
                                ok['closed'] = False
                        for k2 in range(0, n + 1):
                            for S2 in itertools.combinations(sorted(I), k2):
                                S2 = frozenset(S2)
                                T2 = I - S2
                                lhs = {}
                                for key, c in xy.items():
                                    for kk, e in coprod({key: 1}, S2, T2, cmode).items():
                                        lhs[kk] = lhs.get(kk, 0) + c * e
                                lhs = {kk: v for kk, v in lhs.items() if v}
                                A, Bq, C, D = S & S2, S & T2, T & S2, T & T2
                                rhs = tensor_prod(coprod({xa: 1}, A, Bq, cmode),
                                                  coprod({yb: 1}, C, D, cmode),
                                                  pmode)
                                if lhs != rhs:
                                    ok['compat'] = False
        # associativity on triples of small pieces (n <= 3 suffices to see it)
        if n <= 3:
            for parts in itertools.product(range(3), repeat=n):
                Ss = [frozenset(i for i in range(n) if parts[i] == j) for j in range(3)]
                Bs = []
                for Sj in Ss:
                    m = dict(enumerate(sorted(Sj)))
                    Bs.append([(frozenset((m[a], m[b]) for (a, b) in r),
                                tuple(m[z] for z in w)) for (r, w) in bases[len(Sj)]])
                for a_ in Bs[0]:
                    for b_ in Bs[1]:
                        for c_ in Bs[2]:
                            l = prod(prod({a_: 1}, {b_: 1}, pmode), {c_: 1}, pmode)
                            r = prod({a_: 1}, prod({b_: 1}, {c_: 1}, pmode), pmode)
                            if l != r:
                                ok['assoc'] = False
        # naturality under random relabellings of I
        rng = random.Random(n)
        for b in B[:200]:
            perm = list(range(n))
            rng.shuffle(perm)
            s = dict(zip(range(n), perm))

            def rl(e):
                r, w = e
                return (frozenset((s[a], s[c]) for (a, c) in r), tuple(s[z] for z in w))
            for k in range(0, n + 1):
                for S in itertools.combinations(range(n), k):
                    S = frozenset(S)
                    T = I - S
                    d1 = coprod({rl(b): 1}, frozenset(s[z] for z in S),
                                frozenset(s[z] for z in T), cmode)
                    d2 = {(rl(aa), rl(bb)): c for (aa, bb), c in
                          coprod({b: 1}, S, T, cmode).items()}
                    if d1 != d2:
                        ok['natural'] = False
    return ok


def run_axioms(nmax):
    ok = check_axioms(nmax, 'Qp', 'sum')
    for k, v in ok.items():
        report('axioms', v, f"Q' axiom '{k}' on all labelled posets, n <= {nmax}")
    dim0 = len(species_basis([]))
    report('axioms', dim0 == 1, f"connected: dim Q'[empty] = {dim0}")
    okQ = check_axioms(min(nmax, 3), 'Q', 'sum')
    report('axioms', all(okQ.values()),
           f"sanity: [Glob]'s Q (restriction to every S) satisfies all axioms, n <= {min(nmax, 3)}")
    c1 = check_axioms(min(nmax, 3), 'down', 'sum')
    control('axioms', not c1['cocomm'],
            f"down-set coproduct breaks cocommutativity (failed axioms: "
            f"{sorted(k for k, v in c1.items() if not v)})")
    c2 = check_axioms(min(nmax, 3), 'Qp', 'ordinal')
    control('axioms', not c2['compat'],
            f"ordinal-sum product breaks compatibility (failed axioms: "
            f"{sorted(k for k, v in c2.items() if not v)})")


# ---------------------------------------------------------------------------
# [prim] whole-space primitives

def primitive_system(I, basis, mode):
    """Rows of the linear system Delta_{S,T} x = 0 (S, T nonempty).  Each
    Delta_{S,T} sends a basis element to one basis pair or 0, so the rows are
    the fibres.  Returns the list of rows (dict column-index -> 1)."""
    idx = {b: i for i, b in enumerate(basis)}
    I = frozenset(I)
    rows = []
    for k in range(1, len(I)):
        for S in itertools.combinations(sorted(I), k):
            S = frozenset(S)
            T = I - S
            fib = {}
            for b in basis:
                for key in coprod({b: 1}, S, T, mode):
                    fib.setdefault(key, {})[idx[b]] = 1
            rows.extend(fib.values())
    return rows


def kernel_basis(rows, ncols, cols=None, p=P0):
    """Basis (mod p) of {x supported on cols : rows . x = 0}."""
    cols = sorted(range(ncols) if cols is None else cols)
    cset = set(cols)
    R = RREF(p)
    for r in rows:
        rr = {c: v for c, v in r.items() if c in cset}
        if rr:
            R.add(rr)
    piv = set(R.rows)
    free = [c for c in cols if c not in piv]
    ker = []
    for f in free:
        v = {f: 1}
        for q, r in R.rows.items():
            a = r.get(f, 0)
            if a:
                v[q] = (-a) % p
        ker.append(v)
    return ker


def run_prim(nmax):
    for n in range(1, nmax + 1):
        I = range(n)
        basis = species_basis(I)
        poset_of = [b[0] for b in basis]
        rows = primitive_system(I, basis, 'Qp')
        ker = kernel_basis(rows, len(basis))
        expected = sum(e_C(frozenset(I), r) for r in all_labelled(n))
        # homogeneous parts
        byP = {}
        for i, r in enumerate(poset_of):
            byP.setdefault(r, []).append(i)
        homog = sum(len(kernel_basis(rows, len(basis), cols)) for cols in byP.values())
        report('prim', len(ker) == expected == homog,
               f"n={n}: dim Prim(Q')[n] = {len(ker)}, sum_P e_C(P) = {expected}, "
               f"sum_P dim(Prim cap Q'_P) = {homog}")
        rowsQ = primitive_system(I, basis, 'Q')
        kerQ = kernel_basis(rowsQ, len(basis))
        homQ = sum(len(kernel_basis(rowsQ, len(basis), cols)) for cols in byP.values())
        report('prim', len(kerQ) == expected,
               f"n={n}: dim Prim(Q)[n] = {len(kerQ)} = dim Prim(Q')[n] (CMM shadow)")
        if n >= 2:
            control('prim', homQ < len(kerQ),
                    f"n={n}: Prim(Q) is not P-homogeneous: sum_P dim(Prim(Q) cap Q_P) "
                    f"= {homQ} < {len(kerQ)}")


# ---------------------------------------------------------------------------
# [ree]

def run_ree(nmax):
    for n in range(2, nmax + 1):
        g = frozenset(range(n))
        combs = lie_spanning(g)
        sh = R_generators(g, frozenset())     # antichain: all proper shuffles
        ok_orth = all(dot(c, s) == 0 for c in combs for s in sh)
        rl = rank_of(combs)
        rs = rank_of(sh) if n <= 5 else None
        msg = f"n={n}: combs . shuffles = 0 exactly: {ok_orth}; rank Lie_n = {rl} " \
              f"(want {factorial(n - 1)})"
        good = ok_orth and rl == factorial(n - 1)
        if rs is not None:
            msg += f"; rank Sh_n = {rs} (want {factorial(n) - factorial(n - 1)})"
            good = good and rs == factorial(n) - factorial(n - 1)
        report('ree', good, msg)
    # control: Klyachko's w e_zeta (mod p, zeta of order n) is not orthogonal to Sh_n
    n = 3
    p = P0
    z = zeta_mod(n, p)
    fired = False
    for w in itertools.permutations(range(n)):
        ez = {w[j:] + w[:j]: pow(z, (-j) % n, p) for j in range(n)}
        for s in R_generators(frozenset(range(n)), frozenset()):
            if dot(ez, s) % p:
                fired = True
    control('ree', fired, "n=3: some w e_zeta pairs nonzero with a proper shuffle "
            "(Klyachko's module is not the Lie elements)")


def zeta_mod(n, p):
    """An element of exact order n mod p (p = 1 mod 60, n | 60)."""
    for a in range(2, 1000):
        z = pow(a, (p - 1) // n, p)
        if all(pow(z, n // q, p) != 1 for q in range(2, n + 1) if n % q == 0 and _is_prime(q)):
            return z
    raise ValueError


# ---------------------------------------------------------------------------
# [trunc] Thm 7(b),(c) dims; [char]

def run_trunc(posets, nmax):
    tot = bad = 0
    ctl = 0
    for n in range(1, nmax + 1):
        g = frozenset(range(n))
        for rels in posets[n]:
            tot += 1
            L = lin_ext(g, rels)
            eC = e_C(g, rels)
            R = R_generators(g, rels)
            Rp, ints = prim_space(g, rels)
            orth = all(dot(x, r) == 0 for x in ints for r in R)
            rP = rank_of(R)
            ok = orth and Rp.rank() == eC and rP + eC == len(L)
            if not ok:
                bad += 1
            # control: annihilator of the down-set shuffles (other coproduct)
            D = R_generators(g, rels, downsets=True)
            if not all(dot(x, r) == 0 for x in ints for r in D):
                ctl += 1
    report('trunc', bad == 0,
           f"{tot} posets n <= {nmax}: truncated combs are orthogonal to R_P (exact), "
           f"rank pr_P(Lie) = e_C(P) and rank R_P = |Lin P| - e_C(P) (so "
           f"pr_P(Lie) = R_P^perp = p_P); failures: {bad}")
    control('trunc', ctl > 0,
            f"pr_P(Lie) is NOT orthogonal to the down-set shuffles for {ctl} posets")


def run_char(posets, nmax):
    tot = bad = ctl = 0
    for n in range(1, nmax + 1):
        g = frozenset(range(n))
        z = cmath.exp(2j * cmath.pi / n)
        for rels in posets[n]:
            Rp, _ = prim_space(g, rels)
            L = lin_ext(g, rels)
            cls = classes(L)
            for a in automorphisms(g, rels):
                tot += 1
                # the trace formula needs g p_P = p_P: check it
                if not all(Rp.contains(act(a, r)) for r in Rp.rows.values()):
                    bad += 1
                chi_p = signed(Rp.trace(a), Rp.p)
                kly = 0
                cnt = 0
                for C in cls:
                    w = C[0]
                    gw = tuple(a[x] for x in w)
                    if gw in set(C):
                        r = next(k for k in range(n) if w[k:] + w[:k] == gw)
                        kly += z ** r
                        cnt += 1
                if abs(kly - chi_p) > 1e-8:
                    bad += 1
                if cnt != chi_p:
                    ctl += 1
    report('char', bad == 0,
           f"{tot} pairs (P, g in Aut P), n <= {nmax}: p_P is g-stable and trace of g on p_P = "
           f"sum_(gC=C) zeta^r_g(C) = chi of Lie(P) (no sign twist); failures: {bad}")
    control('char', ctl > 0,
            f"untwisted class count sum_(gC=C) 1 differs from chi(p_P) on {ctl} pairs")


# ---------------------------------------------------------------------------
# [brkt]

def run_brkt(posets, nmax, rng):
    tot = bad = 0
    pairs = 0
    for p_ in range(1, nmax):
        for q_ in range(1, nmax - p_ + 1):
            for r1 in posets[p_]:
                for r2 in posets[q_]:
                    pairs += 1
                    gS = frozenset(range(p_))
                    gT = frozenset(range(p_, p_ + q_))
                    sh = {i: i + p_ for i in range(q_)}
                    r2s = frozenset((sh[a], sh[b]) for (a, b) in r2)
                    rr = r1 | r2s
                    LS, LT = set(lin_ext(gS, r1)), set(lin_ext(gT, r2s))
                    LI = set(lin_ext(gS | gT, rr))
                    RI = R_generators(gS | gT, rr)
                    cS, cT = lie_spanning(gS), lie_spanning(gT)
                    for _ in range(3):
                        x, y = rng.choice(cS), rng.choice(cT)
                        tot += 1
                        b = vbracket(truncate(x, LS), truncate(y, LT))
                        ok = all(w in LI for w in b) and \
                            all(dot(b, r) == 0 for r in RI) and \
                            b == truncate(vbracket(x, y), LI)
                        if not ok:
                            bad += 1
    report('brkt', bad == 0,
           f"{pairs} pairs (P, P'), |P|+|P'| <= {nmax}, {tot} random comb pairs: "
           f"[pr x, pr y] lies in W_(P+P'), is orthogonal to R_(P+P') "
           f"(primitive) and equals pr_(P+P')[x, y], exactly; failures: {bad}")

    # control 1 ([Glob 3.4]): the concatenation commutator does not descend
    # from W_P (x) W_Q to W_P e_zeta (x) W_Q e_zeta -> W_(P+Q) e_zeta.
    p = P0
    nd = fail = 0
    for p_ in range(1, nmax):
        for q_ in range(1, nmax - p_ + 1):
            for r1 in posets[p_]:
                for r2 in posets[q_]:
                    gS = frozenset(range(p_))
                    gT = frozenset(range(p_, p_ + q_))
                    sh = {i: i + p_ for i in range(q_)}
                    r2s = frozenset((sh[a], sh[b]) for (a, b) in r2)
                    LS, LT = lin_ext(gS, r1), lin_ext(gT, r2s)
                    zS, zI = zeta_mod(p_, p), zeta_mod(p_ + q_, p)
                    # kernel of W_P -> W_P e_zeta: l - zeta^k w for l = w gamma^k
                    ker = []
                    for C in classes(LS):
                        w = C[0]
                        for l in C[1:]:
                            k = next(j for j in range(p_) if w[j:] + w[:j] == l)
                            ker.append({l: 1, w: (-pow(zS, k, p)) % p})
                    if not ker:
                        continue
                    nd += 1
                    bad_pair = False
                    for xk in ker:
                        for t in LT:
                            c = vsub(vconcat(xk, {t: 1}), vconcat({t: 1}, xk))
                            if any(apply_ez(c, p_ + q_, zI, p).values()):
                                bad_pair = True
                                break
                        if bad_pair:
                            break
                    fail += bad_pair
    control('brkt', nd > 0 and fail > 0,
            f"[Glob 3.4] reproduced: of the {nd} pairs with ker(W_P -> Lie(P)) != 0, "
            f"{fail} have a commutator that does not descend to the e_zeta model")
    # control 2: commutator with a non-primitive element is not primitive
    g2 = frozenset({0, 1})
    x = {(0, 1): 1}       # single word of the 2-antichain: not primitive
    y = {(2,): 1}
    b = vbracket(x, y)
    RI = R_generators(frozenset({0, 1, 2}), frozenset())
    control('brkt', any(dot(b, r) for r in RI),
            "[12, 3] with 12 a non-primitive word of the 2-antichain pairs "
            "nonzero with R_(3-antichain)")


def apply_ez(x, n, z, p):
    """x e_zeta mod p (times n), as coordinates on rotation-class reps."""
    out = {}
    for w, c in x.items():
        rots = [w[j:] + w[:j] for j in range(n)]
        rep = min(rots)
        k = rots.index(rep)            # w gamma^k = rep, so w = rep gamma^-k
        # w e_z = zeta^(-k) rep e_z
        out[rep] = (out.get(rep, 0) + c * pow(z, (-k) % n, p)) % p
    return out


# ---------------------------------------------------------------------------
# [filt] Theorem 8

def r_of(rels):
    return len(rels)


def run_filt(nmax_r, nmax_q):
    bad = tot = 0
    for n in range(1, nmax_r + 1):
        I = frozenset(range(n))
        for rels in all_labelled(n):
            for k in range(0, n + 1):
                for S in itertools.combinations(range(n), k):
                    S = frozenset(S)
                    T = I - S
                    tot += 1
                    s = r_of(restrict(rels, S)) + r_of(restrict(rels, T))
                    eq = (s == r_of(rels))
                    if s > r_of(rels) or eq != is_union_of_components(I, rels, S):
                        bad += 1
    report('filt', bad == 0,
           f"{tot} (labelled P, S), n <= {nmax_r}: r(P|S)+r(P|T) <= r(P), with "
           f"equality iff S is a union of components; failures: {bad}")
    for n in range(2, nmax_q + 1):
        I = range(n)
        basis = species_basis(I)
        rows = primitive_system(I, basis, 'Q')
        rvals = [r_of(b[0]) for b in basis]
        rmax = max(rvals)
        gr_dims, want = [], []
        prev = 0
        lt_ok = True
        lt_ctl = False
        for r in range(0, rmax + 1):
            cols = [i for i, v in enumerate(rvals) if v <= r]
            ker = kernel_basis(rows, len(basis), cols)
            gr_dims.append(len(ker) - prev)
            prev = len(ker)
            want.append(sum(e_C(frozenset(I), rl) for rl in all_labelled(n)
                            if r_of(rl) == r))
            # leading terms: the r-part of each kernel vector of F_r
            for v in ker:
                lead = {basis[i]: c for i, c in v.items() if rvals[i] == r}
                if not lead:
                    continue
                for k in range(1, n):
                    for S in itertools.combinations(I, k):
                        S = frozenset(S)
                        T = frozenset(I) - S
                        if any(c % P0 for c in coprod(lead, S, T, 'Qp').values()):
                            lt_ok = False
                        if not lt_ctl and any(c % P0 for c in
                                              coprod(lead, S, T, 'Q').values()):
                            lt_ctl = True
        report('filt', gr_dims == want and lt_ok,
               f"n={n}: dim gr_r Prim(Q) = {gr_dims}, sum_(r(P)=r) e_C(P) = {want}; "
               f"leading terms Q'-primitive: {lt_ok}")
        control('filt', lt_ctl,
                f"n={n}: some leading term is NOT primitive for Q's own coproduct")


# ---------------------------------------------------------------------------
# [pbw] Theorem 6

def first_block_basis(ground, rels):
    comps = components(ground, rels)
    base = comps[0]
    out = []
    for w in lin_ext(ground, rels):
        # first union-prefix length > 0
        for k in range(1, len(w) + 1):
            if is_union_of_components(ground, rels, frozenset(w[:k])):
                break
        if base <= frozenset(w[:k]):
            out.append({w: 1})
    return out


def pbw_vectors(ground, rels, choice, max_blocks=None):
    comps = components(ground, rels)
    vecs = []
    for sigma in set_partitions(list(range(len(comps)))):
        if max_blocks is not None and len(sigma) > max_blocks:
            continue
        blocks = [frozenset().union(*[comps[i] for i in b]) for b in sigma]
        bases = []
        for B in blocks:
            rB = restrict(rels, B)
            if choice == 'prim':
                bases.append(prim_space(B, rB)[1])
            else:
                bases.append(first_block_basis(B, rB))
        for combo in itertools.product(*bases):
            v = {(): 1}
            for x in combo:
                v = vshuffle(v, x)
            vecs.append(v)
    return vecs


def run_pbw(posets, nmax):
    for choice in ['prim', 'first-block']:
        tot = bad = 0
        for n in range(1, nmax + 1):
            g = frozenset(range(n))
            for rels in posets[n]:
                tot += 1
                L = lin_ext(g, rels)
                vecs = pbw_vectors(g, rels, choice)
                if not (len(vecs) == len(L) and rank_of(vecs) == len(L)
                        and all(w in set(L) for v in vecs for w in v)):
                    bad += 1
        report('pbw', bad == 0,
               f"V_Q = {choice}: {tot} posets n <= {nmax}: the shuffle products over "
               f"all partitions of the components are |Lin P| vectors of rank |Lin P| "
               f"(Thm 6 isomorphism); failures: {bad}")
    # Lemma 1.3
    bad = 0
    for n in range(1, nmax + 1):
        g = frozenset(range(n))
        for rels in posets[n]:
            comps = components(g, rels)
            s = 0
            for sigma in set_partitions(list(range(len(comps)))):
                prodv = 1
                for b in sigma:
                    B = frozenset().union(*[comps[i] for i in b])
                    prodv *= e_C(B, restrict(rels, B))
                s += prodv
            bad += (s != len(lin_ext(g, rels)))
    report('pbw', bad == 0, f"Lemma 1.3: |Lin P| = sum_sigma prod_B e_C(P|_B), "
           f"posets n <= {nmax}; failures: {bad}")
    # control: drop partitions into >= 3 blocks
    fired = 0
    for n in range(3, nmax + 1):
        g = frozenset(range(n))
        for rels in posets[n]:
            if len(components(g, rels)) >= 3:
                vecs = pbw_vectors(g, rels, 'prim', max_blocks=2)
                if rank_of(vecs) < len(lin_ext(g, rels)):
                    fired += 1
    control('pbw', fired > 0,
            f"dropping partitions with >= 3 blocks loses rank on {fired} posets")
    # equivariant form: chi_W(g) = sum_{g sigma = sigma} prod_{orbits} chi_p(g^k|B)
    bad = tot = ctl = 0
    for n in range(1, nmax + 1):
        g0 = frozenset(range(n))
        for rels in posets[n]:
            comps = components(g0, rels)
            L = lin_ext(g0, rels)
            for a in automorphisms(g0, rels):
                tot += 1
                lhs = len(L) if all(a[x] == x for x in g0) else 0
                rhs = rhs_triv = 0
                for sigma in set_partitions(list(range(len(comps)))):
                    blocks = [frozenset().union(*[comps[i] for i in b]) for b in sigma]
                    bset = set(blocks)
                    if any(frozenset(a[x] for x in B) not in bset for B in blocks):
                        continue
                    term = term_t = 1
                    seen = set()
                    for B in blocks:
                        if B in seen:
                            continue
                        orb = [B]
                        while True:
                            nb = frozenset(a[x] for x in orb[-1])
                            if nb == B:
                                break
                            orb.append(nb)
                        seen |= set(orb)
                        k = len(orb)
                        h = {}
                        for x in B:
                            y = x
                            for _ in range(k):
                                y = a[y]
                            h[x] = y
                        Rp, _ = prim_space(B, restrict(rels, B))
                        term *= signed(Rp.trace(h), Rp.p)
                        term_t *= Rp.rank()
                    rhs += term
                    rhs_triv += term_t
                bad += (lhs != rhs)
                ctl += (lhs != rhs_triv)
    report('pbw', bad == 0,
           f"equivariant form: {tot} pairs (P, g), n <= {nmax}: |Lin P|[g=1] = "
           f"sum_(g sigma = sigma) prod_(orbits) chi_p(P|B)(g^k|B); failures: {bad}")
    control('pbw', ctl > 0, f"with dim in place of chi_p the identity fails on {ctl} pairs")


# ---------------------------------------------------------------------------
# [dual] section 2.3

def run_dual(nmax_dual, nmax_lune):
    # dual product / coproduct of W = Q'^* computed from the pairing
    okp = okc = True
    ctlp = False
    for n in range(1, nmax_dual + 1):
        I = frozenset(range(n))
        basis = species_basis(range(n))
        for k in range(1, n):
            for S in itertools.combinations(range(n), k):
                S = frozenset(S)
                T = I - S
                # <f.g, b> = coefficient of f (x) g in Delta_{S,T} b
                prodW, prodWQ = {}, {}
                for b in basis:
                    for (fa, gb) in coprod({b: 1}, S, T, 'Qp'):
                        prodW.setdefault((fa, gb), set()).add(b)
                    for (fa, gb) in coprod({b: 1}, S, T, 'Q'):
                        prodWQ.setdefault((fa, gb), set()).add(b)
                for (fa, gb), bs in prodW.items():
                    want = {(fa[0] | gb[0], w) for w in shuffle_words(fa[1], gb[1])}
                    if bs != want:
                        okp = False
                for (fa, gb), bs in prodWQ.items():
                    want = {(fa[0] | gb[0], w) for w in shuffle_words(fa[1], gb[1])}
                    if bs != want:
                        ctlp = True
                # dual coproduct: <Delta f, a (x) c> = <f, mu(a (x) c)>
                for b in basis:
                    rels, w = b
                    got = set()
                    # pairs (a on S, c on T) with mu(a (x) c) = b
                    if is_union_of_components(I, rels, S) and set(w[:len(S)]) == S:
                        got.add(((restrict(rels, S), w[:len(S)]),
                                 (restrict(rels, T), w[len(S):])))
                    # independent route: the only candidate factors are the
                    # restrictions; keep them iff their product is b
                    brute = set()
                    a_ =(restrict(rels, S), tuple(z for z in w if z in S))
                    c_ = (restrict(rels, T), tuple(z for z in w if z in T))
                    if prod({a_: 1}, {c_: 1}, 'sum') == {b: 1}:
                        brute.add((a_, c_))
                    if got != brute:
                        okc = False
    report('dual', okp, f"n <= {nmax_dual}: dual of Delta(Q') is (P1, s).(P2, t) = "
           f"sum_(l in s sh t) (P1 + P2, l): disjoint union with shuffle")
    report('dual', okc, f"n <= {nmax_dual}: dual of mu(Q') is deconcatenation at cuts "
           f"(prefixes that are unions of components)")
    control('dual', ctlp, "dual of [Glob]'s Q coproduct is NOT disjoint union + shuffle "
            "(it also produces posets with relations across S, T)")

    # braid top-lunes from sign vectors
    tot = bad = ctl = 0
    for n in range(2, nmax_lune + 1):
        lunes = braid_lunes(n)
        g = frozenset(range(n))
        for rels in all_posets_reps(n):
            tot += 1
            L = set(lin_ext(g, rels))
            inside = [lu for lu in lunes if lu <= L]
            R = R_generators(g, rels)
            RR = RREF()
            for v in R:
                RR.add(v)
            lv = [{w: 1 for w in lu} for lu in inside]
            ok = all(RR.contains(v) for v in lv) and rank_of(lv) == RR.rank()
            bad += not ok
            meet = [{w: 1 for w in lu & L} for lu in lunes if lu & L]
            M = RREF()
            for v in meet:
                M.add(v)
            ctl += (M.rank() != RR.rank())
    report('dual', bad == 0, f"{tot} posets 2 <= n <= {nmax_lune}: span of the braid "
           f"top-lunes contained in C_P (computed from sign vectors and the Tits "
           f"product) = R_P = decomposables (W_+ W_+)_P; failures: {bad}")
    control('dual', ctl > 0, f"lunes merely meeting C_P (truncated) span a different "
            f"space on {ctl} posets")


_POSETS = {}


def all_posets_reps(n):
    if n not in _POSETS:
        _POSETS.update(enumerate_posets(n))
    return _POSETS[n]


def braid_lunes(n):
    """Non-singleton top-lunes L(H, D) = {C : HC = D} of the braid arrangement
    A_{n-1}, computed from sign vectors on the hyperplanes x_i = x_j, i < j."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]

    def sv_face(blockidx):
        return tuple((blockidx[i] > blockidx[j]) - (blockidx[i] < blockidx[j])
                     for (i, j) in pairs)

    chambers = {}
    for w in itertools.permutations(range(n)):
        pos = {x: k for k, x in enumerate(w)}
        chambers[sv_face(pos)] = w
    faces = set()
    for f in itertools.product(range(n), repeat=n):
        used = sorted(set(f))
        if len(used) < 2:
            continue                      # only the central face O
        if used != list(range(len(used))):
            continue
        faces.add(sv_face(f))
    out = set()
    for H in faces:
        for C in chambers:
            D = tuple(h if h else c for h, c in zip(H, C))     # Tits product HC
            out_l = frozenset(chambers[C2] for C2 in chambers
                              if tuple(h if h else c for h, c in zip(H, C2)) == D)
            out.add(out_l)
    return [lu for lu in out if len(lu) > 1]


# ---------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=6, help='posets for trunc/char/pbw')
    ap.add_argument('--nax', type=int, default=4, help='axioms / prim / filt on Q[n]')
    ap.add_argument('--nree', type=int, default=6)
    ap.add_argument('--nbr', type=int, default=6, help='|P|+|P\'| for brackets')
    ap.add_argument('--nlune', type=int, default=5)
    args = ap.parse_args(argv)
    del FAILURES[:]
    print(f"primes: {PRIMES}")
    nm = max(args.nmax, args.nbr - 1)
    posets = enumerate_posets(nm)
    _POSETS.update(posets)
    counts = [len(posets[n]) for n in range(1, nm + 1)]
    report('enum', counts == [1, 2, 5, 16, 63, 318][:nm], f"posets n=1..{nm}: {counts}")
    rng = random.Random(1)
    run_axioms(args.nax)
    run_prim(args.nax)
    run_ree(args.nree)
    run_trunc(posets, args.nmax)
    run_char(posets, args.nmax)
    run_brkt(posets, args.nbr, rng)
    run_filt(args.nax + 1, args.nax)
    run_pbw(posets, args.nmax)
    run_dual(args.nax, args.nlune)
    if FAILURES:
        print("FAILURES:")
        for f in FAILURES:
            print("  " + f)
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == '__main__':
    sys.exit(main())
