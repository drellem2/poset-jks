#!/usr/bin/env python3
"""Checks for notes/cr_v_type_a.md: Conjecture CR_V on the cones of the braid
arrangement, in poset language.

For a finite poset P on [n] and g = eps*t in +-S_n with g C_P = C_P (eps = +1:
t in Aut(P); eps = -1: t an anti-automorphism), the lattice is M = OP(P)^t: the
t-stable partitions of [n] whose quotient digraph is acyclic, ordered by
refinement (bottom = discrete partition, top = one block).  This is the dual of
Lambda(C_P)^g; complementation and mu(0,1) are self-dual.

  meet = common refinement      (pair sets intersect)
  join = acyclic closure (merge strongly connected components) of the
         partition join

chi_{C_P}(g) = 0  iff  mu(M) = 0  (the factor (-1)^d det g is a unit).

Self-contained: imports nothing from the other scripts of compute/.

Parts:
  [CTL]  controls: poset counts 1,1,2,5,16,63,318,2045 for n = 0..7; the lattice
         routines on known lattices (a chain = Pi_4^{(1234)}, Pi_3, Pi_4 with
         mu = -1, 2, -6; B_2 = Pi_3^{(12)}); the complement test on a chain
         (fails), on Pi_n (passes); the Crapo direction (every nonzero pair is
         complemented) as a check of the meet/join code.
  [CRIT] the zero pattern of mu(M) against the closed criteria: for +w,
         [Thm, eq. closed] (mu(ord w) != 0 and <w> free on components); for -t,
         Theorem TA of notes/per_cone_vanishing.md, (TA1)-(TA4).
  [WIT]  on every zero, the explicit witness of notes/cr_v_type_a.md (Theorem
         TA-CR) lies in M and has no complement in M; also the full list of
         uncomplemented elements is compared against the witness families.
  [RED]  Lemma K (poset form): for w in M refining c = cl(Fix g), the
         complements of w are exactly the t-stable x coarser than comp(P) with
         x ^ w = 0 and (partition join) x v w = 1.

  [EXTRA] 13 targeted pairs with n = 8, 9, 18 for the witness rows that are rare
         or absent at n <= 7 (W+2, and W-1 with m odd and not squarefree), plus
         nonzero controls.

Every pair (P, g) is taken up to isomorphism: P up to iso, t up to conjugation
by Aut(P).  n = 3..7 (n = 7 is optional and bounded by --budget seconds).

Run:  python3 cr_v_type_a.py [--nmax 7] [--budget SECONDS]
"""
import itertools
import sys
import time
from math import gcd

# ------------------------------------------------------------- partitions


def rgs_all(n):
    """All set partitions of range(n) as restricted growth strings."""
    out = []

    def rec(i, cur, mx):
        if i == n:
            out.append(tuple(cur))
            return
        for b in range(mx + 2):
            cur.append(b)
            rec(i + 1, cur, max(mx, b))
            cur.pop()
    if n == 0:
        return [()]
    rec(1, [0], 0)
    return out


def canon_labels(lab):
    m, out = {}, []
    for x in lab:
        if x not in m:
            m[x] = len(m)
        out.append(m[x])
    return tuple(out)


def pair_index(n):
    idx, k = {}, 0
    for i in range(n):
        for j in range(i + 1, n):
            idx[(i, j)] = k
            k += 1
    return idx


def pmask(lab, PI):
    n, m = len(lab), 0
    for i in range(n):
        for j in range(i + 1, n):
            if lab[i] == lab[j]:
                m |= 1 << PI[(i, j)]
    return m


def blocks_of(lab):
    d = {}
    for i, b in enumerate(lab):
        d.setdefault(b, []).append(i)
    return list(d.values())


def from_blocks(n, blocks):
    lab = [None] * n
    for b, B in enumerate(blocks):
        for x in B:
            lab[x] = b
    assert None not in lab
    return canon_labels(lab)


def common_refinement(a, b):
    return canon_labels(list(zip(a, b)))


def partition_join(a, b):
    n = len(a)
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for lab in (a, b):
        first = {}
        for i, l in enumerate(lab):
            if l in first:
                par[f(i)] = f(first[l])
            else:
                first[l] = i
    return canon_labels([f(i) for i in range(n)])


def image(lab, t):
    """Partition t(lab): block t(B) for each block B."""
    n = len(lab)
    new = [None] * n
    for i in range(n):
        new[t[i]] = lab[i]
    return canon_labels(new)


# ------------------------------------------------------------- posets


class Poset:
    def __init__(self, n, rel):
        self.n = n
        self.rel = frozenset(rel)          # strict, transitively closed: (i, j) means i < j
        self.lt = [[False] * n for _ in range(n)]
        for i, j in self.rel:
            self.lt[i][j] = True

    def quotient_acyclic(self, lab):
        k = max(lab) + 1 if lab else 0
        adj = [set() for _ in range(k)]
        for i, j in self.rel:
            if lab[i] != lab[j]:
                adj[lab[i]].add(lab[j])
        color = [0] * k
        for s in range(k):
            if color[s]:
                continue
            stack = [(s, iter(adj[s]))]
            color[s] = 1
            while stack:
                u, it = stack[-1]
                v = next(it, None)
                if v is None:
                    color[u] = 2
                    stack.pop()
                elif color[v] == 1:
                    return False
                elif color[v] == 0:
                    color[v] = 1
                    stack.append((v, iter(adj[v])))
        return True

    def acyclic_closure(self, lab):
        """Merge the strongly connected components of the quotient digraph."""
        k = max(lab) + 1
        adj = [set() for _ in range(k)]
        for i, j in self.rel:
            if lab[i] != lab[j]:
                adj[lab[i]].add(lab[j])
        # reachability (k <= 7)
        reach = [set([u]) for u in range(k)]
        changed = True
        while changed:
            changed = False
            for u in range(k):
                new = set(reach[u])
                for v in reach[u]:
                    new |= adj[v]
                if new != reach[u]:
                    reach[u] = new
                    changed = True
        scc = [min(v for v in reach[u] if u in reach[v]) for u in range(k)]
        return canon_labels([scc[l] for l in lab])

    def components(self):
        par = list(range(self.n))

        def f(x):
            while par[x] != x:
                x = par[x]
            return x
        for i, j in self.rel:
            par[f(i)] = f(j)
        return canon_labels([f(i) for i in range(self.n)])

    def is_aut(self, t):
        return all(self.lt[t[i]][t[j]] for i, j in self.rel)

    def is_anti(self, t):
        return all(self.lt[t[j]][t[i]] for i, j in self.rel)


def invariants(n, lt):
    down = [sum(lt[j][i] for j in range(n)) for i in range(n)]
    up = [sum(lt[i][j] for j in range(n)) for i in range(n)]
    inv = [(down[i], up[i]) for i in range(n)]
    for _ in range(2):
        inv = [(inv[i], tuple(sorted(inv[j] for j in range(n) if lt[j][i])),
                tuple(sorted(inv[j] for j in range(n) if lt[i][j]))) for i in range(n)]
    return inv


def canon_form(n, rel):
    lt = [[False] * n for _ in range(n)]
    for i, j in rel:
        lt[i][j] = True
    inv = invariants(n, lt)
    keys = sorted(set(inv))
    classes = [[i for i in range(n) if inv[i] == k] for k in keys]
    best = None
    for choice in itertools.product(*[itertools.permutations(c) for c in classes]):
        order = [x for c in choice for x in c]          # new position -> old element
        pos = {old: new for new, old in enumerate(order)}
        f = tuple(sorted((pos[i], pos[j]) for i, j in rel))
        if best is None or f < best:
            best = f
    return (tuple(keys), tuple(len(c) for c in classes), best)


def posets_up_to_iso(nmax):
    """Iso classes of posets on n points, n = 0..nmax, by adding a maximal element."""
    levels = {0: [frozenset()]}
    for n in range(1, nmax + 1):
        seen, out = set(), []
        for rel in levels[n - 1]:
            m = n - 1
            lt = [[False] * m for _ in range(m)]
            for i, j in rel:
                lt[i][j] = True
            # down-sets D of P; new element m with x < m iff x in D
            for r in range(m + 1):
                for D in itertools.combinations(range(m), r):
                    Ds = set(D)
                    if any(lt[y][x] and y not in Ds for x in Ds for y in range(m)):
                        continue
                    new = set(rel) | {(x, m) for x in Ds}
                    cf = canon_form(n, new)
                    if cf not in seen:
                        seen.add(cf)
                        out.append(frozenset(new))
        levels[n] = out
    return levels


def perms_respecting(n, inv_src, inv_dst):
    """Permutations t with inv_dst[t(i)] == inv_src[i]."""
    keys = sorted(set(inv_src))
    if sorted(inv_src) != sorted(inv_dst):
        return
    src = [[i for i in range(n) if inv_src[i] == k] for k in keys]
    dst = [[i for i in range(n) if inv_dst[i] == k] for k in keys]
    for choice in itertools.product(*[itertools.permutations(d) for d in dst]):
        t = [None] * n
        for s, c in zip(src, choice):
            for a, b in zip(s, c):
                t[a] = b
        yield tuple(t)


def symmetries(P):
    """(auts, antis) of P."""
    n = P.n
    inv = invariants(n, P.lt)
    ltop = [[P.lt[j][i] for j in range(n)] for i in range(n)]
    invop = invariants(n, ltop)
    auts = [t for t in perms_respecting(n, inv, inv) if P.is_aut(t)]
    antis = [t for t in perms_respecting(n, inv, invop) if P.is_anti(t)]
    return auts, antis


def compose(s, t):            # (s o t)(i) = s[t[i]]
    return tuple(s[x] for x in t)


def inverse(s):
    r = [0] * len(s)
    for i, x in enumerate(s):
        r[x] = i
    return tuple(r)


def conj_classes(elems, group):
    seen, reps = set(), []
    for t in elems:
        if t in seen:
            continue
        reps.append(t)
        for s in group:
            seen.add(compose(compose(s, t), inverse(s)))
    return reps


# ------------------------------------------------------------- permutations


def cycles(t):
    seen, cs = set(), []
    for i in range(len(t)):
        if i in seen:
            continue
        c, j = [i], t[i]
        seen.add(i)
        while j != i:
            c.append(j)
            seen.add(j)
            j = t[j]
        cs.append(c)
    return cs


def order(t):
    o = 1
    for c in cycles(t):
        o = o * len(c) // gcd(o, len(c))
    return o


def power(t, k):
    r = tuple(range(len(t)))
    for _ in range(k):
        r = compose(t, r)
    return r


def mob(k):
    r, d = 1, 2
    while d * d <= k:
        if k % d == 0:
            k //= d
            if k % d == 0:
                return 0
            r = -r
        d += 1
    return -r if k > 1 else r


def smallest_square_prime(o):
    for p in range(2, o + 1):
        if o % (p * p) == 0 and all(p % q for q in range(2, p)):
            return p
    return None


def cl_fix(n, eps, t):
    """cl(Fix(eps*t)) on R^n_0 as a partition: i ~ j iff x_i = x_j on Fix."""
    cs = cycles(t)
    if eps == 1:
        return from_blocks(n, cs)
    blocks, odd = [], []
    for c in cs:
        if len(c) % 2:
            odd += c
        else:
            blocks.append(c[0::2])
            blocks.append(c[1::2])
    if odd:
        blocks.append(odd)
    return from_blocks(n, blocks)


def component_orbits(comp, t):
    """For each component (block of comp), the length of its <t>-orbit."""
    out = []
    for B in blocks_of(comp):
        K = frozenset(B)
        s, C = 1, frozenset(t[x] for x in K)
        while C != K:
            C, s = frozenset(t[x] for x in C), s + 1
        out.append((K, s))
    return out


def stable_partitions(n, t):
    """All t-stable partitions of range(n), built block-orbit by block-orbit
    (independent of rgs_all; cross-checked against it for n <= 7 in [CTL])."""
    out = []

    def orbit(B):
        orb, C = [B], frozenset(t[x] for x in B)
        while C != B:
            orb.append(C)
            C = frozenset(t[x] for x in C)
        return orb

    def rec(unassigned, blocks):
        if not unassigned:
            out.append(from_blocks(n, blocks))
            return
        x = min(unassigned)
        rest = sorted(unassigned - {x})

        def grow(i, B):
            # prune: an image t^j B meeting B must equal B in the end; elements
            # below rest[i] are decided, so an undecided-free violation is final
            Bf = frozenset(B)
            C = frozenset(t[y] for y in Bf)
            while C != Bf:
                if C & Bf:
                    if not C <= unassigned:
                        return
                    lim = rest[i] if i < len(rest) else n
                    if any(y < lim and y not in Bf for y in C):
                        return
                elif not C <= unassigned:
                    return
                C = frozenset(t[y] for y in C)
            if i == len(rest):
                orb = orbit(Bf)
                if all(not (orb[a] & orb[b]) for a in range(len(orb)) for b in range(a + 1, len(orb))):
                    rec(unassigned - frozenset().union(*orb), blocks + orb)
                return
            grow(i + 1, B)
            grow(i + 1, B + [rest[i]])
        grow(0, [x])
    rec(frozenset(range(n)), [])
    return out


# ------------------------------------------------------------- the lattice M


class Lattice:
    def __init__(self, P, t, allparts, PI):
        self.P, self.t, self.PI = P, t, PI
        n = P.n
        cand = stable_partitions(n, t) if allparts is None else [p for p in allparts if image(p, t) == p]
        self.elems = [p for p in cand if P.quotient_acyclic(p)]
        self.index = {p: i for i, p in enumerate(self.elems)}
        self.mask = [pmask(p, PI) for p in self.elems]
        self.bot = self.index[tuple(range(n))]
        self.top = self.index[tuple([0] * n)]
        self._join = {}

    def contains(self, p):
        return p in self.index

    def join(self, i, j):
        key = (i, j) if i < j else (j, i)
        r = self._join.get(key)
        if r is None:
            pj = partition_join(self.elems[i], self.elems[j])
            r = self.index[self.P.acyclic_closure(pj)]
            self._join[key] = r
        return r

    def meet_is_bot(self, i, j):
        return (self.mask[i] & self.mask[j]) == 0

    def mu(self):
        order_ = sorted(range(len(self.elems)), key=lambda i: bin(self.mask[i]).count('1'))
        mu = {}
        for i in order_:
            if i == self.bot:
                mu[i] = 1
                continue
            mi = self.mask[i]
            mu[i] = -sum(v for j, v in mu.items() if (self.mask[j] | mi) == mi and j != i)
        return mu[self.top]

    def complements(self, a):
        return [x for x in range(len(self.elems))
                if self.meet_is_bot(a, x) and self.join(a, x) == self.top]

    def has_complement(self, a):
        for x in range(len(self.elems)):
            if self.meet_is_bot(a, x) and self.join(a, x) == self.top:
                return True
        return False

    def uncomplemented(self):
        return [a for a in range(len(self.elems)) if not self.has_complement(a)]

    def check_lattice_ops(self, sample=60):
        """Control: the join returned is the least upper bound in M (on a sample)."""
        E = range(len(self.elems))
        idx = list(E)[:sample]
        for i in idx:
            for j in idx:
                k = self.join(i, j)
                mk = self.mask[k]
                if (self.mask[i] | mk) != mk or (self.mask[j] | mk) != mk:
                    return False
                for z in E:
                    mz = self.mask[z]
                    if (self.mask[i] | mz) == mz and (self.mask[j] | mz) == mz and (mk | mz) != mz:
                        return False
        return True


# ------------------------------------------------------------- criteria


def crit_plus(P, w):
    """[Thm, eq. closed]: chi(+w) != 0 iff mu(ord w) != 0 and <w> acts freely on comps."""
    o = order(w)
    if mob(o) == 0:
        return False
    return all(s == o for _, s in component_orbits(P.components(), w))


def crit_minus(P, t):
    """Theorem TA of [PCV]: chi(-t) != 0 iff (TA1)-(TA4)."""
    return ta_failure(P, t) is None


def ta_failure(P, t):
    """First failing condition among TA1..TA4, or None."""
    n = P.n
    cs = cycles(t)
    Ls = set(len(c) for c in cs)
    odd = sorted(l for l in Ls if l % 2)
    ev = sorted(l for l in Ls if l % 2 == 0)
    if len(odd) > 1 or len(ev) > 1:
        return 'TA1'
    m = odd[0] if odd else ev[0] // 2
    if (ev and ev[0] != 2 * m) or m % 2 == 0 or mob(m) == 0:
        return 'TA1'
    O = {x for c in cs if len(c) % 2 for x in c}
    comp = P.components()
    tm = power(t, m)
    orbs = component_orbits(comp, t)
    if any(s not in (m, 2 * m) for _, s in orbs):
        return 'TA2'
    for K, _ in orbs:
        if len((K | frozenset(tm[x] for x in K)) & O) > 1:
            return 'TA3'
    if O and ev:
        iso = {x for K, _ in orbs if len(K) == 1 for x in K}
        if O <= iso:
            return 'TA4'
    return None


# ------------------------------------------------------------- witnesses (Theorem TA-CR)


def witness(P, eps, t):
    """The explicit uncomplemented element of notes/cr_v_type_a.md, as a partition,
    together with the name of the case.  Returns (None, None) when the closed
    criterion says chi != 0."""
    n = P.n
    comp = P.components()
    if eps == 1:
        o = order(t)
        orbs = component_orbits(comp, t)
        if any(s != o for _, s in orbs):
            return 'W+1 cyc(w)', cl_fix(n, 1, t)
        if mob(o) == 0:
            p = smallest_square_prime(o)
            return 'W+2 cyc(w^(o/p))', cl_fix(n, 1, power(t, o // p))
        return None, None
    f = ta_failure(P, t)
    if f is None:
        return None, None
    cs = cycles(t)
    if f == 'TA4':
        O = {x for c in cs if len(c) % 2 for x in c}
        Q = [x for x in range(n) if x not in O]
        return 'W-4 Q|singletons', from_blocks(n, [Q] + [[x] for x in sorted(O)])
    if f in ('TA2', 'TA3'):
        # cl(Fix g) = c; some component holds two points of one block of c
        return f'W-{f[-1]} cl(Fix g)', cl_fix(n, -1, t)
    # TA1: cl(Fix g^k) = cyc(t^k), k even (choose_k)
    k = choose_k(t)
    return f'W-1 cyc(t^{k})', cl_fix(n, 1, power(t, k))


def two_adic(x):
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def choose_k(t):
    """Exponent k of the (TA1) witness cl(Fix (-t)^k) = cyc(t^k) (Theorem TA-CR):
    k = 2m/p if every cycle length lies in {m, 2m} for one odd m (then m is not
    squarefree and p is the least prime with p^2 | m), and k = 2 otherwise."""
    Ls = set(len(c) for c in cycles(t))
    odd = [l for l in Ls if l % 2]
    ev = [l for l in Ls if l % 2 == 0]
    m = odd[0] if odd else ev[0] // 2
    if m % 2 == 1 and Ls <= {m, 2 * m}:
        p = smallest_square_prime(m)
        assert p is not None, "TA1 would hold"
        return 2 * m // p
    return 2


def lemma_C_predicts_complement(comp, t, h):
    """Lemma C: some t-stable x >= comp has x ^ w = 0 and x v w = 1 (partition
    join), w = orbits of <t^h>, iff there is s with gcd(s, h) = 1, s | lambda_K for
    every component K, and l / gcd(l, h) = s for every cycle length l."""
    Ls = set(len(c) for c in cycles(t))
    ss = set(l // gcd(l, h) for l in Ls)
    if len(ss) != 1:
        return False
    s = ss.pop()
    if gcd(s, h) != 1:
        return False
    return all(lam % s == 0 for _, lam in component_orbits(comp, t))


# ------------------------------------------------------------- driver


def hanlon_mu(t):
    """Hanlon: mu(Pi_n^t) = (-1)^{r-1} mu(l) l^{r-1} (r-1)! if all r cycles have
    length l, else 0."""
    Ls = [len(c) for c in cycles(t)]
    if len(set(Ls)) != 1:
        return 0
    l, r = Ls[0], len(Ls)
    f = 1
    for i in range(1, r):
        f *= i
    return (-1) ** (r - 1) * mob(l) * l ** (r - 1) * f


def antichain(n):
    return Poset(n, [])


def part_CTL(levels, nmax, st):
    ok = True
    want = [1, 1, 2, 5, 16, 63, 318, 2045]
    got = [len(levels[k]) for k in range(nmax + 1)]
    c1 = got == want[:nmax + 1]
    print(f"  [CTL] poset iso classes n=0..{nmax}: {got} (OEIS A000112: {want[:nmax + 1]}) {'ok' if c1 else 'FAIL'}")
    ok &= c1
    # mu of Pi_n and Pi_n^t (Hanlon), all t up to conjugacy, n <= 6
    bad, cnt = 0, 0
    for n in range(1, 7):
        allparts, PI = rgs_all(n), pair_index(n)
        P = antichain(n)
        seen = set()
        for t in itertools.permutations(range(n)):
            ct = tuple(sorted(len(c) for c in cycles(t)))
            if ct in seen:
                continue
            seen.add(ct)
            M = Lattice(P, t, allparts, PI)
            cnt += 1
            if M.mu() != hanlon_mu(t):
                bad += 1
    print(f"  [CTL] mu(Pi_n^t) = Hanlon's value on {cnt} cycle types, n <= 6: {'ok' if not bad else 'FAIL %d' % bad}")
    ok &= not bad
    # a chain: Pi_4^(1234) = 0 < {13|24} < 1
    allparts, PI = rgs_all(4), pair_index(4)
    M = Lattice(antichain(4), (1, 2, 3, 0), allparts, PI)
    unc = [M.elems[a] for a in M.uncomplemented()]
    c2 = len(M.elems) == 3 and M.mu() == 0 and unc == [(0, 1, 0, 1)]
    print(f"  [CTL] Pi_4^(1234): {len(M.elems)} elements, mu = {M.mu()}, uncomplemented {unc} {'ok' if c2 else 'FAIL'}")
    ok &= c2
    # Pi_4 is complemented (geometric); the chain 0<1<2 has OP = B_2 (mu = 1)
    M = Lattice(antichain(4), (0, 1, 2, 3), allparts, PI)
    c3 = len(M.elems) == 15 and M.mu() == -6 and not M.uncomplemented() and M.check_lattice_ops(15)
    P = Poset(3, [(0, 1), (1, 2), (0, 2)])
    M2 = Lattice(P, (0, 1, 2), rgs_all(3), pair_index(3))
    c4 = len(M2.elems) == 4 and M2.mu() == 1
    print(f"  [CTL] Pi_4: 15 elements, mu = -6, complemented, joins are lubs {'ok' if c3 else 'FAIL'}; "
          f"OP(chain of 3) = B_2, mu = 1 {'ok' if c4 else 'FAIL'}")
    ok &= c3 and c4
    # acyclic closure: P = {0<2, 1<3}; 03|1|2 v 12|0|3 = 03|12 is cyclic -> one block
    P = Poset(4, [(0, 2), (1, 3)])
    a, b = from_blocks(4, [[0, 3], [1], [2]]), from_blocks(4, [[1, 2], [0], [3]])
    c5 = (not P.quotient_acyclic(partition_join(a, b))) and P.acyclic_closure(partition_join(a, b)) == (0, 0, 0, 0)
    print(f"  [CTL] F6 example of [AudPCV]: X_03|1|2 v X_12|0|3 is not the partition join (closure = one block) {'ok' if c5 else 'FAIL'}")
    ok &= c5
    # pair counts without conjugacy reduction against the archived log of
    # compute/per_cone_vanishing.py (its [TA] part: -tau pairs and lattices per n)
    pcv = {3: (8, 20), 4: (37, 96), 5: (153, 478), 6: (922, 2982)}
    mine = {}
    for n in range(3, min(nmax, 6) + 1):
        A = B = 0
        for rel in levels[n]:
            a, b = symmetries(Poset(n, rel))
            A, B = A + len(a), B + len(b)
        mine[n] = (B, A + B)
    c6 = all(mine[n] == pcv[n] for n in mine)
    print(f"  [CTL] (P, t) pairs without conjugacy reduction, (anti, anti + aut) per n: {mine}; "
          f"output/per_cone_vanishing.txt: {pcv} {'ok' if c6 else 'FAIL'}")
    ok &= c6
    st['CTL'] = ok
    return ok


def chains_poset(k):
    """k disjoint 2-chains: lower i < upper k + i (i < k)."""
    return Poset(2 * k, [(i, k + i) for i in range(k)])


def extra_cases():
    """Targeted pairs beyond n = 7, for the witness cases that first occur there.
    Each entry: (label, P, eps, t, expect_zero)."""
    E = []
    a8 = antichain(8)
    w44 = (1, 2, 3, 0, 5, 6, 7, 4)
    E.append(('antichain 8, +(4,4)         [W+2]', a8, 1, w44, True))
    E.append(('antichain 8, -(4,4)         [W-1, k=2]', a8, -1, w44, True))
    c4 = chains_poset(4)                      # w cycles the four chains
    E.append(('four 2-chains, +(4,4) free  [W+2]', c4, 1, w44, True))
    w8 = tuple((i + 1) % 8 for i in range(8))
    E.append(('antichain 8, +(8)           [W+2]', a8, 1, w8, True))
    E.append(('antichain 8, -(8)           [W-1, k=2]', a8, -1, w8, True))
    a9 = antichain(9)
    w9 = tuple((i + 1) % 9 for i in range(9))
    E.append(('antichain 9, +(9)           [W+2]', a9, 1, w9, True))
    E.append(('antichain 9, -(9)           [W-1, m=9, k=6]', a9, -1, w9, True))
    w333 = (1, 2, 0, 4, 5, 3, 7, 8, 6)
    E.append(('antichain 9, +(3,3,3)       [nonzero]', a9, 1, w333, False))
    E.append(('antichain 9, -(3,3,3)       [nonzero]', a9, -1, w333, False))
    a18 = antichain(18)
    w18 = tuple((i + 1) % 18 for i in range(18))
    E.append(('antichain 18, +(18)         [W+2]', a18, 1, w18, True))
    E.append(('antichain 18, -(18)         [W-1, m=9, k=6]', a18, -1, w18, True))
    # nine 2-chains {2a < 2a+1}, a in Z_9; t(2a) = 2a+3, t(2a+1) = 2a+2 (mod 18)
    P9 = Poset(18, [(2 * a, 2 * a + 1) for a in range(9)])
    t18 = tuple(((x + 3) if x % 2 == 0 else (x + 1)) % 18 for x in range(18))
    E.append(('nine 2-chains, -(18) anti   [W-1, m=9, k=6]', P9, -1, t18, True))
    # same poset, an anti-automorphism of type (6,6,6): chains (a, g), a in Z_3
    def lo(a, g): return 2 * (3 * g + a % 3)
    def up(a, g): return lo(a, g) + 1
    t6 = [None] * 18
    for g in range(3):
        for a in range(3):
            t6[lo(a, g)] = up(a + 1, g)
            t6[up(a, g)] = lo(a + 1, g)
    E.append(('nine 2-chains, -(6,6,6)     [nonzero, case IIa]', P9, -1, tuple(t6), False))
    return E


def part_EXTRA(st, budget):
    ok = True
    t0 = time.time()
    for label, P, eps, t, expect_zero in extra_cases():
        if time.time() - t0 > budget:
            print(f"  [EXTRA] {label}: UNRUN (budget)")
            ok = False
            continue
        n = P.n
        assert (P.is_aut(t) if eps == 1 else P.is_anti(t)), label
        PI = pair_index(n)
        M = Lattice(P, t, None, PI)
        mu = M.mu()
        crit = crit_plus(P, t) if eps == 1 else crit_minus(P, t)
        good = (crit == (mu != 0)) and ((mu == 0) == expect_zero)
        if mu == 0:
            name, wpart = witness(P, eps, t)
            wok = name is not None and M.contains(wpart) and not M.has_complement(M.index[wpart])
            good &= wok
            info = f"witness {name} = {blocks_of(wpart) if n <= 9 else str(len(blocks_of(wpart))) + ' blocks'} uncomplemented: {wok}"
        else:
            unc = M.uncomplemented()
            good &= not unc
            info = f"Crapo control: every element complemented: {not unc}"
        print(f"  [EXTRA] {label}: |M| = {len(M.elems)}, mu = {mu}, {info}  {'ok' if good else 'FAIL'}")
        ok &= good
    st['EXTRA'] = ok
    return ok


def run(levels, nmin, nmax, budget, crapo_nmax, st):
    t0 = time.time()
    ok = True
    for n in range(nmin, nmax + 1):
        tn = time.time()
        allparts, PI = rgs_all(n), pair_index(n)
        S = {k: 0 for k in ('pairs+', 'pairs-', 'zeros+', 'zeros-', 'crit_fail', 'wit_ok', 'wit_fail',
                            'crapo_checked', 'crapo_fail', 'red_checked', 'red_fail', 'K_fail',
                            'nonwitness_complemented', 'red_true')}
        cases = {}
        done_all = True
        for pi, rel in enumerate(levels[n]):
            if time.time() - t0 > budget:
                done_all = False
                print(f"  n={n}: budget exhausted after {pi} of {len(levels[n])} posets -- remaining posets UNRUN")
                break
            P = Poset(n, rel)
            comp = P.components()
            auts, antis = symmetries(P)
            for eps, elems in ((1, auts), (-1, antis)):
                for t in conj_classes(elems, auts):
                    M = Lattice(P, t, allparts, PI)
                    S['pairs+' if eps == 1 else 'pairs-'] += 1
                    mu = M.mu()
                    crit = crit_plus(P, t) if eps == 1 else crit_minus(P, t)
                    if crit != (mu != 0):
                        S['crit_fail'] += 1
                        print(f"    CRIT FAIL n={n} P={sorted(rel)} eps={eps} t={t} mu={mu}")
                    c = cl_fix(n, eps, t)
                    o = order(t) if eps == 1 else order(t) * 2 // gcd(order(t), 2)
                    # [RED]: Lemma K (complements of w <= c are >= comp) and Lemma C
                    for k in range(1, o):
                        e = eps ** k
                        tk = power(t, k)
                        w = cl_fix(n, e, tk)
                        if not M.contains(w):
                            S['K_fail'] += 1
                            print(f"    cl(Fix g^{k}) NOT IN M: n={n} P={sorted(rel)} eps={eps} t={t}")
                            continue
                        wi = M.index[w]
                        comps_ = M.complements(wi)
                        if any((pmask(comp, PI) | M.mask[x]) != M.mask[x] for x in comps_):
                            S['K_fail'] += 1
                            print(f"    LEMMA K FAIL: n={n} P={sorted(rel)} eps={eps} t={t} k={k}")
                        if e == 1:                     # w = orbits of <t^h>, h = gcd(k, ord t)
                            h = gcd(k, order(t))
                            S['red_checked'] += 1
                            S['red_true'] += bool(comps_)
                            if lemma_C_predicts_complement(comp, t, h) != bool(comps_):
                                S['red_fail'] += 1
                                print(f"    LEMMA C FAIL: n={n} P={sorted(rel)} eps={eps} t={t} k={k}")
                    if mu == 0:
                        S['zeros+' if eps == 1 else 'zeros-'] += 1
                        name, wpart = witness(P, eps, t)
                        if name is None or not M.contains(wpart) or M.has_complement(M.index[wpart]):
                            S['wit_fail'] += 1
                            print(f"    WITNESS FAIL n={n} P={sorted(rel)} eps={eps} t={t} {name} {wpart}")
                        else:
                            S['wit_ok'] += 1
                            key = name.split()[0]
                            cases[key] = cases.get(key, 0) + 1
                        # negative control: is c = cl(Fix g) complemented although chi = 0?
                        if M.has_complement(M.index[c]):
                            S['nonwitness_complemented'] += 1
                    elif n <= crapo_nmax:
                        S['crapo_checked'] += 1
                        if M.uncomplemented():
                            S['crapo_fail'] += 1
                            print(f"    CRAPO FAIL n={n} P={sorted(rel)} eps={eps} t={t}")
        fails = S['crit_fail'] + S['wit_fail'] + S['crapo_fail'] + S['red_fail'] + S['K_fail']
        ok &= fails == 0 and done_all
        print(f"  n={n}: pairs +w {S['pairs+']}, -t {S['pairs-']}; zeros +w {S['zeros+']}, -t {S['zeros-']}; "
              f"criterion mismatches {S['crit_fail']}; witness uncomplemented {S['wit_ok']}, failures {S['wit_fail']}")
        print(f"         by case {dict(sorted(cases.items()))}")
        print(f"         Lemma C checks {S['red_checked']} (complemented {S['red_true']}, uncomplemented "
              f"{S['red_checked'] - S['red_true']}; failures {S['red_fail']}); Lemma K/F failures {S['K_fail']}; "
              f"Crapo control (nonzero pairs all complemented) {S['crapo_checked'] if n <= crapo_nmax else 'UNRUN (n > crapo_nmax)'}"
              f"{'' if n > crapo_nmax else ', failures %d' % S['crapo_fail']}")
        print(f"         negative control: zeros where cl(Fix g) itself IS complemented: {S['nonwitness_complemented']}"
              f"  [{time.time() - tn:.1f}s]{'' if done_all else '  (PARTIAL: see UNRUN above)'}", flush=True)
        st[n] = (S, cases, done_all)
        if not done_all:
            for n2 in range(n + 1, nmax + 1):
                print(f"  n={n2}: UNRUN (budget)")
            break
    return ok


def main(argv):
    nmax, budget, crapo_nmax = 7, 3000.0, 6
    if '--nmax' in argv:
        nmax = int(argv[argv.index('--nmax') + 1])
    if '--budget' in argv:
        budget = float(argv[argv.index('--budget') + 1])
    if '--crapo-nmax' in argv:
        crapo_nmax = int(argv[argv.index('--crapo-nmax') + 1])
    t0 = time.time()
    levels = posets_up_to_iso(nmax)
    print(f"cr_v_type_a.py: n = 3..{nmax}, budget {budget:.0f}s; posets generated in {time.time() - t0:.1f}s")
    st = {}
    ok = part_CTL(levels, nmax, st)
    ok &= part_EXTRA(st, budget)
    ok &= run(levels, 3, nmax, budget, crapo_nmax, st)
    print(f"total {time.time() - t0:.1f}s")
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED OR UNRUN")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
