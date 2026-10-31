#!/usr/bin/env python3
"""Independent audit of notes/observation_cc.md (Theorem CC and its steps).

Written from the statements in the note only.  It imports nothing from the
other scripts of this repository (in particular not observation_cc.py or
cr_v_type_a.py).  Plain Python 3, no third-party packages.

Model.  P is a poset on [n] given by down[j] = bitmask of the i with i <_P j.
A set partition is stored by its "pair mask": bit k is set when the k-th pair
{i < j} lies in one block.  Refinement is inclusion of pair masks, and the
common refinement is AND.  M = OP(P)^tau is the set of tau-stable partitions
whose quotient digraph is acyclic.  Nothing about meets or joins *in M* is
assumed: LOW and HIGH are decided from the definitions,
  LOW  <=> some x in M, x != 0, lies below every coatom of M
           (x <= every coatom iff mask(x) is inside the AND of their masks);
  HIGH <=> some x in M, x != 1, lies above every atom of M
           (x >= every atom iff x >= the partition join of the atoms);
and complements are found by scanning M.

Parts:
  [CTL]   controls: poset counts (OEIS A000112), mu(Pi_n), Pi_4 (LOW and
          HIGH both false, mu = -6), Pi_4^(1234) (CC, mu = 0),
          Pi_3^(012) = {0,1}, and an abstract complemented lattice with
          mu = 0 on which the CC test must report a mismatch;
  [SWEEP] every poset with 3 <= n <= NMAX up to isomorphism, every tau in
          Aut(P) (sign +) and every anti-automorphism (sign -) up to
          conjugacy by Aut(P).  Checks: CC, the cited zero criteria, c by
          exact linear algebra against its explicit form, c, D, c^D in M,
          Lemma CD, Lemma CK, Prop. A, Prop. Z+/Z- (coverage), Prop. B,
          Prop. B', Cor. U, Cor. X;
  [NEG]   deliberately broken witnesses that MUST fail somewhere:
          kappa in place of D, Q|singletons in place of O|Q, D built with
          r = 1, the CC test without HIGH;
  [BIG]   tau = (9)(18) on 27 points: c, D, c ^ D, and the coatoms of
          Pi_27^tau listed from Lemma CK.
"""

import argparse
import itertools
import math
import os
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

# ---------------------------------------------------------------- basics


def popcount(x):
    return bin(x).count("1")


def bits(x):
    out = []
    i = 0
    while x:
        if x & 1:
            out.append(i)
        x >>= 1
        i += 1
    return out


def rad(k):
    r, p = 1, 2
    while p * p <= k:
        if k % p == 0:
            r *= p
            while k % p == 0:
                k //= p
        p += 1
    if k > 1:
        r *= k
    return r


def squarefree(k):
    return rad(k) == k


class Pairs:
    """Pair indexing for [n]."""

    def __init__(self, n):
        self.n = n
        self.idx = [[-1] * n for _ in range(n)]
        self.pairs = []
        for i in range(n):
            for j in range(i + 1, n):
                self.idx[i][j] = self.idx[j][i] = len(self.pairs)
                self.pairs.append((i, j))
        self.full = (1 << len(self.pairs)) - 1

    def mask_of_blocks(self, blocks):
        m = 0
        for B in blocks:
            el = sorted(B)
            for a in range(len(el)):
                for b in range(a + 1, len(el)):
                    m |= 1 << self.idx[el[a]][el[b]]
        return m

    def labels(self, mask):
        """Block label of each point (union-find on the pairs of mask)."""
        n = self.n
        par = list(range(n))

        def f(a):
            while par[a] != a:
                par[a] = par[par[a]]
                a = par[a]
            return a

        for k in bits(mask):
            i, j = self.pairs[k]
            a, b = f(i), f(j)
            if a != b:
                par[a] = b
        return [f(i) for i in range(n)]

    def blocks(self, mask):
        lab = self.labels(mask)
        d = {}
        for i, l in enumerate(lab):
            d.setdefault(l, []).append(i)
        return sorted(d.values())

    def join(self, *masks):
        """Partition join (transitive closure of the union)."""
        u = 0
        for m in masks:
            u |= m
        return self.mask_of_blocks(self.blocks(u))

    def perm_tables(self, t):
        """Byte tables that map a pair mask through the permutation t."""
        img = [1 << self.idx[t[i]][t[j]] for (i, j) in self.pairs]
        tabs = []
        for c in range(0, len(img), 8):
            chunk = img[c:c + 8]
            tab = [0] * 256
            for byte in range(256):
                v = 0
                for b in range(len(chunk)):
                    if byte >> b & 1:
                        v |= chunk[b]
                tab[byte] = v
            tabs.append(tab)
        return tabs

    @staticmethod
    def apply(tabs, m):
        v = 0
        s = 0
        for tab in tabs:
            v |= tab[(m >> s) & 255]
            s += 8
        return v


def set_partitions_blocks(n):
    res = []

    def rec(i, blocks):
        if i == n:
            res.append([list(B) for B in blocks])
            return
        for B in blocks:
            B.append(i)
            rec(i + 1, blocks)
            B.pop()
        blocks.append([i])
        rec(i + 1, blocks)
        blocks.pop()

    rec(0, [])
    return res


# ---------------------------------------------------------------- posets


def up_of(n, down):
    up = [0] * n
    for j in range(n):
        for i in bits(down[j]):
            up[i] |= 1 << j
    return up


def canon(n, down):
    """Canonical code of a poset: minimal relation bitmask over all labelings
    compatible with an isomorphism-invariant colour refinement."""
    up = up_of(n, down)
    col = [(popcount(down[i]), popcount(up[i])) for i in range(n)]
    ncls = len(set(col))
    while True:
        raw = [(col[i], tuple(sorted(col[k] for k in bits(down[i]))),
                tuple(sorted(col[k] for k in bits(up[i])))) for i in range(n)]
        keys = sorted(set(raw))
        # integer colours from the sorted invariant keys are invariant too
        col = [keys.index(r) for r in raw]
        if len(keys) == ncls:
            break
        ncls = len(keys)
    keys = sorted(set(col))
    classes = [[i for i in range(n) if col[i] == k] for k in keys]
    rels = [(i, j) for j in range(n) for i in bits(down[j])]
    best = None
    for combo in itertools.product(*[itertools.permutations(c) for c in classes]):
        pos = [0] * n
        k = 0
        for part in combo:
            for v in part:
                pos[v] = k
                k += 1
        code = 0
        for (i, j) in rels:
            code |= 1 << (pos[i] * n + pos[j])
        if best is None or code < best:
            best = code
    return best


def decode(n, code):
    down = [0] * n
    for b in bits(code):
        i, j = divmod(b, n)
        down[j] |= 1 << i
    return down


def posets_upto_iso(nmax):
    """reps[n] = list of down-arrays, one per isomorphism class."""
    reps = {0: [[]], 1: [[0]]}
    for n in range(2, nmax + 1):
        seen = {}
        for down in reps[n - 1]:
            m = n - 1
            for I in range(1 << m):
                # I must be a down-set (order ideal) of the old poset
                ok = True
                for j in bits(I):
                    if down[j] & ~I:
                        ok = False
                        break
                if not ok:
                    continue
                nd = list(down) + [I]
                code = canon(n, nd)
                if code not in seen:
                    seen[code] = decode(n, code)
        reps[n] = [seen[c] for c in sorted(seen)]
    return reps


def morphisms(n, down, anti):
    """All automorphisms (anti=False) or anti-automorphisms (anti=True),
    as tuples t with t[i] = tau(i)."""
    rel = [[(down[j] >> i) & 1 for j in range(n)] for i in range(n)]
    up = up_of(n, down)
    deg = [(popcount(down[i]), popcount(up[i])) for i in range(n)]
    want = [(d[1], d[0]) if anti else d for d in deg]
    res = []
    perm = [-1] * n

    def bt(i, used):
        if i == n:
            res.append(tuple(perm))
            return
        for v in range(n):
            if used >> v & 1 or deg[v] != want[i]:
                continue
            ok = True
            for j in range(i):
                pj = perm[j]
                if anti:
                    if rel[j][i] != rel[v][pj] or rel[i][j] != rel[pj][v]:
                        ok = False
                        break
                else:
                    if rel[j][i] != rel[pj][v] or rel[i][j] != rel[v][pj]:
                        ok = False
                        break
            if ok:
                perm[i] = v
                bt(i + 1, used | 1 << v)
        perm[i] = -1

    bt(0, 0)
    return res


def compose(a, b):
    return tuple(a[x] for x in b)


def inverse(a):
    inv = [0] * len(a)
    for i, x in enumerate(a):
        inv[x] = i
    return tuple(inv)


def generators(group):
    """A generating set of the finite permutation group `group` (a list)."""
    n = len(group[0])
    ident = tuple(range(n))
    gens = []
    closure = {ident}
    for a in group:
        if a in closure:
            continue
        gens.append(a)
        closure = {ident}
        frontier = [ident]
        while frontier:
            nxt = []
            for x in frontier:
                for g in gens:
                    y = compose(g, x)
                    if y not in closure:
                        closure.add(y)
                        nxt.append(y)
            frontier = nxt
    assert len(closure) == len(group)
    return gens


def conj_reps(elems, gens):
    """Orbit representatives of conjugation by <gens> on elems."""
    rest = set(elems)
    reps = []
    ginv = [inverse(g) for g in gens]
    while rest:
        t = min(rest)
        orbit = {t}
        frontier = [t]
        while frontier:
            nxt = []
            for x in frontier:
                for g, gi in zip(gens, ginv):
                    y = compose(compose(g, x), gi)
                    if y not in orbit:
                        orbit.add(y)
                        nxt.append(y)
            frontier = nxt
        rest -= orbit
        reps.append(t)
    return reps


def cycles(t):
    n = len(t)
    seen = [False] * n
    out = []
    for i in range(n):
        if not seen[i]:
            c = []
            j = i
            while not seen[j]:
                seen[j] = True
                c.append(j)
                j = t[j]
            out.append(c)
    return out


def power(t, k):
    res = list(range(len(t)))
    for _ in range(k):
        res = [t[x] for x in res]
    return tuple(res)


# ---------------------------------------------------------------- linear algebra


def nullspace(rows, n):
    """Basis of {x in Q^n : row . x = 0 for every row} (exact)."""
    A = [[Fraction(v) for v in r] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, len(A)):
            if A[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [v / pv for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        x = [Fraction(0)] * n
        x[f] = Fraction(1)
        for i, c in enumerate(piv):
            x[c] = -A[i][f]
        basis.append(x)
    return basis


def cl_fix(eps, t):
    """cl(Fix g) for g = eps*t on R^n_0, by exact linear algebra:
    i ~ j iff every vector of a basis of Fix g agrees at i and j."""
    n = len(t)
    rows = []
    for i in range(n):
        r = [0] * n
        r[t[i]] += 1
        r[i] -= eps
        rows.append(r)
    rows.append([1] * n)
    B = nullspace(rows, n)
    lab = {}
    blocks = {}
    for i in range(n):
        key = tuple(b[i] for b in B)
        blocks.setdefault(key, []).append(i)
    return list(blocks.values())


def c_explicit(eps, t):
    """The explicit form of c in S4 / S6 of [CVA]."""
    cyc = cycles(t)
    if eps == 1:
        return [list(c) for c in cyc]
    blocks = []
    odd = [i for c in cyc if len(c) % 2 for i in c]
    if odd:
        blocks.append(odd)
    for c in cyc:
        if len(c) % 2 == 0:
            blocks.append(c[0::2])
            blocks.append(c[1::2])
    return blocks


# ---------------------------------------------------------------- the pair


def components(n, down):
    par = list(range(n))

    def f(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    for j in range(n):
        for i in bits(down[j]):
            a, b = f(i), f(j)
            if a != b:
                par[a] = b
    d = {}
    for i in range(n):
        d.setdefault(f(i), []).append(i)
    return sorted(d.values())


def comp_data(n, down, t, rr=None):
    """kappa, lambda_K, r and D.  rr overrides r (for a broken control)."""
    kap = components(n, down)
    cid = [0] * n
    for k, K in enumerate(kap):
        for i in K:
            cid[i] = k
    img = [cid[t[K[0]]] for K in kap]  # tau maps component k to img[k]
    lam = []
    for k in range(len(kap)):
        j, L = img[k], 1
        while j != k:
            j, L = img[j], L + 1
        lam.append(L)
    r = rad(math.gcd(*lam)) if rr is None else rr
    # D-block of K: union of tau^{ar} K
    Dblocks = []
    done = set()
    for k in range(len(kap)):
        if k in done:
            continue
        orb = []
        j = k
        while True:
            orb.append(j)
            done.add(j)
            for _ in range(r):
                j = img[j]
            if j == k:
                break
        Dblocks.append(sorted(i for j in orb for i in kap[j]))
    return kap, lam, r, Dblocks, cid, img


def acyclic(lab, rels):
    """Is the quotient digraph of the labelling acyclic?"""
    succ = {}
    indeg = {}
    for l in set(lab):
        succ[l] = set()
        indeg[l] = 0
    for (i, j) in rels:
        a, b = lab[i], lab[j]
        if a != b and b not in succ[a]:
            succ[a].add(b)
            indeg[b] += 1
    stack = [l for l in indeg if indeg[l] == 0]
    seen = 0
    while stack:
        a = stack.pop()
        seen += 1
        for b in succ[a]:
            indeg[b] -= 1
            if indeg[b] == 0:
                stack.append(b)
    return seen == len(indeg)


class Lattice:
    """A finite set of pair masks M (with 0 and full) ordered by inclusion."""

    def __init__(self, PI, masks):
        self.PI = PI
        self.M = sorted(masks, key=popcount)
        self.Mset = set(self.M)
        self.full = PI.full
        assert self.M[0] == 0 and self.M[-1] == self.full

    def mu(self):
        M = self.M
        mu = [0] * len(M)
        mu[0] = 1
        for k in range(1, len(M)):
            m = M[k]
            s = 0
            for j in range(k):
                mj = M[j]
                if mj & m == mj:
                    s += mu[j]
            mu[k] = -s
        return mu[-1]

    def coatoms(self):
        if len(self.M) == 2:
            return [0]
        out = []
        for m in reversed(self.M[1:-1]):
            if not any(m & c == m for c in out):
                out.append(m)
        return out

    def atoms(self):
        if len(self.M) == 2:
            return [self.full]
        out = []
        for m in self.M[1:-1]:
            if not any(a & m == a for a in out):
                out.append(m)
        return out

    def low(self, coat):
        q = self.full
        for c in coat:
            q &= c
        return any(m != 0 and m & q == m for m in self.M)

    def high(self, at):
        u = self.PI.join(*at)
        return any(m != self.full and m & u == u for m in self.M)

    def meet_is_zero(self, a, b):
        q = a & b
        if q == 0:
            return True
        if q in self.Mset:
            return False
        return not any(m != 0 and m & q == m for m in self.M)

    def join_is_one(self, a, b):
        u = self.PI.join(a, b)
        if u == self.full:
            return True
        if u in self.Mset:
            return False
        return not any(m != self.full and m & u == u for m in self.M)

    def complemented(self, z):
        for y in self.M:
            if self.meet_is_zero(z, y) and self.join_is_one(z, y):
                return True
        return False


CHECKS = ["CC", "crit", "c_lin", "c_in_M", "D_in_M", "cD_in_M", "CD", "CK",
          "A_bound", "A_proper", "A_low", "Zcov", "Zfalse", "Bmem", "Batoms",
          "Bjoin", "Bhigh", "Bprime", "U_cD", "U_OQ", "X_plus", "X_minus",
          "between"]
NEGS = ["neg_kappa", "neg_Q", "neg_r1", "neg_lowonly"]


def criterion_zero(n, down, eps, t, kap, lam, O, Q):
    """The cited zero criteria; returns (zero?, row)."""
    cyc = cycles(t)
    Lam = sorted(set(len(c) for c in cyc))
    o = math.lcm(*Lam)
    if eps == 1:
        free = all(L == o for L in lam)
        if not free:
            return True, "W+1"
        if not squarefree(o):
            return True, "W+2"
        return False, "+nz"
    odds = [L for L in Lam if L % 2]
    m = odds[0] if odds else Lam[0] // 2
    ta1 = (m % 2 == 1 and squarefree(m) and all(L in (m, 2 * m) for L in Lam))
    if not ta1:
        return True, "W-1"
    if not all(L in (m, 2 * m) for L in lam):
        return True, "W-2"
    tm = power(t, m)
    Oset = set(O)
    for K in kap:
        b = set(K) | set(tm[i] for i in K)
        if len(b & Oset) > 1:
            return True, "W-3"
    if O and Q:
        nonisolated = [i for i in O
                       if down[i] or any(down[j] >> i & 1 for j in range(n))]
        if not nonisolated:
            return True, "W-4"
    return False, "-nz"


def analyse_pair(n, down, eps, t, OPlist, PI, want_neg=True):
    rels = [(i, j) for j in range(n) for i in bits(down[j])]
    tabs = PI.perm_tables(t)
    Mm = [m for m in OPlist if Pairs.apply(tabs, m) == m]
    L = Lattice(PI, Mm)
    mu = L.mu()
    coat = L.coatoms()
    at = L.atoms()
    low = L.low(coat)
    high = L.high(at)
    zero = (mu == 0)
    fails = {}

    def fail(name):
        fails[name] = fails.get(name, 0) + 1

    if zero != (low or high):
        fail("CC")
    kap, lam, r, Dbl, cid, img = comp_data(n, down, t)
    O = [i for c in cycles(t) if len(c) % 2 for i in c] if eps == -1 else []
    Q = [i for i in range(n) if i not in set(O)] if eps == -1 else []
    czero, row = criterion_zero(n, down, eps, t, kap, lam, O, Q)
    if czero != zero:
        fail("crit")
    cbl = cl_fix(eps, t)
    cm = PI.mask_of_blocks(cbl)
    if cm != PI.mask_of_blocks(c_explicit(eps, t)):
        fail("c_lin")
    km = PI.mask_of_blocks(kap)
    Dm = PI.mask_of_blocks(Dbl)
    cD = cm & Dm
    if cm not in L.Mset:
        fail("c_in_M")
    if Dm not in L.Mset:
        fail("D_in_M")
    if cD not in L.Mset:
        fail("cD_in_M")
    proper = len(L.M) > 2
    if proper:
        for x in coat:
            if not (x & km == km or x & cm == cm):
                fail("CD")
            if x & km == km and x & Dm != Dm:
                fail("CK")
            if cD & x != cD:
                fail("A_bound")
    W4 = (row == "W-4")
    if cD != 0:
        if not proper:
            fail("A_proper")
        if not low:
            fail("A_low")
        if not zero:
            fail("Zfalse")       # c^D != 0 on a nonzero pair
        if W4:
            fail("Bprime")
        if L.complemented(cD):
            fail("U_cD")
    else:
        if zero and not W4:
            fail("Zcov")         # a zero outside W-4 not covered by c^D
    if zero and not (cD != 0 or W4):
        fail("between")
    if W4:
        a = PI.mask_of_blocks([Q] + [[i] for i in O])
        b = PI.mask_of_blocks([O] + [[i] for i in Q])
        oq = PI.mask_of_blocks([O, Q])
        if not (a in L.Mset and b in L.Mset and oq in L.Mset):
            fail("Bmem")
        for x in at:
            if not (x & a == x or x & b == x):
                fail("Batoms")
            if x & oq != x:
                fail("Bjoin")
        if not high:
            fail("Bhigh")
        if L.complemented(oq):
            fail("U_OQ")
    if eps == 1:
        longer = any(len(c) > r for c in cycles(t))
        if longer != zero or (cD != 0) != zero:
            fail("X_plus")
    else:
        if row in ("W-1", "W-2", "W-3"):
            ta13fail = True
        else:
            ta13fail = False
        if (cD != 0) != ta13fail:
            fail("X_minus")
    neg = {}
    if want_neg:
        # NEG1: kappa in place of D
        if zero and not W4 and (cm & km) == 0:
            neg["neg_kappa"] = 1
        # NEG2: Q|singletons in place of O|Q as an upper bound of the atoms
        if W4:
            a = PI.mask_of_blocks([Q] + [[i] for i in O])
            if any(x & a != x for x in at):
                neg["neg_Q"] = 1
        # NEG3: D with r = 1 (the tau-orbit partition of components) in CK
        if proper:
            D1 = PI.mask_of_blocks(comp_data(n, down, t, rr=1)[3])
            if any(x & km == km and x & D1 != D1 for x in coat):
                neg["neg_r1"] = 1
        # NEG4: the CC test without HIGH
        if zero != low:
            neg["neg_lowonly"] = 1
    return dict(zero=zero, mu=mu, low=low, high=high, row=row, cD=(cD != 0),
                W4=W4, fails=fails, neg=neg, size=len(L.M))


def pairs_of_poset(n, down):
    auts = morphisms(n, down, False)
    antis = morphisms(n, down, True)
    gens = generators(auts) if len(auts) > 1 else []
    out = []
    for t in (conj_reps(auts, gens) if gens else sorted(auts)):
        out.append((1, t))
    for t in (conj_reps(antis, gens) if gens else sorted(antis)):
        out.append((-1, t))
    return out


_PART_CACHE = {}


def all_partition_data(n):
    if n not in _PART_CACHE:
        PI = Pairs(n)
        parts = set_partitions_blocks(n)
        data = []
        for bl in parts:
            lab = [0] * n
            for k, B in enumerate(bl):
                for i in B:
                    lab[i] = k
            data.append((PI.mask_of_blocks(bl), lab))
        _PART_CACHE[n] = (PI, data)
    return _PART_CACHE[n]


def work_poset(arg):
    n, down = arg
    PI, data = all_partition_data(n)
    rels = [(i, j) for j in range(n) for i in bits(down[j])]
    OPlist = [m for (m, lab) in data if acyclic(lab, rels)]
    res = []
    for eps, t in pairs_of_poset(n, down):
        rec = analyse_pair(n, down, eps, t, OPlist, PI)
        if rec["fails"]:
            rec["witness"] = (down, eps, t)
        res.append(rec)
    return res


# ---------------------------------------------------------------- controls


def abstract_cc(elems, leq):
    """For an abstract finite bounded poset: (is lattice, mu, LOW, HIGH)."""
    N = len(elems)
    lo = [i for i in range(N) if all(leq(i, j) for j in range(N))]
    hi = [i for i in range(N) if all(leq(j, i) for j in range(N))]
    z, o = lo[0], hi[0]

    def lub(a, b):
        ub = [k for k in range(N) if leq(a, k) and leq(b, k)]
        m = [k for k in ub if all(leq(k, j) for j in ub)]
        return m[0] if m else None

    def glb(a, b):
        lb = [k for k in range(N) if leq(k, a) and leq(k, b)]
        m = [k for k in lb if all(leq(j, k) for j in lb)]
        return m[0] if m else None

    lattice = all(lub(a, b) is not None for a in range(N) for b in range(N))
    if not lattice:
        return False, None, None, None, None
    order = sorted(range(N), key=lambda k: sum(leq(j, k) for j in range(N)))
    mu = {}
    for k in order:
        mu[k] = 1 if k == z else -sum(mu[j] for j in order if j != k and leq(j, k) and j in mu)
    coat = [k for k in range(N) if k != o and all(j in (k, o) for j in range(N) if leq(k, j))]
    at = [k for k in range(N) if k != z and all(j in (k, z) for j in range(N) if leq(j, k))]
    m = coat[0]
    for c in coat[1:]:
        m = glb(m, c)
    jn = at[0]
    for a in at[1:]:
        jn = lub(jn, a)
    comp = all(any(glb(x, y) == z and lub(x, y) == o for y in range(N)) for x in range(N))
    return True, mu[o], m != z, jn != o, comp


def find_complemented_mu0(reps, kmax=6):
    """Smallest bounded lattice (0, 1 adjoined to a poset on k points) with
    mu = 0 and neither LOW nor HIGH."""
    for k in range(1, kmax + 1):
        for down in reps[k]:
            N = k + 2
            Z, ONE = k, k + 1

            def leq(a, b, down=down, k=k):
                if a == b or a == k or b == k + 1:
                    return True
                if a == k + 1 or b == k:
                    return False
                return bool(down[b] >> a & 1)

            lat, mu, low, high, comp = abstract_cc(list(range(N)), leq)
            if lat and mu == 0 and not low and not high:
                return k, down, comp
    return None


def controls(reps, log):
    ok = True
    counts = [len(reps[n]) for n in range(0, max(reps) + 1)]
    want = [1, 1, 2, 5, 16, 63, 318, 2045, 16999, 183231][:len(counts)]
    log(f"[CTL] poset counts {counts} (OEIS A000112 {want}): {'ok' if counts == want else 'FAIL'}")
    ok &= counts == want
    for n in range(1, 7):
        PI, data = all_partition_data(n)
        L = Lattice(PI, [m for m, _ in data])
        good = L.mu() == (-1) ** (n - 1) * math.factorial(n - 1)
        ok &= good
    log(f"[CTL] mu(Pi_n) = (-1)^(n-1)(n-1)! for n <= 6: {'ok' if ok else 'FAIL'}")
    # Pi_4: LOW and HIGH both false, mu = -6 (CC false, consistent)
    PI, data = all_partition_data(4)
    L = Lattice(PI, [m for m, _ in data])
    r = (L.mu(), L.low(L.coatoms()), L.high(L.atoms()))
    log(f"[CTL] Pi_4: mu, LOW, HIGH = {r} (want (-6, False, False))")
    ok &= r == (-6, False, False)
    tabs = PI.perm_tables((1, 2, 3, 0))
    L = Lattice(PI, [m for m, _ in data if Pairs.apply(tabs, m) == m])
    r = (len(L.M), L.mu(), L.low(L.coatoms()), L.high(L.atoms()))
    log(f"[CTL] Pi_4^(0123): |M|, mu, LOW, HIGH = {r} (want (3, 0, True, True))")
    ok &= r == (3, 0, True, True)
    PI3, data3 = all_partition_data(3)
    tabs = PI3.perm_tables((1, 2, 0))
    L = Lattice(PI3, [m for m, _ in data3 if Pairs.apply(tabs, m) == m])
    r = (len(L.M), L.mu(), L.low(L.coatoms()), L.high(L.atoms()))
    log(f"[CTL] Pi_3^(012): |M|, mu, LOW, HIGH = {r} (want (2, -1, False, False))")
    ok &= r == (2, -1, False, False)
    found = find_complemented_mu0(reps)
    if found is None:
        log("[CTL] no bounded lattice with mu = 0 and neither LOW nor HIGH found: FAIL")
        ok = False
    else:
        k, down, comp = found
        rels = [(i, j) for j in range(k) for i in bits(down[j])]
        log(f"[CTL] CC test must fail: bounded lattice on {k}+2 elements, interior relations {rels}: "
            f"mu = 0, LOW = HIGH = False, complemented = {comp} -> CC mismatch detected")
    # broken lattice routine: drop the HIGH half on a known W-4 pair (n = 5)
    return ok


# ---------------------------------------------------------------- [BIG]


def big_case(log):
    """tau = (9)(18) on 27 points; P = the antichain (and the generic
    argument for every poset, printed)."""
    n = 27
    t = list(range(n))
    A = list(range(9))
    B = list(range(9, 27))
    for k in range(9):
        t[A[k]] = A[(k + 1) % 9]
    for k in range(18):
        t[B[k]] = B[(k + 1) % 18]
    t = tuple(t)
    down = [0] * n
    PI = Pairs(n)
    kap, lam, r, Dbl, cid, img = comp_data(n, down, t)
    cbl = cl_fix(-1, t)
    ok = PI.mask_of_blocks(cbl) == PI.mask_of_blocks(c_explicit(-1, t))
    cm = PI.mask_of_blocks(cbl)
    Dm = PI.mask_of_blocks(Dbl)
    cD = cm & Dm
    six = PI.mask_of_blocks(cycles(power(t, 6)))
    three = PI.mask_of_blocks(cycles(power(t, 3)))
    log(f"[BIG] tau = (9)(18), antichain: gcd lambda = {math.gcd(*lam)}, r = {r}, "
        f"c (lin. alg.) = explicit: {ok}; blocks of c: {sorted(len(b) for b in cbl)}; "
        f"blocks of D: {sorted(len(b) for b in Dbl)}")
    log(f"[BIG]   c ^ D != 0: {cD != 0}; c ^ D = cyc(tau^6): {cD == six}; D = cyc(tau^3): {Dm == three}")
    # Coatoms of Pi_27^tau (kappa = 0, so every coatom is >= kappa): by
    # Lemma CK, either two tau-stable blocks, or p cyclic blocks, p prime,
    # p | every lambda.  Build them and check they are tau-stable, proper,
    # and that their meet is >= c ^ D.
    coat = []
    coat.append(PI.mask_of_blocks([A, B]))
    for p in (3,):
        for s in range(p):
            blocks = []
            for j in range(p):
                blk = [A[k] for k in range(9) if k % p == j] + \
                      [B[k] for k in range(18) if k % p == (j + s) % p]
                blocks.append(blk)
            coat.append(PI.mask_of_blocks(blocks))
    tabs = PI.perm_tables(t)
    stable = all(Pairs.apply(tabs, x) == x for x in coat)
    meet = PI.full
    for x in coat:
        meet &= x
    log(f"[BIG]   coatoms from Lemma CK: {len(coat)}, all tau-stable: {stable}; "
        f"meet = cyc(tau^3) = D: {meet == three}; meet >= c ^ D: {meet & cD == cD}")
    return ok and cD != 0 and cD == six and stable and (meet & cD == cD)


# ---------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("POGO_WORKER_CORES", "1")))
    ap.add_argument("--budget", type=float, default=0, help="seconds; 0 = none")
    ap.add_argument("--skip-big", action="store_true")
    args = ap.parse_args()
    t0 = time.time()

    def log(s):
        print(s, flush=True)

    reps = posets_upto_iso(max(args.nmax, 6))
    log(f"poset enumeration done in {time.time() - t0:.1f} s")
    allok = controls(reps, log)
    if not args.skip_big:
        allok &= big_case(log)
    tot_f = {k: 0 for k in CHECKS}
    tot_n = {k: 0 for k in NEGS}
    side = {}  # row -> [LOW only, HIGH only, both], all n
    unrun = False
    log("")
    log("| n | posets | pairs | zeros | LOW only / HIGH only / both | c^D != 0 (of them W-4) | "
        "zeros W+1 / W+2 / W-1 / W-2 / W-3 / W-4 | failures | NEG kappa / Q / r=1 / LOW-only |")
    log("|---|---|---|---|---|---|---|---|---|")
    pool = Pool(args.jobs) if args.jobs > 1 else None
    for n in range(3, args.nmax + 1):
        tn = time.time()
        st = dict(pairs=0, zeros=0, lo=0, hi=0, both=0, cd=0, cd4=0)
        rows = {k: 0 for k in ["W+1", "W+2", "W-1", "W-2", "W-3", "W-4"]}
        fails = {k: 0 for k in CHECKS}
        negs = {k: 0 for k in NEGS}
        witnesses = []
        tasks = [(n, d) for d in reps[n]]
        it = pool.imap_unordered(work_poset, tasks, chunksize=4) if pool else map(work_poset, tasks)
        done = 0
        for res in it:
            done += 1
            for rec in res:
                st["pairs"] += 1
                if rec["zero"]:
                    st["zeros"] += 1
                    rows[rec["row"]] += 1
                    sd = side.setdefault(rec["row"], [0, 0, 0])
                    sd[0 if not rec["high"] else (1 if not rec["low"] else 2)] += 1
                    if rec["low"] and rec["high"]:
                        st["both"] += 1
                    elif rec["low"]:
                        st["lo"] += 1
                    elif rec["high"]:
                        st["hi"] += 1
                if rec["cD"]:
                    st["cd"] += 1
                    if rec["W4"]:
                        st["cd4"] += 1
                for k, v in rec["fails"].items():
                    fails[k] += v
                for k, v in rec["neg"].items():
                    negs[k] += v
                if rec["fails"] and len(witnesses) < 5:
                    witnesses.append((rec["witness"], rec["fails"]))
            if args.budget and time.time() - t0 > args.budget:
                break
        if done < len(tasks):
            unrun = True
            log(f"UNRUN: n = {n}, {len(tasks) - done} of {len(tasks)} posets not reached")
            if pool:
                pool.terminate()
            break
        nf = sum(fails.values())
        log(f"| {n} | {len(reps[n])} | {st['pairs']} | {st['zeros']} | {st['lo']} / {st['hi']} / {st['both']} | "
            f"{st['cd']} ({st['cd4']}) | " + " / ".join(str(rows[k]) for k in rows) +
            f" | {nf} | " + " / ".join(str(negs[k]) for k in NEGS) + f" |   ({time.time() - tn:.0f} s)")
        if nf:
            log(f"   failures by check: { {k: v for k, v in fails.items() if v} }")
            for w in witnesses:
                log(f"   witness: {w}")
        for k in CHECKS:
            tot_f[k] += fails[k]
        for k in NEGS:
            tot_n[k] += negs[k]
    if pool:
        pool.close()
    log("")
    log("zeros by row, all n: LOW only / HIGH only / both: " +
        "; ".join(f"{k}: {v[0]} / {v[1]} / {v[2]}" for k, v in sorted(side.items())))
    log(f"failures by check (all n): {tot_f}")
    log(f"[NEG] broken witnesses, number of pairs where they fail (each must be > 0): {tot_n}")
    negok = all(v > 0 for v in tot_n.values())
    if not negok:
        log("[NEG] some broken witness never failed: the instrument is not shown to fire")
    allok &= (sum(tot_f.values()) == 0) and negok and not unrun
    log(f"total time {time.time() - t0:.0f} s")
    if allok:
        log("ALL CHECKS PASSED")
        sys.exit(0)
    log("SOME CHECK FAILED OR UNRUN")
    sys.exit(1)


if __name__ == "__main__":
    main()
