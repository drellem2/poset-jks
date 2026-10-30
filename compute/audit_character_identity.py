#!/usr/bin/env python3
"""Independent audit of the two proofs of eq. (characterconj).

Audits notes/global_module_operations_plethlog.md section 2 (mg-266cf) and
notes/fixed_point_mobius_identity.md (mg-8878d). Findings:
notes/audit_character_identity_proof.md.

This file is self-contained. It imports nothing from the other scripts in
compute/. Everything is brute force from the definitions:

  * OP(P): all set partitions of [n] whose quotient relation is acyclic.
  * L^g: the g-invariant members, ordered by refinement. Joins in L^g are
    least upper bounds computed inside L^g (never the partition join).
  * mu: computed by the defining recursion on the poset in question.
  * fixed cyclic classes: enumerate Lin(P), group into rotation classes,
    and test g w = w gamma^r directly.
  * homology (--homology): ranks of all boundary maps of the order complex
    of the proper part of OP(P) mod a prime, and the trace of g on the
    kernel of the top boundary map.

Checks, per (P, g) with g != 1 (and g = 1 where noted):
  A  (characterconj): (-1)^{n-3} mu(L^g) == sgn(g) * sum_{gC=C} zeta^{r}
     (compared as exact integers; the Lie side is evaluated as a sum of
     Ramanujan sums from the counts N_r, after checking N_r depends only
     on gcd(n, r)).
  B  closed formula: sgn(g)(-1)^{n-3} mu(L^g) == mu(o) sum_{x in F} e_C(B0(x)).
  C  mg-266cf Lemma 2.2: O_g in L^g; L^g-join(x, O_g) == partition join;
     {x : x v O_g = 1} == X(P, g).
  D  mg-266cf Prop 2.5 inversion: mu_X(x, 1) computed on the poset X(P,g)
     equals mu(o) on F, and f(1) == sum_x mu_X(x,1) F(x) with f, F as in
     the note (f evaluated by direct mu on the restricted lattice).
  E  mg-8878d Crapo: for z merging a longest orbit, the complements z^perp
     (computed in L^g); Crapo's sum equals mu(L^g); z^perp empty iff cycle
     lengths unequal; otherwise z^perp == {y_T} and is an antichain.
  F  N_r (fixed classes with rotation r) == sum_T e_C(T) if gcd(n,r) = k,
     else 0 (mg-8878d Prop 6).

Run from compute/:
    python3 audit_character_identity.py                 # n <= 6 all posets + n = 7..9 families
    python3 audit_character_identity.py --homology 5    # also direct homology traces, n <= 5
Exit status 0 iff every check passes.

Positive controls: each of
    python3 audit_character_identity.py --nmax 5 --large --homology 5 --control C
for C in no_mu_o no_sgn trace_sign no_mu_X crapo_drop lin_not_ec
runs a deliberately wrong variant and must exit 1.
"""

import argparse
import itertools
import math
import sys
from fractions import Fraction

PRIME = 2147483647
CONTROL = None   # set by --control to a deliberately wrong variant


# ---------------------------------------------------------------- posets

def closure(n, rel):
    """Strict order matrix from a set of covering pairs (i, j) meaning i < j."""
    lt = [[False] * n for _ in range(n)]
    for i, j in rel:
        lt[i][j] = True
    for k in range(n):
        for i in range(n):
            if lt[i][k]:
                for j in range(n):
                    if lt[k][j]:
                        lt[i][j] = True
    for i in range(n):
        assert not lt[i][i], "relation has a cycle"
    return tuple(tuple(r) for r in lt)


def disjoint_union(*parts):
    """parts: list of (size, covering pairs). Returns (n, lt)."""
    n = 0
    rel = []
    for size, cov in parts:
        rel += [(n + a, n + b) for a, b in cov]
        n += size
    return n, closure(n, rel)


def chain(m):
    return (m, [(i, i + 1) for i in range(m - 1)])


def automorphisms(n, lt):
    out = []
    for p in itertools.permutations(range(n)):
        if all(lt[p[i]][p[j]] == lt[i][j] for i in range(n) for j in range(n)):
            out.append(p)
    return out


def components(n, lt, verts=None):
    verts = list(range(n)) if verts is None else list(verts)
    vs = set(verts)
    seen, comps = set(), []
    for v in verts:
        if v in seen:
            continue
        stack, comp = [v], []
        seen.add(v)
        while stack:
            a = stack.pop()
            comp.append(a)
            for b in vs:
                if b not in seen and (lt[a][b] or lt[b][a]):
                    seen.add(b)
                    stack.append(b)
        comps.append(frozenset(comp))
    return comps


def canonical(n, lt):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(lt[p[i]][p[j]] for i in range(n) for j in range(n))
        if best is None or key > best:
            best = key
    return best


def all_posets(n):
    """One representative per isomorphism class (natural labelings, deduped)."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    seen = {}
    for mask in range(1 << len(pairs)):
        rel = [pairs[t] for t in range(len(pairs)) if mask >> t & 1]
        lt = [[False] * n for _ in range(n)]
        for i, j in rel:
            lt[i][j] = True
        ok = True
        for i, j in rel:          # keep only transitively closed relations
            for k in range(n):
                if lt[j][k] and not lt[i][k]:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        lt = tuple(tuple(r) for r in lt)
        key = canonical(n, lt)
        if key not in seen:
            seen[key] = lt
    return list(seen.values())


# ---------------------------------------------------------------- partitions

def set_partitions(n):
    """Restricted growth strings."""
    a = [0] * n

    def rec(i, m):
        if i == n:
            yield tuple(a)
            return
        for v in range(m + 1):
            a[i] = v
            yield from rec(i + 1, max(m, v + 1))
    if n == 0:
        yield ()
        return
    yield from rec(1, 1)


def normalize(lab):
    m, out = {}, []
    for v in lab:
        if v not in m:
            m[v] = len(m)
        out.append(m[v])
    return tuple(out)


def pairmask(lab):
    n = len(lab)
    mask, t = 0, 0
    for i in range(n):
        for j in range(i + 1, n):
            if lab[i] == lab[j]:
                mask |= 1 << t
            t += 1
    return mask


def is_op(lt, lab):
    """Quotient relation acyclic."""
    n = len(lab)
    nb = max(lab) + 1
    adj = [set() for _ in range(nb)]
    for i in range(n):
        for j in range(n):
            if lt[i][j] and lab[i] != lab[j]:
                adj[lab[i]].add(lab[j])
    color = [0] * nb

    def dfs(u):
        color[u] = 1
        for v in adj[u]:
            if color[v] == 1:
                return False
            if color[v] == 0 and not dfs(v):
                return False
        color[u] = 2
        return True
    return all(color[u] or dfs(u) for u in range(nb))


def g_fixed(lab, g):
    m = {}
    for i in range(len(lab)):
        a, b = lab[i], lab[g[i]]
        if m.setdefault(a, b) != b:
            return False
    return True


def blocks(lab):
    d = {}
    for i, v in enumerate(lab):
        d.setdefault(v, []).append(i)
    return [frozenset(b) for b in d.values()]


def from_blocks(n, bls):
    lab = [None] * n
    for t, b in enumerate(bls):
        for i in b:
            lab[i] = t
    return normalize(lab)


def partition_join(a, b):
    n = len(a)
    parent = list(range(n))

    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for lab in (a, b):
        first = {}
        for i, v in enumerate(lab):
            if v in first:
                parent[f(i)] = f(first[v])
            else:
                first[v] = i
    return normalize([f(i) for i in range(n)])


# ---------------------------------------------------------------- lattices

class Lat:
    """Finite poset of partitions under refinement, with brute-force mu/joins."""

    def __init__(self, labs):
        self.labs = sorted(set(labs), key=lambda l: -(max(l) + 1))  # finest first
        self.idx = {l: i for i, l in enumerate(self.labs)}
        self.mask = [pairmask(l) for l in self.labs]
        N = len(self.labs)
        self.up = [[j for j in range(N) if self.mask[i] & ~self.mask[j] == 0] for i in range(N)]

    def le(self, i, j):
        return self.mask[i] & ~self.mask[j] == 0

    def mu_from(self, i):
        """mu(i, y) for all y >= i."""
        mu = {i: 1}
        for j in self.up[i]:            # up[i] is in finest-first order
            if j == i:
                continue
            mu[j] = -sum(mu[k] for k in mu if self.le(k, j) and k != j)
        return mu

    def mu(self, i, j):
        return self.mu_from(i).get(j, 0)

    def join(self, i, j):
        ub = [k for k in range(len(self.labs)) if self.le(i, k) and self.le(j, k)]
        mins = [k for k in ub if all(not self.le(m, k) or m == k for m in ub)]
        assert len(mins) == 1, "not a lattice"
        return mins[0]

    def meet(self, i, j):
        lb = [k for k in range(len(self.labs)) if self.le(k, i) and self.le(k, j)]
        maxs = [k for k in lb if all(not self.le(k, m) or m == k for m in lb)]
        assert len(maxs) == 1, "not a lattice"
        return maxs[0]


def op_labs(n, lt, g=None):
    out = []
    for lab in set_partitions(n):
        if g is not None and not g_fixed(lab, g):
            continue
        if is_op(lt, lab):
            out.append(lab)
    return out


def mu_bounded(labs):
    L = Lat(labs)
    return L.mu(0, len(L.labs) - 1)


def restrict(lt, verts):
    verts = sorted(verts)
    return len(verts), tuple(tuple(lt[a][b] for b in verts) for a in verts), verts


# ---------------------------------------------------------------- Lie side

def linear_extensions(n, lt):
    preds = [[j for j in range(n) if lt[j][i]] for i in range(n)]
    out, w, used = [], [], [False] * n

    def rec():
        if len(w) == n:
            out.append(tuple(w))
            return
        for v in range(n):
            if not used[v] and all(used[p] for p in preds[v]):
                used[v] = True
                w.append(v)
                rec()
                w.pop()
                used[v] = False
    rec()
    return out


def cyclic_classes(n, lt):
    reps = set()
    for w in linear_extensions(n, lt):
        reps.add(min(w[j:] + w[:j] for j in range(n)))
    return reps


def e_C(n, lt):
    if n == 0:
        return 1
    if CONTROL == "lin_not_ec":
        return len(linear_extensions(n, lt))
    return len(cyclic_classes(n, lt))


def fixed_class_counts(n, lt, g):
    """N[r] = #classes C with gC = C and (gw)_i = w_{i+r}."""
    N = [0] * n
    for w in cyclic_classes(n, lt):
        gw = tuple(g[x] for x in w)
        r = w.index(gw[0])
        if all(gw[i] == w[(i + r) % n] for i in range(n)):
            N[r] += 1
    return N


def divisors(m):
    return [d for d in range(1, m + 1) if m % d == 0]


def mobius(m):
    res, p = 1, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    return -res if m > 1 else res


def lie_trace(n, N):
    """sum_r N[r] zeta_n^r, exact, provided N[r] depends only on gcd(n, r)."""
    by = {}
    for r in range(n):
        by.setdefault(math.gcd(n, r), set()).add(N[r])
    if any(len(s) > 1 for s in by.values()):
        return None
    # sum over r with gcd(n,r)=k of zeta^r = c_{n/k}(1) = mu(n/k)
    return sum(next(iter(s)) * mobius(n // k) for k, s in by.items())


# ---------------------------------------------------------------- group bits

def cycles(g):
    seen, out = set(), []
    for i in range(len(g)):
        if i not in seen:
            c, j = [], i
            while j not in seen:
                seen.add(j)
                c.append(j)
                j = g[j]
            out.append(c)
    return out


def order(g):
    o = 1
    for c in cycles(g):
        o = o * len(c) // math.gcd(o, len(c))
    return o


def sgn(g):
    return (-1) ** (len(g) - len(cycles(g)))


def power(g, e):
    n = len(g)
    out = list(range(n))
    for _ in range(e):
        out = [g[x] for x in out]
    return tuple(out)


# ---------------------------------------------------------------- the checks

def closed_formula(n, lt, g):
    """mu(o) * sum_{x in F(P,g)} e_C(P|B0(x)), F from brute-force enumeration
    of partitions of the component set (independent of either note's proof)."""
    o = order(g)
    comps = components(n, lt)
    idx = {c: t for t, c in enumerate(comps)}
    gc = [idx[frozenset(g[x] for x in c)] for c in comps]
    total = 0
    for clab in set_partitions(len(comps)):
        if max(clab) + 1 != o:
            continue
        if not g_fixed(clab, gc):
            continue
        # g transitive on the o blocks?
        b0 = clab[0]
        reach, cur = {b0}, b0
        for _ in range(o):
            cur = clab[gc[clab.index(cur)]]
            reach.add(cur)
        if len(reach) != o:
            continue
        # h_x = g^o restricted to B0 must be identity (automatic as g^o = 1)
        b_of_0 = clab[next(t for t, c in enumerate(comps) if 0 in c)]
        B0 = set().union(*[comps[t] for t in range(len(comps)) if clab[t] == b_of_0])
        m, sub, _ = restrict(lt, B0)
        total += e_C(m, sub)
    if CONTROL == "no_mu_o":
        return total
    return mobius(o) * total


def check_pair(n, lt, g, stats, fails, name, deep=True):
    o = order(g)
    labs = op_labs(n, lt, g)
    L = Lat(labs)
    bot, top = 0, len(L.labs) - 1
    assert max(L.labs[bot]) + 1 == n and max(L.labs[top]) == 0
    muL = L.mu(bot, top)
    lhs = (-1) ** (n - 3) * muL
    N = fixed_class_counts(n, lt, g)
    lie = lie_trace(n, N)
    tag = f"{name} g={g}"

    def fail(msg):
        fails.append(f"{tag}: {msg}")

    # A: characterconj
    stats["A"] += 1
    if lie is None:
        fail(f"N_r not constant on gcd classes: {N}")
    elif lhs != (1 if CONTROL == "no_sgn" else sgn(g)) * lie:
        fail(f"A: lhs {lhs} != sgn*lie {sgn(g) * lie}")
    # B: closed formula
    stats["B"] += 1
    cf = closed_formula(n, lt, g)
    if sgn(g) * lhs != cf:
        fail(f"B: sgn*lhs {sgn(g) * lhs} != closed {cf}")
    if cf != 0:
        stats["B_nonzero"] += 1
    if o == 1 or not deep:
        return

    # C: Lemma 2.2 of mg-266cf
    stats["C"] += 1
    Og = normalize(orbit_labels(g))
    if Og not in L.idx:
        fail("C: O_g not in L^g")
        return
    io = L.idx[Og]
    Xset = []
    for i, lab in enumerate(L.labs):
        j = L.join(i, io)
        if L.labs[j] != partition_join(lab, Og):
            fail(f"C: L^g join != partition join at {lab}")
        if j == top:
            Xset.append(i)
    Xdirect = []
    comps = components(n, lt)
    for i, lab in enumerate(L.labs):
        bl = blocks(lab)
        if all(len({lab[x] for x in c}) == 1 for c in comps):
            # blocks are unions of components; transitive?
            b0 = next(b for b in bl if 0 in b)
            orb = {frozenset(power(g, e)[x] for x in b0) for e in range(o)}
            if len(orb) == len(bl):
                Xdirect.append(i)
    if sorted(Xset) != sorted(Xdirect):
        fail(f"C: {{x: x v O_g = 1}} != X(P,g)")

    # D: Mobius inversion on X(P,g)
    stats["D"] += 1
    X = Lat([L.labs[i] for i in Xdirect])
    xtop = len(X.labs) - 1
    muX = {}
    for i in range(len(X.labs)):
        muX[i] = X.mu(i, xtop)
    rhs = 0
    for i, lab in enumerate(X.labs):
        m = max(lab) + 1
        B0 = next(b for b in blocks(lab) if 0 in b)
        h = power(g, m)
        hid = all(h[x] == x for x in B0)
        if hid:
            if m != o:
                fail("D: h_x = 1 with m != o")
            if muX[i] != mobius(o):
                fail(f"D: mu_X(x,1) = {muX[i]} != mu(o) = {mobius(o)}")
            k, sub, _ = restrict(lt, B0)
            rhs += (1 if CONTROL == "no_mu_X" else muX[i]) * e_C(k, sub)
        # f(x) via direct mu on the restricted lattice, compared with the
        # interval [0, x] in L^g (Lemma 2.4(i)) and sign identity 2.4(ii)
        k, sub, verts = restrict(lt, B0)
        hloc = tuple(verts.index(h[v]) for v in verts)
        mu_sub = mu_bounded(op_labs(k, sub, hloc))
        mu_int = L.mu(bot, L.idx[lab])
        if mu_sub != mu_int:
            fail(f"D: mu[0,x]_L^g {mu_int} != mu(OP(P|B0)^h) {mu_sub}")
        if (-1) ** (n - 3) * sgn(g) != (-1) ** (k - 3) * sgn(hloc):
            fail("D: sign identity 2.4(ii) fails")
    if sgn(g) * lhs != rhs:
        fail(f"D: inversion gives {rhs}, M~ = {sgn(g) * lhs}")

    # E: Crapo at z = merge one longest orbit (mg-8878d)
    stats["E"] += 1
    cyc = cycles(g)
    D = max(len(c) for c in cyc)
    c = next(c for c in cyc if len(c) == D)
    zlab = normalize([0 if i in c else i + 1 for i in range(n)])
    if zlab not in L.idx:
        fail("E: z not in L^g")
        return
    iz = L.idx[zlab]
    perp = [y for y in range(len(L.labs)) if L.meet(y, iz) == bot and L.join(y, iz) == top]
    mu0 = L.mu_from(bot)
    crapo = 0
    for a in perp:
        for b in perp:
            if L.le(a, b):
                crapo += mu0[a] * L.mu(b, top) * (0 if CONTROL == "crapo_drop" and a == b else 1)
    if crapo != muL:
        fail(f"E: Crapo sum {crapo} != mu {muL}")
    uniform = len({len(cc) for cc in cyc}) == 1
    if not uniform:
        stats["E_unequal"] += 1
        if perp:
            fail("E: unequal lengths but z has a complement")
    else:
        if any(L.le(a, b) and a != b for a in perp for b in perp):
            fail("E: z^perp not an antichain")
        # z^perp == {y_T}
        d, k = D, n // D
        yT = set()
        if k >= 2:
            for clab in set_partitions(len(comps)):
                bls = {}
                for t, cc in enumerate(comps):
                    bls.setdefault(clab[t], set()).update(cc)
                bl = [frozenset(b) for b in bls.values()]
                if len(bl) != d:
                    continue
                T = next(b for b in bl if c[0] in b)
                tr = [frozenset(power(g, e)[x] for x in T) for e in range(d)]
                if len(set(tr)) == d and set(tr) == set(bl):
                    yT.add(from_blocks(n, bl))
            if {L.labs[y] for y in perp} != yT:
                fail("E: z^perp != {y_T}")
            if perp:
                stats["E_nonempty"] += 1
        # F: N_r
        stats["F"] += 1
        sumT = 0
        for y in yT if k >= 2 else [from_blocks(n, [frozenset([x]) for x in range(n)])]:
            T = next(b for b in blocks(y) if c[0] in b)
            m, sub, _ = restrict(lt, T)
            sumT += e_C(m, sub)
        for r in range(n):
            want = sumT if math.gcd(n, r) == k else 0
            if N[r] != want:
                fail(f"F: N_{r} = {N[r]} != {want}")


def orbit_labels(g):
    lab = [None] * len(g)
    for t, c in enumerate(cycles(g)):
        for x in c:
            lab[x] = t
    return lab


# ---------------------------------------------------------------- homology

def rank_mod_p(rows, ncols):
    """rows: list of dict col->val. Gaussian elimination mod PRIME."""
    pivots = {}
    rank = 0
    for row in rows:
        r = {k: v % PRIME for k, v in row.items() if v % PRIME}
        while r:
            c = min(r)
            if c in pivots:
                prow = pivots[c]
                f = r[c]
                for k, v in prow.items():
                    r[k] = (r.get(k, 0) - f * v) % PRIME
                    if r[k] == 0:
                        del r[k]
            else:
                inv = pow(r[c], PRIME - 2, PRIME)
                pivots[c] = {k: v * inv % PRIME for k, v in r.items()}
                rank += 1
                break
    return rank


def kernel_basis(cols, ncols_dim):
    """Kernel of the map whose columns are given (list of dict row->val), mod p.
    Returns list of vectors (dict index->val) spanning the kernel."""
    m = len(cols)
    # Row-reduce the transpose problem: find relations among columns.
    pivots = {}   # row index -> (vector over rows, combination over columns)
    kernel = []
    for j, col in enumerate(cols):
        v = {k: x % PRIME for k, x in col.items() if x % PRIME}
        comb = {j: 1}
        while v:
            rr = min(v)
            if rr in pivots:
                pv, pc = pivots[rr]
                f = v[rr]
                for k, x in pv.items():
                    v[k] = (v.get(k, 0) - f * x) % PRIME
                    if v[k] == 0:
                        del v[k]
                for k, x in pc.items():
                    comb[k] = (comb.get(k, 0) - f * x) % PRIME
                    if comb[k] == 0:
                        del comb[k]
            else:
                inv = pow(v[rr], PRIME - 2, PRIME)
                pivots[rr] = ({k: x * inv % PRIME for k, x in v.items()},
                              {k: x * inv % PRIME for k, x in comb.items()})
                break
        if not v:
            kernel.append(comb)
    return kernel


def homology_check(n, lt, auts, fails, stats, name):
    labs = op_labs(n, lt)
    L = Lat(labs)
    bot, top = 0, len(L.labs) - 1
    proper = [i for i in range(len(L.labs)) if i not in (bot, top)]
    # chains of the proper part, by length
    up = {i: [j for j in proper if j != i and L.le(i, j)] for i in proper}
    chains = {0: [(i,) for i in proper]}
    d = 0
    while chains[d]:
        nxt = []
        for ch in chains[d]:
            for j in up[ch[-1]]:
                nxt.append(ch + (j,))
        d += 1
        chains[d] = nxt
    dims = [len(chains[t]) for t in range(d)]
    index = [{ch: t for t, ch in enumerate(chains[k])} for k in range(d)]
    # boundary d_k: C_k -> C_{k-1}; augmented with C_{-1} = C
    ranks = {}
    for k in range(d):
        cols = []
        for ch in chains[k]:
            if k == 0:
                cols.append({0: 1})
            else:
                cols.append({index[k - 1][ch[:t] + ch[t + 1:]]: (-1) ** t for t in range(k + 1)})
        ranks[k] = rank_mod_p(cols, None)
    betti = {}
    for k in range(-1, d):
        dimk = 1 if k == -1 else dims[k]
        rk_out = 0 if k == -1 else ranks[k]
        rk_in = ranks.get(k + 1, 0)
        betti[k] = dimk - rk_out - rk_in
    eC = e_C(n, lt)
    stats["H"] += 1
    nonzero = {k: b for k, b in betti.items() if b}
    if n >= 3 and nonzero != ({n - 3: eC} if eC else {}):
        fails.append(f"{name}: betti mod p {nonzero}, expected {{{n - 3}: {eC}}}")
        return
    # trace of each automorphism on ker(d_{n-3}) (top homology since d = n-2)
    k = n - 3
    if d != n - 2:
        fails.append(f"{name}: order complex dimension {d - 1} != n-3")
        return
    cols = []
    for ch in chains[k]:
        if k == 0:
            cols.append({0: 1})
        else:
            cols.append({index[k - 1][ch[:t] + ch[t + 1:]]: (-1) ** t for t in range(k + 1)})
    K = kernel_basis(cols, None)
    assert len(K) == eC
    # pivot structure to express vectors in the kernel basis
    for g in auts:
        if all(g[i] == i for i in range(n)):
            continue
        perm_idx = {}
        for ch in chains[k]:
            img = tuple(L.idx[act(L.labs[e], g)] for e in ch)
            perm_idx[index[k][ch]] = index[k][img]
        # trace = sum over kernel basis of coefficient of g K_i on K_i; solve
        # g K = K M by coordinates on pivot positions of K.
        tr = kernel_trace(K, perm_idx)
        tr = tr if tr <= PRIME // 2 else tr - PRIME
        want = (-1) ** (n - 3) * mu_bounded(op_labs(n, lt, g))
        if CONTROL == "trace_sign":
            want = -want
        stats["H_trace"] += 1
        if tr != want:
            fails.append(f"{name} g={g}: homology trace {tr} != (-1)^(n-3) mu(L^g) {want}")


def act(lab, g):
    """Partition g.pi: i ~ j in g.pi iff g^-1 i ~ g^-1 j."""
    n = len(lab)
    ginv = [0] * n
    for i, x in enumerate(g):
        ginv[x] = i
    return normalize([lab[ginv[i]] for i in range(n)])


def kernel_trace(K, perm):
    """K: list of sparse vectors spanning an invariant subspace; perm: the
    action on coordinates. Returns trace mod p of the action on span K."""
    # Bring K to reduced echelon form: pivot coordinate per vector.
    rows = []
    for v in K:
        v = dict(v)
        for pc, pv in rows:
            if pc in v:
                f = v[pc]
                for a, x in pv.items():
                    v[a] = (v.get(a, 0) - f * x) % PRIME
                    if v[a] == 0:
                        del v[a]
        if not v:
            continue
        pc = min(v)
        inv = pow(v[pc], PRIME - 2, PRIME)
        v = {a: x * inv % PRIME for a, x in v.items()}
        new = []
        for qc, qv in rows:
            if pc in qv:
                f = qv[pc]
                for a, x in v.items():
                    qv[a] = (qv.get(a, 0) - f * x) % PRIME
                    if qv[a] == 0:
                        del qv[a]
            new.append((qc, qv))
        rows = new + [(pc, v)]
    piv = [pc for pc, _ in rows]
    tr = 0
    for pc, v in rows:
        gv = {perm[a]: x for a, x in v.items()}
        # coefficient of basis vector with pivot pc in gv is gv[pc] (reduced form)
        tr = (tr + gv.get(pc, 0)) % PRIME
    return tr


# ---------------------------------------------------------------- families

def families():
    """Disconnected posets at n = 7, 8, 9 where g permutes components."""
    V = (3, [(0, 1), (0, 2)])            # V: one min below two max
    L3 = (3, [(0, 2), (1, 2)])           # Lambda
    N4 = (4, [(0, 2), (1, 2), (1, 3)])   # N
    Y4 = (4, [(0, 1), (1, 2), (1, 3)])   # chain then V
    C22 = (4, [(0, 2), (0, 3), (1, 2), (1, 3)])  # 2+2 complete bipartite (crown-free)
    pt = (1, [])
    out = [
        ("4 x chain2", [chain(2)] * 4),
        ("3 x chain3", [chain(3)] * 3),
        ("2 x chain4", [chain(4)] * 2),
        ("2 x chain3 + 2 x pt", [chain(3)] * 2 + [pt] * 2),
        ("3 x chain2 + pt", [chain(2)] * 3 + [pt]),
        ("2 x V + pt", [V] * 2 + [pt]),
        ("2 x V + 2 x pt", [V] * 2 + [pt] * 2),
        ("2 x N4", [N4] * 2),
        ("2 x C22", [C22] * 2),
        ("V + Lambda + pt", [V, L3, pt]),
        ("2 x chain2 + 3 x pt", [chain(2)] * 2 + [pt] * 3),
        ("2 x chain2 + 2 x V", [chain(2)] * 2 + [V] * 2),
        ("3 x V", [V] * 3),
        ("3 x Lambda", [L3] * 3),
        ("2 x Y4", [Y4] * 2),
        ("3 x chain2 + 2 x pt", [chain(2)] * 3 + [pt] * 2),
        ("2 x chain3 + 3 x pt", [chain(3)] * 2 + [pt] * 3),
        ("4 x chain2 + pt", [chain(2)] * 4 + [pt]),
        ("2 x N4 + pt", [N4] * 2 + [pt]),
        ("2 x V + chain3", [V] * 2 + [chain(3)]),
    ]
    return out


def conj_reps(auts):
    """One representative per Aut(P)-conjugacy class."""
    seen, reps = set(), []
    inv = {}
    for a in auts:
        ai = [0] * len(a)
        for i, x in enumerate(a):
            ai[x] = i
        inv[a] = tuple(ai)
    for g in auts:
        if g in seen:
            continue
        reps.append(g)
        for a in auts:
            seen.add(tuple(a[g[inv[a][i]]] for i in range(len(g))))
    return reps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--large", type=int, nargs="*", default=[7, 8, 9])
    ap.add_argument("--control", choices=["no_mu_o", "no_sgn", "trace_sign", "no_mu_X", "crapo_drop", "lin_not_ec"],
                    help="run a deliberately wrong variant; it must FAIL")
    ap.add_argument("--skip-identity-large", action="store_true",
                    help="for the --large families, skip g = 1 (the full OP lattice)")
    ap.add_argument("--homology", type=int, default=0,
                    help="direct homology traces for all posets with n <= this")
    args = ap.parse_args()
    global CONTROL
    CONTROL = args.control
    stats = {k: 0 for k in ["A", "B", "B_nonzero", "C", "D", "E", "E_unequal",
                            "E_nonempty", "F", "H", "H_trace"]}
    fails = []
    nposets = 0
    for n in range(1, args.nmax + 1):
        for lt in all_posets(n):
            nposets += 1
            auts = automorphisms(n, lt)
            for g in conj_reps(auts):
                check_pair(n, lt, g, stats, fails, f"n={n}")
            if 3 <= n <= args.homology:
                homology_check(n, lt, conj_reps(auts), fails, stats, f"n={n} {lt}")
        print(f"n={n}: done, posets so far {nposets}, failures {len(fails)}", flush=True)
    for name, parts in families():
        n, lt = disjoint_union(*parts)
        if n not in args.large:
            continue
        nposets += 1
        auts = automorphisms(n, lt)
        reps = conj_reps(auts)
        nz = 0
        for g in reps:
            if args.skip_identity_large and order(g) == 1:
                continue
            before = stats["B_nonzero"]
            check_pair(n, lt, g, stats, fails, f"{name} (n={n})")
            nz += stats["B_nonzero"] - before
        print(f"{name}: n={n}, |Aut|={len(auts)}, classes={len(reps)}, nonzero closed-formula classes={nz}, failures so far {len(fails)}", flush=True)
    print("posets checked:", nposets)
    for k, v in stats.items():
        print(f"  {k}: {v}")
    for f in fails[:50]:
        print("FAIL", f)
    print("failures:", len(fails))
    print("ALL CHECKS PASS" if not fails else "SOME CHECKS FAILED")
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
