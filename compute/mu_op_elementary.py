#!/usr/bin/env python3
"""Checks for notes/mu_op_elementary.md.  Plain Python 3, exact integers.

Self-contained: no imports from the other scripts in compute/.

For every poset P on n <= N points (N = 6 by default), one per isomorphism
class, with OP(P) the lattice of order-preserving partitions (P/pi acyclic)
ordered by refinement, mu(L) = mu_L(0,1), e_C(P) the number of rotation
classes w C_n meeting Lin(P), Q_pi the quotient poset P/pi and kappa the
partition into components:

Asserted checks.
  [main]   mu(OP(P)) = (-1)^(n-1) e_C(P)                  (Theorem A).
  [conn]   P connected: e_C(P) = |Lin P|                   (Lemma rot).
  [W]      sum over P-compatible set compositions c of (-1)^|c|
           = (-1)^n [P antichain]                          (Lemma W).
  [faces]  for every pi in OP(P):
           sum_{sigma >= pi} (-1)^|sigma| |Lin Q_sigma| = (-1)^|pi| [pi >= kappa].
  [inv]    (-1)^n |Lin P| = sum_{sigma >= kappa} (-1)^|sigma| mu(0, sigma).
  [meet]   OP(P) is closed under the partition meet, and for a minimal,
           {x : x meet pi_a = 0} = {0} u {pi_ab : pi_ab in OP(P)},
           pi_a = {{a}, P - a}.
  [weis]   for every minimal a: mu(OP(P)) = - sum_b mu_OP(P)(pi_ab, 1).
  [upper]  for every pi in OP(P): mu_OP(P)(pi, 1) = mu(OP(Q_pi)).
  [rec]    for every minimal a: e_C(P) = sum_b e_C(Q_{pi_ab}), and the map
           class -> (successor of a, contracted class) is a bijection.
  [comp]   |Lin P| = sum over partitions sigma of the components of
           prod_B e_C(P|_B)                                (Lemma 1.3 of [GT]).
Negative controls (each must FAIL on some poset, else the run fails).
  [neg-lin]  mu(OP(P)) = (-1)^(n-1) |Lin P| for all P.
  [neg-strict] Lemma W with strict instead of weak compatibility.
  [neg-nonmin] [rec] with a a non-minimal, non-maximal element.

Exit status 0 iff every asserted check passes and every negative control
fails somewhere.

Run from compute/:  python3 mu_op_elementary.py [--max-n N]
"""

import argparse
import itertools
import sys
from functools import lru_cache


# ---------------------------------------------------------------------------
# Posets: a poset on range(n) is a frozenset of strict pairs (i, j), i < j in P.

def transitive_closure(n, rel):
    lt = [[False] * n for _ in range(n)]
    for i, j in rel:
        lt[i][j] = True
    for k in range(n):
        for i in range(n):
            if lt[i][k]:
                for j in range(n):
                    if lt[k][j]:
                        lt[i][j] = True
    return frozenset((i, j) for i in range(n) for j in range(n) if lt[i][j])


def canon(n, rel):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((p[i], p[j]) for i, j in rel))
        if best is None or key < best:
            best = key
    return best


def all_posets(n):
    """One poset per isomorphism class on range(n), built by adding a new
    element whose strict down-set is an order ideal (natural labelling)."""
    level = {(): frozenset()}  # canon -> rel, for size m
    for m in range(n):
        nxt = {}
        for rel in level.values():
            for mask in range(1 << m):
                down = {i for i in range(m) if mask >> i & 1}
                if any((x, y) in rel and y in down and x not in down
                       for x in range(m) for y in range(m)):
                    continue
                new = rel | frozenset((i, m) for i in down)
                c = canon(m + 1, new)
                if c not in nxt:
                    nxt[c] = frozenset(new)
        level = nxt
    return list(level.values())


def components(n, rel):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i, j in rel:
        parent[find(i)] = find(j)
    return normalize([find(i) for i in range(n)])


def lin_exts(n, rel):
    out = []
    for w in itertools.permutations(range(n)):
        pos = {x: k for k, x in enumerate(w)}
        if all(pos[i] < pos[j] for i, j in rel):
            out.append(w)
    return out


def e_C(n, rel):
    seen = set()
    for w in lin_exts(n, rel):
        seen.add(min(w[k:] + w[:k] for k in range(n)))
    return len(seen)


# ---------------------------------------------------------------------------
# Set partitions as restricted-growth tuples.

def normalize(labels):
    m, out = {}, []
    for x in labels:
        if x not in m:
            m[x] = len(m)
        out.append(m[x])
    return tuple(out)


def set_partitions(n):
    def rec(prefix, k):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for b in range(k + 1):
            yield from rec(prefix + [b], max(k, b + 1))
    return list(rec([], 0))


def nblocks(p):
    return max(p) + 1 if p else 0


def leq(p, q):
    """p refines q."""
    rep = {}
    for i, b in enumerate(p):
        if b not in rep:
            rep[b] = i
        elif q[i] != q[rep[b]]:
            return False
    return True


def meet(p, q):
    return normalize(list(zip(p, q)))


def quotient(rel, p):
    """Quotient digraph edges between distinct blocks."""
    return {(p[i], p[j]) for i, j in rel if p[i] != p[j]}


def is_op(rel, p):
    k = nblocks(p)
    edges = quotient(rel, p)
    indeg = [0] * k
    for _, b in edges:
        indeg[b] += 1
    succ = [[] for _ in range(k)]
    for a, b in edges:
        succ[a].append(b)
    stack = [v for v in range(k) if indeg[v] == 0]
    seen = 0
    while stack:
        v = stack.pop()
        seen += 1
        for u in succ[v]:
            indeg[u] -= 1
            if indeg[u] == 0:
                stack.append(u)
    return seen == k


def quotient_poset(rel, p):
    return nblocks(p), transitive_closure(nblocks(p), quotient(rel, p))


def op_lattice(n, rel):
    return [p for p in set_partitions(n) if is_op(rel, p)]


def mu_row(L, bot):
    """mu(bot, x) for x in L, x >= bot."""
    up = sorted((x for x in L if leq(bot, x)), key=lambda x: -nblocks(x))
    mu = {}
    for x in up:
        mu[x] = 1 if x == bot else -sum(mu[y] for y in mu if leq(y, x))
    return mu


def mu_col(L, top):
    """mu(x, top) for x in L, x <= top."""
    down = sorted((x for x in L if leq(x, top)), key=nblocks)
    mu = {}
    for x in down:
        mu[x] = 1 if x == top else -sum(mu[y] for y in mu if leq(x, y))
    return mu


@lru_cache(maxsize=None)
def mu_op_canon(n, crel):
    rel = frozenset(crel)
    L = op_lattice(n, rel)
    return mu_row(L, tuple(range(n)))[tuple([0] * n)] if n else 1


def mu_op(n, rel):
    return mu_op_canon(n, canon(n, rel))


# ---------------------------------------------------------------------------
# Compatible set compositions (faces of the closed order cone).

def compositions(n, rel, strict=False):
    """Yield (blocks-as-map) for ordered set partitions F : range(n) -> [k]
    surjective with i <_P j => F(i) <= F(j) (or < if strict)."""
    for p in set_partitions(n):
        k = nblocks(p)
        for order in itertools.permutations(range(k)):
            F = [order[p[i]] for i in range(n)]
            if all((F[i] < F[j]) if strict else (F[i] <= F[j]) for i, j in rel):
                yield k


def minimal_elements(n, rel):
    return [a for a in range(n) if not any(j == a for _, j in rel)]


def pi_ab(n, a, b):
    return normalize([a if x == b else x for x in range(n)])


def contraction_bijection(n, rel, a):
    """Map each cyclic class to (b, contracted class); return (ok, counts)."""
    classes = set()
    for w in lin_exts(n, rel):
        classes.add(min(w[k:] + w[:k] for k in range(n)))
    image = set()
    for c in classes:
        i = c.index(a)
        b = c[(i + 1) % n]
        p = pi_ab(n, a, b)
        if not is_op(rel, p):
            return False
        rot = c[i:] + c[:i]  # starts a b ...
        word = tuple(p[x] for x in rot[1:])
        qn, qrel = quotient_poset(rel, p)
        # the contracted necklace must be a class of Q: some rotation in Lin Q
        if not any(all(r.index(x) < r.index(y) for x, y in qrel)
                   for r in (word[k:] + word[:k] for k in range(qn))):
            return False
        image.add((b, min(word[k:] + word[:k] for k in range(qn))))
    if len(image) != len(classes):
        return False
    total = 0
    for b in range(n):
        if b == a:
            continue
        p = pi_ab(n, a, b)
        if is_op(rel, p):
            total += e_C(*quotient_poset(rel, p))
    return total == len(classes)


# ---------------------------------------------------------------------------

def check_poset(n, rel, neg):
    fails = []
    L = op_lattice(n, rel)
    bot, top = tuple(range(n)), tuple([0] * n)
    row = mu_row(L, bot)
    col = mu_col(L, top)
    mu = row[top]
    lin = lin_exts(n, rel)
    ec = e_C(n, rel)
    kappa = components(n, rel)
    sign = (-1) ** (n - 1)

    if mu != sign * ec:
        fails.append("main")
    if mu != sign * len(lin):
        neg["neg-lin"] += 1
    if nblocks(kappa) == 1 and ec != len(lin):
        fails.append("conn")

    S = sum((-1) ** k for k in compositions(n, rel))
    if S != (-1) ** n * (not rel):
        fails.append("W")
    S2 = sum((-1) ** k for k in compositions(n, rel, strict=True))
    if S2 != (-1) ** n * (not rel):
        neg["neg-strict"] += 1

    linQ = {s: len(lin_exts(*quotient_poset(rel, s))) for s in L}
    for p in L:
        lhs = sum((-1) ** nblocks(s) * linQ[s] for s in L if leq(p, s))
        if lhs != (-1) ** nblocks(p) * leq(kappa, p):
            fails.append("faces")
            break
        if col[p] != mu_op(*quotient_poset(rel, p)):
            fails.append("upper")
            break

    rhs = sum((-1) ** nblocks(s) * row[s] for s in L if leq(kappa, s))
    if (-1) ** n * len(lin) != rhs:
        fails.append("inv")

    Lset = set(L)
    if any(meet(x, y) not in Lset for x in L for y in L):
        fails.append("meet")

    if n >= 2:
        for a in minimal_elements(n, rel):
            pa = normalize([0 if x == a else 1 for x in range(n)])
            atoms = {pi_ab(n, a, b) for b in range(n)
                     if b != a and is_op(rel, pi_ab(n, a, b))}
            comp = {x for x in L if meet(x, pa) == bot}
            if pa not in Lset or comp != atoms | {bot}:
                fails.append("meet")
            if mu != -sum(col[x] for x in atoms):
                fails.append("weis")
            if not contraction_bijection(n, rel, a):
                fails.append("rec")
        for a in range(n):
            below = any(j == a for _, j in rel)
            above = any(i == a for i, _ in rel)
            if below and above:
                tot = sum(e_C(*quotient_poset(rel, pi_ab(n, a, b)))
                          for b in range(n)
                          if b != a and is_op(rel, pi_ab(n, a, b)))
                if tot != ec:
                    neg["neg-nonmin"] += 1

    # [comp]: |Lin P| = sum_{sigma in Pi(K)} prod_B e_C(P|_B)
    k = nblocks(kappa)
    tot = 0
    for s in set_partitions(k):
        prod = 1
        for blk in range(nblocks(s)):
            B = [x for x in range(n) if s[kappa[x]] == blk]
            idx = {x: t for t, x in enumerate(B)}
            sub = frozenset((idx[i], idx[j]) for i, j in rel
                            if i in idx and j in idx)
            prod *= e_C(len(B), sub)
        tot += prod
    if tot != len(lin):
        fails.append("comp")
    return fails, mu, ec, len(lin)


def run(max_n, out):
    ok = True
    neg = {"neg-lin": 0, "neg-strict": 0, "neg-nonmin": 0}
    total = 0
    for n in range(1, max_n + 1):
        posets = all_posets(n)
        nfail = 0
        table = {}
        for rel in posets:
            fails, mu, ec, lin = check_poset(n, rel, neg)
            if fails:
                nfail += 1
                ok = False
                print(f"FAIL n={n} P={sorted(rel)}: {sorted(set(fails))}",
                      file=out)
            table[(mu, ec)] = table.get((mu, ec), 0) + 1
        total += len(posets)
        print(f"n={n}: posets={len(posets)} failures={nfail} "
              f"distinct (mu, e_C) pairs={len(table)}", file=out)
        if n <= 3:
            print(f"  (mu, e_C) counts: {dict(sorted(table.items()))}",
                  file=out)
    print(f"total posets checked: {total}", file=out)
    print("checks: main conn W faces inv meet weis upper rec comp", file=out)
    for k, v in neg.items():
        status = "fails as required" if v else "DID NOT FAIL (bad control)"
        print(f"negative control {k}: fails on {v} cases ({status})",
              file=out)
        if not v:
            ok = False
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED", file=out)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=6)
    args = ap.parse_args()
    sys.exit(0 if run(args.max_n, sys.stdout) else 1)


if __name__ == "__main__":
    main()
