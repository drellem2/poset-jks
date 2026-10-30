#!/usr/bin/env python3
"""Checks for the direct proof of eq. (characterconj) in
notes/fixed_point_mobius_identity.md.

For a poset P on [n] and g in Aut(P), let L = OP(P)^g (g-invariant
order-preserving partitions; a lattice whose meet is intersection).  The proof
uses the element z = "merge one g-orbit c" of L and Crapo's complementation
theorem.  This script verifies every intermediate statement directly, by brute
force, without using the arguments of the proof:

  (L1) every g-orbit is an antichain, and z (merge one orbit) lies in OP(P);
  (L2) unequal cycle lengths, c an orbit of maximal length: z has no
       complement in L and mu(L) = 0;
  (L3) uniform cycle type d^k, d >= 2, k >= 2, c any orbit, c0 in c: the
       complements of z in L (meet and join computed inside L) are exactly
       the partitions {T, gT, ..., g^(d-1) T}, T a union of connected
       components with c0 in T and P = T u gT u ... u g^(d-1)T disjoint;
       mu_L(0, y) = mu(OP(T)), mu_L(y, 1) = mu(d) (number-theoretic), and
       mu(L) = mu(d) * sum_T mu(OP(T));
  (L4) the number N_r of cyclic classes C with gC = C and r_g(C) = r is
       sum_{T} e_C(T) if gcd(n, r) = k and 0 otherwise (same T as in L3);
  (L5) connected P, g != 1: mu(L) = 0;
  (F)  the full identity (-1)^(n-3) mu(L) = sgn(g) sum zeta^(r_g(C)).

Positive controls: dropping the factor mu(d) in (L3), or replacing e_C(T) by
the number of linear extensions e(T) in (L4), must fail somewhere; the
complement search must find complements somewhere.

Plain Python 3; reuses the enumeration helpers of poset_jks_check.py.
Run `python3 fixed_point_mobius.py --help`.
"""

import argparse
import itertools
import math
import sys
import time
from collections import Counter

import poset_jks_check as pj


def cycle_lengths(g):
    return [len(c) for c in pj.cycles(g)]


def num_moebius(d):
    """Number-theoretic Moebius function."""
    res, m, p = 1, d, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    return -res if m > 1 else res


def components(rel, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in rel:
        parent[find(a)] = find(b)
    comps = {}
    for x in range(n):
        comps.setdefault(find(x), []).append(x)
    return [frozenset(c) for c in comps.values()]


def induced(rel, S):
    """Induced subposet on S, relabelled to 0..|S|-1 (sorted order)."""
    idx = {x: i for i, x in enumerate(sorted(S))}
    return frozenset((idx[a], idx[b]) for a, b in rel if a in S and b in S), len(S)


def mu_of_OP(rel, m):
    if m == 0:
        return 1
    return pj.moebius_bottom_top(pj.order_preserving_partitions(rel, m), m)


def e_C(rel, m):
    return len(pj.cyclic_classes(pj.linear_extensions(rel, m)))


def mu_interval(L, lo, hi):
    """mu(lo, hi) inside the finite subposet L of Pi_n (refinement order)."""
    elems = [x for x in L if pj.refines(lo, x) and pj.refines(x, hi)]
    elems.sort(key=lambda p: -len(p))
    mu = {}
    for x in elems:
        mu[x] = 1 if x == lo else -sum(mu[y] for y in mu if y != x and pj.refines(y, x))
    return mu[hi]


def meet(x, y):
    return frozenset(B & C for B in x for C in y if B & C)


def join_in(L, x, y):
    ub = [u for u in L if pj.refines(x, u) and pj.refines(y, u)]
    least = [u for u in ub if all(pj.refines(u, v) for v in ub)]
    assert len(least) == 1, "L is not a lattice"
    return least[0]


def transversals(rel, n, g, c0):
    """Unions T of connected components with c0 in T such that
    P = T u gT u ... u g^(d-1)T disjointly (g of order d on P)."""
    comps = components(rel, n)
    d = len(pj.cycles(g)[0])
    out = []
    for r in range(1, len(comps) + 1):
        for sub in itertools.combinations(comps, r):
            T = frozenset().union(*sub)
            if c0 not in T or len(T) * d != n:
                continue
            imgs, cur = [], T
            for _ in range(d):
                imgs.append(cur)
                cur = frozenset(g[x] for x in cur)
            if len(frozenset().union(*imgs)) == n:
                out.append((T, frozenset(imgs)))
    return out


def analyse(rel, n, stats, fails, name="", uniform_only=False):
    """uniform_only: only g of fixed-point-free uniform cycle type d^k, d >= 2
    (used for n >= 7, where the full OP lattice of g = 1 is slow)."""
    G = pj.automorphisms(rel, n)
    OP = pj.order_preserving_partitions(rel, n)
    lin = pj.linear_extensions(rel, n)
    cyc = pj.cyclic_classes(lin)
    connected = pj.is_connected(rel, n)
    bottom = frozenset(frozenset([i]) for i in range(n))
    top = frozenset([frozenset(range(n))])
    sub_cache = {}

    def sub_data(T):
        if T not in sub_cache:
            r2, m = induced(rel, T)
            sub_cache[T] = (mu_of_OP(r2, m), e_C(r2, m), len(pj.linear_extensions(r2, m)))
        return sub_cache[T]

    def fail(msg):
        fails.append(f"{name} g={pj.cycle_str(g)}: {msg}")

    for cl in pj.conjugacy_classes(G):
        g = cl[0]
        if uniform_only and (len(set(cycle_lengths(g))) > 1 or cycle_lengths(g)[0] == 1):
            continue
        stats["pairs"] += 1
        L = [pi for pi in OP if pj.act_partition(g, pi) == pi]
        mu = pj.moebius_bottom_top(L, n)
        cyc_lens = sorted({len(c) for c in pj.cycles(g)})
        orbits = [frozenset(c) for c in pj.cycles(g)]

        # (L1)
        for c in orbits:
            if any((a, b) in rel for a in c for b in c):
                fail("orbit not an antichain")
            zc = frozenset([c]) | frozenset(frozenset([x]) for x in range(n) if x not in c)
            if zc not in OP:
                fail("merging an orbit is not order-preserving")

        # (F) full identity
        counts = [0] * n
        for u in cyc:
            r = pj.rotation_amount(g, u)
            if r is not None:
                counts[r] += 1
        lhs = (-1) ** ((n - 3) % 2) * mu
        if not pj.zeta_sum_equals_int(counts, pj.sign(g) * lhs, n):
            fail("full identity fails")
        stats["F"] += 1

        if g == tuple(range(n)):
            continue
        if connected:  # (L5)
            stats["L5"] += 1
            if mu != 0:
                fail("connected, g != 1, mu != 0")

        def complements(z):
            return [y for y in L if meet(y, z) == bottom and join_in(L, y, z) == top]

        if len(cyc_lens) > 1:  # (L2)
            stats["L2"] += 1
            D = cyc_lens[-1]
            c = next(o for o in orbits if len(o) == D)
            z = frozenset([c]) | frozenset(frozenset([x]) for x in range(n) if x not in c)
            if complements(z):
                fail("L2: z has a complement")
            if mu != 0:
                fail("L2: mu != 0")
            if any(counts):
                fail("L2: some cyclic class is fixed")
            continue

        d = cyc_lens[0]
        k = n // d
        if k == 1:  # P is one orbit, an antichain; L = subgroup lattice of Z/d
            stats["k1"] += 1
            if mu != num_moebius(d):
                fail("k = 1: mu != mu(d)")
            continue
        stats["L3"] += 1
        Ts_all = []
        for c in orbits:  # every choice of orbit c and base point c0
            for c0 in sorted(c):
                z = frozenset([c]) | frozenset(frozenset([x]) for x in range(n) if x not in c)
                comp = set(complements(z))
                Ts = transversals(rel, n, g, c0)
                if comp != {y for _, y in Ts}:
                    fail("L3: complements != transversal partitions")
                if comp:
                    stats["L3_with_complements"] += 1
                for T, y in Ts:
                    m0, _, _ = sub_data(T)
                    if mu_interval(L, bottom, y) != m0:
                        fail("L3: mu(0,y) != mu(OP(T))")
                    if mu_interval(L, y, top) != num_moebius(d):
                        fail("L3: mu(y,1) != mu(d)")
                rec = num_moebius(d) * sum(sub_data(T)[0] for T, _ in Ts)
                if rec != mu:
                    fail("L3: recursion value != mu(L)")
                if sum(sub_data(T)[0] for T, _ in Ts) != mu:
                    stats["control_no_mud_detected"] += 1
                Ts_all.append(Ts)
        # (L4), base point = smallest element of the first orbit
        Ts = Ts_all[0]
        N = sum(sub_data(T)[1] for T, _ in Ts)
        Nlin = sum(sub_data(T)[2] for T, _ in Ts)
        for r in range(n):
            want = N if math.gcd(n, r) == k else 0
            if counts[r] != want:
                fail(f"L4: N_{r} = {counts[r]} != {want}")
            if math.gcd(n, r) == k and counts[r] != Nlin:
                stats["control_lin_detected"] += 1
        stats["L4"] += 1


def disjoint_union(parts):
    rel, off = set(), 0
    for r, m in parts:
        rel |= {(a + off, b + off) for a, b in r}
        off += m
    return frozenset(rel), off


def families(nmax_all, nlarge):
    """All unlabeled posets with n <= nmax_all, then, for each n in nlarge,
    every disjoint union of connected posets of size <= 4 in which some
    connected component occurs at least twice (so Aut(P) permutes components)."""
    posets = pj.unlabeled_posets_by_extension(max(nmax_all, 4))
    for n in range(1, nmax_all + 1):
        for i, rel in enumerate(posets[n]):
            yield f"n{n}#{i}", rel, n
    conn = [(rel, m) for m in range(1, 5) for rel in posets[m] if pj.is_connected(rel, m)]
    for n in nlarge:
        def rec(start, left, acc):
            if left == 0:
                yield acc
                return
            for j in range(start, len(conn)):
                if conn[j][1] <= left:
                    yield from rec(j, left - conn[j][1], acc + [j])
        for combo in rec(0, n, []):
            if max(Counter(combo).values()) < 2:
                continue
            rel, m = disjoint_union([conn[j] for j in combo])
            yield f"n{n}:union{combo}", rel, m


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--nmax", type=int, default=6, help="all unlabeled posets up to this n")
    ap.add_argument("--large", type=int, nargs="*", default=[7],
                    help="sizes for the repeated-component disjoint-union families")
    args = ap.parse_args(argv)
    t0 = time.time()
    stats, fails, nposets = Counter(), [], 0
    for name, rel, n in families(args.nmax, args.large):
        if n < 3:
            continue
        nposets += 1
        analyse(rel, n, stats, fails, name, uniform_only=n > args.nmax)
    print(f"posets checked: {nposets} (all unlabeled 3 <= n <= {args.nmax}, every "
          f"conjugacy class of Aut(P); repeated-component disjoint unions at n in "
          f"{args.large}, fixed-point-free uniform classes d^k only)")
    for key in ["pairs", "F", "L2", "L3", "L3_with_complements", "L4", "L5", "k1",
                "control_no_mud_detected", "control_lin_detected"]:
        print(f"  {key}: {stats[key]}")
    print(f"failures: {len(fails)}")
    for f in fails[:50]:
        print("  " + f)
    print(f"time: {time.time() - t0:.1f}s", file=sys.stderr)
    ok = not fails and stats["control_no_mud_detected"] > 0 \
        and stats["control_lin_detected"] > 0 and stats["L3_with_complements"] > 0
    print("ALL CHECKS PASS" if ok else "CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
