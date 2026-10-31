#!/usr/bin/env python3
"""Check for notes/prior_art_theorem_e.md, section 2.1 (the claw case).

Claim checked. Let K_n be the "claw": the poset on {0, 1, ..., n-1} with 0 < i for
every i >= 1 and no other relations. Then
  (a) every set partition of {0, ..., n-1} is order-preserving for K_n, i.e. its
      quotient digraph is acyclic, so OP(K_n) is the full partition lattice Pi_n;
  (b) Aut(K_n) is the symmetric group on the leaves, of order (n-1)!;
  (c) K_n has (n-1)! linear extensions, and Aut(K_n) acts on them freely
      (indeed simply transitively);
  (d) for 3 <= n <= 5, among all connected labeled posets on n elements, OP(P) = Pi_n
      holds exactly for the claw and the dual claw (2n labelings). The number of
      connected labeled posets enumerated (12, 146, 3060) is printed as a control.

Controls (the instrument must be able to say "no"):
  [CTL] the 3-chain 0 < 1 < 2: not every partition is order-preserving
        ({0,2},{1} has the cycle {0,2} -> {1} -> {0,2});
  [CTL] the poset "N" (0<2, 1<2, 1<3): not every partition is order-preserving,
        and its automorphism group is trivial.

Plain Python 3, no third-party packages, imports nothing from the repo.
"""
import itertools
import math
import sys


def set_partitions(elems):
    elems = list(elems)
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p


def is_order_preserving(rel, part):
    """rel: set of cover/strict pairs (a, b) meaning a < b. Acyclic quotient digraph?"""
    block = {}
    for i, B in enumerate(part):
        for x in B:
            block[x] = i
    k = len(part)
    adj = {i: set() for i in range(k)}
    for a, b in rel:
        if block[a] != block[b]:
            adj[block[a]].add(block[b])
    # Kahn's algorithm
    indeg = {i: 0 for i in range(k)}
    for i in adj:
        for j in adj[i]:
            indeg[j] += 1
    queue = [i for i in range(k) if indeg[i] == 0]
    seen = 0
    while queue:
        i = queue.pop()
        seen += 1
        for j in adj[i]:
            indeg[j] -= 1
            if indeg[j] == 0:
                queue.append(j)
    return seen == k


def closure(n, rel):
    lt = set(rel)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(lt):
            for (c, d) in list(lt):
                if b == c and (a, d) not in lt:
                    lt.add((a, d))
                    changed = True
    return lt


def automorphisms(n, lt):
    out = []
    for g in itertools.permutations(range(n)):
        if all(((g[a], g[b]) in lt) for (a, b) in lt):
            out.append(g)
    return out


def linear_extensions(n, lt):
    return [w for w in itertools.permutations(range(n))
            if all(w.index(a) < w.index(b) for (a, b) in lt)]


def bell(n):
    return sum(1 for _ in set_partitions(range(n)))


def check(name, n, rel, expect_all_op, expect_aut=None, expect_free=None):
    lt = closure(n, rel)
    parts = list(set_partitions(range(n)))
    n_op = sum(1 for p in parts if is_order_preserving(lt, p))
    aut = automorphisms(n, lt)
    ext = linear_extensions(n, lt)
    ext_set = set(ext)
    free = True
    orbit_count = 0
    seen = set()
    for w in ext:
        if w in seen:
            continue
        orbit_count += 1
        for g in aut:
            gw = tuple(g[x] for x in w)
            assert gw in ext_set
            seen.add(gw)
        stab = [g for g in aut if tuple(g[x] for x in w) == w]
        if len(stab) != 1:
            free = False
    all_op = (n_op == len(parts))
    ok = (all_op == expect_all_op)
    if expect_aut is not None:
        ok = ok and len(aut) == expect_aut
    if expect_free is not None:
        ok = ok and free == expect_free
    print(f"{name}: n={n} |Pi_n|={len(parts)} #OP={n_op} all_OP={all_op} "
          f"|Aut|={len(aut)} e(P)={len(ext)} free={free} orbits={orbit_count} "
          f"-> {'OK' if ok else 'FAIL'}")
    return ok


def main():
    nmax = 7
    if "--nmax" in sys.argv:
        nmax = int(sys.argv[sys.argv.index("--nmax") + 1])
    all_ok = True
    # controls
    all_ok &= check("[CTL] 3-chain", 3, {(0, 1), (1, 2)}, expect_all_op=False,
                    expect_aut=1)
    all_ok &= check("[CTL] N-poset", 4, {(0, 2), (1, 2), (1, 3)}, expect_all_op=False,
                    expect_aut=1)
    # claws
    for n in range(3, nmax + 1):
        rel = {(0, i) for i in range(1, n)}
        f = math.factorial(n - 1)
        all_ok &= check(f"[CLAW] K_{n}", n, rel, expect_all_op=True,
                        expect_aut=f, expect_free=True)
        lt = closure(n, rel)
        e = len(linear_extensions(n, lt))
        if e != f:
            print(f"  FAIL: e(K_{n}) = {e} != {f}")
            all_ok = False
    # classification: connected labeled posets with OP(P) = Pi_n are exactly the
    # claw and the dual claw (note, section 2.2)
    for n in range(3, min(nmax, 5) + 1):
        pairs = [(a, b) for a in range(n) for b in range(n) if a != b]
        parts = list(set_partitions(range(n)))
        seen_lt = set()
        n_conn = n_all = n_star = 0
        bad = 0
        for mask in range(1 << len(pairs)):
            rel = {pairs[i] for i in range(len(pairs)) if mask >> i & 1}
            if any((b, a) in rel for (a, b) in rel):
                continue
            lt = frozenset(closure(n, rel))
            if lt != frozenset(rel) or any(a == b for (a, b) in lt):
                continue  # count each strict order once (transitively closed)
            if lt in seen_lt:
                continue
            seen_lt.add(lt)
            # connected comparability graph?
            comp = {0}
            stack = [0]
            while stack:
                x = stack.pop()
                for (a, b) in lt:
                    for (u, v) in ((a, b), (b, a)):
                        if u == x and v not in comp:
                            comp.add(v)
                            stack.append(v)
            if len(comp) != n:
                continue
            n_conn += 1
            all_op = all(is_order_preserving(lt, p) for p in parts)
            mins = [x for x in range(n) if all(b != x for (_, b) in lt)]
            maxs = [x for x in range(n) if all(a != x for (a, _) in lt)]
            star = (len(lt) == n - 1 and (len(mins) == 1 or len(maxs) == 1))
            n_all += all_op
            n_star += star
            if all_op != star:
                bad += 1
        ok = bad == 0 and n_all == 2 * n  # n labelings of the claw + n of the dual
        print(f"[CLASS] n={n}: connected labeled posets={n_conn} with OP=Pi_n: {n_all} "
              f"claw-or-dual: {n_star} mismatches={bad} -> {'OK' if ok else 'FAIL'}")
        all_ok &= ok
    print("ALL CHECKS PASS:", bool(all_ok))
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
