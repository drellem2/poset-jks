#!/usr/bin/env python3
"""Character-identity sweep over ALL unlabeled posets with n = 7 (mg-6bbe0).

Reuses poset_jks_check.analyse for both sides of eq. (characterconj).  The
only new code here is

  * a faster canonical form (color refinement by down/up-set sizes, then
    minimum over permutations that respect the refined cells), so that the
    2045 posets on 7 points can be enumerated by the same extension method
    as poset_jks_check.unlabeled_posets_by_extension;
  * a faster automorphism search (permutations respecting the same cells);
  * a recognizer that tags members of the symmetric families named in the
    work item (unions of equal chains, ordinal sums of antichains, crowns,
    products, stars, ...) by their canonical code;
  * per-n tallies of how many (P, g) pairs each wrong control formula
    (F1-F4 of poset_jks_check) is rejected on.

Run from compute/:

    python3 n7_sweep.py --n 7 --jobs 3 --tsv output/n7_character_table.tsv \
        > output/n7_summary.txt

Exit status 0 iff the note's identity F0 holds on every (P, g).
"""

import argparse
import itertools
import os
import sys
import time
from collections import Counter
from multiprocessing import Pool

import poset_jks_check as pj

# ---------------------------------------------------------------------------
# Canonical form and automorphisms via cell refinement


def refined_cells(rel, n):
    """Ordered partition of [n] into cells of an isomorphism-invariant
    coloring: start from (|down|, |up|), refine by the multisets of colors of
    the elements strictly below and strictly above, until stable."""
    down = [[a for a in range(n) if (a, x) in rel] for x in range(n)]
    up = [[b for b in range(n) if (x, b) in rel] for x in range(n)]
    col = [(len(down[x]), len(up[x])) for x in range(n)]
    while True:
        new = [(col[x], tuple(sorted(col[a] for a in down[x])),
                tuple(sorted(col[b] for b in up[x]))) for x in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    cells = {}
    for x in range(n):
        cells.setdefault(col[x], []).append(x)
    return [cells[k] for k in sorted(cells)]


def cell_perms(cells, n):
    """All p with p mapping cell k onto positions block k (canonical
    positions are the cells laid out in order)."""
    targets, pos = [], 0
    for c in cells:
        targets.append(list(range(pos, pos + len(c))))
        pos += len(c)
    for choice in itertools.product(*[itertools.permutations(t) for t in targets]):
        p = [0] * n
        for c, img in zip(cells, choice):
            for x, y in zip(c, img):
                p[x] = y
        yield tuple(p)


def canonical_fast(rel, n):
    cells = refined_cells(rel, n)
    return min(pj.rel_code(pj.relabel(rel, p), n) for p in cell_perms(cells, n))


def automorphisms_fast(rel, n):
    cells = refined_cells(rel, n)
    out = []
    for choice in itertools.product(*[itertools.permutations(c) for c in cells]):
        p = [0] * n
        for c, img in zip(cells, choice):
            for x, y in zip(c, img):
                p[x] = y
        p = tuple(p)
        if pj.relabel(rel, p) == rel:
            out.append(p)
    return sorted(out)


def unlabeled_posets(nmax):
    """Same extension method as pj.unlabeled_posets_by_extension, with the
    fast canonical form."""
    out = {0: [frozenset()]}
    for n in range(0, nmax):
        seen = {}
        for rel in out[n]:
            for mask in range(1 << n):
                down = [i for i in range(n) if mask >> i & 1]
                if any((a, b) in rel and not mask >> a & 1 for b in down for a in range(n)):
                    continue
                new = frozenset(rel) | {(i, n) for i in down}
                c = canonical_fast(new, n + 1)
                if c not in seen:
                    seen[c] = pj.from_code(c, n + 1)
        out[n + 1] = [seen[c] for c in sorted(seen)]
    return out


# ---------------------------------------------------------------------------
# Named symmetric families


def disjoint_union(*parts):
    rel, off = set(), 0
    for (r, m) in parts:
        rel |= {(a + off, b + off) for a, b in r}
        off += m
    return frozenset(rel), off


def chain(m):
    return frozenset((i, j) for i in range(m) for j in range(i + 1, m)), m


def antichain(m):
    return frozenset(), m


def ordinal_sum(*parts):
    rel, off, blocks = set(), 0, []
    for (r, m) in parts:
        rel |= {(a + off, b + off) for a, b in r}
        blocks.append(range(off, off + m))
        off += m
    for i in range(len(blocks)):
        for j in range(i + 1, len(blocks)):
            rel |= {(a, b) for a in blocks[i] for b in blocks[j]}
    return frozenset(rel), off


def product(p1, p2):
    (r1, m1), (r2, m2) = p1, p2
    idx = {(x, y): x * m2 + y for x in range(m1) for y in range(m2)}
    le1 = lambda a, b: a == b or (a, b) in r1
    le2 = lambda a, b: a == b or (a, b) in r2
    rel = {(idx[a], idx[b]) for a in idx for b in idx
           if a != b and le1(a[0], b[0]) and le2(a[1], b[1])}
    return frozenset(rel), m1 * m2


def crown(k):
    """Minima 0..k-1, maxima k..2k-1, i < k+i and i < k+(i+1 mod k)."""
    return frozenset({(i, k + i) for i in range(k)} | {(i, k + (i + 1) % k)
                                                        for i in range(k)}), 2 * k


def families(n):
    """(name, (rel, n)) for the symmetric families of the work item."""
    F = []
    for k in range(1, n + 1):
        if n % k == 0:
            m = n // k
            F.append((f"{k}x{m}-chain", disjoint_union(*[chain(m)] * k)))
    for m in range(2, n):  # k copies of an m-chain plus isolated points
        for k in range(2, n // m + 1):
            if k * m < n:
                F.append((f"{k}x{m}-chain+{n - k * m}pt",
                          disjoint_union(*[chain(m)] * k, antichain(n - k * m))))
    for comp in compositions(n):  # complete layered posets
        if len(comp) >= 2:
            F.append(("layered" + "+".join(map(str, comp)),
                      ordinal_sum(*[antichain(c) for c in comp])))
    for k in range(2, n // 2 + 1):
        if 2 * k <= n:
            nm = f"crown{k}" if k >= 3 else "2+2 crown (=K22)"
            F.append((nm + (f"+{n - 2 * k}pt" if n > 2 * k else ""),
                      disjoint_union(crown(k), antichain(n - 2 * k))))
    for a in range(2, n + 1):
        for b in range(a, n + 1):
            if a * b <= n:
                rest = n - a * b
                F.append((f"chain{a}*chain{b}" + (f"+{rest}pt" if rest else ""),
                          disjoint_union(product(chain(a), chain(b)), antichain(rest))))
    if n > 4:  # Boolean square 2x2 with an antichain stacked on it
        sq, rest = product(chain(2), chain(2)), n - 4
        F.append((f"2x2 < {rest}-antichain", ordinal_sum(sq, antichain(rest))))
        F.append((f"{rest}-antichain < 2x2", ordinal_sum(antichain(rest), sq)))
    for k in range(2, n // 4 + 1):  # (2x2) x antichain_k = k Boolean squares
        rest = n - 4 * k
        F.append((f"{k}x(2x2)" + (f"+{rest}pt" if rest else ""),
                  disjoint_union(*[product(chain(2), chain(2))] * k, antichain(rest))))
    F.append(("claw up (1 < n-1 arms)", ordinal_sum(antichain(1), antichain(n - 1))))
    F.append(("claw down", ordinal_sum(antichain(n - 1), antichain(1))))
    # spiders: center below k arms that are chains of equal length
    for L in range(2, n):
        if (n - 1) % L == 0 and (n - 1) // L >= 2:
            k = (n - 1) // L
            arms, _ = disjoint_union(*[chain(L)] * k)
            rel = {(a + 1, b + 1) for a, b in arms} | {(0, x) for x in range(1, n)}
            F.append((f"spider {k} arms of length {L}", (frozenset(rel), n)))
    # width-2 symmetric: two equal chains with a "ladder" (= chain2 * chain_m)
    # is covered by products; also two chains joined by a common bottom/top
    for m in range(1, n):
        if 2 * m + 1 == n:
            two, _ = disjoint_union(chain(m), chain(m))
            F.append((f"2x{m}-chain + common bottom",
                      ordinal_sum(antichain(1), (two, 2 * m))))
            F.append((f"2x{m}-chain + common top",
                      ordinal_sum((two, 2 * m), antichain(1))))
    return [(nm, (r, m)) for nm, (r, m) in F if m == n]


def compositions(n):
    for cuts in itertools.product([0, 1], repeat=n - 1):
        comp, c = [], 1
        for b in cuts:
            if b:
                comp.append(c)
                c = 1
            else:
                c += 1
        comp.append(c)
        yield comp


# ---------------------------------------------------------------------------
# Driver

CONTROLS = ["F0_note", "F1_conj", "F2_nosgn", "F3_count", "F4_nopar"]


def _work(args):
    rel, n, name = args
    t = time.time()
    res = pj.analyse(rel, n, name=name)
    res["seconds"] = time.time() - t
    return res


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=7)
    ap.add_argument("--jobs", type=int,
                    default=int(os.environ.get("POGO_WORKER_CORES", "1")))
    ap.add_argument("--tsv")
    a = ap.parse_args(argv)
    pj.automorphisms = automorphisms_fast  # verified equal in the tests

    t0 = time.time()
    posets = unlabeled_posets(a.n)
    print("unlabeled poset counts (fast canonical form):",
          {k: len(posets[k]) for k in range(1, a.n + 1)})
    print(f"enumeration: {time.time() - t0:.1f}s")
    n = a.n
    code_to_id = {canonical_fast(rel, n): f"n{n}_{k:04d}" for k, rel in enumerate(posets[n])}
    fam = {}
    for nm, (rel, m) in families(n):
        assert pj.is_poset(rel, m), nm
        fam.setdefault(code_to_id[canonical_fast(rel, m)], []).append(nm)

    t1 = time.time()
    jobs = [(rel, n, f"n{n}_{k:04d}") for k, rel in enumerate(posets[n])]
    with Pool(max(1, a.jobs)) as pool:
        results = pool.map(_work, jobs, chunksize=4)
    wall = time.time() - t1
    for r in results:
        r["family"] = "; ".join(fam.get(r["name"], []))

    pj.summarize(results, sys.stdout)
    pairs = [(r, c) for r in results for c in r["classes"]]
    print(f"nonidentity pairs: {sum(1 for _, c in pairs if c['rep'] != 'id')}")
    print("control rejections at n=%d (pairs / posets):" % n)
    for f in CONTROLS:
        bad = [(r["name"], c["rep"]) for r, c in pairs if not c["ok"][f]]
        print(f"  {f:9s} {len(bad):5d} / {len({b[0] for b in bad}):4d}")
    print("pairs with nonzero character at g != id:",
          sum(1 for _, c in pairs if c["rep"] != "id" and c["lhs"] != 0))

    print("\nDISCRIMINATING pairs (some wrong control F1-F4 other than F4 fails):")
    for r, c in pairs:
        bad = [f for f in CONTROLS[1:4] if not c["ok"][f]]
        if bad:
            print(f"  {r['name']} [{r['family'] or '-'}] covers="
                  f"{' '.join(f'{x}<{y}' for x, y in r['covers']) or '-'} "
                  f"|Aut|={r['aut_order']} |OP|={r['num_OP']} e_C={r['num_cyc']} "
                  f"g={c['rep']} sgn={c['sgn']:+d} mu={c['mu']:+d} "
                  f"#fix={c['num_fixed_classes']} rot={c['rotations']} "
                  f"lhs={c['lhs']:+d} rhs={c['rhs']} fails={','.join(bad)}")

    print("\nNamed symmetric families:")
    for r in results:
        if r["family"]:
            nz = [(c["rep"], c["lhs"]) for c in r["classes"] if c["rep"] != "id" and c["lhs"]]
            print(f"  {r['name']} {r['family']}: |Aut|={r['aut_order']} "
                  f"|OP|={r['num_OP']} e_C={r['num_cyc']} classes={len(r['classes'])} "
                  f"F0 ok={all(c['ok']['F0_note'] for c in r['classes'])} "
                  f"nonzero g!=id: {nz or 'none'}")

    secs = sorted(r["seconds"] for r in results)
    print(f"\ntiming: analyse() wall {wall:.1f}s on {a.jobs} workers; per poset "
          f"median {secs[len(secs) // 2]:.2f}s, max {secs[-1]:.2f}s, "
          f"sum {sum(secs):.1f}s CPU")
    slow = sorted(results, key=lambda r: -r["seconds"])[:3]
    print("  slowest:", ", ".join(f"{r['name']}(|OP|={r['num_OP']}, |Aut|={r['aut_order']},"
                                 f" {r['seconds']:.1f}s)" for r in slow))
    if a.tsv:
        with open(a.tsv, "w") as f:
            rows = pj.tsv_rows(results)
            head = next(rows)
            f.write("\t".join(head + ["family"]) + "\n")
            for r in results:
                for _ in r["classes"]:
                    f.write("\t".join(map(str, next(rows) + [r["family"] or "-"])) + "\n")
    allok = all(c["ok"]["F0_note"] for _, c in pairs)
    print(f"ALL F0 (note's identity) CHECKS PASS at n={n}: {allok}")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
