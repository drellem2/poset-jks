#!/usr/bin/env python3
"""Independent check of the poset-JKS character identity (eq. characterconj).

For a poset P on [n] and g in Aut(P) the note conjectures

    (-1)^(n-3) mu(OP(P)^g) = sgn(g) * sum_{C in Cyc(P), gC = C} zeta^(r_g(C)).

Plain Python 3, no dependencies.  Run `python3 poset_jks_check.py --help`.

Conventions (all 0-based internally, printed 1-based):
  * A poset is a frozenset of strict relations (i, j) meaning i <_P j,
    transitively closed.
  * A permutation p is a tuple with p[i] = image of i; composition is
    (p*q)[i] = p[q[i]], i.e. q acts first.
  * A word / linear extension w = w_1...w_n is the permutation
    position -> label, w[i] = w_{i+1}.  w is a linear extension iff
    a <_P b implies a occurs before b in w.
  * gamma = (1 2 ... n), gamma[i] = i+1 mod n.  Hence (w*gamma^j)[i] =
    w[i+j]: right multiplication by gamma^j rotates the word LEFT by j
    (acts on positions).  g in Aut(P) acts on words by g*w (relabels
    letters, acts on values).
  * For a g-fixed cyclic class C and w in C, r_g(C) is the unique r in Z/n
    with g*w = w*gamma^r.  It does not depend on w in C.
  * e_zeta = (1/n) sum_j zeta^(-j) gamma^j with zeta = exp(2 pi i / n).
    Then gamma^r e_zeta = zeta^r e_zeta, so g (w e_zeta) = zeta^r (w e_zeta).
    This is verified numerically, not assumed (see lie_trace_explicit).
"""

import argparse
import cmath
import itertools
import json
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction

# ---------------------------------------------------------------------------
# Posets


def transitive_closure(rel, n):
    rel = set(rel)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(rel):
            for (c, d) in list(rel):
                if b == c and (a, d) not in rel:
                    rel.add((a, d))
                    changed = True
    return frozenset(rel)


def is_poset(rel, n):
    if any(a == b for a, b in rel):
        return False
    if any((b, a) in rel for a, b in rel):
        return False
    return transitive_closure(rel, n) == frozenset(rel)


def relabel(rel, p):
    return frozenset((p[a], p[b]) for a, b in rel)


def rel_code(rel, n):
    return sum(1 << (a * n + b) for a, b in rel)


def canonical(rel, n, perms):
    """Minimal bitmask code over all relabelings (perms = all of S_n)."""
    return min(rel_code(relabel(rel, p), n) for p in perms)


def from_code(code, n):
    return frozenset((k // n, k % n) for k in range(n * n) if code >> k & 1)


def covers(rel):
    return sorted((a, b) for a, b in rel
                  if not any((a, c) in rel and (c, b) in rel for c in {x for _, x in rel}))


def is_connected(rel, n):
    adj = defaultdict(set)
    for a, b in rel:
        adj[a].add(b)
        adj[b].add(a)
    seen, stack = {0}, [0]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == n


def unlabeled_posets_by_extension(nmax):
    """Method A: every poset on n+1 points is a poset on n points plus a new
    maximal element whose down-set is an order ideal.  Dedupe by canonical form."""
    out = {0: [frozenset()]}
    for n in range(0, nmax):
        perms = list(itertools.permutations(range(n + 1)))
        seen = {}
        for rel in out[n]:
            for mask in range(1 << n):
                down = [i for i in range(n) if mask >> i & 1]
                # order ideal: closed downward
                if any((a, b) in rel and not mask >> a & 1 for b in down for a in range(n)):
                    continue
                new = frozenset(rel) | {(i, n) for i in down}
                c = canonical(new, n + 1, perms)
                if c not in seen:
                    seen[c] = from_code(c, n + 1)
        out[n + 1] = [seen[c] for c in sorted(seen)]
    return out


def poset_counts_bruteforce(n):
    """Method B (control): enumerate naturally labeled posets (i <_P j => i < j)
    as transitively closed subsets of {(i,j): i<j}; count labeled posets as the
    distinct relabelings and unlabeled ones as distinct canonical forms."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    perms = list(itertools.permutations(range(n)))
    natural, labeled, unlabeled = 0, set(), set()
    for mask in range(1 << len(pairs)):
        rel = frozenset(p for k, p in enumerate(pairs) if mask >> k & 1)
        if transitive_closure(rel, n) != rel:
            continue
        natural += 1
        codes = [rel_code(relabel(rel, p), n) for p in perms]
        labeled.update(codes)
        unlabeled.add(min(codes))
    return natural, len(labeled), len(unlabeled)


# ---------------------------------------------------------------------------
# Permutations


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    inv = [0] * len(p)
    for i, x in enumerate(p):
        inv[x] = i
    return tuple(inv)


def sign(p):
    s, seen = 1, [False] * len(p)
    for i in range(len(p)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s


def cycles(p):
    seen, out = [False] * len(p), []
    for i in range(len(p)):
        if not seen[i]:
            c, j = [], i
            while not seen[j]:
                seen[j] = True
                c.append(j)
                j = p[j]
            out.append(c)
    return out


def cycle_str(p):
    cs = [c for c in cycles(p) if len(c) > 1]
    return "".join("(" + " ".join(str(x + 1) for x in c) + ")" for c in cs) or "id"


def cycle_type(p):
    return tuple(sorted((len(c) for c in cycles(p)), reverse=True))


def automorphisms(rel, n):
    return [p for p in itertools.permutations(range(n)) if relabel(rel, p) == rel]


def conjugacy_classes(G):
    Gset, done, classes = set(G), set(), []
    for g in sorted(G):
        if g in done:
            continue
        cl = {compose(compose(h, g), inverse(h)) for h in G}
        assert cl <= Gset
        done |= cl
        classes.append(sorted(cl))
    return classes


# ---------------------------------------------------------------------------
# Order-preserving partitions and Moebius numbers


def set_partitions(n):
    """Restricted growth strings -> tuple block-id per element."""
    def rec(prefix, m):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for b in range(m + 1):
            yield from rec(prefix + [b], max(m, b + 1))
    if n == 0:
        yield ()
        return
    yield from rec([0], 1)


def blocks_of(rgs):
    d = defaultdict(list)
    for i, b in enumerate(rgs):
        d[b].append(i)
    return frozenset(frozenset(v) for v in d.values())


def is_order_preserving(rgs, rel):
    """P/pi acyclic: digraph on blocks with B->B' when x<y, x in B, y in B',
    B != B', has no directed cycle."""
    k = max(rgs) + 1 if rgs else 0
    adj = defaultdict(set)
    for a, b in rel:
        if rgs[a] != rgs[b]:
            adj[rgs[a]].add(rgs[b])
    state = [0] * k  # 0 new, 1 on stack, 2 done
    def dfs(u):
        state[u] = 1
        for v in adj[u]:
            if state[v] == 1 or (state[v] == 0 and not dfs(v)):
                return False
        state[u] = 2
        return True
    return all(state[u] or dfs(u) for u in range(k))


def order_preserving_partitions(rel, n):
    return [blocks_of(r) for r in set_partitions(n) if is_order_preserving(r, rel)]


def refines(x, y):
    """x <= y in refinement order: every block of x inside a block of y."""
    return all(any(B <= C for C in y) for B in x)


def act_partition(g, pi):
    return frozenset(frozenset(g[i] for i in B) for B in pi)


def moebius_bottom_top(elems, n):
    """mu(0^, 1^) of the subposet `elems` of Pi_n (must contain the discrete
    and one-block partitions), by the recursion mu(0,x) = -sum_{y<x} mu(0,y)."""
    elems = sorted(elems, key=lambda p: -len(p))  # finer first
    bottom = frozenset(frozenset([i]) for i in range(n))
    top = frozenset([frozenset(range(n))])
    assert elems[0] == bottom and elems[-1] == top
    mu = {}
    for x in elems:
        if x == bottom:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if y != x and len(y) > len(x) and refines(y, x))
    return mu[top]


# ---------------------------------------------------------------------------
# Linear extensions and cyclic classes


def linear_extensions(rel, n):
    out = []
    for w in itertools.permutations(range(n)):
        pos = inverse(w)
        if all(pos[a] < pos[b] for a, b in rel):
            out.append(w)
    return out


def rot(w, j):
    """w * gamma^j : left rotation of the word by j."""
    j %= len(w)
    return w[j:] + w[:j]


def class_rep(w):
    return min(rot(w, j) for j in range(len(w)))


def cyclic_classes(lin):
    return sorted({class_rep(w) for w in lin})


def rotation_amount(g, w):
    """r with g*w = w*gamma^r, or None if g does not fix the class of w."""
    gw = compose(g, w)
    for r in range(len(w)):
        if rot(w, r) == gw:
            return r
    return None


# ---------------------------------------------------------------------------
# Exact arithmetic in Z[zeta_n]


def poly_divmod(num, den):
    """Integer polynomials as coefficient lists (low degree first); den monic."""
    num = list(num)
    q = [0] * max(len(num) - len(den) + 1, 1)
    while len(num) >= len(den) and any(num):
        while num and num[-1] == 0:
            num.pop()
        if len(num) < len(den):
            break
        c = num[-1]
        s = len(num) - len(den)
        q[s] = c
        for i, d in enumerate(den):
            num[s + i] -= c * d
        num.pop()
    while num and num[-1] == 0:
        num.pop()
    return q, num


_CYC = {}


def cyclotomic(n):
    if n not in _CYC:
        p = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0:
                p, r = poly_divmod(p, cyclotomic(d))
                assert not r
        while p and p[-1] == 0:
            p.pop()
        _CYC[n] = p
    return _CYC[n]


def zeta_sum_equals_int(counts, m, n):
    """Is sum_r counts[r] zeta^r == m exactly (zeta primitive n-th root)?"""
    c = list(counts)
    c[0] -= m
    _, rem = poly_divmod(c, cyclotomic(n))
    return not rem


def zeta_sum_value(counts, n):
    z = cmath.exp(2j * cmath.pi / n)
    return sum(c * z ** r for r, c in enumerate(counts))


def as_int_if_rational(counts, n):
    """Return the integer m if sum counts[r] zeta^r is a rational integer."""
    v = zeta_sum_value(counts, n)
    m = round(v.real)
    return m if zeta_sum_equals_int(counts, m, n) else None


# ---------------------------------------------------------------------------
# Explicit group-algebra trace on Lie(P) = span{w e_zeta}


def lie_trace_explicit(g, classes, n):
    """Trace of left multiplication by g on span{u_C e_zeta : C in Cyc(P)},
    computed in C[S_n] with no use of the formula zeta^r.  Returns
    (trace, {C: scalar}) for g-fixed classes."""
    z = cmath.exp(2j * cmath.pi / n)
    gam = tuple((i + 1) % n for i in range(n))
    gpow = [tuple(range(n))]
    for _ in range(n - 1):
        gpow.append(compose(gpow[-1], gam))
    idx = {u: k for k, u in enumerate(classes)}
    tr, scal = 0, {}
    for u in classes:
        # g * u * e_zeta = (1/n) sum_j zeta^{-j} (g u gamma^j)
        vec = defaultdict(complex)
        for j in range(n):
            vec[compose(compose(g, u), gpow[j])] += z ** (-j) / n
        # basis vector b_C = u_C e_zeta has coefficient 1/n at u_C itself
        target = class_rep(compose(g, u))
        assert target in idx, "g does not preserve Cyc(P)"
        lam = vec[target] * n  # coefficient of b_target
        # verify g u e_zeta == lam * b_target on the whole support
        for j in range(n):
            assert abs(vec[compose(target, gpow[j])] - lam * z ** (-j) / n) < 1e-9
        if target == u:
            tr += lam
            scal[u] = lam
    return tr, scal


# ---------------------------------------------------------------------------
# Per-poset computation


FORMULAS = {
    # name: description, function(sgn, counts_plus, counts_minus, nfixed) -> integer or None
    "F0_note": "sgn(g) * sum zeta^{r_g(C)}   [note, eq. characterconj]",
    "F1_conj": "sgn(g) * sum zeta^{-r_g(C)}  [opposite Fourier/rotation convention]",
    "F2_nosgn": "sum zeta^{r_g(C)}            [WRONG: sign twist dropped]",
    "F3_count": "sgn(g) * #{C : gC = C}       [WRONG: phase dropped]",
    "F4_nopar": "LHS without (-1)^{n-3}, vs F0 [WRONG: degree sign dropped]",
}


def analyse(rel, n, name="", all_elements=True, explicit=True):
    G = automorphisms(rel, n)
    classes_G = conjugacy_classes(G)
    OP = order_preserving_partitions(rel, n)
    lin = linear_extensions(rel, n)
    cyc = cyclic_classes(lin)
    res = {
        "name": name, "n": n,
        "covers": [(a + 1, b + 1) for a, b in covers(rel)],
        "connected": is_connected(rel, n) if n else True,
        "aut_order": len(G), "num_OP": len(OP), "num_lin": len(lin),
        "num_cyc": len(cyc), "classes": [],
    }
    sgnpar = (-1) ** ((n - 3) % 2)

    def rhs_data(g):
        counts = [0] * max(n, 1)
        for u in cyc:
            r = rotation_amount(g, u)
            if r is not None:
                counts[r] += 1
        return counts

    for cl in classes_G:
        g = cl[0]
        fixed = [pi for pi in OP if act_partition(g, pi) == pi]
        mu = moebius_bottom_top(fixed, n) if n else 1
        lhs = sgnpar * mu
        counts = rhs_data(g)
        s = sign(g)
        nfix = sum(counts)
        neg = [counts[0]] + counts[1:][::-1]
        zc = as_int_if_rational(counts, n) if n else 1
        zn = as_int_if_rational(neg, n) if n else 1
        F = {  # None: the zeta-sum is not a rational integer
            "F0_note": None if zc is None else s * zc,
            "F1_conj": None if zn is None else s * zn,
            "F2_nosgn": zc,
            "F3_count": s * nfix,
        }
        # exact checks (None means the zeta-sum is not even rational)
        ok = {
            "F0_note": n == 0 or zeta_sum_equals_int(counts, s * lhs, n),
            "F1_conj": n == 0 or zeta_sum_equals_int(neg, s * lhs, n),
            "F2_nosgn": n == 0 or zeta_sum_equals_int(counts, lhs, n),
            "F3_count": s * nfix == lhs,
            "F4_nopar": n == 0 or zeta_sum_equals_int(counts, s * mu, n),
        }
        # class-function check of the RHS over the whole conjugacy class
        if all_elements:
            v = zeta_sum_value(counts, n)
            for h in cl[1:]:
                assert abs(zeta_sum_value(rhs_data(h), n) - v) < 1e-9, \
                    "RHS not a class function"
        if explicit and n >= 1:
            tr, scal = lie_trace_explicit(g, cyc, n)
            z = cmath.exp(2j * cmath.pi / n)
            for u, lam in scal.items():
                assert abs(lam - z ** rotation_amount(g, u)) < 1e-9, "convention mismatch"
            assert abs(tr - zeta_sum_value(counts, n)) < 1e-9
        res["classes"].append({
            "rep": cycle_str(g), "cycle_type": list(cycle_type(g)), "size": len(cl),
            "sgn": s, "num_fixed_OP": len(fixed), "mu": mu,
            "num_fixed_classes": nfix,
            "rotations": {str(r): c for r, c in enumerate(counts) if c},
            "lhs": lhs, "rhs": F["F0_note"], "values": F, "ok": ok,
        })
    return res


# ---------------------------------------------------------------------------
# Named n = 6 examples


def named_examples():
    star_up = frozenset((0, i) for i in range(1, 6))     # 1 below five arms
    star_down = frozenset((i, 0) for i in range(1, 6))   # 1 above five arms
    k33 = frozenset((a, b) for a in range(3) for b in range(3, 6))
    chains = frozenset([(0, 1), (2, 3), (4, 5)])
    return [("star5_up (1 < 2,3,4,5,6)", star_up),
            ("star5_down (2,3,4,5,6 < 1)", star_down),
            ("K33 ({1,2,3} < {4,5,6})", k33),
            ("3x2chain (1<2, 3<4, 5<6)", chains)]


# ---------------------------------------------------------------------------
# Output


def tsv_rows(results):
    yield ["poset_id", "n", "covers", "connected", "aut", "num_OP", "num_lin",
           "e_C", "class_rep", "cycle_type", "class_size", "sgn", "num_fixed_OP",
           "mu_OP_g", "num_fixed_classes", "rotation_multiset", "lhs", "rhs",
           "match", "F1_conj_ok", "F2_nosgn_ok", "F3_count_ok", "F4_nopar_ok"]
    for res in results:
        for c in res["classes"]:
            yield [res["name"], res["n"],
                   " ".join(f"{a}<{b}" for a, b in res["covers"]) or "-",
                   int(res["connected"]), res["aut_order"], res["num_OP"],
                   res["num_lin"], res["num_cyc"], c["rep"],
                   ",".join(map(str, c["cycle_type"])), c["size"], c["sgn"],
                   c["num_fixed_OP"], c["mu"], c["num_fixed_classes"],
                   ",".join(f"{r}^{m}" for r, m in c["rotations"].items()) or "-",
                   c["lhs"], c["rhs"], int(c["ok"]["F0_note"]),
                   int(c["ok"]["F1_conj"]), int(c["ok"]["F2_nosgn"]),
                   int(c["ok"]["F3_count"]), int(c["ok"]["F4_nopar"])]


def summarize(results, out):
    by_n = defaultdict(list)
    for r in results:
        by_n[r["n"]].append(r)
    for n in sorted(by_n):
        rs = by_n[n]
        ncl = sum(len(r["classes"]) for r in rs)
        print(f"n={n}: {len(rs)} posets, {ncl} (poset, conjugacy class) pairs", file=out)
        for f in ["F0_note", "F1_conj", "F2_nosgn", "F3_count", "F4_nopar"]:
            bad = [(r["name"], c["rep"]) for r in rs for c in r["classes"] if not c["ok"][f]]
            badp = sorted({b[0] for b in bad})
            print(f"  {f:9s} fails on {len(bad):4d} pairs / {len(badp):3d} posets"
                  f"   ({FORMULAS[f]})", file=out)
        js_bad = [r["name"] for r in rs
                  if r["classes"][0]["rep"] == "id" and r["classes"][0]["lhs"] != r["num_cyc"]]
        conn_bad = [r["name"] for r in rs if r["connected"] and r["num_cyc"] != r["num_lin"]]
        disc = [r["name"] for r in rs if not r["connected"] and r["num_cyc"] != r["num_lin"]]
        print(f"  JS dim (-1)^(n-3) mu(OP(P)) == e_C(P): failures {len(js_bad)}", file=out)
        print(f"  connected => e_C == |Lin|: failures {len(conn_bad)}; "
              f"disconnected posets with e_C != |Lin|: {len(disc)}", file=out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--nmax", type=int, default=5, help="all unlabeled posets with n <= NMAX")
    ap.add_argument("--nmin", type=int, default=1)
    ap.add_argument("--examples", action="store_true", help="also run the named n=6 examples")
    ap.add_argument("--control-counts", action="store_true",
                    help="cross-check poset counts by brute force (n <= 5)")
    ap.add_argument("--tsv", help="write the per-class table here")
    ap.add_argument("--json", help="write full results as JSON here")
    ap.add_argument("--no-explicit", action="store_true",
                    help="skip the explicit C[S_n] trace check (faster)")
    a = ap.parse_args(argv)

    t0 = time.time()
    posets = unlabeled_posets_by_extension(a.nmax)
    print("unlabeled poset counts by extension method:",
          {n: len(posets[n]) for n in range(1, a.nmax + 1)})
    if a.control_counts:
        for n in range(1, min(a.nmax, 5) + 1):
            nat, lab, unl = poset_counts_bruteforce(n)
            print(f"  brute force n={n}: naturally labeled {nat}, labeled {lab}, unlabeled {unl}")

    results = []
    for n in range(a.nmin, a.nmax + 1):
        for k, rel in enumerate(posets[n]):
            results.append(analyse(rel, n, name=f"n{n}_{k:03d}",
                                   explicit=not a.no_explicit))
    if a.examples:
        for nm, rel in named_examples():
            assert is_poset(rel, 6)
            results.append(analyse(rel, 6, name=nm, explicit=not a.no_explicit))

    summarize([r for r in results if r["name"].startswith("n")], sys.stdout)
    if a.examples:
        print("named n=6 examples:")
        for r in results:
            if not r["name"].startswith("n"):
                print(f"  {r['name']}: |Aut|={r['aut_order']} |OP|={r['num_OP']} "
                      f"|Lin|={r['num_lin']} e_C={r['num_cyc']}")
                for c in r["classes"]:
                    print(f"    g={c['rep']:16s} sgn={c['sgn']:+d} mu={c['mu']:+d} "
                          f"#fix={c['num_fixed_classes']:3d} rot={c['rotations']} "
                          f"lhs={c['lhs']:+d} rhs={c['rhs']:+d} "
                          f"{'OK' if c['ok']['F0_note'] else 'FAIL'}"
                          f"{'' if c['ok']['F3_count'] else '  [phase-discriminating]'}")
    if a.tsv:
        with open(a.tsv, "w") as f:
            for row in tsv_rows(results):
                f.write("\t".join(map(str, row)) + "\n")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(results, f, indent=1)
    allok = all(c["ok"]["F0_note"] for r in results for c in r["classes"])
    print(f"ALL F0 (note's identity) CHECKS PASS: {allok}")
    print(f"[{time.time() - t0:.1f}s]", file=sys.stderr)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
