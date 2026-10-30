#!/usr/bin/env python3
"""Checks for notes/global_module_operations_plethlog.md (mg-266cf).

Sections (each can be run alone; all are run by default):

  --theorem NMAX   For every unlabeled poset P with n <= NMAX and every
                   conjugacy class of Aut(P), check each step of the proof
                   of the character identity (characterconj) given in the
                   notes file (section 2):
                     T1  the orbit partition O_g is order-preserving;
                     T2  {x in OP(P)^g : x v O_g = 1^}  ==  X(P, g), the
                         partitions of the component set permuted
                         transitively by g;
                     T3  Weisner recursion  mu(OP(P)^g) =
                         - sum_{x in X(P,g), x != 1^} mu(OP(P|B0)^(g^m));
                     T4  closed formula  (-1)^(n-3) sgn(g) mu(OP(P)^g)
                         = mu(o) * sum_{x fundamental} e_C(P|B0)
                         = sum_{gC=C} zeta^(r_g(C))     (both sides);
                     T5  e_C(P) = sum_pi mu_Pi(pi,1^) prod_T |Lin(P|T)|
                         over partitions pi of the component set.
                   Also runs T1-T4 on a few larger examples (n = 7, 8),
                   for g != 1 only.
  --homology NMAX  Direct top homology (kernel of the top boundary map of
                   the order complex, mod a large prime) for every unlabeled
                   P with n <= NMAX <= 6, traces of every g in Aut(P), and
                   the induced character of the global module HH_n,
                   compared with eq. (frob) (sign-twisted) and with the
                   untwisted formula (positive control).
  --hopf NMAX      Primitive part of the Hopf monoid Q of posets with a
                   chosen linear extension, n <= NMAX <= 4: dimension and
                   S_n-character, compared with ch V_n.
  --bracket NMAX   Does the commutator of concatenations,
                   W_P x W_Q -> W_{P+Q}, descend to
                   Lie(P) x Lie(Q) -> Lie(P+Q)  (e_zeta model)?

Plain Python 3; imports the reproduction script poset_jks_check.py.
"""

import argparse
import itertools
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from math import factorial, gcd

from poset_jks_check import (
    act_partition, as_int_if_rational, automorphisms, blocks_of, compose,
    conjugacy_classes, cycle_str, cycle_type, cyclic_classes, inverse,
    is_poset, linear_extensions, moebius_bottom_top,
    order_preserving_partitions, refines, rotation_amount, set_partitions,
    sign, transitive_closure, unlabeled_posets_by_extension)

PRIME = 2147483647  # 2^31 - 1

# ---------------------------------------------------------------------------
# Small helpers


def mobius(k):
    res, p = 1, 2
    while p * p <= k:
        if k % p == 0:
            k //= p
            if k % p == 0:
                return 0
            res = -res
        p += 1
    return -res if k > 1 else res


def order(g):
    e, k = tuple(range(len(g))), 1
    h = g
    while h != e:
        h = compose(g, h)
        k += 1
    return k


def power(g, k):
    h = tuple(range(len(g)))
    for _ in range(k):
        h = compose(g, h)
    return h


def components(rel, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in rel:
        parent[find(a)] = find(b)
    d = defaultdict(set)
    for i in range(n):
        d[find(i)].add(i)
    return sorted((frozenset(v) for v in d.values()), key=min)


def restrict(rel, B):
    """P|B relabeled to 0..k-1 in increasing order; returns (rel, labels)."""
    lab = sorted(B)
    idx = {x: i for i, x in enumerate(lab)}
    return frozenset((idx[a], idx[b]) for a, b in rel if a in idx and b in idx), lab


def restrict_perm(g, lab):
    idx = {x: i for i, x in enumerate(lab)}
    return tuple(idx[g[x]] for x in lab)


def e_C(rel, n):
    return len(cyclic_classes(linear_extensions(rel, n)))


def orbit_partition(g):
    n = len(g)
    seen, out = set(), []
    for i in range(n):
        if i not in seen:
            orb, j = set(), i
            while j not in orb:
                orb.add(j)
                j = g[j]
            seen |= orb
            out.append(frozenset(orb))
    return frozenset(out)


def partition_join(x, y, n):
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for B in itertools.chain(x, y):
        B = list(B)
        for b in B[1:]:
            parent[find(b)] = find(B[0])
    d = defaultdict(set)
    for i in range(n):
        d[find(i)].add(i)
    return frozenset(frozenset(v) for v in d.values())


def is_op(pi, rel):
    blk = {}
    for k, B in enumerate(pi):
        for x in B:
            blk[x] = k
    adj = defaultdict(set)
    for a, b in rel:
        if blk[a] != blk[b]:
            adj[blk[a]].add(blk[b])
    state = {}

    def dfs(u):
        state[u] = 1
        for v in adj[u]:
            s = state.get(v, 0)
            if s == 1 or (s == 0 and not dfs(v)):
                return False
        state[u] = 2
        return True
    return all(state.get(u) or dfs(u) for u in range(len(pi)))


def mu_fixed(rel, n, g):
    if n <= 1:
        return 1
    OP = order_preserving_partitions(rel, n)
    return moebius_bottom_top([p for p in OP if act_partition(g, p) == p], n)


def lie_value(rel, n, g, cyc=None):
    """sum over g-fixed cyclic classes of zeta^{r_g(C)}, as an exact integer."""
    if cyc is None:
        cyc = cyclic_classes(linear_extensions(rel, n))
    counts = [0] * n
    for u in cyc:
        r = rotation_amount(g, u)
        if r is not None:
            counts[r] += 1
    v = as_int_if_rational(counts, n)
    assert v is not None
    return v


def transitive_component_partitions(comps, g):
    """X(P,g): partitions of the component set, invariant under g, with g
    transitive on blocks.  Returned as partitions of [n]."""
    k = len(comps)
    cidx = {}
    for i, C in enumerate(comps):
        for x in C:
            cidx[x] = i
    gc = [cidx[g[min(C)]] for C in comps]  # action on component indices
    out = []
    for rgs in set_partitions(k):
        blocks = [frozenset(i for i in range(k) if rgs[i] == b) for b in range(max(rgs) + 1)]
        bset = set(blocks)
        img = {B: frozenset(gc[i] for i in B) for B in blocks}
        if any(img[B] not in bset for B in blocks):
            continue
        orb, B = {blocks[0]}, img[blocks[0]]
        while B not in orb:
            orb.add(B)
            B = img[B]
        if len(orb) != len(blocks):
            continue
        out.append(frozenset(frozenset().union(*(comps[i] for i in B)) for B in blocks))
    return out


def closed_formula(rel, n, g, comps=None, use_mu=True):
    """mu(o) * sum over fundamental-domain partitions x of e_C(P|B0);
    0 unless <g> acts freely on the components."""
    if comps is None:
        comps = components(rel, n)
    o = order(g)
    cidx = {}
    for i, C in enumerate(comps):
        for x in C:
            cidx[x] = i
    gc = tuple(cidx[g[min(C)]] for C in comps)
    # free action of <g> on components: every component orbit has size o
    orbits, seen = [], set()
    for i in range(len(comps)):
        if i in seen:
            continue
        orb, j = [], i
        while j not in orb:
            orb.append(j)
            j = gc[j]
        seen |= set(orb)
        if len(orb) != o:
            return 0
        orbits.append(orb)
    total = 0
    for choice in itertools.product(*orbits):
        B0 = frozenset().union(*(comps[i] for i in choice))
        sub, _ = restrict(rel, B0)
        total += e_C(sub, len(B0))
    assert total % o == 0  # each x counted o times (B0 -> g^j B0)
    return (mobius(o) if use_mu else 1) * (total // o)


def ec_component_formula(rel, n):
    comps = components(rel, n)
    k = len(comps)
    tot = 0
    for rgs in set_partitions(k):
        m = max(rgs) + 1
        prod = 1
        for b in range(m):
            T = frozenset().union(*(comps[i] for i in range(k) if rgs[i] == b))
            sub, _ = restrict(rel, T)
            prod *= len(linear_extensions(sub, len(T)))
        tot += (-1) ** (m - 1) * factorial(m - 1) * prod
    return tot


# ---------------------------------------------------------------------------
# Section: theorem steps


def check_theorem_steps(rel, n, g, OP=None, cyc=None, comps=None, stats=None):
    """Run T1-T4 for (P, g).  Returns dict of booleans."""
    if OP is None:
        OP = order_preserving_partitions(rel, n)
    if comps is None:
        comps = components(rel, n)
    fixed = [p for p in OP if act_partition(g, p) == p]
    fixed_set = set(fixed)
    bottom = frozenset(frozenset([i]) for i in range(n))
    top = frozenset([frozenset(range(n))])
    mu = moebius_bottom_top(fixed, n)
    res = {}
    lhs = (-1) ** (n - 3) * sign(g) * mu
    L = lie_value(rel, n, g, cyc)
    res["T4_lie"] = (lhs == L)
    res["T4_formula"] = (lhs == closed_formula(rel, n, g, comps))
    # positive control: the same formula without the factor mu(o) must fail
    res["control_no_mu"] = (lhs == closed_formula(rel, n, g, comps, use_mu=False))
    if g == tuple(range(n)):
        return res, lhs
    Og = orbit_partition(g)
    res["T1"] = is_op(Og, rel) and Og in fixed_set
    # join in OP^g: least fixed upper bound
    X_join = set()
    for x in fixed:
        ubs = [y for y in fixed if refines(x, y) and refines(Og, y)]
        least = [y for y in ubs if all(refines(y, z) for z in ubs)]
        assert len(least) == 1, "OP(P)^g is not a lattice?"
        # T1': the join is the partition join
        assert least[0] == partition_join(x, Og, n)
        if least[0] == top:
            X_join.add(x)
    X = transitive_component_partitions(comps, g)
    res["T2"] = (X_join == set(X))
    # T3: Weisner recursion via direct mu of the restricted posets
    rec = 0
    for x in X:
        if x == top:
            continue
        m = len(x)
        B0 = min(x, key=min)
        sub, lab = restrict(rel, B0)
        h = restrict_perm(power(g, m), lab)
        rec -= mu_fixed(sub, len(B0), h)
    res["T3"] = (rec == mu)
    return res, lhs


def extra_examples():
    def chains(lengths):
        rel, base = set(), 0
        for L in lengths:
            for i in range(L):
                for j in range(i + 1, L):
                    rel.add((base + i, base + j))
            base += L
        return frozenset(rel)
    V2 = frozenset([(0, 1), (0, 2), (3, 4), (3, 5)])  # two V's on 6
    ex = [
        ("antichain_7", 7, frozenset()),
        ("2-chains x3 + point", 7, chains([2, 2, 2, 1])),
        ("2-chains x4", 8, chains([2, 2, 2, 2])),
        ("4-chains x2", 8, chains([4, 4])),
        ("V x2 + 2-chain", 8, V2 | {(6, 7)}),
    ]
    return ex


def section_theorem(nmax):
    print(f"== theorem steps T1-T5, all unlabeled posets with n <= {nmax} ==")
    t0 = time.time()
    posets = unlabeled_posets_by_extension(nmax)
    tally = Counter()
    fails = []
    for n in range(1, nmax + 1):
        npairs = 0
        for rel in posets[n]:
            OP = order_preserving_partitions(rel, n)
            cyc = cyclic_classes(linear_extensions(rel, n))
            comps = components(rel, n)
            ec = len(cyc)
            ok5 = ec_component_formula(rel, n) == ec
            tally["T5", ok5] += 1
            if not ok5:
                fails.append(("T5", n, sorted(rel)))
            G = automorphisms(rel, n)
            for cl in conjugacy_classes(G):
                g = cl[0]
                res, _ = check_theorem_steps(rel, n, g, OP, cyc, comps)
                npairs += 1
                for k, v in res.items():
                    tally[k, v] += 1
                    if not v and not k.startswith("control"):
                        fails.append((k, n, sorted(rel), cycle_str(g)))
        print(f"  n={n}: {len(posets[n])} posets, {npairs} (poset, class) pairs")
    for key in ["T1", "T2", "T3", "T4_lie", "T4_formula", "T5", "control_no_mu"]:
        print(f"  {key:13s}: pass {tally[key, True]:5d}   fail {tally[key, False]}")
    if tally["control_no_mu", False] == 0:
        fails.append(("positive control did not fire",))
    print("== larger examples (g != 1 only) ==")
    for name, n, rel in extra_examples():
        assert is_poset(rel, n)
        OP = order_preserving_partitions(rel, n)
        cyc = cyclic_classes(linear_extensions(rel, n))
        comps = components(rel, n)
        G = automorphisms(rel, n)
        for cl in conjugacy_classes(G):
            g = cl[0]
            if g == tuple(range(n)):
                continue
            res, lhs = check_theorem_steps(rel, n, g, OP, cyc, comps)
            res.pop("control_no_mu")
            allok = all(res.values())
            if not allok:
                fails.append(("example", name, cycle_str(g), res))
            print(f"  {name:22s} n={n} g={cycle_str(g):24s} "
                  f"(-1)^(n-3)sgn*mu={lhs:+d}  {'OK' if allok else 'FAIL ' + str(res)}")
    print(f"  failures: {fails if fails else 'none'}   [{time.time() - t0:.1f}s]")
    return not fails


# ---------------------------------------------------------------------------
# Section: direct homology and the global module


def rank_rows_mod(rows, ncols, p=PRIME):
    """Row-reduce sparse rows (dict col -> value) mod p.  Returns the RREF as
    {pivot column: row}; every row has a 1 at its pivot and no entry in any
    other pivot column."""
    piv = {}
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        for c in [c for c in r if c in piv]:
            f = r.get(c, 0)
            if not f:
                continue
            for cc, vv in piv[c].items():
                x = (r.get(cc, 0) - f * vv) % p
                if x:
                    r[cc] = x
                else:
                    r.pop(cc, None)
        if not r:
            continue
        c0 = min(r)
        inv = pow(r[c0], p - 2, p)
        r = {c: v * inv % p for c, v in r.items()}
        for prow in piv.values():
            f = prow.get(c0)
            if f:
                for cc, vv in r.items():
                    x = (prow.get(cc, 0) - f * vv) % p
                    if x:
                        prow[cc] = x
                    else:
                        prow.pop(cc, None)
        piv[c0] = r
    return piv


def kernel_trace(piv, ncols, perm_cols, p=PRIME):
    """Trace on {x : Rx = 0} of the coordinate permutation c -> perm_cols[c]
    ((tau x)_{perm[c]} = x_c).  Uses free-coordinate projection."""
    free = [c for c in range(ncols) if c not in piv]
    pivset = set(piv)
    # k_f = e_f - sum_{pivot c} R[c][f] e_c ; coefficient of k_f in tau k_f is
    # the f-coordinate of tau k_f = (k_f)_{perm^{-1}(f)}
    invp = [0] * ncols
    for c, d in enumerate(perm_cols):
        invp[d] = c
    tr = 0
    for f in free:
        c = invp[f]
        if c == f:
            tr += 1
        elif c in pivset:
            tr -= piv[c].get(f, 0)
    tr %= p
    return tr - p if tr > p // 2 else tr


def top_homology_traces(rel, n, gs):
    """Direct computation: H_P = ker(d: C_{n-3} -> C_{n-4}) of the order
    complex of the proper part of OP(P).  Returns (dim, {g: trace})."""
    OP = order_preserving_partitions(rel, n)
    proper = [x for x in OP if 1 < len(x) < n]
    bylev = defaultdict(list)
    for x in proper:
        bylev[len(x)].append(x)
    # top chains: one element at each level n-1, ..., 2
    up = {x: [y for y in bylev[len(x) - 1] if refines(x, y)] for x in proper}
    chains = [[x] for x in bylev[n - 1]]
    for lev in range(n - 2, 1, -1):
        chains = [c + [y] for c in chains for y in up[c[-1]]]
    chains = [tuple(c) for c in chains]
    cidx = {c: i for i, c in enumerate(chains)}
    N = len(chains)
    # boundary: d(c) = sum_i (-1)^i (c minus i-th element)
    faces = {}
    rows = defaultdict(dict)  # face -> {chain: coeff}; constraint rows
    for j, c in enumerate(chains):
        for i in range(len(c)):
            f = c[:i] + c[i + 1:]
            fi = faces.setdefault(f, len(faces))
            rows[fi][j] = rows[fi].get(j, 0) + (-1) ** i
    piv = rank_rows_mod(list(rows.values()), N)
    dim = N - len(piv)
    traces = {}
    for g in gs:
        perm = [cidx[tuple(act_partition(g, x) for x in c)] for c in chains]
        traces[g] = kernel_trace(piv, N, perm)
    return dim, traces


def frob_prediction(n, b, lam, twisted=True):
    """Character value of sgn^tw (x) Ind_{C_n}^{S_n}(zeta (x) C[B_n]) on class lam."""
    if len(set(lam)) != 1:
        return 0
    d = lam[0]
    z = 1
    for part, mult in Counter(lam).items():
        z *= part ** mult * factorial(mult)
    val = Fraction(z * mobius(d) * b[n // d], n)
    assert val.denominator == 1
    s = (-1) ** (n - len(lam)) if twisted else 1
    return s * int(val)


def bn_values(nmax):
    """b_n = n [x^n] log A(x), A from naturally labeled posets (brute force)."""
    a = [1]
    for n in range(1, nmax + 1):
        cnt = 0
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        # naturally labeled posets: transitively closed subsets of pairs i<j
        for mask in range(1 << len(pairs)):
            rel = {pairs[k] for k in range(len(pairs)) if mask >> k & 1}
            if all((a_, d) in rel for (a_, b_) in rel for (c, d) in rel if b_ == c):
                cnt += 1
        a.append(cnt)
    # log A coefficients: n l_n = n a_n - sum_{k=1}^{n-1} k l_k a_{n-k}
    l = [Fraction(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        l[n] = Fraction(n * a[n] - sum(k * l[k] * a[n - k] for k in range(1, n)), n)
    b = [None] + [int(n * l[n]) for n in range(1, nmax + 1)]
    return a, b


def partitions_of(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions_of(n - k, k):
            yield (k,) + rest


def section_homology_real(nmax):
    print(f"== direct top homology and the global module HH_n, 3 <= n <= {nmax} ==")
    t0 = time.time()
    posets = unlabeled_posets_by_extension(nmax)
    a, b = bn_values(nmax)
    print(f"  a_n = {a[1:]}   b_n = n[x^n] log A = {b[1:]}")
    allok = True
    for n in range(3, nmax + 1):
        chi = Counter()  # cycle type -> character value of HH_n
        dimtot = 0
        bad_dim = 0
        for rel in posets[n]:
            G = automorphisms(rel, n)
            cls = conjugacy_classes(G)
            dim, tr = top_homology_traces(rel, n, [cl[0] for cl in cls])
            ec = e_C(rel, n)
            if dim != ec:
                bad_dim += 1
            # local identity, directly: trace of g on H_P vs sgn(g) * Lie side
            for cl in cls:
                g = cl[0]
                if tr[g] != sign(g) * lie_value(rel, n, g):
                    allok = False
                    print(f"  LOCAL MISMATCH n={n} rel={sorted(rel)} g={cycle_str(g)}")
            # induced character: chi(tau) = |C(tau)|/|Aut| * sum_{g in Aut, g~tau} tr(g)
            for cl in cls:
                chi[cycle_type(cl[0])] += Fraction(len(cl) * tr[cl[0]], len(G))
            dimtot += Fraction(factorial(n), len(G)) * dim
        print(f"  n={n}: sum over labeled P of dim H_P = {dimtot}; "
              f"(n-1)! b_n = {factorial(n - 1) * b[n]}; dim H_P != e_C(P) for {bad_dim} posets")
        allok &= (dimtot == factorial(n - 1) * b[n]) and bad_dim == 0
        for lam in partitions_of(n):
            z = 1
            for part, mult in Counter(lam).items():
                z *= part ** mult * factorial(mult)
            # chi[lam] accumulated sum_{g ~ lam} tr / |Aut|; times |C_{S_n}(lam)| = z
            val = chi[lam] * z
            assert val.denominator == 1
            val = int(val)
            pt = frob_prediction(n, b, lam, True)
            pu = frob_prediction(n, b, lam, False)
            ok = (val == pt)
            allok &= ok
            mark = "" if pt == pu else "   <- twist matters; untwisted predicts %+d" % pu
            print(f"    class {str(lam):18s} chi_HH = {val:+8d}  frob(twisted) = {pt:+8d}"
                  f"  {'OK' if ok else 'FAIL'}{mark}")
    print(f"  all homology checks pass: {allok}   [{time.time() - t0:.1f}s]")
    return allok


# ---------------------------------------------------------------------------
# Section: Hopf monoid of posets with a linear extension


def all_labeled_posets(n):
    """All posets on [n] as frozensets (insert element n-1 with ideal/filter)."""
    if n == 0:
        return [frozenset()]
    out = []
    for rel in all_labeled_posets(n - 1):
        m = n - 1
        for dmask in range(1 << m):
            down = {i for i in range(m) if dmask >> i & 1}
            if any((a, x) in rel and a not in down for x in down for a in range(m)):
                continue
            for umask in range(1 << m):
                upset = {i for i in range(m) if umask >> i & 1}
                if upset & down:
                    continue
                if any((x, a) in rel and a not in upset for x in upset for a in range(m)):
                    continue
                if any((d, u) not in rel for d in down for u in upset):
                    continue
                new = set(rel) | {(d, m) for d in down} | {(m, u) for u in upset}
                out.append(frozenset(new))
    return out


def section_hopf(nmax):
    print(f"== Hopf monoid Q (posets with a linear extension), n <= {nmax} ==")
    t0 = time.time()
    a, b = bn_values(nmax)
    allok = True
    for n in range(1, nmax + 1):
        basis = []
        for rel in all_labeled_posets(n):
            for w in linear_extensions(rel, n):
                basis.append((rel, w))
        idx = {x: i for i, x in enumerate(basis)}
        N = len(basis)
        assert N == factorial(n) * a[n]
        rows = []
        for smask in range(1, (1 << n) - 1):
            S = frozenset(i for i in range(n) if smask >> i & 1)
            fib = defaultdict(dict)
            for i, (rel, w) in enumerate(basis):
                key = (frozenset(r for r in rel if r[0] in S and r[1] in S),
                       tuple(x for x in w if x in S),
                       frozenset(r for r in rel if r[0] not in S and r[1] not in S),
                       tuple(x for x in w if x not in S))
                fib[key][i] = 1
            rows.extend(fib.values())
        piv = rank_rows_mod(rows, N)
        dim = N - len(piv)
        ok = dim == factorial(n - 1) * b[n]
        line = f"  n={n}: dim Q[n] = {N}, dim Prim(Q)[n] = {dim}, (n-1)! b_n = {factorial(n - 1) * b[n]}"
        # character on each cycle type
        chars = {}
        for lam in partitions_of(n):
            tau, base = [], 0
            for part in lam:
                tau += [base + (i + 1) % part for i in range(part)]
                base += part
            tau = tuple(tau)
            perm = [idx[(frozenset((tau[x], tau[y]) for x, y in rel), compose(tau, w))]
                    for rel, w in basis]
            chars[lam] = kernel_trace(piv, N, perm)
            pred = frob_prediction(n, b, lam, twisted=False)
            ok &= chars[lam] == pred
        allok &= ok
        print(line + f"; character = ch V_n (untwisted): {ok}")
    print(f"  all Hopf checks pass: {allok}   [{time.time() - t0:.1f}s]")
    return allok


# ---------------------------------------------------------------------------
# Section: does the concatenation commutator descend to the e_zeta model?


def section_bracket(nmax):
    """Exact test over Q(zeta_N) is heavy; we test with the complex
    embedding and a tolerance, recording the largest residual."""
    import cmath
    print(f"== bracket test, e_zeta model, |P| + |Q| <= {nmax} ==")
    posets = unlabeled_posets_by_extension(nmax)

    def ez_coords(vec, n):
        # vec: dict word -> coeff.  Return dict class_rep -> coefficient of
        # rep*e_zeta in vec*e_zeta.  w = rep*gamma^j  =>  w e = zeta^j rep e.
        z = cmath.exp(2j * cmath.pi / n)
        out = defaultdict(complex)
        for w, c in vec.items():
            reps = [w[j:] + w[:j] for j in range(n)]
            rep = min(reps)
            j = (n - reps.index(rep)) % n  # w = rep rotated left by j
            out[rep] += c * z ** j
        return out

    worst, tested, descends = 0.0, 0, Counter()
    for p in range(1, nmax):
        for q in range(1, nmax - p + 1):
            n = p + q
            for P in posets[p]:
                for Q in posets[q]:
                    linP = linear_extensions(P, p)
                    linQ = [tuple(x + p for x in v) for v in linear_extensions(Q, q)]
                    # kernel of W_P -> W_P e_zeta(p): relations w*gamma^j - zeta_p^j w
                    zp = cmath.exp(2j * cmath.pi / p)
                    kers = []
                    linset = set(linP)
                    for w in linP:
                        for j in range(1, p):
                            u = w[j:] + w[:j]
                            if u in linset:
                                kers.append({u: 1, w: -zp ** j})
                    ok = True
                    for kv in kers:
                        for v in linQ:
                            vec = defaultdict(complex)
                            for u, c in kv.items():
                                vec[u + v] += c
                                vec[v + u] -= c
                            co = ez_coords(vec, n)
                            res = max((abs(c) for c in co.values()), default=0)
                            worst = max(worst, res)
                            if res > 1e-9:
                                ok = False
                    tested += 1
                    descends[bool(kers), ok, len(P) == 0] += 1
    print(f"  pairs (P,Q) tested: {tested}")
    print(f"  ker(W_P -> Lie(P)) = 0 (nothing to test): {sum(v for k, v in descends.items() if not k[0])}")
    print(f"  ker != 0, commutator descends: {sum(v for k, v in descends.items() if k[0] and k[1])}")
    print(f"  ker != 0, commutator does NOT descend: {sum(v for k, v in descends.items() if k[0] and not k[1])}"
          f" (of which P is an antichain: {descends[True, False, True]})")
    return descends


# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--theorem", type=int, metavar="NMAX")
    ap.add_argument("--homology", type=int, metavar="NMAX")
    ap.add_argument("--hopf", type=int, metavar="NMAX")
    ap.add_argument("--bracket", type=int, metavar="NMAX")
    a = ap.parse_args(argv)
    if not any([a.theorem, a.homology, a.hopf, a.bracket]):
        a.theorem, a.homology, a.hopf, a.bracket = 6, 6, 4, 5
    ok = True
    if a.theorem:
        ok &= section_theorem(a.theorem)
    if a.homology:
        ok &= section_homology_real(min(a.homology, 6))
    if a.hopf:
        ok &= section_hopf(min(a.hopf, 4))
    if a.bracket:
        section_bracket(a.bracket)
    print(f"ALL CHECKS PASS: {ok}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
