#!/usr/bin/env python3
"""Checks for notes/moonshine_scoping.md.  Plain Python 3, exact arithmetic.

Imports the reproduction scripts poset_jks_check.py and poset_lie_structure.py
(posets, automorphisms, the closed character formula of Lie(P)).

Sections (all run by default; each prints a verdict line):

  --controls   The eta-quotient detector and its positive and negative
               controls: Euler's pentagonal series (= eta), Jacobi's theta_3
               (= eta(2t)^5 / eta(t)^2 eta(4t)^2), Delta, the Witt/necklace
               product for the free Lie algebra on one generator in each
               degree; rejection of 1/(1-2q), sum q^(n^3), and the MacMahon
               product.
  --witt       Candidate 1: the Witt layer Prim(Q) = (+)_P Lie(P), graded by
               n = |P|.  a_n (A006455) from OEIS, brute force for n <= 6;
               b_n = n[x^n] log A; c_n = dim V_n^{S_n}; the sign- and
               A_n-isotypic multiplicities; checked against a direct sum over
               unlabeled posets for n <= 5; super-exponential growth.
  --ppart      Candidate 2: g-fixed P-partitions, g in Aut(P) cap A_n.
               Brute force against the quotient formula over Lin(P/<g>);
               detector on every series.
  --infinite   Candidate 3: P-partitions of k.N (S_k), chain_m x N, N x N
               (with the transpose).
  --fock       Candidate 4: Frame shapes of g on Lie(P) and on H_P, the
               Fock-space trace prod_n det(1 - g q^n)^(-1) computed from
               characters only, detector recovery of the Frame shape, level,
               character and cusp orders of eta_g; the Sturm check of
               eta(5t)^5/eta(t) = sum_n sum_{d|n} (n/d | 5) d q^n.

Exit status 0 iff every asserted check passes.

Run from compute/:  python3 moonshine_scoping.py [--controls|--witt|...]
"""

import argparse
import itertools
import sys
import time
from fractions import Fraction
from math import factorial, gcd

from poset_jks_check import (automorphisms, compose, cycle_type, linear_extensions,
                             sign, transitive_closure, unlabeled_posets_by_extension)
from poset_lie_structure import bn_values, closed_formula, lie_value

NTERMS = 30  # number of q-coefficients reported per series

# ---------------------------------------------------------------------------
# Number theory


def mobius(n):
    res, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            res = -res
        p += 1
    return -res if n > 1 else res


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def lcm(a, b):
    return a * b // gcd(a, b)


def kronecker(a, n):
    """Kronecker symbol (a/n) for n >= 1."""
    if n == 1:
        return 1
    res = 1
    while n % 2 == 0:
        n //= 2
        if a % 2 == 0:
            return 0
        if a % 8 in (3, 5):
            res = -res
    # Jacobi symbol (a/n), n odd
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a %= n
    return res if n == 1 else 0


# ---------------------------------------------------------------------------
# Power series (lists, index = power of q), truncated at length N


def smul(f, g, N):
    out = [0] * N
    for i, a in enumerate(f[:N]):
        if a:
            for j, b in enumerate(g[:N - i]):
                out[i + j] += a * b
    return out


def euler_product(exps, N):
    """prod_n (1 - q^n)^(exps[n]) truncated at q^N (exps: dict n -> int)."""
    f = [1] + [0] * (N - 1)
    for n, e in exps.items():
        if e == 0 or n >= N:
            continue
        if e > 0:
            for _ in range(e):
                for i in range(N - 1, n - 1, -1):
                    f[i] -= f[i - n]
        else:
            for _ in range(-e):
                for i in range(n, N):
                    f[i] += f[i - n]
    return f


def eta_quotient(r, N):
    """prod_t prod_n (1 - q^(tn))^(r_t), without the q^(sum t r_t / 24)."""
    exps = {}
    for t, rt in r.items():
        for m in range(t, N, t):
            exps[m] = exps.get(m, 0) + rt
    return euler_product(exps, N)


def plethystic_exp(power_sums, N):
    """f = exp(sum_{j>=1} s_j q^j / j), i.e. q f'/f = sum_j s_j q^j, with s
    given as the list power_sums (index j).  Exact, by n f_n = sum_j s_j f_(n-j)."""
    f = [Fraction(1)] + [Fraction(0)] * (N - 1)
    for n in range(1, N):
        f[n] = sum(power_sums[j] * f[n - j] for j in range(1, n + 1)) / n
    assert all(x.denominator == 1 for x in f)
    return [int(x) for x in f]


# ---------------------------------------------------------------------------
# The eta-quotient detector


def product_exponents(f):
    """For f = c q^a (1 + ...), return (a, c, e) with
    f = c q^a prod_{n>=1} (1 - q^n)^(e_n) through the available precision, or
    None for an exponent that is not an integer.  e is a list, e[0] unused."""
    a = next(i for i, x in enumerate(f) if x)
    c = f[a]
    g = [Fraction(x, c) for x in f[a:]]
    N = len(g)
    # s = q g'/g, by s * g = q g'
    qd = [i * g[i] for i in range(N)]
    s = [Fraction(0)] * N
    for m in range(1, N):
        s[m] = qd[m] - sum(s[j] * g[m - j] for j in range(1, m))
    # s_m = -sum_{n|m} n e_n
    e = [None] * N
    for n in range(1, N):
        val = -sum(mobius(n // d) * s[d] for d in divisors(n)) / n
        e[n] = val if val.denominator != 1 else int(val)
    return a, c, e


def detect_eta_quotient(f):
    """Return a dict with keys
       'ok'   : True if f = q^a prod_t eta-type factors (1 - q^(tn))^(r_t)
                with every r_t integral and support of r inside [1, len/2]
                (so the second half of the window certifies the zeros);
       'r'    : the exponents r_t found (support only);
       'tmax' : largest t in the support of r within the window;
       'a', 'c'."""
    a, c, e = product_exponents(f)
    N = len(e)
    if any(isinstance(x, Fraction) for x in e[1:]):
        return {"ok": False, "r": None, "tmax": None, "a": a, "c": c,
                "why": "non-integral product exponent"}
    r = {}
    for t in range(1, N):
        v = sum(mobius(t // d) * e[d] for d in divisors(t))
        if v:
            r[t] = v
    tmax = max(r) if r else 0
    ok = (c in (1, -1)) and tmax <= (N - 1) // 2
    return {"ok": ok, "r": r, "tmax": tmax, "a": a, "c": c,
            "why": "" if ok else f"exponent support reaches t = {tmax} of window {N - 1}"}


def eta_form_data(r):
    """Gordon-Hughes-Newman data of eta_r = prod_t eta(t tau)^(r_t): weight,
    q-order, the least level N (multiple of lcm t) with sum t r_t = 0 and
    sum (N/t) r_t = 0 mod 24, the character d -> ((-1)^k s / d), and the
    order of vanishing at the cusp c/d for each d | N (Ligozat)."""
    k2 = sum(r.values())          # 2 * weight
    tr = sum(t * x for t, x in r.items())
    out = {"weight": Fraction(k2, 2), "qorder": Fraction(tr, 24)}
    N0 = 1
    for t in r:
        N0 = lcm(N0, t)
    N = None
    if tr % 24 == 0:
        for m in range(1, 25):
            if sum((N0 * m // t) * x for t, x in r.items()) % 24 == 0:
                N = N0 * m
                break
    out["level"] = N
    out["gamma0"] = N is not None and k2 % 2 == 0
    if N is None:
        return out
    cusp = {}
    for d in divisors(N):
        num = sum(Fraction(gcd(d, t) ** 2 * x, t) for t, x in r.items())
        cusp[d] = Fraction(N, 24) * num / (gcd(d, N // d) * d)
    out["cusp_orders"] = cusp
    out["holomorphic"] = all(v >= 0 for v in cusp.values())
    if k2 % 2 == 0:
        # character d -> ((-1)^k s / d), s = prod t^(r_t); only the square
        # class of s matters, so negative exponents may be made positive
        k = k2 // 2
        s = 1
        for t, x in r.items():
            s *= t ** abs(x)
        disc = (-1) ** k * s
        out["disc"] = disc
        out["char"] = lambda d, disc=disc: kronecker(disc, d)
    return out


def sturm_bound(k, N):
    idx = N
    p = 2
    m = N
    while p * p <= m:
        if m % p == 0:
            idx = idx * (p + 1) // p
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        idx = idx * (m + 1) // m
    return Fraction(k * idx, 12)


def fmt_r(r):
    if not r:
        return "1"
    return " ".join(f"{t}^{x}" for t, x in sorted(r.items()))


def fmt_series(f, n=NTERMS):
    return ", ".join(str(x) for x in f[:n])


class Report:
    def __init__(self):
        self.ok = True

    def check(self, cond, msg):
        print(("  ok    " if cond else "  FAIL  ") + msg)
        self.ok &= bool(cond)
        return cond


# ---------------------------------------------------------------------------
# Section: controls


def witt_one_per_degree(N):
    """dims l_n of the free Lie algebra on one generator in each degree n >= 1:
    n l_n = sum_{d|n} mu(n/d) (2^d - 1)   (necklace / Witt formula)."""
    out = [0] * N
    for n in range(1, N):
        v = sum(mobius(n // d) * (2 ** d - 1) for d in divisors(n))
        assert v % n == 0
        out[n] = v // n
    return out


def section_controls(rep):
    print("== controls for the eta-quotient detector ==")
    N = 61
    pent = [0] * N
    k = 0
    while True:
        done = True
        for j in (k, -k) if k else (0,):
            m = j * (3 * j - 1) // 2
            if m < N:
                pent[m] += (-1) ** abs(j)
                done = False
        if done:
            break
        k += 1
    d = detect_eta_quotient(pent)
    rep.check(d["ok"] and d["r"] == {1: 1},
              f"pentagonal series sum (-1)^k q^(k(3k-1)/2): r = {fmt_r(d['r'])} (expect 1^1 = eta)")
    th = [0] * N
    for n in range(-8, 9):
        if n * n < N:
            th[n * n] += 1
    d = detect_eta_quotient(th)
    rep.check(d["ok"] and d["r"] == {1: -2, 2: 5, 4: -2},
              f"theta_3 = sum q^(n^2): r = {fmt_r(d['r'])} (expect 1^-2 2^5 4^-2)")
    fd = eta_form_data(d["r"])
    rep.check(fd["weight"] == Fraction(1, 2) and fd["level"] == 4 and fd["holomorphic"],
              f"theta_3: weight {fd['weight']}, level {fd['level']}, holomorphic at cusps "
              f"{fd['holomorphic']} (expect 1/2, 4, True)")
    tau = [0] + eta_quotient({1: 24}, N)[:N - 1]
    rep.check(tau[1:6] == [1, -24, 252, -1472, 4830] and tau[11] == 534612,
              "Delta = q prod (1-q^n)^24: tau(1..5) = 1, -24, 252, -1472, 4830, tau(11) = 534612")
    d = detect_eta_quotient(tau)
    fd = eta_form_data(d["r"])
    rep.check(d["r"] == {1: 24} and fd["level"] == 1 and fd["weight"] == 12 and fd["holomorphic"],
              "Delta recovered as 1^24, weight 12, level 1")
    # Witt / necklace control: U(free Lie on x_1, x_2, ...) has Hilbert series
    # 1/(1 - q/(1-q)) = (1-q)/(1-2q) = prod_n (1-q^n)^(-l_n)
    hil = [1] + [2 ** (n - 1) for n in range(1, N)]
    a, c, e = product_exponents(hil)
    l = witt_one_per_degree(N)
    rep.check(all(e[n] == -l[n] for n in range(1, N)),
              f"Witt product (1-q)/(1-2q) = prod (1-q^n)^(-l_n), l_n = {l[1:13]} ... (A059966), n < {N}")
    d = detect_eta_quotient(hil)
    rep.check(not d["ok"], f"rejects (1-q)/(1-2q): {d['why']}")
    cube = [0] * N
    for n in range(0, 4):
        cube[n ** 3] += 1
    d = detect_eta_quotient(cube)
    rep.check(not d["ok"], f"rejects sum q^(n^3): {d['why']}")
    mac = euler_product({n: -n for n in range(1, N)}, N)
    d = detect_eta_quotient(mac)
    rep.check(not d["ok"] and all(d["r"].get(t) == -euler_phi(t) for t in range(1, 20)),
              f"rejects MacMahon prod (1-q^n)^-n (r_t = -phi(t); found r_1..r_6 = "
              f"{[d['r'].get(t) for t in range(1, 7)]})")


def euler_phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


# ---------------------------------------------------------------------------
# Section: candidate 1, the Witt layer

# OEIS A006455: naturally labeled posets on [n] (n = 0..18), fetched 2026-10-31.
A006455 = [1, 1, 2, 7, 40, 357, 4824, 96428, 2800472, 116473461, 6855780268,
           565505147444, 64824245807684, 10252978223661714, 2223739823604074838,
           657800677264030983838, 264134770940774037129920,
           143373621178035684238742792, 104816927860381921400775335496]


def witt_layer_numbers(a):
    """b_n = n [x^n] log A(x); c_n, c^-_n = multiplicities of triv, sgn in V_n."""
    N = len(a)
    L = [Fraction(0)] * N
    for n in range(1, N):
        L[n] = Fraction(n * a[n] - sum(k * L[k] * a[n - k] for k in range(1, n)), n)
    b = [None] + [n * L[n] for n in range(1, N)]
    assert all(x.denominator == 1 for x in b[1:])
    b = [None] + [int(x) for x in b[1:]]
    c, cm = [0] * N, [0] * N
    for n in range(1, N):
        # <ch V_n, h_n> and <ch V_n, e_n>; ch V_n = sum_{d|n} mu(d)/d L_{n/d} p_d^{n/d}
        v = sum(Fraction(mobius(d) * b[n // d], n) for d in divisors(n))
        w = sum(Fraction(mobius(d) * b[n // d] * (-1) ** ((n // d) * (d - 1)), n)
                for d in divisors(n))
        assert v.denominator == 1 and w.denominator == 1
        c[n], cm[n] = int(v), int(w)
    return b, c, cm


def section_witt(rep):
    print("== candidate 1: the Witt layer V_n = (+)_P Lie(P) ==")
    a_bf, b_bf = bn_values(6)
    rep.check(a_bf == A006455[:7],
              f"brute-force a_n (n <= 6) = {a_bf} agrees with OEIS A006455")
    a = A006455
    b, c, cm = witt_layer_numbers(a)
    rep.check(b[1:7] == b_bf[1:7], f"b_n = n[x^n] log A: {b[1:9]} ...")
    dims = [factorial(n - 1) * b[n] for n in range(1, len(a))]
    rep.check(dims[2:6] == [32, 786, 37464, 3183840],
              f"dim V_n = (n-1)! b_n: {dims[:6]} (n = 1..6; 32, 786, 37464, 3183840 as in "
              "global_module_operations_plethlog.md)")
    # direct count of the multiplicities over unlabeled posets, n <= 5
    posets = unlabeled_posets_by_extension(5)
    for n in range(1, 6):
        tot, totm = Fraction(0), Fraction(0)
        for rel in posets[n]:
            G = automorphisms(rel, n)
            for g in G:
                x = closed_formula(rel, n, g)
                tot += Fraction(x, len(G))
                totm += Fraction(sign(g) * x, len(G))
        rep.check(tot == c[n] and totm == cm[n],
                  f"n={n}: sum over unlabeled P of dim Lie(P)^Aut(P) = {tot} = c_n; "
                  f"sgn-isotypic {totm} = c^-_n")
    rep.check(all(x >= 0 for x in c[1:]) and all(x >= 0 for x in cm[1:]),
              f"c_n >= 0 and c^-_n >= 0 for n <= {len(a) - 1}")
    print(f"  c_n   (S_n-invariants)        = {c[1:]}")
    print(f"  c^-_n (sign-isotypic)         = {cm[1:]}")
    print(f"  c_n + c^-_n (A_n-invariants)  = {[x + y for x, y in zip(c[1:], cm[1:])]}")
    # A(q) = prod (1-q^n)^(-c_n): verify through the available range
    _, _, e = product_exponents(a)
    rep.check(all(e[n] == -c[n] for n in range(1, len(a))),
              "A(q) = sum a_n q^n = prod_n (1-q^n)^(-c_n) through q^18 (inverse Euler transform)")
    # growth: bipartite naturally labeled posets give a_n >= 2^(floor(n/2) ceil(n/2))
    rep.check(all(a[n] >= 2 ** ((n // 2) * ((n + 1) // 2)) for n in range(len(a))),
              "a_n >= 2^(floor(n/2) ceil(n/2)) for n <= 18")
    ratios = [round((a[n + 1] / a[n]) / (a[n] / a[n - 1]), 2) for n in range(10, 18)]
    print(f"  a_(n+1) a_(n-1) / a_n^2 for n = 10..17: {ratios}  (bounded away from 1: "
          "log a_n is convex, growth ~ 2^(n^2/4))")
    for d in (1, 2, 3, 5):
        vals = []
        for m in range(1, (len(a) - 1) // d + 1):
            vals.append(mobius(d) * d ** (m - 1) * factorial(m - 1) * b[m])
        print(f"  chi_(V_dm)(cycle type {d}^m), m = 1..: {vals[:8]}")
    d = detect_eta_quotient(a)
    rep.check(not d["ok"], f"detector on A(q): rejected ({d['why']})")
    dA = detect_eta_quotient([1] + [x + y for x, y in zip(c[1:], cm[1:])])
    rep.check(not dA["ok"], f"detector on 1 + sum (c_n + c^-_n) q^n: rejected ({dA['why']})")


# ---------------------------------------------------------------------------
# Section: candidate 2, g-fixed P-partitions


def chains(lengths):
    rel, start = set(), 0
    for L in lengths:
        for i in range(start, start + L):
            for j in range(i + 1, start + L):
                rel.add((i, j))
        start += L
    return frozenset(rel), start


def boolean3():
    els = list(range(8))  # subsets of {0,1,2} as bitmasks
    rel = {(x, y) for x in els for y in els if x != y and x & y == x}
    return frozenset(rel), 8


def bowtie():
    return frozenset({(0, 2), (0, 3), (1, 2), (1, 3)}), 4


def antichain(n):
    return frozenset(), n


PP_EXAMPLES = [
    ("antichain 4", antichain(4), 30),
    ("2+2 (two 2-chains)", chains([2, 2]), 30),
    ("bowtie 0,1 < 2,3", bowtie(), 30),
    ("2+2+2", chains([2, 2, 2]), 22),
    ("3+3", chains([3, 3]), 24),
    ("Boolean lattice B_3", boolean3(), 16),
]


def brute_fixed_ppartitions(rel, n, g, D):
    """sum over order-reversing sigma: P -> N with sigma o g = sigma and
    |sigma| < D of q^|sigma| (direct enumeration over P)."""
    above = [[b for (a, b) in rel if a == x] for x in range(n)]
    lin = next(iter(linear_extensions(rel, n)))
    order = list(reversed(lin))  # maxima first
    out = [0] * D
    sig = [None] * n

    def rec(i, budget):
        if i == n:
            if all(sig[g[x]] == sig[x] for x in range(n)):
                out[D - 1 - budget] += 1
            return
        x = order[i]
        lo = max((sig[y] for y in above[x]), default=0)
        v = lo
        while v <= budget:
            sig[x] = v
            rec(i + 1, budget - v)
            v += 1
        sig[x] = None

    rec(0, D - 1)
    return out


def quotient_poset(rel, n, g):
    orbits, seen = [], set()
    for x in range(n):
        if x not in seen:
            orb, y = [], x
            while y not in orb:
                orb.append(y)
                y = g[y]
            seen |= set(orb)
            orbits.append(orb)
    idx = {x: i for i, O in enumerate(orbits) for x in O}
    qrel = {(idx[a], idx[b]) for a, b in rel}
    assert all(i != j for i, j in qrel), "quotient relation is not irreflexive"
    qrel = transitive_closure(qrel, len(orbits))
    assert not any((j, i) in qrel for i, j in qrel), "quotient is not a poset"
    return qrel, [len(O) for O in orbits]


def quotient_formula(rel, n, g, D):
    """T_g = sum_{w in Lin(Q)} q^(sum_{j in Des w} S_j) / prod_j (1 - q^(S_j)),
    Q = P/<g> naturally labeled, S_j = total weight of w_1..w_j."""
    qrel, wt = quotient_poset(rel, n, g)
    m = len(wt)
    # natural labeling of Q: relabel along one linear extension
    base = linear_extensions(qrel, m)[0]
    lab = {x: i for i, x in enumerate(base)}
    total = [0] * D
    numer = {}
    for w in linear_extensions(qrel, m):
        S, acc = [], 0
        for x in w:
            acc += wt[x]
            S.append(acc)
        e = sum(S[j] for j in range(m - 1) if lab[w[j]] > lab[w[j + 1]])
        key = tuple(S)
        numer.setdefault(key, {})
        numer[key][e] = numer[key].get(e, 0) + 1
        if e < D:
            term = [0] * D
            term[e] = 1
            for s in S:
                term = smul(term, [1 if i % s == 0 else 0 for i in range(D)], D)
            total = [x + y for x, y in zip(total, term)]
    return total, numer, wt


def section_ppart(rep):
    print("== candidate 2: g-fixed P-partitions, g in Aut(P) cap A_n ==")
    for name, (rel, n), D in PP_EXAMPLES:
        rel = transitive_closure(rel, n)
        G = automorphisms(rel, n)
        Geven = [g for g in G if sign(g) == 1]
        seen_types = set()
        print(f"  {name}: |Aut| = {len(G)}, |Aut cap A_n| = {len(Geven)}")
        for g in sorted(Geven):
            ct = cycle_type(g)
            if ct in seen_types:
                continue
            seen_types.add(ct)
            Db = min(D, 16 if n >= 6 else D)
            bf = brute_fixed_ppartitions(rel, n, g, Db)
            qf, numer, wt = quotient_formula(rel, n, g, NTERMS + 1)
            rep.check(bf == qf[:Db], f"    g of type {ct}: brute force = quotient formula "
                                     f"through q^{Db - 1}")
            print(f"      T_g = {fmt_series(qf, NTERMS + 1)}")
            nlin = sum(sum(v.values()) for v in numer.values())
            print(f"      orbit weights {wt}; |Lin(P/<g>)| = {nlin}")
            d = detect_eta_quotient(qf)
            rep.check(not d["ok"], f"      detector: not an eta quotient ({d['why']})")
    print("  verdict input: every T_g is a rational function of q with poles only at "
          "roots of unity (Lemma R in the note), so none is modular.")


# ---------------------------------------------------------------------------
# Section: candidate 3, infinite posets


def plane_partitions_rows(m, D):
    """number of plane partitions of each size < D with at most m rows
    (= P-partitions of chain_m x N) by direct enumeration."""
    out = [0] * D

    def parts(budget, bound):
        """partitions (weakly decreasing tuples) of size <= budget that are
        dominated entrywise by bound (None = no bound)."""
        res = []

        def rec(prefix, rem, maxv):
            res.append(tuple(prefix))
            i = len(prefix)
            cap = maxv
            if bound is not None:
                if i >= len(bound):
                    return
                cap = min(cap, bound[i])
            for v in range(1, min(cap, rem) + 1):
                prefix.append(v)
                rec(prefix, rem - v, v)
                prefix.pop()
        rec([], budget, budget)
        return res

    def rows(k, budget, prev, size):
        out[size] += 1
        if k == m:
            return
        for lam in parts(budget, prev):
            if not lam:
                continue
            rows(k + 1, budget - sum(lam), lam, size + sum(lam))
    rows(0, D - 1, None, 0)
    return out


def symmetric_plane_partitions(D):
    """plane partitions pi with pi = pi^T, by size, direct enumeration."""
    out = [0] * D

    # enumerate plane partitions as lists of rows, keep the symmetric ones
    def gen(prev, budget, rows_):
        yield rows_
        for lam in all_parts(budget, prev):
            if lam:
                yield from gen(lam, budget - sum(lam), rows_ + [lam])

    def all_parts(budget, bound):
        res = []

        def r(prefix, rem, maxv):
            res.append(tuple(prefix))
            i = len(prefix)
            cap = maxv
            if bound is not None:
                if i >= len(bound):
                    return
                cap = min(cap, bound[i])
            for v in range(1, min(cap, rem) + 1):
                prefix.append(v)
                r(prefix, rem - v, v)
                prefix.pop()
        r([], budget, budget)
        return res

    for rows_ in gen(None, D - 1, []):
        ok = True
        for i, row in enumerate(rows_):
            for j, v in enumerate(row):
                if j >= len(rows_) or i >= len(rows_[j]) or rows_[j][i] != v:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out[sum(map(sum, rows_))] += 1
    return out


def section_infinite(rep):
    print("== candidate 3: P-partitions of infinite posets ==")
    N = NTERMS + 1
    part = euler_product({n: -1 for n in range(1, N)}, N)
    for k in (3, 4, 5):
        for ct in sorted({tuple(sorted(lam, reverse=True)) for lam in partitions(k)}):
            g = perm_of_type(ct)
            # direct: k-tuples of partitions fixed by g are constant on cycles
            f = [1] + [0] * (N - 1)
            for lam in ct:
                f = smul(f, [part[i // lam] if i % lam == 0 else 0 for i in range(N)], N)
            d = detect_eta_quotient(f)
            expect = {}
            for lam in ct:
                expect[lam] = expect.get(lam, 0) - 1
            ok = d["ok"] and d["r"] == expect
            fd = eta_form_data(d["r"])
            par = "even" if sign(g) == 1 else "odd"
            rep.check(ok, f"k.N, k={k}, g of type {ct} ({par}): T_g = q^(-{sum(ct)}/24) / "
                          f"prod eta(lam tau); r = {fmt_r(d['r'])}, weight {fd['weight']}")
    for m in (1, 2, 3):
        D = 18 if m > 1 else N
        bf = plane_partitions_rows(m, D)
        f = euler_product({n: -min(n, m) for n in range(1, N)}, N)
        rep.check(bf == f[:D], f"chain_{m} x N: brute force = prod (1-q^n)^(-min(n,{m})) "
                               f"through q^{D - 1}")
        d = detect_eta_quotient(f)
        if m == 1:
            rep.check(d["ok"] and d["r"] == {1: -1}, "chain_1 x N = N: 1/eta (control)")
        else:
            rep.check(not d["ok"], f"chain_{m} x N: not an eta quotient ({d['why']}); "
                                   f"times eta^{m} it is a nonconstant polynomial")
    D = 20
    bf = symmetric_plane_partitions(D)
    exps = {}
    for i in range(1, N):
        if 2 * i - 1 < N:
            exps[2 * i - 1] = exps.get(2 * i - 1, 0) - 1
        for j in range(i + 1, N):
            m = 2 * (i + j - 1)
            if m < N:
                exps[m] = exps.get(m, 0) - 1
    f = euler_product(exps, N)
    rep.check(bf == f[:D], f"N x N with the transpose: brute force symmetric plane partitions = "
                           f"prod (1-q^(2i-1))^-1 prod_(i<j) (1-q^(2(i+j-1)))^-1 through q^{D - 1}")
    print(f"      T_transpose = {fmt_series(f)}")
    d = detect_eta_quotient(f)
    rep.check(not d["ok"], f"N x N, transpose: not an eta quotient ({d['why']})")
    mac = euler_product({n: -n for n in range(1, N)}, N)
    d = detect_eta_quotient(mac)
    rep.check(not d["ok"], f"N x N, identity (MacMahon): not an eta quotient ({d['why']})")


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def perm_of_type(ct):
    p, start = [], 0
    for L in ct:
        p += [start + (i + 1) % L for i in range(L)]
        start += L
    return tuple(p)


# ---------------------------------------------------------------------------
# Section: candidate 4, Fock space and Frame shapes


def power(g, e):
    p = tuple(range(len(g)))
    for _ in range(e):
        p = compose(g, p)
    return p


def order(g):
    o, p = 1, g
    while p != tuple(range(len(g))):
        p = compose(g, p)
        o += 1
    return o


def frame_shape(chis, o):
    """chis[e] = trace of g^e (e | o).  Returns {t: r_t} with
    char poly = prod (x^t - 1)^(r_t), via t r_t = sum_{e|t} mu(t/e) chi(g^e)."""
    r = {}
    for t in divisors(o):
        v = sum(mobius(t // e) * chis[e] for e in divisors(t))
        assert v % t == 0, "Frame-shape exponent not integral"
        if v:
            r[t] = v // t
    return r


def fock_trace(chis, o, N):
    """graded trace of g on Sym(M (x) t C[t]) from the characters only:
    log T = sum_{k>=1} sum_{m>=1} chi(g^k) q^(mk) / k."""
    s = [0] * N
    for j in range(1, N):
        # q d/dq log T at q^j
        s[j] = sum(chis[k % o or o] * (j // k) for k in divisors(j))
    return plethystic_exp(s, N)


FOCK_EXAMPLES = [
    ("antichain 4 (Lie_4)", antichain(4)),
    ("antichain 5 (Lie_5)", antichain(5)),
    ("antichain 6 (Lie_6)", antichain(6)),
    ("antichain 7 (Lie_7)", antichain(7)),
    ("2+2", chains([2, 2])),
    ("2+2+2", chains([2, 2, 2])),
    ("1+1+2", chains([1, 1, 2])),
    ("bowtie (connected)", bowtie()),
]


def section_fock(rep):
    print("== candidate 4: Fock space Sym(Lie(P) (x) tC[t]) and Frame shapes ==")
    N = NTERMS + 1
    found_modular = []
    for name, (rel, n) in FOCK_EXAMPLES:
        rel = transitive_closure(rel, n)
        G = automorphisms(rel, n)
        reps = {}
        for g in G:
            reps.setdefault(cycle_type(g), g)
        print(f"  {name}: n = {n}, |Aut| = {len(G)}")
        for ct, g in sorted(reps.items()):
            o = order(g)
            chis = {}
            for e in range(1, o + 1):
                chis[e] = closed_formula(rel, n, power(g, e))
            if n <= 6:
                rep.check(all(chis[e] == lie_value(rel, n, power(g, e)) for e in chis),
                          f"    {ct}: closed formula = cyclic-class trace for every power")
            r = frame_shape(chis, o)
            T = fock_trace(chis, o, N)
            d = detect_eta_quotient(T)
            neg = {t: -x for t, x in r.items()}
            rep.check(d["ok"] and d["r"] == neg,
                      f"    {ct} ({'even' if sign(g) == 1 else 'odd'}): dim {chis[o]}, "
                      f"Frame shape {fmt_r(r)}; Fock trace = 1/eta_g recovered by detector")
            # H_P = sgn (x) Lie(P): Frame shape of g on H_P, and the rule for odd g
            oH = o if sign(g) == 1 or o % 2 == 0 else 2 * o
            chisH2 = {e: sign(power(g, e)) * closed_formula(rel, n, power(g, e))
                      for e in range(1, oH + 1)}
            rH = frame_shape(chisH2, oH)
            if sign(g) == 1:
                rep.check(rH == r, "      even g: H_P and Lie(P) have the same Frame shape")
            else:
                pred = {}
                for t, x in r.items():
                    if t % 2:
                        pred[2 * t] = pred.get(2 * t, 0) + x
                        pred[t] = pred.get(t, 0) - x
                    else:
                        pred[t] = pred.get(t, 0) + x
                pred = {t: x for t, x in pred.items() if x}
                rep.check(rH == pred, f"      odd g: H_P Frame shape {fmt_r(rH)} = rule "
                                      "(odd t^r -> (2t)^r t^-r)")
            fd = eta_form_data(r)
            if fd.get("gamma0") and fd.get("holomorphic") and r != {1: chis[1]} and r:
                found_modular.append((name, ct, r, fd))
            hol = fd.get("holomorphic")
            print(f"      eta_g = {fmt_r(r)}: weight {fd['weight']}, q-order {fd['qorder']}, "
                  f"Gamma0 level {fd['level']}, holomorphic at all cusps: {hol}")
    print("  eta_g that are holomorphic modular forms on Gamma0(N) with integral weight:")
    for name, ct, r, fd in found_modular:
        print(f"    {name}, g of type {ct}: {fmt_r(r)}, weight {fd['weight']}, level {fd['level']}")
    # dim Lie_5 = 24: every eta_g has q-order 1.  Which are multiplicative
    # (normalized Hecke eigenforms)?  Control: the regular representation of
    # S_4 (also 24-dimensional; an element of order t has Frame shape t^(24/t)).
    M = 121
    rel, n = antichain(5)
    shapes = {}
    for g in automorphisms(rel, n):
        ct = cycle_type(g)
        if ct not in shapes:
            o = order(g)
            shapes[ct] = frame_shape({e: closed_formula(rel, n, power(g, e))
                                      for e in range(1, o + 1)}, o)
    reg = {t: {t: 24 // t} for t in (1, 2, 3, 4)}
    for label, table in (("Lie_5, S_5", shapes), ("regular rep of S_4", reg)):
        for key, r in sorted(table.items()):
            f = [0] + eta_quotient(r, M)[:M - 1]
            mult = f[1] == 1 and all(f[m * k] == f[m] * f[k] for m in range(2, M)
                                     for k in range(2, M) if m * k < M and gcd(m, k) == 1)
            rep.check(mult, f"{label}, {key}: eta_g = {fmt_r(r)} is multiplicative through q^{M - 1}")
    # negative control: a 24-dim Frame shape that is not of this kind
    f = [0] + eta_quotient({1: 20, 2: 2}, M)[:M - 1]
    rep.check(not all(f[m * k] == f[m] * f[k] for m in range(2, M) for k in range(2, M)
                      if m * k < M and gcd(m, k) == 1),
              "control: 1^20 2^2 (q-order 1, weight 11) is not multiplicative")
    # Sturm check for Lie_5, 5-cycle: eta(5t)^5/eta(t) = E_2^{chi_5, 1}
    r = {1: -1, 5: 5}
    fd = eta_form_data(r)
    rep.check(fd["level"] == 5 and fd["weight"] == 2 and fd["holomorphic"]
              and all(fd["char"](d) == kronecker(d, 5) for d in range(1, 50) if gcd(d, 5) == 1),
              "eta(5t)^5/eta(t) in M_2(Gamma0(5), (./5)) by Gordon-Hughes-Newman + Ligozat")
    B = sturm_bound(2, 5)
    M = 201
    f = [0] + eta_quotient(r, M)[:M - 1]
    E = [0] + [sum(kronecker(n // dd, 5) * dd for dd in divisors(n)) for n in range(1, M)]
    rep.check(f == E, f"eta(5t)^5/eta(t) = sum_n (sum_(d|n) (n/d | 5) d) q^n through q^{M - 1}; "
                      f"Sturm bound {B} -> PROVEN identity (given both sides in the space)")


SECTIONS = {
    "controls": section_controls,
    "witt": section_witt,
    "ppart": section_ppart,
    "infinite": section_infinite,
    "fock": section_fock,
}


def main(argv=None):
    ap = argparse.ArgumentParser()
    for s in SECTIONS:
        ap.add_argument("--" + s, action="store_true")
    args = ap.parse_args(argv)
    chosen = [s for s in SECTIONS if getattr(args, s)] or list(SECTIONS)
    rep = Report()
    for s in chosen:
        t0 = time.time()
        SECTIONS[s](rep)
        print(f"  [{s}: {time.time() - t0:.1f}s]")
    print(f"ALL CHECKS PASS: {rep.ok}")
    return 0 if rep.ok else 1


if __name__ == "__main__":
    sys.exit(main())
