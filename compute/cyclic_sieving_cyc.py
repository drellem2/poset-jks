#!/usr/bin/env python3
"""Cyclic sieving for automorphisms acting on the cyclic classes Cyc(P).

Companion to ../notes/cyclic_sieving_cyc.md.  Sections (each prints tagged
lines; the script exits 0 iff every check that is meant to hold holds and
every negative control is rejected):

  ctl     positive controls for the instruments: the RSW q-multinomial CSP
          for words under rotation, the q-binomial as the fake degree of
          k-subsets, the Kraskiewicz-Weyman form of the fake degree of
          S_k/C_k; a negative control (a perturbed polynomial).
  tk      every P = T^{+k} (k >= 2 copies of a connected T) with |P| <= 8:
          fixed-point counts of the component rotation sigma and its
          powers, the closed fixed-point formula, the fake-degree
          polynomial X_P and the closed form in c_j = e_C(T^{+j}).
  sweep   every unlabeled P with n <= NMAX and Aut(P) != 1, every
          conjugacy class of g in Aut(P): which candidate polynomials sieve
          <g>, against Springer regularity of g.
  obst    the smallest P on which no single polynomial sieves every cyclic
          subgroup of Aut(P).

Run from compute/:

    python3 cyclic_sieving_cyc.py --nmax 7 --tkmax 8 > output/cyclic_sieving_cyc.txt

Plain Python 3, no dependencies.
"""

import argparse
import cmath
import itertools
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from math import comb, factorial, gcd

import n7_sweep
import poset_jks_check as pj
from linear_extensions import components, cuts, linexts, restrict, rot

FAILS = []


def check(ok, label):
    if not ok:
        FAILS.append(label)
    return ok


# ---------------------------------------------------------------------------
# Polynomials: lists of ints or Fractions, index = degree.


def padd(p, q):
    out = [0] * max(len(p), len(q))
    for i, a in enumerate(p):
        out[i] += a
    for i, a in enumerate(q):
        out[i] += a
    return out


def pmul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def pscale(p, c):
    return [c * a for a in p]


def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def one_minus_qk(k):
    p = [0] * (k + 1)
    p[0], p[k] = 1, -1
    return p


def pdiv_one_minus_qk(p, k):
    """p / (1 - q^k), asserting exactness."""
    p = ptrim(p)
    if len(p) - 1 < k:
        raise AssertionError("not divisible")
    out = [0] * (len(p) - k)
    for i in range(len(out)):
        out[i] = p[i] + (out[i - k] if i >= k else 0)
    check(ptrim(pmul(out, one_minus_qk(k))) == p, "division by 1-q^k exact")
    return out


def q_int(m):
    return [1] * m


def q_fact(m):
    p = [1]
    for i in range(1, m + 1):
        p = pmul(p, q_int(i))
    return p


def q_multinomial(ms):
    num = q_fact(sum(ms))
    for m in ms:
        den = q_fact(m)
        # exact division by a polynomial with leading coefficient 1
        num = list(num)
        out = [0] * (len(num) - len(den) + 1)
        for i in range(len(out) - 1, -1, -1):
            c = num[i + len(den) - 1]
            out[i] = c
            for j, b in enumerate(den):
                num[i + j] -= c * b
        assert all(v == 0 for v in num)
        num = out
    return num


def fold(p, N):
    """p mod q^N - 1, as a list of length N."""
    out = [0] * N
    for i, a in enumerate(p):
        out[i % N] += a
    return out


def canonical_from_fix(fix):
    """The unique X mod q^N - 1 with X(w^j) = fix[j]; integer, nonnegative."""
    N = len(fix)
    out = []
    for t in range(N):
        v = sum(fix[j] * cmath.exp(-2j * cmath.pi * j * t / N) for j in range(N)) / N
        r = round(v.real)
        check(abs(v - r) < 1e-6 and r >= 0, f"canonical coefficient integral {fix}")
        out.append(r)
    return out


def sieves(X, fix):
    """(X, <g>) is a CSP for data fix[j] = |Fix g^j|, j = 0..N-1.  Exact:
    X mod q^N - 1 must equal the canonical polynomial."""
    return fold(X, len(fix)) == canonical_from_fix(fix)


def perturb(p):
    """Move one unit from q^1 to q^0: same value at q = 1, different value at
    every other root of unity.  The negative control."""
    p = list(p) + [0, 0]
    p[0] += 1
    p[1] -= 1
    return ptrim(p)


def pstr(p):
    terms = []
    for i, a in enumerate(p):
        if a == 0:
            continue
        c = "" if (a == 1 and i > 0) else str(a)
        terms.append(c + ("" if i == 0 else ("q" if i == 1 else f"q^{i}")))
    return " + ".join(terms) if terms else "0"


# ---------------------------------------------------------------------------
# Partitions, cycle types


def partitions(k, maxpart=None):
    if maxpart is None:
        maxpart = k
    if k == 0:
        yield ()
        return
    for p in range(min(k, maxpart), 0, -1):
        for rest in partitions(k - p, p):
            yield (p,) + rest


def z_lambda(lam):
    out = 1
    for part, mult in Counter(lam).items():
        out *= part ** mult * factorial(mult)
    return out


def perm_of_type(lam):
    """A permutation of range(sum(lam)) with cycle type lam (consecutive cycles)."""
    perm, off = [], 0
    for part in lam:
        perm += [off + (i + 1) % part for i in range(part)]
        off += part
    return perm


def euler_phi(m):
    return sum(1 for a in range(1, m + 1) if gcd(a, m) == 1)


def divisors(m):
    return [d for d in range(1, m + 1) if m % d == 0]


# ---------------------------------------------------------------------------
# A poset with its cyclic classes and its component structure


def find_iso(r1, r2, m):
    for p in itertools.permutations(range(m)):
        if pj.relabel(r1, p) == r2:
            return p
    return None


def compose(a, b):
    """(a o b)(t) = a(b(t))."""
    return tuple(a[b[t]] for t in range(len(b)))


def inverse(a):
    out = [0] * len(a)
    for t, s in enumerate(a):
        out[s] = t
    return tuple(out)


def perm_order(g):
    n = len(g)
    seen, o = [False] * n, 1
    for x in range(n):
        if not seen[x]:
            ln, y = 0, x
            while not seen[y]:
                seen[y] = True
                y = g[y]
                ln += 1
            o = o * ln // gcd(o, ln)
    return o


def perm_pow(g, j):
    out = list(range(len(g)))
    for _ in range(j):
        out = [g[x] for x in out]
    return tuple(out)


class Poset:
    def __init__(self, rel, n):
        self.rel, self.n = rel, n
        self.comps, self.lab = components(rel, n)
        self.lin = linexts(rel, n)
        rep = {}
        for w in self.lin:
            if w in rep:
                continue
            cls = [rot(w, k) for k in cuts(w, self.lab, self.comps)]
            r = min(cls)
            for v in cls:
                rep[v] = r
        self.cls = rep
        self.reps = sorted(set(rep.values()))
        self.eC = len(self.reps)
        self._types()
        self._fcache = {}

    def _types(self):
        groups = defaultdict(list)
        restr = []
        for i, c in enumerate(self.comps):
            r, B = restrict(self.rel, c)
            restr.append((r, B))
            groups[n7_sweep.canonical_fast(r, len(c))].append(i)
        self.blocks = []
        for key in sorted(groups):
            idxs = groups[key]
            rref, _ = restr[idxs[0]]
            m = len(self.comps[idxs[0]])
            phis = []
            for i in idxs:
                r, B = restr[i]
                p = find_iso(rref, r, m)
                phis.append(tuple(B[p[t]] for t in range(m)))
            aut = [tuple(a) for a in n7_sweep.automorphisms_fast(rref, m)] if m > 1 else [(0,)]
            self.blocks.append(dict(idx=idxs, phi=phis, aut=aut, m=m, rel=rref))
        # position of each element: (block, copy, t)
        self.pos = {}
        for bi, b in enumerate(self.blocks):
            for ci, phi in enumerate(b["phi"]):
                for t, x in enumerate(phi):
                    self.pos[x] = (bi, ci, t)

    def fixed(self, g):
        g = tuple(g)
        if g not in self._fcache:
            cls = self.cls
            self._fcache[g] = sum(1 for w in self.reps if cls[tuple(g[x] for x in w)] == w)
        return self._fcache[g]

    def element(self, perms, auts):
        """The automorphism with component permutation perms[bi] (on copies)
        and component maps auts[bi][ci] in Aut(T): phi_i(t) -> phi_{pi i}(a_i t)."""
        g = [0] * self.n
        for bi, b in enumerate(self.blocks):
            for ci, phi in enumerate(b["phi"]):
                cj = perms[bi][ci]
                a = auts[bi][ci]
                for t, x in enumerate(phi):
                    g[x] = b["phi"][cj][a[t]]
        return tuple(g)

    def decompose(self, g):
        """Per block: component permutation and component maps a_i."""
        perms, auts = [], []
        for bi, b in enumerate(self.blocks):
            k = len(b["idx"])
            pi, al = [0] * k, [None] * k
            for ci, phi in enumerate(b["phi"]):
                bj, cj, _ = self.pos[g[phi[0]]]
                assert bj == bi
                pi[ci] = cj
                al[ci] = tuple(self.pos[g[phi[t]]][2] for t in range(b["m"]))
            perms.append(pi)
            auts.append(al)
        return perms, auts

    def cycle_data(self, g):
        """Per block: list of (length, cycle product b in Aut(T))."""
        perms, auts = self.decompose(g)
        out = []
        for bi, b in enumerate(self.blocks):
            pi, al = perms[bi], auts[bi]
            seen, cyc = set(), []
            for c0 in range(len(pi)):
                if c0 in seen:
                    continue
                prod, c, ln = tuple(range(b["m"])), c0, 0
                while c not in seen:
                    seen.add(c)
                    prod = compose(al[c], prod)
                    c = pi[c]
                    ln += 1
                cyc.append((ln, prod))
            out.append(cyc)
        return out

    def conj_class_key(self, b, bi):
        aut = self.blocks[bi]["aut"]
        return min(compose(compose(x, b), inverse(x)) for x in aut)

    def conj_key(self, g):
        cd = self.cycle_data(g)
        return tuple(tuple(sorted((ln, self.conj_class_key(b, bi)) for ln, b in cyc))
                     for bi, cyc in enumerate(cd))

    def fix_data(self, g):
        N = perm_order(g)
        return [self.fixed(perm_pow(g, j)) for j in range(N)]

    def automorphisms(self):
        return [tuple(a) for a in n7_sweep.automorphisms_fast(self.rel, self.n)]

    def class_reps(self):
        """One g per conjugacy class of Aut(P)."""
        seen = {}
        for g in self.automorphisms():
            key = self.conj_key(g)
            if key not in seen:
                seen[key] = g
        return list(seen.values())


# ---------------------------------------------------------------------------
# The fake-degree polynomial of Cyc(P) for G = prod_T <c_T> wr S_{k_T}


def F_of_types(P, lams):
    """|Fix| of the element (1; pi) with pi of cycle type lams[bi] on block bi."""
    perms = [perm_of_type(l) for l in lams]
    auts = [[tuple(range(b["m"]))] * len(b["idx"]) for b in P.blocks]
    return P.fixed(P.element(perms, auts))


def fake_degree(P, rs=None):
    """X_P^{(r)}(q) = prod_T prod_{i<=k_T}(1-q^{r_T i}) * (1/|G|) sum_{h in G}
    |Fix h| / det(1 - q h), G = prod_T C_{r_T} wr S_{k_T}.  Only h with every
    cycle product trivial fix a class; they contribute r^{-cyc} / z_lambda."""
    if rs is None:
        rs = [1] * len(P.blocks)
    ks = [len(b["idx"]) for b in P.blocks]
    total = [Fraction(0)]
    for lams in itertools.product(*[list(partitions(k)) for k in ks]):
        F = F_of_types(P, lams)
        if F == 0:
            continue
        num = [1]
        for k, r in zip(ks, rs):
            for i in range(1, k + 1):
                num = pmul(num, one_minus_qk(r * i))
        for lam in lams:
            for part in lam:
                num = pdiv_one_minus_qk(num, part)
        w = Fraction(F)
        for lam, r in zip(lams, rs):
            w /= z_lambda(lam) * Fraction(r) ** len(lam)
        total = padd(total, pscale(num, w))
    total = ptrim(total)
    ok = all(c.denominator == 1 and c >= 0 for c in total)
    check(ok, f"fake degree integral nonnegative {sorted(P.rel)} rs={rs}")
    return [int(c) for c in total]


def fake_degree_of_Sk_set(k, fix_of_type):
    """Fake degree of an S_k-set given |Fix| as a function of cycle type."""
    total = [Fraction(0)]
    for lam in partitions(k):
        F = fix_of_type(lam)
        if F == 0:
            continue
        num = [1]
        for i in range(1, k + 1):
            num = pmul(num, one_minus_qk(i))
        for part in lam:
            num = pdiv_one_minus_qk(num, part)
        total = padd(total, pscale(num, Fraction(F, z_lambda(lam))))
    total = ptrim(total)
    assert all(c.denominator == 1 for c in total)
    return [int(c) for c in total]


# ---------------------------------------------------------------------------
# Springer regularity of g in G = prod_T <c_T> wr S_{k_T}


def cyclic_normal_form(P, g):
    """Choose c_T and write each cycle product as a power of c_T (up to
    conjugacy in Aut(T)).  Returns (rs, cycles) with cycles[bi] a list of
    (length, s) meaning b ~ c_T^s, or None if some block's cycle products do
    not lie in one cyclic subgroup up to conjugacy."""
    cd = P.cycle_data(g)
    rs, out = [], []
    for bi, cyc in enumerate(cd):
        aut = P.blocks[bi]["aut"]
        idt = tuple(range(P.blocks[bi]["m"]))
        c = max((b for _, b in cyc), key=lambda b: (perm_order(b), b))
        r = perm_order(c)
        powers = [idt]
        for _ in range(r - 1):
            powers.append(compose(c, powers[-1]))
        lst = []
        for ln, b in cyc:
            cls = {compose(compose(x, b), inverse(x)) for x in aut}
            s = next((s for s, pw in enumerate(powers) if pw in cls), None)
            if s is None:
                return None
            lst.append((ln, s))
        rs.append(r)
        out.append(lst)
    return rs, out


def is_regular(rs, cycles):
    """Springer regularity of the monomial element with the given cycles in
    prod_T G(r_T, 1, k_T) acting on prod C^{k_T}.  Eigenvalue angles are
    rationals mod 1.  Returns the order of the regular eigenvalue or None."""
    cands = set()
    for r, cyc in zip(rs, cycles):
        for ln, s in cyc:
            beta = Fraction(s, r)
            for t in range(ln):
                cands.add(((beta + t) / ln) % 1)
    for th in sorted(cands):
        ok = True
        for r, cyc in zip(rs, cycles):
            uncovered = 0
            for ln, s in cyc:
                covered = (ln * th - Fraction(s, r)) % 1 == 0
                if not covered:
                    uncovered += ln
                    continue
                for e in range(1, ln):
                    if (e * th * r) % 1 == 0:
                        ok = False
            if r > 1 and uncovered > 0:
                ok = False
            if r == 1 and uncovered > 1:
                ok = False
        if ok:
            return th.denominator
    return None


def in_W(P, g):
    """g permutes isomorphic copies with every cycle product trivial (so g is
    Aut(P)-conjugate to an element of W = prod_T S_{k_T})."""
    idt = [tuple(range(b["m"])) for b in P.blocks]
    return all(b == idt[bi] for bi, cyc in enumerate(P.cycle_data(g)) for _, b in cyc)


def criterion_W(P, g):
    """Theorem C's criterion for X^W to sieve <g>, g in W: for every e > 1
    dividing o(g), e <= max k_T, and if e divides every k_T then the element
    g^{o(g)/e} has every component cycle of length e."""
    ks = [len(b["idx"]) for b in P.blocks]
    N = perm_order(g)
    for e in divisors(N)[1:]:
        if e > max(ks):
            return False
        if all(k % e == 0 for k in ks):
            h = perm_pow(g, N // e)
            if any(ln != e for cyc in P.cycle_data(h) for ln, _ in cyc):
                return False
    return True


# ---------------------------------------------------------------------------
# Candidate polynomials independent of g


def natural_relabel(P):
    """Labels by position in the first linear extension (a natural labelling)."""
    w0 = P.lin[0]
    return {x: i for i, x in enumerate(w0)}


def maj(w, lab):
    return sum(i + 1 for i in range(len(w) - 1) if lab[w[i]] > lab[w[i + 1]])


def inv(w, lab):
    return sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if lab[w[i]] > lab[w[j]])


def base_reps(P):
    """B_P: the rotation of each class whose first block contains the
    component of the minimal element labelled 0."""
    lab = natural_relabel(P)
    x0 = P.lin[0][0]
    c0 = P.lab[x0]
    by_cls = defaultdict(list)
    for w, r in P.cls.items():
        by_cls[r].append(w)
    out = []
    for r, ws in by_cls.items():
        good = []
        for w in ws:
            cs = cuts(w, P.lab, P.comps)
            end = cs[1] if len(cs) > 1 else P.n
            if any(P.lab[x] == c0 for x in w[:end]):
                good.append(w)
        check(len(good) == 1, f"B_P unique rep {sorted(P.rel)}")
        out.append(good[0])
    return out, lab


def stat_poly(words, f, lab, shift=False):
    cnt = Counter(f(w, lab) for w in words)
    lo = min(cnt) if shift else 0
    p = [0] * (max(cnt) - lo + 1)
    for v, c in cnt.items():
        p[v - lo] += c
    return p


def cutless_maj(P, B):
    """maj generating function (natural labels of P) of the words in
    Lin(P|_B) with no nonzero cut."""
    lab = natural_relabel(P)
    r, elems = restrict(P.rel, B)
    comps, clab = components(r, len(elems))
    out = Counter()
    for w in linexts(r, len(elems)):
        if len(cuts(w, clab, comps)) == 1:
            out[maj(tuple(elems[x] for x in w), lab)] += 1
    if not out:
        return [0]
    p = [0] * (max(out) + 1)
    for v, c in out.items():
        p[v] += c
    return p


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]
        yield [[first]] + part


def block_candidate(P):
    """sum over set partitions pi of the components of [|pi|-1]_q! prod_B
    (maj g.f. of cutless words on B): a q-version of e_C = sum_pi
    (|pi|-1)! prod ir(B)."""
    total = [0]
    cache = {}
    for pi in set_partitions(range(len(P.comps))):
        term = q_fact(len(pi) - 1)
        for Bc in pi:
            key = tuple(sorted(Bc))
            if key not in cache:
                cache[key] = cutless_maj(P, [x for i in key for x in P.comps[i]])
            term = pmul(term, cache[key])
        total = padd(total, term)
    return ptrim(total)


def candidates(P):
    """g-independent candidates with X(1) = e_C(P)."""
    B, lab = base_reps(P)
    lex = P.reps
    out = {
        "fake": fake_degree(P),
        "maj(B_P)": stat_poly(B, maj, lab),
        "maj(B_P) shifted": stat_poly(B, maj, lab, shift=True),
        "inv(B_P)": stat_poly(B, inv, lab),
        "maj(lexmin)": stat_poly(lex, maj, lab),
        "block q-cumulant": block_candidate(P),
    }
    for name, X in out.items():
        check(sum(X) == P.eC, f"candidate {name} has X(1) = e_C {sorted(P.rel)}")
    return out


# ---------------------------------------------------------------------------
# Section ctl: controls for the instruments


def words_with_content(ms):
    letters = [i for i, m in enumerate(ms) for _ in range(m)]
    return sorted(set(itertools.permutations(letters)))


def section_ctl(out):
    print("== [ctl] controls", file=out)
    # RSW Thm 1.1 / Prop 4.4: words of content m under rotation, q-multinomial.
    n_ok = 0
    for ms in [(2, 2), (3, 1), (2, 1, 1), (2, 2, 2), (3, 3), (4, 2), (2, 2, 1, 1), (3, 2, 1), (4, 4)]:
        W = words_with_content(ms)
        n = sum(ms)
        fix = []
        for j in range(n):
            fix.append(sum(1 for w in W if rot(w, j) == w))
        X = q_multinomial(ms)
        ok = check(sieves(X, fix), f"RSW control {ms}")
        neg = check(not sieves(perturb(X), fix), f"RSW negative control {ms}")
        n_ok += ok and neg
    print(f"  [ctl-rsw] q-multinomial sieves words of content m under rotation; "
          f"perturbed X rejected: {n_ok}/9", file=out)
    # Fake degree of k-subsets of [k] (S_k-set) is the q-binomial.
    n_ok = 0
    for k in range(2, 8):
        for j in range(0, k + 1):
            def fix_sub(lam, j=j):
                # subsets fixed by pi of type lam: unions of cycles of total size j
                cnt = Counter()
                cnt[0] = 1
                for part in lam:
                    new = Counter()
                    for s, c in cnt.items():
                        new[s] += c
                        new[s + part] += c
                    cnt = new
                return cnt[j]
            X = fake_degree_of_Sk_set(k, fix_sub)
            n_ok += check(X == q_multinomial((j, k - j)), f"fake degree of {j}-subsets of [{k}]")
    print(f"  [ctl-binom] fake degree engine on k-subsets of [k] gives [k; j]_q: {n_ok}/33", file=out)
    # Kraskiewicz-Weyman: fake degree of S_k/C_k = sum_{maj w = 0 mod k} q^{maj w^-1}.
    n_ok = 0
    for k in range(2, 8):
        def fix_coset(lam, k=k):
            if len(set(lam)) != 1:
                return 0
            d = lam[0]
            return euler_phi(d) * d ** (k // d - 1) * factorial(k // d - 1)
        X = fake_degree_of_Sk_set(k, fix_coset)
        cnt = Counter()
        for w in itertools.permutations(range(k)):
            mj = sum(i + 1 for i in range(k - 1) if w[i] > w[i + 1])
            if mj % k == 0:
                wi = inverse(w)
                cnt[sum(i + 1 for i in range(k - 1) if wi[i] > wi[i + 1])] += 1
        Y = [cnt[i] for i in range(max(cnt) + 1)]
        n_ok += check(ptrim(X) == ptrim(Y), f"KW control k={k}")
        # and the poset computation of the antichain gives the same X
        if k <= 6:
            P = Poset(frozenset(), k)
            n_ok += check(fake_degree(P) == ptrim(X), f"antichain fake degree k={k}")
    print(f"  [ctl-kw] fake degree of S_k/C_k equals sum_(maj w = 0 mod k) q^maj(w^-1) "
          f"(k <= 7), and the poset code reproduces it for the antichain (k <= 6): {n_ok}/11", file=out)


# ---------------------------------------------------------------------------
# Section tk: P = T^{+k}


def connected_posets(mmax):
    allp = n7_sweep.unlabeled_posets(mmax)
    out = {}
    for m in range(1, mmax + 1):
        out[m] = [r for r in allp[m] if len(components(r, m)[0]) == 1]
    return out


def poset_name(rel, m):
    if m == 1:
        return "pt"
    if len(rel) == m * (m - 1) // 2:
        return f"C{m}"
    covers = sorted((a, b) for a, b in rel
                    if not any((a, c) in rel and (c, b) in rel for c in range(m)))
    return "cov" + ",".join(f"{a}<{b}" for a, b in covers)


def disjoint_copies(rel, m, k):
    return n7_sweep.disjoint_union(*[(rel, m)] * k)


def closed_form_tk(cs, k):
    """sum_{d | k} phi(d)/d * c_{k/d}/(k/d)! * (q;q)_k / (1 - q^d)^{k/d}."""
    total = [Fraction(0)]
    for d in divisors(k):
        num = [1]
        for i in range(1, k + 1):
            num = pmul(num, one_minus_qk(i))
        for _ in range(k // d):
            num = pdiv_one_minus_qk(num, d)
        w = Fraction(euler_phi(d) * cs[k // d], d * factorial(k // d))
        total = padd(total, pscale(num, w))
    total = ptrim(total)
    assert all(c.denominator == 1 for c in total)
    return [int(c) for c in total]


def words_maj(E, k):
    """sum over x in [E]^k of q^maj(x): the RSW polynomial for k-tuples under rotation."""
    cnt = Counter()
    for x in itertools.product(range(E), repeat=k):
        cnt[sum(i + 1 for i in range(k - 1) if x[i] > x[i + 1])] += 1
    return [cnt[i] for i in range(max(cnt) + 1)]


def section_tk(out, tkmax):
    print(f"== [tk] P = T^(+k), k >= 2, |P| <= {tkmax}", file=out)
    conn = connected_posets(tkmax // 2)
    rows = []
    t = Counter()
    for m in sorted(conn):
        for rel in conn[m]:
            T = Poset(rel, m)
            E = len(T.lin)
            name = poset_name(rel, m)
            cs = {0: 1}
            for k in range(1, tkmax // m + 1):
                r, n = disjoint_copies(rel, m, k)
                P = Poset(r, n) if k >= 2 else T
                cs[k] = P.eC
                if k < 2:
                    continue
                # sigma: rotation of the k copies with trivial component maps
                b = P.blocks[0]
                assert len(P.blocks) == 1 and len(b["idx"]) == k
                sigma = P.element([[(c + 1) % k for c in range(k)]],
                                  [[tuple(range(m))] * k])
                fix = P.fix_data(sigma)
                # closed fixed-point formula phi(d) d^{k/d - 1} c_{k/d}
                pred = []
                for j in range(k):
                    d = k // gcd(j, k)
                    pred.append(euler_phi(d) * d ** (k // d - 1) * cs[k // d])
                check(fix == pred, f"fixed-point formula {name}^{k}")
                t["formula"] += fix == pred
                X = fake_degree(P)
                Xc = closed_form_tk(cs, k)
                check(X == Xc, f"closed form {name}^{k}")
                t["closed"] += X == Xc
                ok = check(sieves(X, fix), f"fake degree sieves sigma on {name}^{k}")
                t["sigma"] += ok
                # sigma^j for every j generates a subgroup; the restriction of X sieves it
                for j in range(1, k):
                    g = perm_pow(sigma, j)
                    check(sieves(X, P.fix_data(g)), f"fake degree sieves sigma^{j} on {name}^{k}")
                # the (k-1)-cycle on k-1 of the copies (regular in S_k)
                if k >= 3:
                    tau = P.element([[(c + 1) % (k - 1) if c < k - 1 else c for c in range(k)]],
                                    [[tuple(range(m))] * k])
                    check(sieves(X, P.fix_data(tau)), f"fake degree sieves (k-1)-cycle on {name}^{k}")
                    t["tau"] += 1
                # pattern factor times words: also sieves sigma
                Q = Poset(*disjoint_copies(*n7_sweep.chain(m), k))
                A = fake_degree(Q)
                Y1 = pmul(A, words_maj(E, k))
                t["pat*words"] += check(sieves(Y1, fix), f"pattern*words {name}^{k}")
                # pattern factor times maj_T^k: the naive component factor
                Mt = stat_poly(T.lin, maj, natural_relabel(T), shift=True)
                Y2 = A
                for _ in range(k):
                    Y2 = pmul(Y2, Mt)
                ok2 = sieves(Y2, fix)
                t["pat*majT^k pass"] += ok2
                t["pat*majT^k tested"] += 1
                cands = candidates(P)
                res = {nm: sieves(Xn, fix) for nm, Xn in cands.items()}
                for nm, v in res.items():
                    t[f"cand {nm}"] += v
                t["cases"] += 1
                rows.append((name, m, k, n, E, P.eC, fix, X, res, ok2))
    # every conjugacy class of Aut(P), not only sigma
    nonfree_nonreg = []
    for m in sorted(conn):
        for rel in conn[m]:
            name = poset_name(rel, m)
            for k in range(2, tkmax // m + 1):
                P = Poset(*disjoint_copies(rel, m, k))
                for g in P.class_reps():
                    if perm_order(g) == 1:
                        continue
                    fxd = P.fix_data(g)
                    free = all(f == 0 for f in fxd[1:])
                    nf = cyclic_normal_form(P, g)
                    if nf is None:
                        t["all nowreath"] += 1
                        t["all nowreath free"] += free
                        continue
                    rs, cyc = nf
                    reg = is_regular(rs, cyc)
                    okG = sieves(fake_degree(P, rs), fxd)
                    key = ("reg" if reg else "nonreg") + ("/free" if free else "/nonfree")
                    t[f"all {key}"] += 1
                    t[f"all {key} XG"] += okG
                    if reg is not None:
                        check(okG, f"Springer on T^k {name}^{k} {g}")
                    if in_W(P, g):
                        okW = sieves(fake_degree(P), fxd)
                        t["allW"] += 1
                        t["allW agree"] += okW == criterion_W(P, g)
                        check(okW or not criterion_W(P, g), f"criterion sufficient {name}^{k} {g}")
                    if reg is None and not free:
                        nonfree_nonreg.append((name, k, g, P.cycle_data(g), fxd, okG,
                                               pstr(canonical_from_fix(fxd))))
    print("  [tk-allg] every class g != 1 of Aut(T^(+k)), |P| <= 8: (regular or not) x (<g> free on Cyc or not): "
          + ", ".join(f"{key} {t['all ' + key]} (X^G sieves {t['all ' + key + ' XG']})"
                      for key in ["reg/free", "reg/nonfree", "nonreg/free", "nonreg/nonfree"])
          + f"; no cyclic wreath subgroup contains g: {t['all nowreath']} (free: {t['all nowreath free']})", file=out)
    print(f"  [tk-W] classes g != 1 in W = S_k: X^W sieves <g> iff the criterion of Theorem C: "
          f"{t['allW agree']}/{t['allW']}", file=out)
    for name, k, g, cd, fxd, okG, can in nonfree_nonreg:
        lens = [ln for cyc in cd for ln, _ in cyc]
        print(f"  [tk-nonreg-nonfree] {name}^{k}: g = {g}, component cycle lengths {lens}, "
              f"fix = {fxd}, X^G sieves: {okG}, canonical X mod q^N-1 = {can}", file=out)
    print("  [tk-table] T | |T| | k | n | e(T) | e_C(P) | |Cyc^{sigma^j}|, j=0..k-1 | X_P(q) mod q^k-1 | X_P(q)", file=out)
    for name, m, k, n, E, eC, fix, X, res, ok2 in rows:
        print(f"    {name} | {m} | {k} | {n} | {E} | {eC} | {fix} | {pstr(fold(X, k))} | {pstr(X)}", file=out)
    print(f"  [tk-formula] |Cyc^(sigma^j)| = phi(d) d^(k/d-1) e_C(T^(+k/d)), d = k/gcd(j,k): "
          f"{t['formula']}/{t['cases']}", file=out)
    print(f"  [tk-closed] fake degree = sum_(d|k) phi(d)/d c_(k/d)/(k/d)! (q;q)_k/(1-q^d)^(k/d): "
          f"{t['closed']}/{t['cases']}", file=out)
    print(f"  [tk-sigma] fake degree X_P sieves <sigma> (and every <sigma^j>): {t['sigma']}/{t['cases']}; "
          f"also sieves the (k-1)-cycle on {t['tau']} cases with k >= 3", file=out)
    print(f"  [tk-pattern] X_(C_m^(+k))(q) * sum_(x in [e(T)]^k) q^maj(x) sieves <sigma>: "
          f"{t['pat*words']}/{t['cases']}; X_(C_m^(+k))(q) * maj_T(q)^k sieves: "
          f"{t['pat*majT^k pass']}/{t['pat*majT^k tested']}", file=out)
    for nm in ["fake", "maj(B_P)", "maj(B_P) shifted", "inv(B_P)", "maj(lexmin)", "block q-cumulant"]:
        print(f"  [tk-cand] {nm}: sieves <sigma> on {t['cand ' + nm]}/{t['cases']}", file=out)
    return rows


# ---------------------------------------------------------------------------
# Section sweep: every P with Aut(P) != 1, n <= NMAX


def section_sweep(out, nmax):
    print(f"== [sweep] every unlabeled P with n <= {nmax} and Aut(P) != 1, one g per conjugacy class", file=out)
    allp = n7_sweep.unlabeled_posets(nmax)
    t = Counter()
    by_n = defaultdict(Counter)
    first_fail = {}
    for n in range(1, nmax + 1):
        for rel in allp[n]:
            P = Poset(rel, n)
            G = P.automorphisms()
            if len(G) == 1:
                continue
            t["posets"] += 1
            by_n[n]["posets"] += 1
            disc = len(P.comps) > 1
            cands = candidates(P)
            for g in P.class_reps():
                if perm_order(g) == 1:
                    continue
                fix = P.fix_data(g)
                nf = cyclic_normal_form(P, g)
                if nf is None:
                    reg, rs = None, None
                    t["no cyclic wreath"] += 1
                else:
                    rs, cyc = nf
                    reg = is_regular(rs, cyc)
                    if reg is not None:
                        check(reg == perm_order(g), f"regular eigenvalue order {sorted(rel)} {g}")
                key = "reg" if reg is not None else "nonreg"
                t[f"pairs {key}"] += 1
                by_n[n][f"pairs {key}"] += 1
                if all(f == 0 for f in fix[1:]):
                    t[f"free {key}"] += 1
                # the G-adapted fake degree (Springer: must sieve every regular g)
                if rs is not None:
                    XG = fake_degree(P, rs)
                    ok = sieves(XG, fix)
                    if reg is not None:
                        check(ok, f"Springer: X^G sieves regular g {sorted(rel)} {g}")
                    t[f"XG {key} pass"] += ok
                    by_n[n][f"XG {key} pass"] += ok
                if in_W(P, g):
                    okW = sieves(cands["fake"], fix)
                    crit = criterion_W(P, g)
                    t["W pairs"] += 1
                    t["W pass"] += okW
                    t["W crit agrees"] += okW == crit
                    check(okW or not crit, f"criterion sufficient {sorted(rel)} {g}")
                free = all(f == 0 for f in fix[1:])
                wreg = reg is not None and all(r == 1 for r in rs)
                if disc:
                    t["disc " + ("free" if free else "nonfree")] += 1
                    t["disc wreg"] += wreg
                for nm, X in cands.items():
                    ok = sieves(X, fix)
                    if disc:
                        t[f"{nm} disc {'free' if free else 'nonfree'} pass"] += ok
                        if wreg:
                            t[f"{nm} disc wreg pass"] += ok
                    t[f"{nm} {key} pass"] += ok
                    if disc:
                        t[f"{nm} {key} disc pass"] += ok
                    if not ok and nm not in first_fail and disc:
                        first_fail[nm] = (n, sorted(rel), g, fix, pstr(fold(X, len(fix))))
                    # the fake degree for W must sieve every W-regular g (all b = 1)
                    if nm == "fake" and reg is not None and rs is not None and all(r == 1 for r in rs):
                        check(ok, f"fake degree sieves W-regular g {sorted(rel)} {g}")
                if disc:
                    t[f"disc pairs {key}"] += 1
    print("  [sweep-count] n | posets with Aut != 1 | classes g != 1 regular | non-regular | "
          "X^G sieves (regular) | X^G sieves (non-regular)", file=out)
    for n in sorted(by_n):
        c = by_n[n]
        print(f"    {n} | {c['posets']} | {c['pairs reg']} | {c['pairs nonreg']} | "
              f"{c['XG reg pass']} | {c['XG nonreg pass']}", file=out)
    print(f"  [sweep-springer] X^G sieves every regular class: {t['XG reg pass']}/{t['pairs reg']}; "
          f"non-regular classes where it still sieves: {t['XG nonreg pass']}/{t['pairs nonreg']} "
          f"(of which the action of <g> on Cyc(P) is free: {t['free nonreg']}); "
          f"classes with no cyclic wreath subgroup containing g: {t['no cyclic wreath']}", file=out)
    print(f"  [sweep-cand] g-independent candidates; counts are (regular pass/regular, "
          f"non-regular pass/non-regular) over disconnected P:", file=out)
    for nm in ["fake", "maj(B_P)", "maj(B_P) shifted", "inv(B_P)", "maj(lexmin)", "block q-cumulant"]:
        print(f"    {nm}: {t[nm + ' reg disc pass']}/{t['disc pairs reg']}, "
              f"{t[nm + ' nonreg disc pass']}/{t['disc pairs nonreg']}", file=out)
    print(f"  [sweep-W] g conjugate into W = prod S_(k_T) (trivial cycle products), g != 1: {t['W pairs']} classes; "
          f"X^W sieves <g>: {t['W pass']}; agrees with the criterion of Theorem C (sieves iff criterion): "
          f"{t['W crit agrees']}/{t['W pairs']}", file=out)
    print(f"  [sweep-cand2] disconnected P: (pairs where <g> is free, not free, g in W = prod S_k "
          f"and W-regular) = ({t['disc free']}, {t['disc nonfree']}, {t['disc wreg']}); passes:", file=out)
    for nm in ["fake", "maj(B_P)", "maj(B_P) shifted", "inv(B_P)", "maj(lexmin)", "block q-cumulant"]:
        print(f"    {nm}: free {t[nm + ' disc free pass']}, not free {t[nm + ' disc nonfree pass']}, "
              f"W-regular {t[nm + ' disc wreg pass']}", file=out)
    for nm, (n, rel, g, fix, Xs) in sorted(first_fail.items()):
        print(f"  [sweep-firstfail] {nm}: n={n} P={rel} g={g} fix={fix} X mod q^N-1 = {Xs}", file=out)
    return t


# ---------------------------------------------------------------------------
# Section obst: no single polynomial for every cyclic subgroup


def section_obst(out, nmax):
    print("== [obst] smallest P where two g of the same order have different fixed data", file=out)
    allp = n7_sweep.unlabeled_posets(nmax)
    found = None
    count = 0
    for n in range(1, nmax + 1):
        for rel in allp[n]:
            P = Poset(rel, n)
            if len(P.automorphisms()) == 1:
                continue
            data = defaultdict(set)
            for g in P.class_reps():
                data[perm_order(g)].add(tuple(P.fix_data(g)))
            bad = {N: s for N, s in data.items() if len(s) > 1}
            if bad:
                count += 1
                if found is None:
                    found = (n, sorted(rel), bad)
        if found is not None and found[0] == n:
            print(f"  [obst] smallest n = {n}: {count} poset(s) at this n; first P = {found[1]}, "
                  f"conflicting data by order: {dict((N, sorted(s)) for N, s in found[2].items())}", file=out)
            return found
    print("  [obst] none found", file=out)
    return None


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--tkmax", type=int, default=8)
    ap.add_argument("--sections", default="ctl,tk,sweep,obst")
    args = ap.parse_args(argv)
    out = sys.stdout
    secs = args.sections.split(",")
    if "ctl" in secs:
        section_ctl(out)
    if "tk" in secs:
        section_tk(out, args.tkmax)
    if "sweep" in secs:
        section_sweep(out, args.nmax)
    if "obst" in secs:
        section_obst(out, args.nmax)
    print(f"FAILED CHECKS: {len(FAILS)}", file=out)
    for f in FAILS[:30]:
        print("  " + f, file=out)
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
