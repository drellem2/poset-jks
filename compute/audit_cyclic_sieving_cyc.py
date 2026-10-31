"""Independent audit of notes/cyclic_sieving_cyc.md.

Self-contained: imports nothing from the other scripts of compute/.

Conventions.  A poset on [n] is a tuple `down` of bitmasks, down[j] = the set
of i < j (strict, transitively closed).  A word is a tuple of the n elements.
Cyc(P) is the set of rotation classes {w gamma^r} that contain a linear
extension; a class is keyed by the lexicographically least of its n
rotations.  g in Aut(P) acts by relabelling letters.  Fixed-point counts are
always computed by brute force from this action, never from a formula.

A CSP test for <g>, N = o(g) (the order of g as a permutation of [n]), uses
the canonical polynomial: m_t = #{<g>-orbits O on Cyc(P) : (N/|O|) | t}, and
(Cyc P, <g>, X) is a CSP iff X mod (q^N - 1) == sum_t m_t q^t.

Checks (bracketed tags are line labels in the output)
  [ctl-gen]    unlabelled posets n <= 7 (1, 2, 5, 16, 63, 318, 2045)
  [ctl-rsw]    RSW: words of content mu under rotation, X = q-multinomial
  [ctl-neg]    negative controls: perturbed polynomials are rejected
  [ctl-qbin]   fake degree of S_k on j-subsets == q-binomial, k <= 7
  [ctl-kw]     fake degree of S_k/C_k == sum_{maj w = 0 (k)} q^{maj w^-1}
  [ctl-eC]     e_C(chains) from the exponential formula vs brute force
  [tk]         the 23 posets T^{+k}, |P| <= 8: Prop. 2, (star), Thm A,
               sigma, (k-1)-cycle, every conjugacy class, X^G, regularity
  [thmC]       Theorem C criterion against the CSP, every class conjugate
               into W, every P with n <= 7, and T^{+k} with n = 8
  [springer]   X^G for every class of every P with n <= 7, Aut(P) != 1
  [cand]       the candidate polynomials of note Sec. 6
  [obst]       posets where F is not a function of the order, n <= 6
  [neca]       necessity of clause (a): symbolic in e(T), many (k, m)
"""

import itertools
import math
import os
import sys
from fractions import Fraction
from functools import lru_cache

# ---------------------------------------------------------------- polynomials
# A polynomial is a list of coefficients (int or Fraction), index = degree.


def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += x
    return ptrim(r)


def pscale(a, c):
    return ptrim([c * x for x in a])


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return ptrim(r)


def pdivmod(a, b):
    a = [Fraction(x) for x in ptrim(a)]
    b = ptrim(b)
    q = [Fraction(0)] * max(len(a) - len(b) + 1, 0)
    while len(a) >= len(b) and a:
        c = a[-1] / b[-1]
        s = len(a) - len(b)
        q[s] = c
        for i, y in enumerate(b):
            a[s + i] -= c * y
        a = ptrim(a)
    return ptrim(q), a


def pdiv_exact(a, b):
    q, r = pdivmod(a, b)
    assert not r, "inexact polynomial division"
    return q


def pmod_cyc(a, N):
    """a mod q^N - 1, as a length-N list."""
    r = [0] * N
    for i, x in enumerate(a):
        r[i % N] += x
    return r


def one_minus_qp(p):
    return [1] + [0] * (p - 1) + [-1]


def qpoch(k, step=1):
    """prod_{j=1..k} (1 - q^{step*j})."""
    r = [1]
    for j in range(1, k + 1):
        r = pmul(r, one_minus_qp(step * j))
    return r


def qint(j):
    return [1] * j


def qfact(k):
    r = [1]
    for j in range(1, k + 1):
        r = pmul(r, qint(j))
    return r


def qmultinomial(mu):
    r = qfact(sum(mu))
    for m in mu:
        r = pdiv_exact(r, qfact(m))
    return [int(x) for x in r]


@lru_cache(None)
def cyclotomic(e):
    r = [-1] + [0] * (e - 1) + [1]
    for d in range(1, e):
        if e % d == 0:
            r = pdiv_exact(r, cyclotomic(d))
    return tuple(int(x) for x in r)


def pgcd(a, b):
    a, b = ptrim([Fraction(x) for x in a]), ptrim([Fraction(x) for x in b])
    while b:
        _, r = pdivmod(a, b)
        a, b = b, r
    return [x / a[-1] for x in a] if a else []


def positive_roots(p, lower=None):
    """Number of distinct real roots of p in (0, oo), or in [lower, oo), by a Sturm sequence."""
    p = ptrim([Fraction(x) for x in p])
    while p and p[0] == 0:
        p = p[1:]
    if len(p) <= 1:
        return 0
    seq = [p, ptrim([i * x for i, x in enumerate(p)][1:])]
    while len(seq[-1]) > 1:
        _, r = pdivmod(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-x for x in r])

    def changes(vals):
        vals = [v for v in vals if v != 0]
        return sum(1 for u, v in zip(vals, vals[1:]) if (u > 0) != (v > 0))
    def at(q, y):
        return sum(c * y ** i for i, c in enumerate(q))
    lo = 0 if lower is None else lower
    n_lo = changes([at(q, lo) for q in seq]) if lower is not None else changes([q[0] for q in seq])
    root_at_lo = lower is not None and at(p, lower) == 0
    return n_lo - changes([q[-1] for q in seq]) + root_at_lo


def is_int_poly(p):
    return all(Fraction(x).denominator == 1 for x in p)


def fmt(p):
    p = ptrim(p)
    if not p:
        return "0"
    out = []
    for i, c in enumerate(p):
        if c:
            c = int(c) if Fraction(c).denominator == 1 else c
            out.append(f"{c}" if i == 0 else (f"{c}q^{i}" if c != 1 else f"q^{i}"))
    return " + ".join(out)


# --------------------------------------------------------- CSP test (exact)

def canonical_poly(perm_cls, N):
    """m_t for the cyclic group generated by a permutation of order | N."""
    n = len(perm_cls)
    seen = [False] * n
    m = [0] * N
    for s in range(n):
        if not seen[s]:
            size, x = 0, s
            while not seen[x]:
                seen[x] = True
                x = perm_cls[x]
                size += 1
            assert N % size == 0
            step = N // size
            for t in range(0, N, step):
                m[t] += 1
    return m


def sieves(X, perm_cls, N):
    return [Fraction(x) for x in pmod_cyc(X, N)] == [Fraction(x) for x in canonical_poly(perm_cls, N)]


# ---------------------------------------------------------------- permutations

def compose(a, b):
    return tuple(a[x] for x in b)


def inverse(a):
    r = [0] * len(a)
    for i, x in enumerate(a):
        r[x] = i
    return tuple(r)


def cycles(a):
    n, seen, out = len(a), set(), []
    for i in range(n):
        if i not in seen:
            c, x = [], i
            while x not in seen:
                seen.add(x)
                c.append(x)
                x = a[x]
            out.append(c)
    return out


def order(a):
    r = 1
    for c in cycles(a):
        r = r * len(c) // math.gcd(r, len(c))
    return r


def ppow(a, j):
    r = tuple(range(len(a)))
    for _ in range(j):
        r = compose(a, r)
    return r


def closure(gens, n):
    idt = tuple(range(n))
    G, frontier = {idt}, [idt]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = compose(g, x)
                if y not in G:
                    G.add(y)
                    nf.append(y)
        frontier = nf
    return G


def conj_classes(G, n):
    G = list(G)
    gens, H = [], {tuple(range(n))}
    for g in G:
        if g not in H:
            gens.append(g)
            H = closure(gens, n)
    ginv = [inverse(g) for g in gens]
    seen, classes = set(), []
    for x in sorted(G):
        if x in seen:
            continue
        cl, fr = {x}, [x]
        while fr:
            nf = []
            for y in fr:
                for g, gi in zip(gens, ginv):
                    z = compose(g, compose(y, gi))
                    if z not in cl:
                        cl.add(z)
                        nf.append(z)
            fr = nf
        seen |= cl
        classes.append((min(cl), len(cl)))
    return classes


# ---------------------------------------------------------------- posets

def make_poset(n, rels):
    """rels: pairs (i, j) meaning i < j; returns transitively closed `down`."""
    down = [0] * n
    for i, j in rels:
        down[j] |= 1 << i
    changed = True
    while changed:
        changed = False
        for j in range(n):
            m = down[j]
            for i in range(n):
                if m >> i & 1:
                    m |= down[i]
            if m != down[j]:
                down[j] = m
                changed = True
    for j in range(n):
        assert not down[j] >> j & 1
    return tuple(down)


def up_masks(down):
    n = len(down)
    up = [0] * n
    for j in range(n):
        for i in range(n):
            if down[j] >> i & 1:
                up[i] |= 1 << j
    return up


def lt(down, i, j):
    return bool(down[j] >> i & 1)


def colors(down):
    n = len(down)
    up = up_masks(down)
    col = [(bin(down[i]).count("1"), bin(up[i]).count("1")) for i in range(n)]
    while True:
        new = [(col[i], tuple(sorted(col[j] for j in range(n) if down[i] >> j & 1)),
                tuple(sorted(col[j] for j in range(n) if up[i] >> j & 1))) for i in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            return new
        col = new


def relabel(down, p):
    """p[old] = new."""
    n = len(down)
    nd = [0] * n
    for j in range(n):
        m = 0
        for i in range(n):
            if down[j] >> i & 1:
                m |= 1 << p[i]
        nd[p[j]] = m
    return tuple(nd)


def color_perms(down):
    """All bijections old->new that put colour classes in increasing order."""
    n = len(down)
    col = colors(down)
    cells = [[i for i in range(n) if col[i] == c] for c in sorted(set(col))]
    for choice in itertools.product(*[itertools.permutations(c) for c in cells]):
        p = [0] * n
        pos = 0
        for cell in choice:
            for x in cell:
                p[x] = pos
                pos += 1
        yield tuple(p)


def canon(down):
    return min(relabel(down, p) for p in color_perms(down))


def automorphisms(down):
    n = len(down)
    col = colors(down)
    cells = [[i for i in range(n) if col[i] == c] for c in sorted(set(col))]
    out = []
    for choice in itertools.product(*[itertools.permutations(c) for c in cells]):
        g = [0] * n
        for cell, img in zip(cells, choice):
            for x, y in zip(cell, img):
                g[x] = y
        g = tuple(g)
        if relabel(down, g) == down:
            out.append(g)
    return out


def all_posets(nmax):
    """Unlabelled posets by size: add a maximal element above a down-set."""
    res = {1: [(0,)]}
    for n in range(2, nmax + 1):
        seen = set()
        for P in res[n - 1]:
            m = n - 1
            for D in range(1 << m):
                if all((P[i] & ~D) == 0 for i in range(m) if D >> i & 1):
                    seen.add(canon(tuple(P) + (D,)))
        res[n] = sorted(seen)
    return res


def components(down):
    n = len(down)
    up = up_masks(down)
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for i in range(n):
        for j in range(n):
            if (down[i] | up[i]) >> j & 1:
                par[f(i)] = f(j)
    comps = {}
    for i in range(n):
        comps.setdefault(f(i), []).append(i)
    return sorted(comps.values())


def induced(down, elems):
    idx = {x: t for t, x in enumerate(elems)}
    return tuple(sum(1 << idx[i] for i in elems if down[x] >> i & 1) for x in elems)


def disjoint_union(*Ps):
    out, off = [], 0
    for P in Ps:
        out += [m << off for m in P]
        off += len(P)
    return tuple(out)


def natural_relabel(down):
    """Relabel so that i < j in P implies label i < label j (lex-first lin. ext.)."""
    L = next(lin_exts(down))
    p = [0] * len(down)
    for pos, x in enumerate(L):
        p[x] = pos
    return relabel(down, p)


def lin_exts(down):
    n = len(down)
    full = (1 << n) - 1
    w = []

    def rec(used):
        if used == full:
            yield tuple(w)
            return
        for x in range(n):
            if not used >> x & 1 and (down[x] & ~used) == 0:
                w.append(x)
                yield from rec(used | 1 << x)
                w.pop()
    yield from rec(0)


def minrot(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


class Cyc:
    """Cyc(P) with the action of permutations of [n]."""

    def __init__(self, down):
        self.down = down
        self.n = len(down)
        self.lin = list(lin_exts(down))
        keys = sorted({minrot(w) for w in self.lin})
        self.reps = keys
        self.idx = {k: i for i, k in enumerate(keys)}

    def __len__(self):
        return len(self.reps)

    def act(self, g):
        return [self.idx[minrot(tuple(g[x] for x in r))] for r in self.reps]

    def fix(self, g):
        return sum(1 for i, j in enumerate(self.act(g)) if i == j)


def perm_pow(p, j):
    r = list(range(len(p)))
    for _ in range(j):
        r = [p[x] for x in r]
    return r


# ------------------------------------------------------- S_k cycle types

def partitions(k, maxpart=None):
    if maxpart is None:
        maxpart = k
    if k == 0:
        yield ()
        return
    for p in range(min(k, maxpart), 0, -1):
        for rest in partitions(k - p, p):
            yield (p,) + rest


def zee(lam):
    r = 1
    for p in set(lam):
        c = lam.count(p)
        r *= p ** c * math.factorial(c)
    return r


def perm_of_type(lam):
    k = sum(lam)
    p, s = list(range(k)), 0
    for part in lam:
        for t in range(part):
            p[s + t] = s + (t + 1) % part
        s += part
    return tuple(p)


def fake_degree_Sk(k, F):
    """sum_t <M, R_t> q^t for an S_k-set with permutation character F(type)."""
    tot = []
    for lam in partitions(k):
        f = F(lam)
        if f:
            den = [1]
            for p in lam:
                den = pmul(den, one_minus_qp(p))
            tot = padd(tot, pscale(pdiv_exact(qpoch(k), den), Fraction(f, zee(lam))))
    return tot


def maj(w):
    return sum(i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def inv(w):
    return sum(1 for i in range(len(w)) for j in range(i + 1, len(w)) if w[i] > w[j])


# ------------------------------------------------------- W, G and X_P, X^G

class Structure:
    """Components, isomorphism types, identifications phi, Aut(T) per type."""

    def __init__(self, down):
        self.down = down
        self.n = len(down)
        comps = components(down)
        bytype = {}
        for c in comps:
            bytype.setdefault(canon(induced(down, c)), []).append(c)
        self.types = []
        for key in sorted(bytype, key=lambda k: (len(k), k)):
            copies = bytype[key]
            ref = induced(down, copies[0])
            phis = []
            for c in copies:
                sub = induced(down, c)
                for p in itertools.permutations(range(len(c))):
                    if relabel(ref, p) == sub:   # ref element t -> sub element p[t]
                        phis.append(tuple(c[p[t]] for t in range(len(c))))
                        break
            self.types.append(dict(ref=ref, copies=copies, phis=phis,
                                   aut=automorphisms(ref)))
        self.copy_of = {}
        for ti, T in enumerate(self.types):
            for j, phi in enumerate(T["phis"]):
                for t, x in enumerate(phi):
                    self.copy_of[x] = (ti, j, t)

    def ks(self):
        return [len(T["copies"]) for T in self.types]

    def element(self, data):
        """data[ti] = (pi, a) with pi a perm of copies and a[j] in Aut(T) (as tuple)."""
        g = [0] * self.n
        for ti, (pi, a) in enumerate(data):
            T = self.types[ti]
            for j, phi in enumerate(T["phis"]):
                for t, x in enumerate(phi):
                    g[x] = T["phis"][pi[j]][a[j][t]]
        return tuple(g)

    def decompose(self, g):
        """g -> per type (pi, a), a[j] = phi_{pi j}^{-1} g phi_j."""
        out = []
        for ti, T in enumerate(self.types):
            m = len(T["ref"])
            pi, a = [], []
            for j, phi in enumerate(T["phis"]):
                imgs = [self.copy_of[g[x]] for x in phi]
                assert len({(u, v) for u, v, _ in imgs}) == 1 and imgs[0][0] == ti
                pi.append(imgs[0][1])
                a.append(tuple(imgs[t][2] for t in range(m)))
            out.append((tuple(pi), a))
        return out

    def w_of_types(self, lams):
        idm = [tuple(range(len(T["ref"]))) for T in self.types]
        return self.element([(perm_of_type(lam), [idm[ti]] * sum(lam))
                             for ti, lam in enumerate(lams)])


def X_W(st, cyc):
    """Fake-degree polynomial of Cyc(P) for W = prod S_{k_i} (Molien, brute-force F)."""
    ks = st.ks()
    num = [1]
    for k in ks:
        num = pmul(num, qpoch(k))
    tot, Fw = [], {}
    for lams in itertools.product(*[list(partitions(k)) for k in ks]):
        w = st.w_of_types(lams)
        f = cyc.fix(w)
        Fw[lams] = f
        if f:
            den, z = [1], 1
            for lam in lams:
                z *= zee(lam)
                for p in lam:
                    den = pmul(den, one_minus_qp(p))
            tot = padd(tot, pscale(pdiv_exact(num, den), Fraction(f, z)))
    return tot, Fw


def cycle_products(st, data):
    """Per type: list of (cycle of copies, cycle product in Aut(T))."""
    res = []
    for ti, (pi, a) in enumerate(data):
        m = len(st.types[ti]["ref"])
        out = []
        for c in cycles(pi):
            prod = tuple(range(m))
            for j in c:          # apply a_{c0} first
                prod = compose(a[j], prod)
            out.append((c, prod))
        res.append(out)
    return res


def conj_in(aut, x, y):
    return any(compose(h, compose(x, inverse(h))) == y for h in aut)


def normal_form(st, g):
    """Return (c per type, normal-form g', monomial data) or None if mixed."""
    data = st.decompose(g)
    cps = cycle_products(st, data)
    cs, mono, newdata = [], [], []
    for ti, T in enumerate(st.types):
        m = len(T["ref"])
        idm = tuple(range(m))
        prods = [p for _, p in cps[ti]]
        cands = sorted(set(prods), key=lambda p: -order(p))
        chosen = None
        for c in cands:
            powers = [ppow(c, b) for b in range(order(c))]
            exps = []
            for p in prods:
                b = next((b for b, cb in enumerate(powers) if conj_in(T["aut"], p, cb)), None)
                if b is None:
                    break
                exps.append(b)
            else:
                chosen = (c, exps)
                break
        if chosen is None:
            return None
        c, exps = chosen
        r = order(c)
        k = len(T["copies"])
        pi, a = [0] * k, [idm] * k
        tdata = []
        for (cyc_, _), b in zip(cps[ti], exps):
            for t, j in enumerate(cyc_):
                pi[j] = cyc_[(t + 1) % len(cyc_)]
            a[cyc_[-1]] = ppow(c, b)
            tdata.append((len(cyc_), b))
        cs.append(c)
        mono.append((r, tdata))
        newdata.append((tuple(pi), a))
    return cs, st.element(newdata), mono


def group_G(st, cs):
    gens = []
    for ti, T in enumerate(st.types):
        k = len(T["copies"])
        idm = [tuple(range(len(T["ref"])))] * k
        other = [(tuple(range(len(U["copies"]))), [tuple(range(len(U["ref"])))] * len(U["copies"]))
                 for U in st.types]
        if k >= 2:
            for sw in [(1, 0) + tuple(range(2, k)), tuple(list(range(1, k)) + [0])]:
                d = list(other)
                d[ti] = (sw, idm)
                gens.append(st.element(d))
        d = list(other)
        a = list(idm)
        a[0] = cs[ti]
        d[ti] = (tuple(range(k)), a)
        gens.append(st.element(d))
    return closure(gens, st.n)


def X_G(st, cyc, cs):
    """Fake-degree polynomial for G = prod <c_i> wr S_{k_i}, summing over all of G.
    Asserts that every h with F(h) != 0 has all cycle products trivial."""
    G = group_G(st, cs)
    rs = [order(c) for c in cs]
    num = [1]
    for T, r in zip(st.types, rs):
        num = pmul(num, qpoch(len(T["copies"]), r))
    tot = []
    for h in G:
        f = cyc.fix(h)
        if not f:
            continue
        data = st.decompose(h)
        den = [1]
        for ti, cps in enumerate(cycle_products(st, data)):
            for c, p in cps:
                assert p == tuple(range(len(p))), "a class is fixed by h with a nontrivial cycle product"
                den = pmul(den, one_minus_qp(len(c)))
        tot = padd(tot, pscale(pdiv_exact(num, den), Fraction(f, len(G))))
    return tot, len(G)


def is_regular(mono, N):
    """Springer regularity of a monomial element of prod G(r_i,1,k_i).
    mono[i] = (r_i, [(cycle length, exponent b of the cycle product c^b)]).
    Eigenvalue lambda = exp(2 pi i u/N).  Returns the regular u's."""
    good = []
    for u in range(N):
        ok = True
        for r, cyc_ in mono:
            zero_len = 0
            for l, b in cyc_:
                # lambda^l == zeta_r^b  <=>  u*l*r == b*N (mod N*r)
                if (u * l * r - b * N) % (N * r) != 0:
                    zero_len += l
                    continue
                for t in range(1, l):    # lambda^t a r-th root of unity
                    if (u * t * r) % N == 0:
                        ok = False
            k = sum(l for l, _ in cyc_)
            if r >= 2 and zero_len > 0:
                ok = False
            if r == 1 and zero_len > 1:
                ok = False
        if ok:
            good.append(u)
    return good


# ------------------------------------------------------- Theorem C criterion

def thmC_criterion(ks, g_pi_types):
    """g in W given by its cycle lengths on copies, per type."""
    lens = [l for t in g_pi_types for l in t]
    N = 1
    for l in lens:
        N = N * l // math.gcd(N, l)
    a_ok, b_ok = True, True
    for e in range(2, N + 1):
        if N % e:
            continue
        if e > max(ks):
            a_ok = False
        if all(k % e == 0 for k in ks):
            # g^{N/e}: a cycle of length l becomes cycles of length l/gcd(l, N/e)
            s = N // e
            if any(l // math.gcd(l, s) != e for l in lens):
                b_ok = False
    return a_ok, b_ok


# ------------------------------------------------------- e_C of chains (exponential formula)

def eC_chains(ms_counts):
    """e_C(disjoint union of chains) for content {m: count} via
    sum_n e_C(n) x^n/n! = log sum_n M(n) x^n/n!, M(n) = (sum m n_m)!/prod m!^{n_m}."""
    ms = sorted(ms_counts)
    target = tuple(ms_counts[m] for m in ms)
    boxes = list(itertools.product(*[range(t + 1) for t in target]))

    def M(v):
        tot = sum(m * c for m, c in zip(ms, v))
        r = Fraction(math.factorial(tot))
        for m, c in zip(ms, v):
            r /= Fraction(math.factorial(m)) ** c * math.factorial(c)
        return r
    H = {v: M(v) for v in boxes if any(v)}

    def mul(A, B):
        C = {}
        for u, x in A.items():
            for v, y in B.items():
                w = tuple(a + b for a, b in zip(u, v))
                if all(a <= t for a, t in zip(w, target)):
                    C[w] = C.get(w, 0) + x * y
        return C
    L, Hr = {}, dict(H)
    for r in range(1, sum(target) + 1):
        for v, x in Hr.items():
            L[v] = L.get(v, 0) + Fraction((-1) ** (r + 1), r) * x
        Hr = mul(Hr, H)
    val = L.get(target, 0)
    for c in target:
        val *= math.factorial(c)
    assert val.denominator == 1
    return int(val)


# ------------------------------------------------------- output

OUT = []
FAIL = []


def say(tag, msg):
    line = f"[{tag}] {msg}"
    OUT.append(line)
    print(line, flush=True)


def check(tag, cond, msg):
    say(tag, ("ok   " if cond else "FAIL ") + msg)
    if not cond:
        FAIL.append(f"[{tag}] {msg}")


# ------------------------------------------------------- controls

def controls():
    # [ctl-rsw] words of content mu under rotation by one position
    n_ok = n_neg = tot = 0
    for mu in [(1, 1), (2, 1), (2, 2), (3, 1), (2, 1, 1), (3, 2), (2, 2, 1), (3, 3), (2, 2, 2), (4, 2), (3, 2, 1)]:
        letters = [i for i, m in enumerate(mu) for _ in range(m)]
        words = sorted(set(itertools.permutations(letters)))
        idx = {w: i for i, w in enumerate(words)}
        n = len(letters)
        rot = [idx[w[1:] + w[:1]] for w in words]
        X = qmultinomial(mu)
        tot += 1
        n_ok += sieves(X, rot, n)
        Y = list(X)
        Y[0] += 1
        Y[1] -= 1
        n_neg += not sieves(Y, rot, n)
    check("ctl-rsw", n_ok == tot, f"q-multinomial sieves rotation of words: {n_ok}/{tot}")
    check("ctl-neg", n_neg == tot, f"perturbed q-multinomial (q^1 -> q^0) rejected: {n_neg}/{tot}")
    # [ctl-qbin]
    ok = cnt = 0
    for k in range(1, 8):
        for j in range(k + 1):
            def F(lam, j=j):
                # number of j-subsets that are unions of cycles
                cnts = [0] * (j + 1)
                cnts[0] = 1
                for p in lam:
                    for s in range(j, p - 1, -1):
                        cnts[s] += cnts[s - p]
                return cnts[j]
            X = fake_degree_Sk(k, F)
            cnt += 1
            ok += [Fraction(x) for x in X] == [Fraction(x) for x in qmultinomial((j, k - j))]
    check("ctl-qbin", ok == cnt, f"fake degree of S_k on j-subsets == [k;j]_q: {ok}/{cnt}")
    # [ctl-kw] fake degree of S_k/C_k (fixed points of type lambda on cosets)
    ok = cnt = 0
    for k in range(2, 8):
        def F(lam, k=k):
            d = lam[0]
            if any(p != d for p in lam):
                return 0
            # |Fix(w) on S_k/C_k| = |C_k cap class(w)| * |C_S(w)| / |C_k|
            return sum(1 for j in range(k) if k // math.gcd(k, j) == d) * zee(lam) // k
        X = fake_degree_Sk(k, F)
        KW = [0] * (k * (k - 1) // 2 + 1)
        for w in itertools.permutations(range(k)):
            if maj(w) % k == 0:
                KW[maj(inverse(w))] += 1
        cnt += 1
        ok += [Fraction(x) for x in X] == [Fraction(x) for x in ptrim(KW)]
    check("ctl-kw", ok == cnt, f"fake degree of S_k/C_k == sum_(maj w = 0 mod k) q^maj(w^-1), k=2..7: {ok}/{cnt}")
    # [ctl-eC]
    ok = cnt = 0
    for content in [{1: 3}, {2: 2}, {2: 3}, {1: 2, 2: 1}, {3: 2}, {1: 1, 3: 1}, {2: 1, 3: 1}, {1: 4}, {2: 4}]:
        Ps = [tuple(range(m)) for m, c in content.items() for _ in range(c)]
        chains = [make_poset(m, [(i, i + 1) for i in range(m - 1)]) for m, c in content.items() for _ in range(c)]
        cnt += 1
        ok += len(Cyc(disjoint_union(*chains))) == eC_chains(content)
    check("ctl-eC", ok == cnt, f"exponential formula for e_C(chains) == brute force: {ok}/{cnt}")


# ------------------------------------------------------- one poset, all classes

def analyse(down, want_cand=False):
    """Everything per conjugacy class of Aut(P)."""
    st = Structure(down)
    cyc = Cyc(down)
    aut = automorphisms(down)
    classes = conj_classes(aut, len(down))
    XW, Fw = X_W(st, cyc)
    res = dict(n=len(down), eC=len(cyc), XW=XW, Fw=Fw, ks=st.ks(), classes=[])
    cacheG = {}
    for g, size in classes:
        if g == tuple(range(len(down))):
            continue
        N = order(g)
        act = cyc.act(g)
        Fs = [sum(1 for i, j in enumerate(perm_pow(act, s)) if i == j) for s in range(N)]
        free = all(f == 0 for f in Fs[1:])
        data = st.decompose(g)
        cps = cycle_products(st, data)
        inW = all(p == tuple(range(len(p))) for t in cps for _, p in t)
        rec = dict(g=g, N=N, Fs=Fs, free=free, inW=inW, size=size,
                   XW_sieves=sieves(XW, act, N))
        if inW:
            lens = [[len(c) for c, _ in t] for t in cps]
            rec["thmC"] = thmC_criterion(st.ks(), lens)
            rec["lens"] = lens
        nf = normal_form(st, g)
        if nf is None:
            rec["mixed"] = True
        else:
            cs, g2, mono = nf
            act2 = cyc.act(g2)
            rec["nf_ok"] = all(sum(1 for i, j in enumerate(perm_pow(act2, s)) if i == j) == Fs[s]
                               for s in range(N)) and order(g2) == N
            key = tuple(cs)
            if key not in cacheG:
                if all(order(c) == 1 for c in cs):
                    cacheG[key] = (XW, None)       # G = W
                else:
                    cacheG[key] = X_G(st, cyc, cs)
            XG, sizeG = cacheG[key]
            rec["XG"] = XG
            rec["XG_sieves"] = sieves(XG, act, N)
            reg = is_regular(mono, N)
            rec["regular"] = bool(reg)
            rec["reg_orders"] = sorted({N // math.gcd(N, u) for u in reg})
            rec["rs"] = [order(c) for c in cs]
        res["classes"].append(rec)
    if want_cand:
        res["cand"] = candidates(down, st, cyc)
    return res


def _job(args):
    down, want = args
    return down, analyse(down, want)


# ------------------------------------------------------- candidates (note Sec. 6)

def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def candidates(down, st, cyc):
    """Candidate polynomials (independent of g), for a naturally labelled P.
    Base component P_1 = the component containing element 0."""
    n = len(down)
    comps = components(down)
    compid = {x: i for i, c in enumerate(comps) for x in c}
    base = compid[0]

    def cuts(w):
        out, seen = [], set()
        for k in range(n):
            ids = {compid[x] for x in w[:k]}
            if all(all(y in w[:k] for y in comps[i]) for i in ids):
                out.append(k)
        return out
    BP, lexmin = {}, {}
    for w in cyc.lin:
        key = cyc.idx[minrot(w)]
        lexmin[key] = min(lexmin.get(key, w), w)
        cs = cuts(w)
        first_block = w[:cs[1]] if len(cs) > 1 else w
        if any(compid[x] == base for x in first_block):
            assert key not in BP
            BP[key] = w
    assert len(BP) == len(cyc)

    def gen(vals):
        p = [0] * (max(vals) + 1)
        for v in vals:
            p[v] += 1
        return p
    out = {}
    out["maj B_P"] = gen([maj(w) for w in BP.values()])
    mj = [maj(w) for w in BP.values()]
    out["maj B_P shifted"] = gen([v - min(mj) for v in mj])
    out["inv B_P"] = gen([inv(w) for w in BP.values()])
    out["maj lexmin"] = gen([maj(w) for w in lexmin.values()])
    # block q-cumulant
    tot = []
    memo = {}
    for part in set_partitions(list(range(len(comps)))):
        term = qfact(len(part) - 1)
        for B in part:
            key = tuple(sorted(B))
            if key in memo:
                term = pmul(term, memo[key])
                continue
            elems = sorted(x for i in B for x in comps[i])
            sub = induced(down, elems)
            sc = components(sub)
            vals = []
            for u in lin_exts(sub):
                # cutless: no proper nonempty prefix is a union of components of sub
                cutless = True
                for k in range(1, len(u)):
                    pre = set(u[:k])
                    if all(all(y in pre for y in c) or not any(y in pre for y in c) for c in sc):
                        cutless = False
                        break
                if cutless:
                    vals.append(maj(tuple(elems[x] for x in u)))
            memo[key] = gen(vals) if vals else []
            term = pmul(term, memo[key])
        tot = padd(tot, term)
    out["block q-cumulant"] = tot
    for name, p in out.items():
        assert sum(p) == len(cyc), name
    return out


# ------------------------------------------------------- [tk]

def connected_posets(m):
    return [P for P in all_posets(m)[m] if len(components(P)) == 1]


def tk_list(nmax=8):
    out = []
    for m in range(1, nmax // 2 + 1):
        for T in connected_posets(m):
            T = natural_relabel(T)
            for k in range(2, nmax // m + 1):
                out.append((T, k))
    return out


def tk_section(nmax=8):
    lst = tk_list(nmax)
    check("tk", len(lst) == 23, f"number of posets T^(+k) with k >= 2, |P| <= {nmax}: {len(lst)}")
    eC_cache = {}
    rows, allcls = [], []
    cand_counts = {}
    n_prop2 = n_star = n_sig = n_km1 = n_km1_tot = n_A = 0
    for T, k in lst:
        m = len(T)
        P = disjoint_union(*([T] * k))
        st = Structure(P)
        cyc = Cyc(P)
        XW, Fw = X_W(st, cyc)

        def c(j):
            if (T, j) not in eC_cache:
                eC_cache[(T, j)] = len(Cyc(disjoint_union(*([T] * j))))
            return eC_cache[(T, j)]
        # Proposition 2 on every type d^{k/d}, and F = 0 on all other types
        ok2 = True
        for lams, f in Fw.items():
            lam = lams[0]
            d = lam[0]
            if all(p == d for p in lam):
                ok2 &= f == sum(1 for a in range(1, d + 1) if math.gcd(a, d) == 1) * d ** (k // d - 1) * c(k // d)
            else:
                ok2 &= f == 0
        n_prop2 += ok2
        # (star)
        star = []
        for d in range(1, k + 1):
            if k % d == 0:
                phi = sum(1 for a in range(1, d + 1) if math.gcd(a, d) == 1)
                t = pdiv_exact(qpoch(k), _pow(one_minus_qp(d), k // d))
                star = padd(star, pscale(t, Fraction(phi * c(k // d), d * math.factorial(k // d))))
        n_star += [Fraction(x) for x in star] == [Fraction(x) for x in XW]
        # Theorem A
        n_A += is_int_poly(XW) and all(x >= 0 for x in XW) and sum(XW) == len(cyc)
        # sigma
        idm = tuple(range(m))
        sigma = st.element([(tuple(list(range(1, k)) + [0]), [idm] * k)])
        act = cyc.act(sigma)
        fixes = [sum(1 for i, j in enumerate(perm_pow(act, s)) if i == j) for s in range(k)]
        sg = sieves(XW, act, k)
        n_sig += sg
        if k >= 3:
            km1 = st.element([(tuple(list(range(1, k - 1)) + [0, k - 1]), [idm] * k)])
            n_km1_tot += 1
            n_km1 += sieves(XW, cyc.act(km1), k - 1)
        # candidates on sigma
        cands = candidates(P, st, cyc)
        Tlin = list(lin_exts(T))
        majT = [0] * (max(maj(u) for u in Tlin) + 1)
        for u in Tlin:
            majT[maj(u)] += 1
        Cm = make_poset(m, [(i, i + 1) for i in range(m - 1)])
        PC = disjoint_union(*([Cm] * k))
        XC, _ = X_W(Structure(PC), Cyc(PC))
        cands["X_C * majT^k"] = pmul(XC, _pow(majT, k))
        E = len(Tlin)
        wordmaj = [0] * (k * (k - 1) // 2 + 1)
        for x in itertools.product(range(E), repeat=k):
            wordmaj[maj(x)] += 1
        cands["X_C * sum_x q^maj x (pattern)"] = pmul(XC, ptrim(wordmaj))
        for name, p in cands.items():
            cand_counts[name] = cand_counts.get(name, 0) + sieves(p, act, k)
        pat = cands["X_C * sum_x q^maj x (pattern)"]
        rows.append((T, k, len(Tlin), len(cyc), fixes, pmod_cyc(XW, k), XW,
                     pmod_cyc(pat, k) == pmod_cyc(XW, k), ptrim(pat) == ptrim(XW)))
        say("tk-row", f"T={T} k={k} n={m*k} e(T)={len(Tlin)} e_C={len(cyc)} fix(sigma^j)={fixes} "
                      f"X mod q^k-1 = {fmt(pmod_cyc(XW, k))} | X = {fmt(XW)} | sieves sigma: {sg}")
    check("tk-prop2", n_prop2 == 23, f"Proposition 2 (and F = 0 off the types d^(k/d)): {n_prop2}/23")
    check("tk-star", n_star == 23, f"closed form (star) == Molien sum with brute-force F: {n_star}/23")
    check("tk-thmA", n_A == 23, f"X_P in N[q], X_P(1) = e_C(P): {n_A}/23")
    check("tk-sigma", n_sig == 23, f"X_P sieves sigma: {n_sig}/23")
    check("tk-km1", n_km1 == n_km1_tot == 8, f"X_P sieves the (k-1)-cycle: {n_km1}/{n_km1_tot}")
    for name, v in cand_counts.items():
        say("tk-cand", f"{name}: sieves sigma on {v}/23")
    npat_mod = sum(r[7] for r in rows)
    npat_eq = sum(r[8] for r in rows)
    say("tk-pattern", f"pattern x RSW product == X_P mod q^k-1 on {npat_mod}/23; equal as polynomials on {npat_eq}/23")
    return rows, cand_counts


def _pow(p, e):
    r = [1]
    for _ in range(e):
        r = pmul(r, p)
    return r


def tk_allg(nmax, pool):
    lst = tk_list(nmax)
    downs = [disjoint_union(*([T] * k)) for T, k in lst]
    results = pool.map(_job, [(d, False) for d in downs]) if pool else [_job((d, False)) for d in downs]
    tab = {}
    nonreg_nonfree = []
    for (down, res), (T, k) in zip(results, lst):
        for r in res["classes"]:
            if r.get("mixed"):
                key = ("mixed", r["free"])
                tab[key] = tab.get(key, [0, 0])
                tab[key][0] += 1
                continue
            assert r["nf_ok"]
            key = (r["regular"], r["free"])
            tab.setdefault(key, [0, 0])
            tab[key][0] += 1
            tab[key][1] += r["XG_sieves"]
            if not r["regular"] and not r["free"]:
                nonreg_nonfree.append((T, k, cycles(r["g"]), r["XG_sieves"], r["Fs"]))
    for key in sorted(tab, key=str):
        say("tk-allg", f"(regular, free) = {key}: {tab[key][0]} classes, X^G sieves {tab[key][1]}")
    for x in nonreg_nonfree:
        say("tk-allg", f"non-regular non-free: T={x[0]} k={x[1]} cycles={[len(c) for c in x[2]]} X^G sieves {x[3]} F(g^j)={x[4]}")
    return results, tab


# ------------------------------------------------------- driver

def main():
    nmax = 7
    tkmax = 8
    for a in sys.argv[1:]:
        if a.startswith("--nmax="):
            nmax = int(a.split("=")[1])
        if a.startswith("--tkmax="):
            tkmax = int(a.split("=")[1])
    cores = 1
    for a in sys.argv[1:]:
        if a.startswith("--jobs="):
            cores = int(a.split("=")[1])
    import multiprocessing as mp
    pool = mp.Pool(cores) if cores > 1 else None

    controls()
    P = all_posets(nmax)
    expected = [1, 2, 5, 16, 63, 318, 2045, 16999]
    check("ctl-gen", [len(P[n]) for n in range(1, nmax + 1)] == expected[:nmax],
          f"unlabelled posets: {[len(P[n]) for n in range(1, nmax + 1)]}")

    tk_section(tkmax)
    tkres, _ = tk_allg(tkmax, pool)

    # sweep all posets n <= nmax with Aut != 1
    jobs = []
    for n in range(2, nmax + 1):
        for down in P[n]:
            down = natural_relabel(down)
            if len(automorphisms(down)) > 1:
                jobs.append((down, len(components(down)) > 1))
    results = pool.map(_job, jobs, chunksize=4) if pool else [_job(j) for j in jobs]

    # [springer]
    for n in range(2, nmax + 1):
        rs = [res for d, res in results if len(d) == n]
        cl = [r for res in rs for r in res["classes"]]
        mixed = sum(1 for r in cl if r.get("mixed"))
        reg = [r for r in cl if not r.get("mixed") and r["regular"]]
        nreg = [r for r in cl if not r.get("mixed") and not r["regular"]]
        say("springer", f"n={n}: P with Aut!=1: {len(rs)}, regular classes {len(reg)}, non-regular {len(nreg)}, "
                        f"mixed {mixed}; X^G sieves regular {sum(r['XG_sieves'] for r in reg)}, "
                        f"non-regular {sum(r['XG_sieves'] for r in nreg)}; non-regular non-free "
                        f"{sum(1 for r in nreg if not r['free'])}")
    allcl = [r for d, res in results for r in res["classes"]]
    check("springer-nf", all(r.get("nf_ok", True) for r in allcl), "normal form g' has the same F(g^j) and order as g")
    reg = [r for r in allcl if r.get("regular")]
    check("springer-all", all(r["XG_sieves"] for r in reg), f"X^G sieves every regular class: {sum(r['XG_sieves'] for r in reg)}/{len(reg)}")
    check("springer-ord", all(r["N"] in r["reg_orders"] for r in reg), "some regular eigenvalue has order o(g) on every regular class")
    connected = [(d, res) for d, res in results if len(components(d)) == 1]
    ok = all(ptrim([Fraction(x) for x in r["XG"]]) == ptrim(pscale(qint(r["rs"][0]), Fraction(res["eC"], r["rs"][0])))
             for d, res in connected for r in res["classes"])
    check("springer-conn", ok, "connected P: X^G == (e(P)/r)[r]_q")

    # [thmC]: every class conjugate into W
    inW = [(d, r) for d, res in results for r in res["classes"] if r["inW"]]
    inW8 = [(d, r) for d, res in tkres if len(d) == tkmax for r in res["classes"] if r["inW"]]
    allW = inW + inW8
    agree = sum(1 for d, r in allW if (r["thmC"][0] and r["thmC"][1]) == r["XW_sieves"])
    check("thmC", agree == len(allW), f"Theorem C criterion == CSP of X_P: {agree}/{len(allW)} classes "
                                      f"({len(inW)} with n <= {nmax}, {len(inW8)} T^(+k) with n = {tkmax})")
    a_fail = [(d, r) for d, r in allW if not r["thmC"][0]]
    a_fail_b_ok = [(d, r) for d, r in a_fail if r["thmC"][1]]
    say("thmC", f"(a) fails on {len(a_fail)} classes ({len(a_fail_b_ok)} with (b) holding); CSP fails on all of them: "
                f"{all(not r['XW_sieves'] for d, r in a_fail)}")
    # the Prop. 2 / multi-type fixed-point formula on every class in W
    ok = 0
    for d, r in allW:
        lens = [l for t in r["lens"] for l in t]
        if len(set(lens)) > 1:
            ok += r["Fs"][1 % r["N"]] == 0 or r["N"] == 1
            continue
        dd = lens[0]
        st = Structure(d)
        blocks = [st.types[ti]["ref"] for ti, t in enumerate(r["lens"]) for _ in range(len(t))]
        e0 = len(Cyc(disjoint_union(*blocks)))
        phi = sum(1 for a in range(1, dd + 1) if math.gcd(a, dd) == 1)
        ok += r["Fs"][1] == phi * dd ** (len(lens) - 1) * e0
    check("thmC-F", ok == len(allW), f"F(w_d) = phi(d) d^(#cycles-1) e_C(one copy per cycle), F = 0 if cycle lengths differ: {ok}/{len(allW)}")

    # [cand]: disconnected P, classes g != 1
    disc = [(d, res) for d, res in results if len(components(d)) > 1]
    cl = [(d, res, r) for d, res in disc for r in res["classes"]]
    nonfree = [x for x in cl if not x[2]["free"]]
    free = [x for x in cl if x[2]["free"]]
    say("cand", f"disconnected (P, g != 1) classes, n <= {nmax}: {len(cl)} ({len(free)} free, {len(nonfree)} non-free)")
    names = ["maj B_P", "maj B_P shifted", "inv B_P", "maj lexmin", "block q-cumulant"]
    cyc_cache = {}
    for name in ["fake degree X_P"] + names:
        cnt = []
        for group in (nonfree, free):
            s = 0
            for d, res, r in group:
                if d not in cyc_cache:
                    cyc_cache[d] = Cyc(d)
                act = cyc_cache[d].act(r["g"])
                X = res["XW"] if name == "fake degree X_P" else res["cand"][name]
                s += sieves(X, act, r["N"])
            cnt.append(s)
        say("cand", f"{name}: non-free {cnt[0]}/{len(nonfree)}, free {cnt[1]}/{len(free)}")
    for d, res, r in nonfree:
        say("cand-nonfree", f"P={d} cycles={sorted(len(c) for c in cycles(r['g']))} inW={r['inW']} F={r['Fs']}")

    # [obst]
    obst = []
    for n in range(2, min(nmax, 6) + 1):
        for down in P[n]:
            aut = automorphisms(down)
            if len(aut) == 1:
                continue
            cyc = Cyc(down)
            byord = {}
            for g in aut:
                byord.setdefault(order(g), set()).add(cyc.fix(g))
            bad = {o: v for o, v in byord.items() if len(v) > 1}
            if bad:
                obst.append((n, down, bad))
    for n in range(2, min(nmax, 6) + 1):
        say("obst", f"n={n}: posets where F is not a function of o(g): {sum(1 for x in obst if x[0] == n)}")
    for x in obst:
        if x[0] <= 5:
            say("obst", f"  n={x[0]} P={x[1]} orders with several F values: {x[2]}")
    A4 = make_poset(4, [])
    cyc = Cyc(A4)
    check("obst-A4", cyc.fix((1, 0, 2, 3)) == 0 and cyc.fix((1, 0, 3, 2)) == 2, "A_4: F((12)) = 0, F((12)(34)) = 2")

    neca_section()

    say("done", f"{len(FAIL)} failures")
    for f in FAIL:
        say("done", f)
    if pool:
        pool.close()
    return 0 if not FAIL else 1


# ------------------------------------------------------- [neca]

def bad_es(ks):
    """e > max k_i that divide o(w) for some w in prod S_{k_i}."""
    orders = {1}
    for k in ks:
        new = set()
        for lam in partitions(k):
            l = 1
            for p in lam:
                l = l * p // math.gcd(l, p)
            for o in orders:
                new.add(o * l // math.gcd(o, l))
        orders = new
    return sorted({e for o in orders for e in range(max(ks) + 1, o + 1) if o % e == 0})


def neca_case(ms, ks):
    """Types with chain sizes ms and multiplicities ks; e(T_i) enters only via
    y = prod_i e(T_i)^{k_i/g}, g = gcd(k_i).  Returns, for each bad e, the gcd over
    Q[y] of the coordinates of X_P mod Phi_e (constant => X_P(zeta_e) != 0 for all y)."""
    g = 0
    for k in ks:
        g = math.gcd(g, k)
    K = sum(ks)
    num = [1]
    for k in ks:
        num = pmul(num, qpoch(k))
    terms = {}
    for d in range(1, g + 1):
        if g % d:
            continue
        content = {}
        for m, k in zip(ms, ks):
            content[m] = content.get(m, 0) + k // d
        p = eC_chains(content)
        phi = sum(1 for a in range(1, d + 1) if math.gcd(a, d) == 1)
        coef = Fraction(phi * d ** (K // d - 1) * p)
        for k in ks:
            coef /= d ** (k // d) * math.factorial(k // d)
        terms[g // d] = pscale(pdiv_exact(num, _pow(one_minus_qp(d), K // d)), coef)  # times y^{g/d}
    out = {}
    for e in bad_es(ks):
        Phi = list(cyclotomic(e))
        coords = {}
        for ydeg, poly in terms.items():
            _, r = pdivmod(poly, Phi)
            for i, x in enumerate(r):
                coords.setdefault(i, [0] * (g + 1))
                coords[i][ydeg] += x
        G = []
        for v in coords.values():
            G = pgcd(G, v) if G else ptrim([Fraction(x) for x in v])
        out[e] = G
    return out


def neca_section(kmax=16, mmax=6):
    n_cases = n_es = 0
    roots = []
    for k in range(3, kmax + 1):
        for m in range(1, mmax + 1):
            for e, G in neca_case([m], [k]).items():
                n_es += 1
                if positive_roots(G, 1):
                    roots.append((m, k, e, G))
            n_cases += 1
    say("neca", f"single type, k=3..{kmax}, |T|=1..{mmax}: {n_cases} (k, m), {n_es} pairs (k, m, e) with e > k; "
                f"X_P(zeta_e) has a root y >= 1 in {len(roots)} of them")
    for r in roots:
        say("neca", f"  root possible: m={r[0]} k={r[1]} e={r[2]} gcd={r[3]}")
    n2 = n2e = 0
    roots2, small = [], []
    for k1 in range(2, 9):
        for k2 in range(k1, 11 - k1):
            if math.gcd(k1, k2) == 1:
                continue
            for m1 in range(1, 4):
                for m2 in range(1, 4):
                    for e, G in neca_case([m1, m2], [k1, k2]).items():
                        n2e += 1
                        if positive_roots(G):
                            small.append((m1, m2, k1, k2, e))
                        if positive_roots(G, 1):
                            roots2.append((m1, m2, k1, k2, e, G))
                    n2 += 1
    say("neca", f"two types with gcd(k1,k2) > 1: {n2} (k1,k2,m1,m2), {n2e} bad e; root y >= 1 possible in {len(roots2)}")
    for r in roots2:
        say("neca", f"  root possible: {r}")
    say("neca", f"two types: X_P(zeta_e) as a polynomial in y has a root 0 < y < 1 in {len(small)} cases "
                f"(so nonvanishing is not a formal consequence of (star)): {small}")
    check("neca", not roots and not roots2, "X_P(zeta_e) != 0 for every e > max k_i in range, for every y = prod e(T_i)^(k_i/g) >= 1")


if __name__ == "__main__":
    sys.exit(main())
