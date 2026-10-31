#!/usr/bin/env python3
"""Necessity of clause (a) of Theorem C when gcd(k_i) > 1.

Companion to notes/cyclic_sieving_gcd.md ([GCD]).  Plain Python 3, no
dependencies, imports nothing from compute/.  Every section prints lines
tagged [tag]; the script exits 0 iff every check holds and every positive
control fails as it must.

Sections
  [eC]      e_C of chain unions: exponential formula vs brute force
  [brute]   real posets: brute-force Molien X_P vs the closed form (Lemma 2),
            and the CSP failure at a bad e (Theorem G in action)
  [phase]   the phase identity (Lemma 3) vs exact X_P(zeta)
  [ratio]   Lemma 4: A_d/A_1 <= (phi(d)/d) K mult_d(K)/mult_d(n) <= phi(d) K/d
  [ineq]    Lemma 5: the inequality (C), rigorously (exact rationals,
            interval bounds for sin), finite range + tail
  [exc]     the three exceptional (e, K, g)
  [exact]   independent exact check: Phi_e does not divide X_P (many cases),
            with the B(ii) vanishing as the positive control
  [yroot]   control: for y < 1 the conclusion is false (k = (4,4), e = 6)
"""
import cmath
import itertools
import math
import random
import sys
from fractions import Fraction
from functools import lru_cache

OUT, FAIL = [], []


def say(tag, msg):
    line = f"[{tag}] {msg}"
    OUT.append(line)
    print(line, flush=True)


def check(tag, cond, msg):
    say(tag, ("PASS " if cond else "FAIL ") + msg)
    if not cond:
        FAIL.append(f"[{tag}] {msg}")


# ------------------------------------------------------------- polynomials
# lists of Fractions, low degree first

def ptrim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(a, b):
    n = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pscale(a, c):
    return ptrim([x * c for x in a])


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
    if len(a) < len(b):
        return [], a
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    lead = Fraction(b[-1])
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1] / lead
        q[i] = c
        if c:
            for j, y in enumerate(b):
                a[i + j] -= c * y
    return ptrim(q), ptrim(a[:len(b) - 1])


def pdiv_exact(a, b):
    q, r = pdivmod(a, b)
    assert not r, "inexact division"
    return q


def one_minus_qp(p):
    r = [0] * (p + 1)
    r[0], r[p] = 1, -1
    return r


def qpoch(k):
    r = [1]
    for j in range(1, k + 1):
        r = pmul(r, one_minus_qp(j))
    return r


def ppow(a, n):
    r = [1]
    for _ in range(n):
        r = pmul(r, a)
    return r


@lru_cache(None)
def cyclotomic(e):
    r = [-1] + [0] * (e - 1) + [1]
    for d in range(1, e):
        if e % d == 0:
            r = pdiv_exact(r, list(cyclotomic(d)))
    return tuple(int(x) for x in r)


def peval(p, z):
    return sum(complex(c) * z ** i for i, c in enumerate(p))


def phi(d):
    return sum(1 for a in range(1, d + 1) if math.gcd(a, d) == 1)


def mult(x, d):
    """x! / ((x/d)!)^d, the d-way equal multinomial."""
    return math.factorial(x) // math.factorial(x // d) ** d


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
    z = 1
    for p in set(lam):
        c = lam.count(p)
        z *= p ** c * math.factorial(c)
    return z


def lcm_all(xs):
    r = 1
    for x in xs:
        r = r * x // math.gcd(r, x)
    return r


def element_orders(ks):
    orders = {1}
    for k in ks:
        orders = {o * lcm_all(lam) // math.gcd(o, lcm_all(lam)) for o in orders for lam in partitions(k)}
    return orders


def bad_es(ks):
    """e > max k_i dividing the order of some element of prod S_{k_i}."""
    os_ = element_orders(ks)
    return sorted({e for o in os_ for e in range(max(ks) + 1, o + 1) if o % e == 0})


def is_prime_power(e):
    ps = [p for p in range(2, e + 1) if e % p == 0 and all(p % q for q in range(2, p))]
    return len(ps) == 1


# ------------------------------------------------------------- e_C of chain unions

@lru_cache(None)
def eC_chains(content):
    """e_C(disjoint union of chains), content = tuple of (m, count) sorted.
    Exponential formula: sum e_C x^v / v! = log sum M(v) x^v / v!,
    M(v) = (sum m v_m)! / prod m!^{v_m}  (count of linear extensions)."""
    ms = [m for m, _ in content]
    target = tuple(c for _, c in content)
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


def content_of(ms, ks, d):
    c = {}
    for m, k in zip(ms, ks):
        c[m] = c.get(m, 0) + k // d
    return tuple(sorted(c.items()))


# ------------------------------------------------------------- the closed form (Lemma 2)

def gcd_all(ks):
    g = 0
    for k in ks:
        g = math.gcd(g, k)
    return g


def A_coeffs(ks, ms, y=Fraction(1)):
    """A_d = (phi(d)/d) * y^{g/d} * E_d / prod (k_i/d)!,  d | g, with
    E_d = e_C(disjoint union of C_{m_i}^{k_i/d})."""
    g = gcd_all(ks)
    A = {}
    for d in range(1, g + 1):
        if g % d:
            continue
        den = 1
        for k in ks:
            den *= math.factorial(k // d)
        A[d] = Fraction(phi(d), d) * Fraction(y) ** (g // d) * eC_chains(content_of(ms, ks, d)) / den
    return A


def X_closed(ks, ms, y=Fraction(1)):
    K = sum(ks)
    num = [1]
    for k in ks:
        num = pmul(num, qpoch(k))
    X = []
    for d, a in A_coeffs(ks, ms, y).items():
        X = padd(X, pscale(pdiv_exact(num, ppow(one_minus_qp(d), K // d)), a))
    return X


# ------------------------------------------------------------- [eC] brute force for chain unions

def lin_exts(n, less):
    """less[x] = bitmask of elements below x."""
    out = []

    def rec(w, used):
        if len(w) == n:
            out.append(tuple(w))
            return
        for x in range(n):
            if not used >> x & 1 and (less[x] & ~used) == 0:
                w.append(x)
                rec(w, used | 1 << x)
                w.pop()
    rec([], 0)
    return out


def build(components):
    """components: list of (m, relations as pairs (a,b) a<b, transitively closed or not).
    Returns n, less-masks, list of component element lists."""
    n, less, comps = 0, [], []
    for m, rels in components:
        base = n
        lm = [0] * m
        for a, b in rels:
            lm[b] |= 1 << a
        changed = True
        while changed:   # transitive closure
            changed = False
            for x in range(m):
                new = lm[x]
                for y in range(m):
                    if lm[x] >> y & 1:
                        new |= lm[y]
                if new != lm[x]:
                    lm[x], changed = new, True
        for x in range(m):
            less.append(lm[x] << base)
        comps.append(list(range(base, base + m)))
        n += m
    return n, less, comps


def minrot(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


def cyc_classes(n, less):
    L = lin_exts(n, less)
    return L, {minrot(w) for w in L}


def section_eC():
    tested = 0
    ok = True
    for content in [((1, 3),), ((1, 4),), ((2, 2),), ((2, 3),), ((1, 2), (2, 2)), ((1, 1), (2, 2)),
                    ((3, 2),), ((1, 3), (2, 1)), ((1, 2), (3, 1)), ((2, 2), (3, 1)), ((1, 5),)]:
        comps = []
        for m, c in content:
            comps += [(m, [(i, i + 1) for i in range(m - 1)])] * c
        n, less, _ = build(comps)
        _, C = cyc_classes(n, less)
        ok &= len(C) == eC_chains(content)
        tested += 1
    check("eC", ok, f"exponential formula = brute-force |Cyc| on {tested} chain unions")
    # control: the formula with M replaced by the multinomial without the c! is wrong
    bad = eC_chains(((2, 2),)) + 1
    check("eC", bad != 5 and eC_chains(((2, 2),)) == 5, "e_C(C_2 + C_2) = 5 ([CSC] §0 correction), control value 6 rejected")


# ------------------------------------------------------------- [brute] real posets

POSETS = {
    "pt": (1, []),
    "C2": (2, [(0, 1)]),
    "C3": (3, [(0, 1), (1, 2)]),
    "V": (3, [(0, 1), (0, 2)]),
    "L": (3, [(0, 2), (1, 2)]),
}


def e_of(T):
    m, rels = POSETS[T]
    n, less, _ = build([(m, rels)])
    return len(lin_exts(n, less))


def molien_brute(types, ks):
    """Brute-force X_P via Molien over W = prod S_{k_i} acting on copies by identity maps.
    Returns X (Fraction poly), dict of F by cycle type, and the data needed to act."""
    comps = []
    for T, k in zip(types, ks):
        comps += [POSETS[T]] * k
    n, less, cl = build(comps)
    L, C = cyc_classes(n, less)
    # copies of type i occupy component indices offs[i] .. offs[i]+k_i-1
    offs = list(itertools.accumulate([0] + list(ks)))[:-1]

    def perm_from_copyperms(cps):
        """cps[i] = permutation (tuple) of range(k_i). Returns perm of [n]."""
        p = list(range(n))
        for i, cp in enumerate(cps):
            for j, tj in enumerate(cp):
                src, dst = cl[offs[i] + j], cl[offs[i] + tj]
                for a, b in zip(src, dst):
                    p[a] = b
        return p

    def perm_of_type(lam):
        out, s = [], 0
        p = []
        for part in lam:
            p += [s + (t + 1) % part for t in range(part)]
            s += part
        return tuple(p)

    def F(p):
        return sum(1 for c in C if minrot(tuple(p[x] for x in c)) == c)

    num = [1]
    for k in ks:
        num = pmul(num, qpoch(k))
    X, Fs = [], {}
    for lams in itertools.product(*[list(partitions(k)) for k in ks]):
        p = perm_from_copyperms([perm_of_type(l) for l in lams])
        f = F(p)
        Fs[lams] = f
        if f:
            den, z = [1], 1
            for lam in lams:
                z *= zee(lam)
                for part in lam:
                    den = pmul(den, one_minus_qp(part))
            X = padd(X, pscale(pdiv_exact(num, den), Fraction(f, z)))
    return X, Fs, (C, perm_from_copyperms, perm_of_type, F)


def canonical_poly(fixes, N):
    """fixes[j] = |fixed points of g^j|, j = 0..N-1. Returns multiplicities m_t."""
    w = cmath.exp(2j * math.pi / N)
    out = []
    for t in range(N):
        v = sum(fixes[j] * w ** (-j * t) for j in range(N)) / N
        out.append(round(v.real))
        assert abs(v - round(v.real)) < 1e-6
    return out


def fold(X, N):
    r = [Fraction(0)] * N
    for i, c in enumerate(X):
        r[i % N] += c
    return r


def section_brute():
    cases = [
        # (types, ks, copy-cycle type of g per type)  -- (a)-only classes of [CSC] §3 and more
        (["pt"], [5], [(3, 2)]),
        (["pt"], [7], [(5, 2)]),
        (["pt"], [7], [(4, 3)]),
        (["pt"], [8], [(5, 3)]),
        (["pt", "C2"], [3, 3], [(3,), (2, 1)]),
        (["pt", "C2"], [2, 2], [(2,), (2,)]),        # no bad e: formula check only
        (["V", "pt"], [2, 2], [(2,), (1, 1)]),       # e(T) = 2 enters y
        (["V"], [2], [(2,)]),
        (["L", "C2"], [2, 2], [(2,), (2,)]),         # y = e(L) * e(C2) = 2
        (["pt", "C2"], [4, 2], [(3, 1), (2,)]),
    ]
    n_formula = n_csp = 0
    for types, ks, gtype in cases:
        X, Fs, (C, pcp, pot, F) = molien_brute(types, ks)
        g = gcd_all(ks)
        y = Fraction(1)
        for T, k in zip(types, ks):
            y *= Fraction(e_of(T)) ** (k // g)
        ms = [POSETS[T][0] for T in types]
        Xc = X_closed(ks, ms, y)
        same = Xc == X
        n_formula += same
        check("brute", same, f"{'+'.join(f'{T}^{k}' for T, k in zip(types, ks))}: Molien X_P = closed form "
                             f"(Lemma 2), y = {y}, X_P(1) = {sum(X)} = |Cyc| = {len(C)}")
        # Lemma 1 support: F vanishes off equal-cycle types with d | g
        supp_ok = all((f == 0) or (len({p for lam in lams for p in lam}) == 1 and g % lams[0][0] == 0)
                      for lams, f in Fs.items())
        check("brute", supp_ok, "   supp F within Lemma 1 types")
        bes = bad_es(ks)
        if not bes:
            continue
        # act by the chosen g, compute all powers' fixed points, test CSP
        p = pcp([pot(l) for l in gtype])
        N = lcm_all([part for l in gtype for part in l])
        fixes, q = [], list(range(len(p)))
        for j in range(N):
            fixes.append(F(q))
            q = [p[x] for x in q]
        canon = canonical_poly(fixes, N)
        sieves = fold(X, N) == canon
        es = [e for e in bes if N % e == 0]
        vals = []
        for e in es:
            z = cmath.exp(2j * math.pi / e)
            vals.append((e, fixes[N // e], peval(X, z)))
        info = ", ".join(f"e={e}: F(g^{N // e})={f}, |X_P(zeta_e)|={abs(v):.4g}" for e, f, v in vals)
        fails = (not sieves) and all(f == 0 and abs(v) > 1e-6 for e, f, v in vals) and es
        n_csp += bool(fails)
        check("brute", bool(fails), f"   g of copy type {gtype}, N={N}: CSP fails; {info}")
    say("brute", f"closed form matched on {n_formula}/{len(cases)} posets; CSP failure at a bad e on {n_csp} classes")
    # positive control: the closed form with the phi(d) dropped must disagree somewhere
    X, _, _ = molien_brute(["pt"], [5])
    num = qpoch(5)
    wrong = []
    for d in (1, 5):
        a = Fraction(1, d) * eC_chains(content_of([1], [5], d)) / math.factorial(5 // d)
        wrong = padd(wrong, pscale(pdiv_exact(num, ppow(one_minus_qp(d), 5 // d)), a))
    check("brute", wrong != X, "control: closed form without phi(d) differs from Molien on A_5")


# ------------------------------------------------------------- [phase] Lemma 3

def phase_value(ks, ms, y, e):
    """prod (zeta;zeta)_{k_i} e^{-i pi K/e} sum_d A_d R_d i^{K/d}, zeta = e^{2 pi i/e}."""
    K = sum(ks)
    z = cmath.exp(2j * math.pi / e)
    pre = 1
    for k in ks:
        for j in range(1, k + 1):
            pre *= 1 - z ** j
    S = 0
    for d, a in A_coeffs(ks, ms, y).items():
        R = (2 * math.sin(math.pi * d / e)) ** (-(K // d))
        S += float(a) * R * 1j ** (K // d)
    return pre * cmath.exp(-1j * math.pi * K / e) * S, S


def section_phase():
    rnd = random.Random(7)
    cases = [([5], [1]), ([5], [2]), ([4, 4], [1, 2]), ([4, 4], [2, 3]), ([3, 3], [1, 2]), ([6, 6], [1, 2]),
             ([7], [1]), ([8], [1]), ([4, 2], [1, 2]), ([2, 2, 4], [1, 2, 3]), ([6, 3], [2, 1]),
             ([5, 5], [1, 3]), ([9], [2]), ([10], [1])]
    agree = ctl = tot = 0
    for ks, ms in cases:
        for e in range(max(ks) + 1, max(ks) + 9):
            y = Fraction(rnd.randint(1, 6))
            X = X_closed(ks, ms, y)
            exact = peval(X, cmath.exp(2j * math.pi / e))
            val, S = phase_value(ks, ms, y, e)
            tot += 1
            agree += abs(exact - val) <= 1e-9 * max(1, abs(exact))
            # control: drop the phase i^{K/d}
            K = sum(ks)
            S0 = sum(float(a) * (2 * math.sin(math.pi * d / e)) ** (-(K // d)) for d, a in A_coeffs(ks, ms, y).items())
            v0 = val / S * S0 if S else 0
            ctl += abs(exact - v0) > 1e-6 * max(1, abs(exact))
    check("phase", agree == tot, f"Lemma 3 phase form = exact X_P(zeta_e) in {agree}/{tot} (k, m, y, e > max k)")
    check("phase", ctl > 0, f"control: dropping i^(K/d) gives a different value in {ctl}/{tot}")


# ------------------------------------------------------------- [ratio] Lemma 4

def section_ratio():
    n_ok = n_tot = 0
    worst = 0.0
    n_sub = [0, 0, 0]
    n_km = 0
    for ks in [(4,), (5,), (6,), (8,), (9,), (2, 2), (2, 4), (4, 4), (3, 3), (3, 6), (6, 6), (2, 2, 2), (4, 4, 4),
               (2, 2, 4), (6, 3, 3), (5, 5), (10,), (12,)]:
        g = gcd_all(ks)
        if g == 1:
            continue
        for ms in itertools.product(range(1, 4), repeat=len(ks)):
            if len(ks) > 1 and sum(1 for m in ms if m == 1) > 1:
                continue      # at most one type is the point
            K, n = sum(ks), sum(m * k for m, k in zip(ms, ks))
            if n > 40:
                continue
            A = A_coeffs(list(ks), list(ms))
            E1 = eC_chains(content_of(ms, ks, 1))
            eQ = math.factorial(n)
            for m, k in zip(ms, ks):
                eQ //= math.factorial(m) ** k
            n_sub[0] += E1 * K >= eQ
            n_km += 1
            for d in A:
                if d == 1:
                    continue
                ratio = A[d] / A[1]
                Bd = Fraction(phi(d), d) * K * Fraction(mult(K, d), mult(n, d))
                n_tot += 1
                n_ok += ratio <= Bd <= Fraction(phi(d) * K, d)
                worst = max(worst, float(ratio / Bd))
                Ed = eC_chains(content_of(ms, ks, d))
                eQd = math.factorial(n // d)
                for m, k in zip(ms, ks):
                    eQd //= math.factorial(m) ** (k // d)
                n_sub[1] += Ed <= eQd
                ff = 1
                for k in ks:
                    ff *= math.factorial(k) // math.factorial(k // d)
                n_sub[2] += ff <= math.factorial(K) // math.factorial(K // d)
    check("ratio", n_ok == n_tot, f"A_d/A_1 <= (phi(d)/d) K mult_d(K)/mult_d(n) <= phi(d) K/d on {n_ok}/{n_tot} (k, m, d); "
                                  f"max ratio/bound = {worst:.4f}")
    check("ratio", n_sub[1] == n_tot and n_sub[2] == n_tot and n_sub[0] == n_km,
          f"sub-steps: E_d <= e(Q_d) {n_sub[1]}/{n_tot}; prod k_i!/(k_i/d)! <= K!/(K/d)! {n_sub[2]}/{n_tot}; "
          f"K E_1 >= e(Q) {n_sub[0]}/{n_km} (k, m)")
    # antichain: the bound phi(d)K/d is attained up to the factor K/d
    A = A_coeffs([6], [1])
    check("ratio", all(A[d] / A[1] == phi(d) for d in A), "A_k antichain: A_d/A_1 = phi(d) exactly (k = 6)")
    # control: with y < 1 the inequality fails (y enters as y^{-(g-g/d)})
    y = Fraction(1, 50)
    A = A_coeffs([4, 4], [1, 2], y)
    K, n = 8, 12
    Bd = Fraction(phi(4), 4) * K * Fraction(mult(K, 4), mult(n, 4))
    check("ratio", A[4] / A[1] > Bd, f"control: k=(4,4), m=(1,2), y=1/50: A_4/A_1 = {float(A[4] / A[1]):.4g} > bound {float(Bd):.4g}")


# ------------------------------------------------------------- [ineq] Lemma 5, rigorous

PI_LO = Fraction(314159265358979323846, 10 ** 20)
PI_HI = Fraction(314159265358979323847, 10 ** 20)
SCALE = 2 ** 96


def _taylor_sin(x, N):
    s, t = Fraction(0), Fraction(x)
    for j in range(N + 1):
        s += t
        t = -t * x * x / ((2 * j + 2) * (2 * j + 3))
    return s


def sin_interval(num, den):
    """Rigorous [lo, hi] for sin(pi*num/den), with 0 < num/den <= 1/2 after reflection."""
    if 2 * num > den:
        num = den - num
    assert 0 < 2 * num <= den
    xlo, xhi = PI_LO * num / den, PI_HI * num / den
    if xhi > PI_HI / 2:
        xhi = PI_HI / 2
    N = 25   # alternating series, terms decreasing for x <= 2; truncation brackets sin
    lo = min(_taylor_sin(xlo, N), _taylor_sin(xlo, N + 1))
    hi = max(_taylor_sin(xhi, N), _taylor_sin(xhi, N + 1))
    if 2 * num == den:
        hi = Fraction(1)
    lo = Fraction(math.floor(lo * SCALE), SCALE)
    hi = Fraction(math.ceil(hi * SCALE), SCALE)
    return lo, hi


@lru_cache(None)
def s_int(d, e):
    lo, hi = sin_interval(d, e)
    return 2 * lo, 2 * hi


def Dminus(K, g):
    return [d for d in range(2, g + 1) if g % d == 0 and (K - K // d) % 4 == 2]


def C_upper(e, K, g, B=None):
    """Rigorous upper bound for sum_{d in D^-} B_d R_d/R_1 with B_d = phi(d)K/d by default."""
    s_hi = s_int(1, e)[1]
    tot = Fraction(0)
    for d in Dminus(K, g):
        Bd = Fraction(phi(d) * K, d) if B is None else B(d)
        tot += Bd * s_hi ** K / s_int(d, e)[0] ** (K // d)
    return tot


def C_full_upper_lower(e, K, g):
    """Lower bound for the no-phase sum over all d > 1 with the true antichain-type B_d = phi(d)
    (used only as a must-fail control)."""
    s_lo = s_int(1, e)[0]
    tot = Fraction(0)
    for d in range(2, g + 1):
        if g % d == 0:
            tot += phi(d) * s_lo ** K / s_int(d, e)[1] ** (K // d)
    return tot


def h_tail(K, s):
    """(K-1)(K/2) s^{ceil(K/2)} : the e >= 7 tail bound."""
    return Fraction((K - 1) * K, 2) * s ** ((K + 1) // 2)


R6 = Fraction(57736, 100000)   # > 1/sqrt(3)


def h6(K):
    return Fraction(5 * K, 2) * R6 ** (K // 4)


def section_ineq():
    # e >= 18: s <= 2 sin(pi/18) < 0.3474, h_tail(K) < 1 for all K >= 2
    s18 = s_int(1, 18)[1]
    sig = Fraction(3474, 10000)
    ok18 = s18 < sig and all(h_tail(K, sig) < 1 for K in range(2, 10)) and Fraction(9 * 10) * sig <= 7 * 8
    check("ineq", ok18, f"e >= 18: 2 sin(pi/18) <= {float(s18):.6f} < 0.3474; h(K) < 1 for K = 2..9 "
                        f"(max {max(float(h_tail(K, sig)) for K in range(2, 10)):.4f}), and h(K+2)/h(K) <= 1 for K >= 8")
    # e = 6 tail
    assert R6 * R6 * 3 > 1 and R6 < 1
    K6 = next(K for K in range(8, 400) if all(h6(K + t) < 1 for t in range(4)))
    ok6 = (K6 + 4) * R6 <= K6
    check("ineq", ok6 and 3 * R6 * R6 > 1, f"e = 6: h6(K) = (5K/2) r^floor(K/4) < 1 for K = {K6}..{K6 + 3}, "
                                          f"r = 0.57736 > 1/sqrt3, h6(K+4)/h6(K) <= 1 there; so K_6 = {K6}")
    Ke = {6: K6}
    for e in range(7, 18):
        s = s_int(1, e)[1]
        assert s < 1
        K0 = next(K for K in range(2, 2000)
                  if h_tail(K, s) < 1 and h_tail(K + 1, s) < 1 and (K + 1) * (K + 2) * s <= (K - 1) * K)
        Ke[e] = K0
    say("ineq", "tail thresholds K_e (for K >= K_e the sum is < 1 by the tail bound): "
                + ", ".join(f"e={e}: {k}" for e, k in Ke.items()))
    # finite range: every e in 6..17, g in 2..e-1, K multiple of g, K < K_e
    exc, worst, n = [], Fraction(0), 0
    for e in range(6, 18):
        for g in range(2, e):
            for K in range(g, Ke[e], g):
                if e == 6 and g == 5:
                    # d = 5 is excluded from D^- because K = 5t gives K - K/5 = 4t = 0 mod 4
                    assert 5 not in Dminus(K, g)
                n += 1
                u = C_upper(e, K, g)
                if u >= 1:
                    exc.append((e, K, g, float(u)))
                else:
                    worst = max(worst, u)
    say("ineq", f"finite range: {n} triples (e, K, g) with 6 <= e <= 17, g | K, 2 <= g < e, K < K_e")
    say("ineq", f"  sum < 1 in all but {len(exc)}: {[(e, K, g) for e, K, g, _ in exc]}; "
                f"largest non-exceptional upper bound = {float(worst):.6f}")
    check("ineq", sorted((e, K, g) for e, K, g, _ in exc) == [(6, 3, 3), (6, 8, 4), (7, 12, 6), (8, 7, 7)],
          "exceptional set is exactly {(6,3,3), (6,8,4), (7,12,6), (8,7,7)}")
    real = [(e, K, g) for e, K, g, _ in exc
            if any(e in bad_es(list(ks)) for ks in [[g] * (K // g)])]
    say("ineq", f"  exceptional triples where e can violate (a) (e divides an element order): {real}")
    # where e = 6 sits in the bad e
    bads = sorted({e for e in range(6, 18) if not is_prime_power(e)})
    say("ineq", f"non-prime-power e in 6..17 (the only e that can violate (a) below 18): {bads}")
    # control 1: without the phase restriction (all d > 1, even with the exact antichain B_d = phi(d))
    # the inequality fails, e.g. A_5 at e = 6 (d = 5 has the same phase as d = 1)
    lo = C_full_upper_lower(6, 5, 5)
    check("ineq", lo >= 1, f"control: no-phase sum for A_5, e = 6 is >= {float(lo):.4f} >= 1 (dominance alone fails)")
    cnt = sum(1 for e in range(6, 18) for g in range(2, e) for K in range(g, min(Ke[e], 60), g)
              if C_full_upper_lower(e, K, g) >= 1)
    check("ineq", cnt > 0, f"control: no-phase sum >= 1 in {cnt} triples of the finite range")


# ------------------------------------------------------------- [exc]

def section_exc():
    # (6, 3, 3): k = (3); m >= 2 gives n >= 6; m = 1 is A_3, where X = 1 + q^3 vanishes at zeta_6
    assert Dminus(3, 3) == [3]
    u = Fraction(phi(3), 3) * 3 * Fraction(mult(3, 3), mult(6, 3)) / s_int(3, 6)[0]
    check("exc", u < 1, f"(6,3,3): k=(3), m >= 2: sum <= {float(u):.4f} < 1")
    X = X_closed([3], [1])
    check("exc", X == [1, 0, 0, 1] and phi_divides(X, 6) and 6 not in element_orders([3]),
          "(6,3,3), A_3: X = 1 + q^3 vanishes at zeta_6 -- the one genuine exception; 6 is not an element order of S_3")
    # (6, 8, 4): k = (4,4), two distinct types, n = 4(m1+m2) >= 12; D^- = {4}
    assert Dminus(8, 4) == [4]
    B4 = Fraction(phi(4), 4) * 8 * Fraction(mult(8, 4), mult(12, 4))
    u = B4 / s_int(4, 6)[0] ** 2       # s = 1 at e = 6
    check("exc", u < 1, f"(6,8,4): k=(4,4), n >= 12: B_4 <= {float(B4):.5f}, R_4/R_1 = 1/3, sum <= {float(u):.5f} < 1")
    # (7, 12, 6): k = (6,6), n >= 18; D^- = {2, 6}
    assert Dminus(12, 6) == [2, 6]
    s_hi = s_int(1, 7)[1]
    u = sum(Fraction(phi(d), d) * 12 * Fraction(mult(12, d), mult(18, d)) * s_hi ** 12 / s_int(d, 7)[0] ** (12 // d)
            for d in (2, 6))
    check("exc", u < 1, f"(7,12,6): k=(6,6), n >= 18: sum <= {float(u):.3g} < 1")
    # (8, 7, 7): k = (7); m >= 2 gives n >= 14
    assert Dminus(7, 7) == [7]
    s_hi = s_int(1, 8)[1]
    u = Fraction(phi(7), 7) * 7 * Fraction(mult(7, 7), mult(14, 7)) * s_hi ** 7 / s_int(7, 8)[0]
    check("exc", u < 1, f"(8,7,7): k=(7), m >= 2: sum <= {float(u):.3g} < 1")
    # m = 1 (A_7, y = 1): only d = 1, 7, phases i^7 and i opposite; zero iff 6 s^6 = 1, s^2 = 2 - sqrt2
    A = A_coeffs([7], [1])
    s = 2 * math.sin(math.pi / 8)
    v = float(A[1]) * s ** -7 - float(A[7]) * s ** -1
    check("exc", A[1] == Fraction(1, 7) and A[7] == Fraction(6, 7) and abs(v) > 0.1,
          f"(8,7,7), A_7: A_1 = 1/7, A_7 = 6/7, A_1 R_1 - A_7 R_7 = {v:.4f} != 0 "
          f"(exactly: zero iff 6(20 - 14 sqrt2) = 1, false)")
    X = X_closed([7], [1])
    check("exc", abs(peval(X, cmath.exp(2j * math.pi / 8))) > 1e-3, "  and X_{A_7}(zeta_8) != 0 from the exact polynomial")


# ------------------------------------------------------------- [exact] independent check

def phi_divides(X, e):
    _, r = pdivmod(X, list(cyclotomic(e)))
    return not r


def type_vectors(Kmax, gmin=2):
    """multisets of (m, k), at most one m = 1, gcd(k) >= gmin, sum k <= Kmax, m <= 3."""
    out = []
    pairs = [(m, k) for m in (1, 2, 3) for k in range(1, Kmax + 1)]
    for r in (1, 2, 3):
        for combo in itertools.combinations_with_replacement(pairs, r):
            ks = [k for _, k in combo]
            ms = [m for m, _ in combo]
            if sum(ks) > Kmax or gcd_all(ks) < gmin:
                continue
            if sum(1 for m in ms if m == 1) > 1:
                continue
            if any(combo.count((m, k)) > 1 and m <= 2 for m, k in combo):
                continue   # sizes 1, 2 have a single connected poset: equal types would merge
            out.append((ks, ms))
    return out


def section_exact():
    n_cases = n_es = n_bad = 0
    ctl_cases = ctl_vanish = 0
    for ks, ms in type_vectors(12):
        bes = bad_es(ks)
        for y in (Fraction(1), Fraction(2), Fraction(7)):
            X = X_closed(ks, ms, y)
            for e in bes:
                n_es += 1
                if phi_divides(X, e):
                    n_bad += 1
            # positive control: Theorem B(ii), e <= max k_i, e not dividing some k_i => Phi_e | X
            for e in range(2, max(ks) + 1):
                if any(k % e for k in ks):
                    ctl_cases += 1
                    ctl_vanish += phi_divides(X, e)
        n_cases += 1
    check("exact", n_bad == 0, f"Phi_e does not divide X_P for every bad e: {n_cases} type vectors "
                               f"(<= 3 types, K <= 12, m <= 3, gcd >= 2), y in {{1,2,7}}, {n_es} (vector, y, e) triples")
    check("exact", ctl_vanish == ctl_cases and ctl_cases > 0,
          f"control: Phi_e divides X_P in {ctl_vanish}/{ctl_cases} B(ii) cases (the instrument detects zeros)")
    # larger single type, the A_k family (y = 1) and m = 2
    n2 = bad2 = 0
    for k in range(3, 21):
        for m in (1, 2):
            X = X_closed([k], [m])
            for e in bad_es([k]):
                n2 += 1
                bad2 += phi_divides(X, e)
    check("exact", bad2 == 0, f"single type k = 3..20, m = 1, 2: Phi_e never divides X_P ({n2} (k, m, e))")


# ------------------------------------------------------------- [yroot] y < 1 control

def section_yroot():
    """For k = (4,4), m = (1,2), e = 6, X_P(zeta_6) vanishes at some 0 < y < 1:
    the real projection sum_d A_d R_d Re(i^{K/d - K}) changes sign on (0, 1)."""
    ks, ms, e = [4, 4], [1, 2], 6
    K = 8

    def proj(y):
        A = A_coeffs(ks, ms, Fraction(y))
        tot = 0.0
        for d, a in A.items():
            tot += float(a) * (2 * math.sin(math.pi * d / e)) ** (-(K // d)) * (1j ** (K // d - K)).real
        return tot

    def imag(y):
        A = A_coeffs(ks, ms, Fraction(y))
        return sum(float(a) * (2 * math.sin(math.pi * d / e)) ** (-(K // d)) * (1j ** (K // d - K)).imag
                   for d, a in A.items())
    lo, hi = Fraction(1, 100), Fraction(1, 10)
    sign_change = proj(lo) < 0 < proj(hi)
    for _ in range(60):
        mid = (lo + hi) / 2
        if proj(mid) < 0:
            lo = mid
        else:
            hi = mid
    y0 = float(lo)
    X = X_closed(ks, ms, Fraction(lo))
    val = abs(peval(X, cmath.exp(2j * math.pi / 6)))
    X1 = X_closed(ks, ms, Fraction(1))
    check("yroot", sign_change and abs(imag(lo)) < 1e-12 and val < 1e-6 * abs(peval(X1, cmath.exp(2j * math.pi / 6))),
          f"control: k=(4,4), m=(1,2), e=6: X_P(zeta_6) = 0 at y = {y0:.6f} < 1 "
          f"(|X| = {val:.2e} there vs {abs(peval(X1, cmath.exp(2j * math.pi / 6))):.4g} at y = 1)")
    # [AUD] reported the root of 1048410 y^3 + 50 y - 12 near 0.0225
    check("yroot", abs(1048410 * y0 ** 3 + 50 * y0 - 12) < 1e-6, "  it is the root of 1048410y^3 + 50y - 12 found by [AUD]")


def main():
    for f in (section_eC, section_brute, section_phase, section_ratio, section_ineq, section_exc,
              section_exact, section_yroot):
        f()
    say("summary", f"{len(FAIL)} failure(s)")
    for x in FAIL:
        say("summary", "  " + x)
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
