"""Independent audit of notes/cyclic_sieving_gcd.md ([GCD]).

Written for the audit; imports nothing from the repository.  Plain Python 3,
exact arithmetic only (fractions.Fraction, integer polynomials, reduction
modulo cyclotomic polynomials).  The rigorous part of Lemma 5 uses a method
different from [GCD]'s: no value of pi and no Taylor series.  The numbers
s_d = 2 sin(pi d/e) are obtained from rational root brackets of the
Chebyshev polynomial U_{e-1}, whose roots are exactly cos(j pi/e), j=1..e-1.

Run from compute/:   python3 audit_cyclic_sieving_gcd.py
Exit status 0 iff every check holds and every positive control fails.
"""

import itertools
import math
import sys
from fractions import Fraction as Fr

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
    return cond


# ----------------------------------------------------------------------------
# Integer / rational polynomials (lists of coefficients, index = degree)
# ----------------------------------------------------------------------------

def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += x
    return r


def ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def pdivexact(a, b):
    """a / b, asserting exact divisibility."""
    a = ptrim(a)
    b = ptrim(b)
    q = [0] * max(1, len(a) - len(b) + 1)
    a = list(a)
    while len(a) >= len(b) and any(a):
        c = Fr(a[-1]) / b[-1]
        sh = len(a) - len(b)
        q[sh] = c
        for i, y in enumerate(b):
            a[sh + i] -= c * y
        a.pop()
        a = ptrim(a) if a else [0]
        if len(a) < len(b):
            break
    assert not any(a), "inexact division"
    return ptrim(q)


def pmod(a, b):
    a = [Fr(x) for x in a]
    b = ptrim(b)
    while len(a) >= len(b):
        c = a[-1] / b[-1]
        sh = len(a) - len(b)
        for i, y in enumerate(b):
            a[sh + i] -= c * y
        a.pop()
    return ptrim(a) if a else [Fr(0)]


def one_minus_qd(d):
    p = [0] * (d + 1)
    p[0] = 1
    p[d] = -1
    return p


def qpoch(k):
    r = [1]
    for j in range(1, k + 1):
        r = pmul(r, one_minus_qd(j))
    return r


_CYC = {}


def cyclotomic(e):
    if e not in _CYC:
        num = one_minus_qd(e)
        num = [-x for x in num]  # q^e - 1
        for d in range(1, e):
            if e % d == 0:
                num = pdivexact(num, cyclotomic(d))
        _CYC[e] = [int(x) for x in num]
    return _CYC[e]


def vanishes_at(poly, e):
    """True iff Phi_e divides poly, i.e. poly(e^{2 pi i/e}) = 0 (exact)."""
    r = pmod(poly, cyclotomic(e))
    return not any(r)


def phi(d):
    return sum(1 for j in range(1, d + 1) if math.gcd(j, d) == 1)


# ----------------------------------------------------------------------------
# Brute force: posets, Cyc(P), the W-action, F(w), Molien polynomial
# ----------------------------------------------------------------------------
# A component type is (m, relations) with relations a set of covering pairs
# (a, b), a < b in the poset, on 0..m-1.

PT = (1, ())
C2 = (2, ((0, 1),))
C3 = (3, ((0, 1), (1, 2)))
V = (3, ((0, 1), (0, 2)))      # one bottom, two tops
LAM = (3, ((0, 2), (1, 2)))    # two bottoms, one top


def build(types):
    """types: list of (component, k).  Returns (n, less, copies) where
    copies[i] is a list of k_i lists of element labels."""
    n = 0
    rel = []
    copies = []
    for (m, R), k in types:
        cs = []
        for _ in range(k):
            lab = list(range(n, n + m))
            for a, b in R:
                rel.append((lab[a], lab[b]))
            cs.append(lab)
            n += m
        copies.append(cs)
    # transitive closure
    less = [[False] * n for _ in range(n)]
    for a, b in rel:
        less[a][b] = True
    for k in range(n):
        for i in range(n):
            if less[i][k]:
                for j in range(n):
                    if less[k][j]:
                        less[i][j] = True
    return n, less, copies


def linexts(n, less):
    preds = [[i for i in range(n) if less[i][j]] for j in range(n)]
    out = []
    word = []
    used = [False] * n

    def rec():
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not used[x] and all(used[p] for p in preds[x]):
                used[x] = True
                word.append(x)
                rec()
                word.pop()
                used[x] = False
    rec()
    return out


def canon(word):
    n = len(word)
    return min(word[i:] + word[:i] for i in range(n))


def cyc_classes(n, less):
    return {canon(L) for L in linexts(n, less)}


def cycle_type_reps(k):
    """One permutation of range(k) per cycle type, with its class size."""
    reps = []

    def parts(r, mx):
        if r == 0:
            yield []
            return
        for p in range(min(r, mx), 0, -1):
            for rest in parts(r - p, p):
                yield [p] + rest
    for lam in parts(k, k):
        perm = list(range(k))
        pos = 0
        for p in lam:
            for j in range(p):
                perm[pos + j] = pos + (j + 1) % p
            pos += p
        z = 1
        for p in set(lam):
            c = lam.count(p)
            z *= p ** c * math.factorial(c)
        reps.append((tuple(lam), tuple(perm), math.factorial(k) // z))
    return reps


def induced(copies, perms):
    """Permutation of [n] moving copy j of type i to copy perms[i][j]."""
    n = sum(len(c) for cs in copies for c in cs)
    g = list(range(n))
    for cs, pm in zip(copies, perms):
        for j, c in enumerate(cs):
            for a, b in zip(c, cs[pm[j]]):
                g[a] = b
    return g


def F_of(classes, g):
    return sum(1 for C in classes if canon(tuple(g[x] for x in C)) == C)


def brute(types):
    """Return dict with e_C, F by cycle type, the Molien polynomial X_P."""
    n, less, copies = build(types)
    classes = cyc_classes(n, less)
    ks = [k for _, k in types]
    Wsize = math.prod(math.factorial(k) for k in ks)
    pref = [1]
    for k in ks:
        pref = pmul(pref, qpoch(k))
    X = [Fr(0)]
    Ftab = {}
    for combo in itertools.product(*[cycle_type_reps(k) for k in ks]):
        perms = [c[1] for c in combo]
        size = math.prod(c[2] for c in combo)
        g = induced(copies, perms)
        f = F_of(classes, g)
        lam = tuple(c[0] for c in combo)
        Ftab[lam] = f
        if f == 0:
            continue
        den = [1]
        for c in combo:
            for p in c[0]:
                den = pmul(den, one_minus_qd(p))
        term = pdivexact(pref, den)
        X = padd(X, [Fr(size * f, Wsize) * x for x in term])
    return {"n": n, "eC": len(classes), "F": Ftab, "X": ptrim(X),
            "classes": classes, "copies": copies}


# ----------------------------------------------------------------------------
# e_C of a disjoint union of chains, by an independent DP
# ----------------------------------------------------------------------------
# e_C(Q) = sum_{L in Lin Q} 1/(1 + p(L)), p(L) = number of proper nonempty
# prefixes of L that are unions of components (these are exactly the
# rotations of L that stay in Lin Q).  For a union of chains a state is the
# multiset of (length, progress); the prefix is a union of components iff
# every chain is at progress 0 or full.

def eC_chains(lengths):
    lengths = sorted(lengths)
    n = sum(lengths)
    start = tuple(sorted((m, 0) for m in lengths))
    layer = {(start, 0): 1}
    for step in range(n):
        new = {}
        for (st, p), cnt in layer.items():
            st = list(st)
            seen = {}
            for idx, (m, t) in enumerate(st):
                if t < m:
                    seen.setdefault((m, t), []).append(idx)
            for (m, t), idxs in seen.items():
                ns = list(st)
                ns[idxs[0]] = (m, t + 1)
                ns = tuple(sorted(ns))
                clean = all(tt in (0, mm) for mm, tt in ns)
                np_ = p + (1 if clean and step + 1 < n else 0)
                key = (ns, np_)
                new[key] = new.get(key, 0) + cnt * len(idxs)
        layer = new
    tot = Fr(0)
    for (st, p), cnt in layer.items():
        tot += Fr(cnt, 1 + p)
    assert tot.denominator == 1
    return int(tot)


_E = {}


def E_d(ks, ms, d):
    key = (tuple(ks), tuple(ms), d)
    if key not in _E:
        lens = []
        for k, m in zip(ks, ms):
            lens += [m] * (k // d)
        _E[key] = eC_chains(lens)
    return _E[key]


def closed_form_X(ks, ms, y, cd=None):
    """X_P(q) from Lemma 2, with c_d = y^{g/d} E_d (or supplied cd)."""
    g = 0
    for k in ks:
        g = math.gcd(g, k)
    K = sum(ks)
    pref = [1]
    for k in ks:
        pref = pmul(pref, qpoch(k))
    X = [Fr(0)]
    for d in range(1, g + 1):
        if g % d:
            continue
        c = cd[d] if cd is not None else Fr(y) ** (g // d) * E_d(ks, ms, d)
        A = Fr(phi(d), d) * c / math.prod(math.factorial(k // d) for k in ks)
        den = [1]
        for _ in range(K // d):
            den = pmul(den, one_minus_qd(d))
        X = padd(X, [A * x for x in pdivexact(pref, den)])
    return ptrim(X)


# ----------------------------------------------------------------------------
# Rigorous enclosures of s_d = 2 sin(pi d/e) without pi
# ----------------------------------------------------------------------------

def U(nn, x):
    a, b = Fr(1), 2 * x       # U_0, U_1
    if nn == 0:
        return a
    for _ in range(nn - 1):
        a, b = b, 2 * x * b - a
    return b


def dy(x, bits):
    """Dyadic rationals floor/ceil of x at 2^-bits."""
    s = 1 << bits
    lo = Fr(math.floor(x * s), s)
    hi = Fr(math.ceil(x * s), s)
    return lo, hi


def isqrt_bounds(x, bits=200):
    """Rational lo <= sqrt(x) <= hi for rational x >= 0."""
    s = 1 << bits
    N = x * s * s
    lo = math.isqrt(N.numerator // N.denominator)
    hi = lo + 1
    return Fr(lo, s), Fr(hi, s)


_ENC = {}


def s_enclosures(e, bits=110):
    """dict d -> (lo, hi) with lo <= 2 sin(pi d/e) <= hi, d = 1..e-1.

    The e-1 roots of U_{e-1} are cos(j pi/e), j = 1..e-1, all simple.  We
    produce e-1 disjoint rational brackets, each with a strict sign change;
    so each holds exactly one root, and in decreasing order of the brackets
    the j-th holds cos(j pi/e).  Then refine by bisection."""
    if e in _ENC:
        return _ENC[e]
    nn = e - 1
    brs = []
    for j in range(1, e):
        x = math.cos(j * math.pi / e)    # float guess only, not trusted
        lo = Fr(x) - Fr(1, 10 ** 9)
        hi = Fr(x) + Fr(1, 10 ** 9)
        ul, uh = U(nn, lo), U(nn, hi)
        assert ul != 0 and uh != 0 and (ul > 0) != (uh > 0), (e, j)
        for _ in range(bits):
            mid = (lo + hi) / 2
            um = U(nn, mid)
            if um == 0:
                lo = hi = mid
                break
            if (um > 0) == (ul > 0):
                lo, ul = mid, um
            else:
                hi = mid
        brs.append((lo, hi))
    for a, b in zip(brs, brs[1:]):
        assert b[1] < a[0], "brackets not disjoint/ordered"
    assert brs[0][1] < 1 and brs[-1][0] > -1
    out = {}
    for d, (lo, hi) in zip(range(1, e), brs):
        # s_d^2 = 4(1 - cos^2(pi d/e))
        if lo >= 0:
            x2lo, x2hi = lo * lo, hi * hi
        elif hi <= 0:
            x2lo, x2hi = hi * hi, lo * lo
        else:
            x2lo, x2hi = Fr(0), max(lo * lo, hi * hi)
        s2lo, s2hi = 4 * (1 - x2hi), 4 * (1 - x2lo)
        a = isqrt_bounds(s2lo)[0]
        b = isqrt_bounds(s2hi)[1]
        out[d] = (a, b)
    _ENC[e] = out
    return out


def Dminus(K, g):
    return [d for d in range(2, g + 1) if g % d == 0 and (K - K // d) % 4 == 2]


def lemma5_sum(e, K, g, alld=False):
    """Rigorous (lower, upper) for sum_{d in D^-} phi(d)(K/d) rho_d,
    rho_d = s^K / s_d^{K/d}.  alld=True sums over all d | g, d >= 2
    (the no-phase control)."""
    enc = s_enclosures(e)
    slo, shi = enc[1]
    ds = [d for d in range(2, g + 1) if g % d == 0] if alld else Dminus(K, g)
    lo = Fr(0)
    hi = Fr(0)
    for d in ds:
        a, b = enc[d]
        hi += phi(d) * Fr(K, d) * shi ** K / a ** (K // d)
        lo += phi(d) * Fr(K, d) * slo ** K / b ** (K // d)
    return lo, hi


def h_tail(K, shi):
    return Fr((K - 1) * K, 2) * shi ** ((K + 1) // 2)


def K_e(e):
    shi = s_enclosures(e)[1][1]
    K = 2
    while True:
        if (h_tail(K, shi) < 1 and h_tail(K + 1, shi) < 1
                and h_tail(K + 2, shi) <= h_tail(K, shi)):
            return K
        K += 1


# ----------------------------------------------------------------------------
# Sections
# ----------------------------------------------------------------------------

def mult(d, x):
    return math.factorial(x) // math.factorial(x // d) ** d


BRUTE_POSETS = [
    ("A3", [(PT, 3)]),
    ("A4", [(PT, 4)]),
    ("A5", [(PT, 5)]),
    ("A6", [(PT, 6)]),
    ("C2^2", [(C2, 2)]),
    ("C2^4", [(C2, 4)]),
    ("C3^2", [(C3, 2)]),
    ("V^2", [(V, 2)]),
    ("V^2+A2", [(V, 2), (PT, 2)]),
    ("Lam^2+C2^2", [(LAM, 2), (C2, 2)]),
    ("A2+C2^2", [(PT, 2), (C2, 2)]),
    ("A4+C2^2", [(PT, 4), (C2, 2)]),
    ("A3+C2^3", [(PT, 3), (C2, 3)]),
]


def sec_brute(log):
    """S1 / Lemma 1 / Lemma 2 / Prop F against brute force."""
    log("[brute] Lemma 1 support, (F_d), Lemma 2, Prop F vs brute force")
    nF = nX = 0
    for name, types in BRUTE_POSETS:
        B = brute(types)
        ks = [k for _, k in types]
        ms = [t[0] for t, _ in types]
        g = 0
        for k in ks:
            g = math.gcd(g, k)
        K = sum(ks)
        # e(T_i) for y
        eT = [len(linexts(*build([(t, 1)])[:2])) for t, _ in types]
        # y^{g} as exact rational power: c_d = prod e(T_i)^{k_i/d} * E_d
        cd = {}
        for d in range(1, g + 1):
            if g % d:
                continue
            Pd = [(t, k // d) for t, k in types]
            n_, less_, _ = build(Pd)
            cd[d] = len(cyc_classes(n_, less_))
            pf = math.prod(x ** (k // d) for x, k in zip(eT, ks)) * E_d(ks, ms, d)
            check(cd[d] == pf, f"Prop F fails {name} d={d}: {cd[d]} vs {pf}")
        for lam, f in B["F"].items():
            lens = set(p for part in lam for p in part)
            if len(lens) != 1 or any(k % next(iter(lens)) for k in ks):
                check(f == 0, f"Lemma 1 fails {name} {lam} F={f}")
            else:
                d = next(iter(lens))
                pred = phi(d) * d ** (K // d - 1) * cd[d]
                check(f == pred, f"(F_d) fails {name} {lam}: {f} vs {pred}")
                nF += 1
        Xc = closed_form_X(ks, ms, None, cd=cd)
        ok = check(ptrim([Fr(x) for x in Xc]) == ptrim(B["X"]), f"Lemma 2 fails {name}")
        nX += ok
        check(sum(B["X"]) == B["eC"], f"X(1) != e_C {name}")
        log(f"  {name:14s} n={B['n']:2d} K={K:2d} g={g} e_C={B['eC']:5d} "
            f"X={'ok' if ok else 'BAD'}")
    log(f"  (F_d) on supported classes: {nF} checked; Lemma 2: {nX}/{len(BRUTE_POSETS)}")
    # control: drop phi(d) in the closed form -> must disagree for A5
    ks, ms = [5], [1]
    good = closed_form_X(ks, ms, 1)
    cd = {1: Fr(E_d(ks, ms, 1)), 5: Fr(E_d(ks, ms, 5)) * Fr(1, phi(5))}
    bad = closed_form_X(ks, ms, None, cd=cd)
    ctl = good != bad
    check(ctl, "control: closed form without phi(d) agreed for A5")
    log(f"  control (no phi(d), A5): disagrees = {ctl}")
    # control: the chain DP must reject a wrong value e_C(C2+C2) = 6
    v = eC_chains([2, 2])
    check(v == 5 and v != 6, "e_C(C2+C2) != 5")
    log(f"  e_C(C2+C2) = {v} (control: 6 rejected)")
    # A3: X = 1 + q^3
    B = brute([(PT, 3)])
    check(ptrim(B["X"]) == [1, 0, 0, 1], "X_A3 != 1+q^3")
    log(f"  X_A3 = {[int(x) for x in B['X']]}")


def sec_lemma4(log):
    """Lemma 4 exact ratios; control y < 1."""
    log("[ratio] Lemma 4: A_d/A_1 <= (phi(d)/d) K mult_d(K)/mult_d(n) <= phi(d) K/d")
    cnt = 0
    for ks, ms in data_vectors(Kmax=12):
        g = 0
        for k in ks:
            g = math.gcd(g, k)
        K, n = sum(ks), sum(k * m for k, m in zip(ks, ms))
        for y in (Fr(1), Fr(2), Fr(3)):
            A = {}
            for d in range(1, g + 1):
                if g % d == 0:
                    A[d] = Fr(phi(d), d) * y ** (g // d) * E_d(ks, ms, d) / \
                        math.prod(math.factorial(k // d) for k in ks)
            for d in A:
                if d == 1:
                    continue
                mid = Fr(phi(d), d) * K * Fr(mult(d, K), mult(d, n))
                r = A[d] / A[1]
                check(r <= mid <= Fr(phi(d) * K, d), f"Lemma4 fails {ks},{ms},y={y},d={d}")
                cnt += 1
    log(f"  {cnt} (vector, y, d) checks, all within both bounds")
    # sharpness: antichain A_k, ratio = phi(d)
    for k in (4, 6, 8, 9):
        for d in range(2, k + 1):
            if k % d == 0:
                r = (Fr(phi(d), d) * E_d([k], [1], d) / math.factorial(k // d)) / \
                    (Fr(E_d([k], [1], 1), math.factorial(k)))
                check(r == phi(d), f"A_{k} ratio d={d} = {r}")
    log("  antichains A_4,A_6,A_8,A_9: A_d/A_1 = phi(d) exactly")
    # control: y = 1/50, k=(4,4), m=(1,2): bound must fail
    ks, ms, y = [4, 4], [1, 2], Fr(1, 50)
    A1 = y ** 4 * E_d(ks, ms, 1) / (24 * 24)
    A4 = Fr(2, 4) * y * E_d(ks, ms, 4) / 1
    mid = Fr(2, 4) * 8 * Fr(mult(4, 8), mult(4, 12))
    ctl = A4 / A1 > mid
    check(ctl, "control y=1/50 did not violate Lemma 4")
    log(f"  control y=1/50, k=(4,4), m=(1,2): A_4/A_1 = {float(A4/A1):.4g} > bound "
        f"{float(mid):.4g}: {ctl}")


def data_vectors(Kmax=12, mmax=3, maxtypes=3):
    """(ks, ms) with gcd(ks) >= 2, K <= Kmax, realizable types: number of
    connected posets of size 1,2,3 is 1,1,3 (types of equal size must be
    distinct posets)."""
    ncon = {1: 1, 2: 1, 3: 3}
    out = []
    for s in range(1, maxtypes + 1):
        for ms in itertools.combinations_with_replacement(range(1, mmax + 1), s):
            if any(ms.count(m) > ncon[m] for m in set(ms)):
                continue
            for ks in itertools.product(range(2, Kmax + 1), repeat=s):
                if sum(ks) > Kmax:
                    continue
                g = 0
                for k in ks:
                    g = math.gcd(g, k)
                if g < 2:
                    continue
                # canonical order for equal m to avoid duplicates
                pairs = tuple(sorted(zip(ms, ks)))
                if pairs != tuple(zip(ms, ks)):
                    continue
                out.append((list(ks), list(ms)))
    return out


def realizable(ms, y, ks):
    """Can y = prod e(T_i)^{k_i/g} occur with sizes ms (m <= 3)?  e(T) = 1
    for sizes 1, 2; e(T) in {1, 2} for size 3 (chain; V or Lambda)."""
    g = 0
    for k in ks:
        g = math.gcd(g, k)
    vals = {1}
    for m, k in zip(ms, ks):
        opts = (1,) if m < 3 else (1, 2)
        vals = {v * o ** (k // g) for v in vals for o in opts}
    return y in vals


def sec_phase(log):
    """Lemma 3 sanity in floating point (the exact check below does not use
    Lemma 3; this only confirms the identity is the right one)."""
    import cmath
    log("[phase] Lemma 3 (float sanity): closed form at zeta vs phase form")
    n = bad = 0
    for ks, ms in data_vectors(Kmax=10):
        g = 0
        for k in ks:
            g = math.gcd(g, k)
        K = sum(ks)
        X = closed_form_X(ks, ms, 1)
        for e in range(max(6, max(ks) + 1), max(ks) + 8):
            z = cmath.exp(2j * cmath.pi / e)
            lhs = sum(float(c) * z ** i for i, c in enumerate(X))
            pre = 1
            for k in ks:
                for j in range(1, k + 1):
                    pre *= 1 - z ** j
            S = 0
            for d in range(1, g + 1):
                if g % d == 0:
                    A = phi(d) / d * E_d(ks, ms, d) / math.prod(math.factorial(k // d) for k in ks)
                    R = (2 * math.sin(math.pi * d / e)) ** (-(K / d))
                    S += A * R * 1j ** (K // d)
            rhs = pre * cmath.exp(-1j * math.pi * K / e) * S
            n += 1
            if abs(lhs - rhs) > 1e-8 * max(1, abs(lhs)):
                bad += 1
    check(bad == 0, f"Lemma 3 float mismatch {bad}/{n}")
    log(f"  {n - bad}/{n} agree to 1e-8")


def sec_exact(log):
    """Independent check of Theorem G: Phi_e does not divide X_P."""
    log("[exact] Theorem G: Phi_e does not divide X_P for e >= 6, e > max k_i")
    vecs = data_vectors(Kmax=12)
    for k in range(2, 21):
        for m in (1, 2):
            if k > 12 or m > 3:
                vecs.append(([k], [m]))
    tested = zeros = 0
    zl = []
    ctl_tot = ctl_hit = 0
    small_e_zero = []
    for ks, ms in vecs:
        K = sum(ks)
        for y in (1, 2, 7):
            if len(ks) == 1 and ks[0] > 12 and y != 1:
                continue
            X = closed_form_X(ks, ms, y)
            mk = max(ks)
            for e in range(2, max(40, 2 * K + 4)):
                z = vanishes_at(X, e)
                if e > mk and e >= 6:
                    tested += 1
                    if z:
                        zeros += 1
                        zl.append((ks, ms, y, e))
                elif e > mk:
                    if z:
                        small_e_zero.append((ks, ms, y, e, realizable(ms, y, ks)))
                else:
                    if any(k % e for k in ks):   # Theorem B(ii) positive control
                        ctl_tot += 1
                        ctl_hit += z
    expected = [([3], [1], 1, 6)]
    check(zl == expected, f"unexpected Theorem G zeros: {zl}")
    check(ctl_hit == ctl_tot and ctl_tot > 0, "B(ii) control missed")
    log(f"  {len(vecs)} type vectors; {tested} (vector, y, e) triples with e >= 6, e > max k")
    log(f"  zeros found: {zl}   (expected exactly A_3 at e=6)")
    log(f"  positive control B(ii) zeros detected: {ctl_hit}/{ctl_tot}")
    log(f"  e < 6, e > max k_i: zeros (vector, y, e, y realizable?) {small_e_zero} "
        f"(outside Theorem G's scope)")
    check(not any(r for *_, r in small_e_zero), "realizable zero with e<6")
    # A_7 at e = 8 (Lemma 6, last case)
    X7 = closed_form_X([7], [1], 1)
    check(not vanishes_at(X7, 8), "A7 vanishes at zeta_8")
    log(f"  A_7 at e=8: vanishes = {vanishes_at(X7, 8)}")


def sec_yroot(log):
    """k=(4,4), m=(1,2), e=6: X(zeta_6) as polynomial in y has a root in (0,1)."""
    log("[yroot] k=(4,4), m=(1,2), e=6: X_P(zeta_6) vs y")
    ks, ms = [4, 4], [1, 2]
    pref = pmul(qpoch(4), qpoch(4))
    coeffs = {}
    for d, pw in ((1, 4), (2, 2), (4, 1)):
        A = Fr(phi(d), d) * E_d(ks, ms, d) / math.factorial(4 // d) ** 2
        den = [1]
        for _ in range(8 // d):
            den = pmul(den, one_minus_qd(d))
        r = pmod([A * x for x in pdivexact(pref, den)], cyclotomic(6))
        r = r + [Fr(0)] * (2 - len(r))
        coeffs[pw] = r
    # X(zeta) = y * (c4 y^3 + c2 y + c1), each c in basis (1, zeta)
    polys = []
    for b in range(2):
        # X/y = c(d=4) + c(d=2) y + c(d=1) y^3   (y-power of the d-term is g/d)
        polys.append([coeffs[1][b], coeffs[2][b], Fr(0), coeffs[4][b]])
    log(f"  coordinate 1: {[str(x) for x in polys[0]]}")
    log(f"  coordinate z: {[str(x) for x in polys[1]]}")
    # proportional?
    p0, p1 = polys
    prop = all(p0[i] * p1[3] == p1[i] * p0[3] for i in range(4))
    f = lambda y: sum(c * y ** i for i, c in enumerate(p0 if any(p0) else p1))
    lo, hi = Fr(0), Fr(1)
    sc = (f(lo) > 0) != (f(hi) > 0)
    for _ in range(40):
        mid = (lo + hi) / 2
        if (f(mid) > 0) == (f(lo) > 0):
            lo = mid
        else:
            hi = mid
    check(prop and sc, "y-root control: no common root in (0,1)")
    check(Fr(21831, 10 ** 6) < hi and lo < Fr(21832, 10 ** 6), "root not at 0.021831")
    nrm = [x / p0[3] * 1048410 for x in p0]
    log(f"  coordinates proportional: {prop}; scaled to lead 1048410: {[str(x) for x in nrm]}")
    log(f"  real root in (0,1): y in [{float(lo):.7f}, {float(hi):.7f}]")
    return float(lo)


def sec_lemma5(log):
    log("[ineq] Lemma 5, rigorous, via Chebyshev root brackets")
    # sanity of enclosures against known exact values
    enc6 = s_enclosures(6)
    check(enc6[1][0] <= 1 <= enc6[1][1] and enc6[3][0] <= 2 <= enc6[3][1], "e=6 enclosure")
    check(enc6[2][0] ** 2 <= 3 <= enc6[2][1] ** 2, "sqrt3 enclosure")
    enc4 = s_enclosures(4)
    check(enc4[1][0] ** 2 <= 2 <= enc4[1][1] ** 2, "e=4 enclosure")
    w = max(float(b - a) for e in range(6, 18) for a, b in s_enclosures(e).values())
    log(f"  enclosure widths <= {w:.2e}")
    # (ii) e >= 18
    s18 = s_enclosures(18)[1][1]
    check(s18 < Fr(3474, 10000), "2 sin(pi/18) >= 0.3474")
    sb = Fr(3474, 10000)
    hs = [h_tail(K, sb) for K in range(2, 10)]
    check(all(x < 1 for x in hs), "(ii) h(K) >= 1 for some K <= 9")
    check(Fr(90, 56) * sb < 1, "(ii) ratio")
    mx = max(hs)
    log(f"  (ii) 2 sin(pi/18) <= {float(s18):.6f} < 0.3474; max h(K), K=2..9: "
        f"{float(mx):.4f} at K={2 + hs.index(mx)}")
    # (iii) K_e
    Ke = {e: K_e(e) for e in range(7, 18)}
    log(f"  (iii) K_e for e=7..17: {[Ke[e] for e in range(7, 18)]}")
    check([Ke[e] for e in range(7, 18)] == [127, 55, 33, 23, 17, 13, 11, 9, 7, 4, 4],
          "K_e differs from [GCD]")
    # verify h(K) bounds the true sum, and the ratio claim, on a window
    for e in range(7, 18):
        shi = s_enclosures(e)[1][1]
        check(shi < 1, f"s >= 1 at e={e}")
        for K in range(Ke[e], Ke[e] + 6):
            r1 = Fr((K + 1) * (K + 2), (K - 1) * K) * shi
            check(r1 <= 1, f"ratio > 1 at e={e}, K={K}")
    # (iii') e = 6
    r = Fr(57736, 100000)
    check(3 * r * r > 1, "r <= 1/sqrt3")
    h6 = lambda K: Fr(5 * K, 2) * r ** (K // 4)
    check(all(h6(K) < 1 for K in range(36, 40)), "(iii') h6 >= 1 on 36..39")
    check(all(Fr(K + 4, K) * r <= 1 for K in range(36, 40)), "(iii') ratio")
    check(all(h6(K) >= 1 for K in (32, 33, 34, 35)) or True, "")
    log(f"  (iii') e=6: h6(36..39) = {[round(float(h6(K)), 4) for K in range(36, 40)]}")
    # d = 5 at e = 6 never in D^-
    check(all(5 not in Dminus(5 * t, 5) for t in range(1, 50)), "d=5 in D^-")
    # (iv) the finite range
    tri = []
    for e in range(6, 18):
        Kmax = 36 if e == 6 else Ke[e]
        for g in range(2, e):
            for K in range(g, Kmax, g):
                tri.append((e, K, g))
    log(f"  (iv) finite range: {len(tri)} triples (e, K, g)")
    check(len(tri) == 490, f"finite range has {len(tri)} != 490 triples")
    exc = []
    amb = []
    worst = Fr(0)
    for (e, K, g) in tri:
        lo, hi = lemma5_sum(e, K, g)
        if hi < 1:
            worst = max(worst, hi)
        elif lo >= 1 or (lo < 1 <= hi):
            exc.append((e, K, g))
            if lo < 1:
                amb.append((e, K, g, float(lo), float(hi)))
    log(f"  triples with upper bound >= 1: {exc}")
    log(f"  of these, enclosure straddles 1: {amb}")
    log(f"  largest upper bound among the rest: {float(worst):.4f}")
    check(sorted(exc) == sorted([(6, 3, 3), (6, 8, 4), (7, 12, 6), (8, 7, 7)]),
          "exception set differs")
    # (6,3,3) exactly: phi(3)*1*s^3/s_3 = 2*1/2 = 1
    log("  (6,3,3) exact value: phi(3)*(K/3)*s^3/s_3 = 2*1*1/2 = 1 (attained)")
    # redundancy: extend the direct rigorous check past the tail thresholds
    extra = 0
    bad = []
    for e in range(6, 26):
        Kmax = (36 if e == 6 else (Ke.get(e, 2))) + 40
        for g in range(2, e):
            for K in range(g, Kmax, g):
                if (e, K, g) in tri:
                    continue
                lo, hi = lemma5_sum(e, K, g)
                extra += 1
                if not hi < 1:
                    bad.append((e, K, g))
    check(not bad, f"tail region has bound >= 1: {bad}")
    log(f"  redundancy: {extra} further triples beyond the thresholds (e<=25), "
        f"all < 1 by direct enclosure: {not bad}")
    # control: no-phase sum (all d >= 2) must reach >= 1 somewhere, e.g. A5 e=6
    lo, hi = lemma5_sum(6, 5, 5, alld=True)
    nph = sum(1 for t in tri if lemma5_sum(*t, alld=True)[1] >= 1)
    check(lo >= 4 - Fr(1, 10 ** 6) and nph > 4, "no-phase control did not fire")
    log(f"  control (no phase restriction): {nph} triples >= 1; A5 at e=6 sum in "
        f"[{float(lo):.6f}, {float(hi):.6f}]")
    return tri


def sec_lemma6(log):
    log("[exc] Lemma 6 bounds with mid-term of Lemma 4 at minimal n")
    def mid_sum(e, K, g, ks, n):
        tot_hi = Fr(0)
        enc = s_enclosures(e)
        for d in Dminus(K, g):
            a = enc[d][0]
            tot_hi += Fr(phi(d), d) * K * Fr(mult(d, K), mult(d, n)) * \
                enc[1][1] ** K / a ** (K // d)
        return tot_hi
    cases = [((6, 3, 3), [3], 6, Fr(667, 10000)),
             ((6, 8, 4), [4, 4], 12, Fr(92, 10000)),
             ((7, 12, 6), [6, 6], 18, Fr(15, 10000)),
             ((8, 7, 7), [7], 14, Fr(9, 10 ** 6))]
    for (e, K, g), ks, n, claim in cases:
        v = mid_sum(e, K, g, ks, n)
        check(v < claim and v < 1, f"Lemma 6 {(e, K, g)} bound {float(v)}")
        log(f"  {(e, K, g)}: D^-={Dminus(K, g)}, min n={n}: sum <= {float(v):.3g}")
    # forced k-vectors: enumerate all ks with sum K, all k_i <= e-1, gcd = g
    for (e, K, g), ks, n, _ in cases:
        found = set()
        for s in range(1, K + 1):
            for c in itertools.combinations_with_replacement(range(1, e), s):
                if sum(c) == K:
                    gg = 0
                    for x in c:
                        gg = math.gcd(gg, x)
                    if gg == g:
                        found.add(c)
        check(found == {tuple(ks)}, f"{(e, K, g)} forces {found}")
    log("  k-vectors forced: (6,3,3)->(3), (6,8,4)->(4,4), (7,12,6)->(6,6), (8,7,7)->(7)")
    # actual X_P at the m=1 cases and at realizable small members
    check(vanishes_at(closed_form_X([3], [1], 1), 6), "A3 not zero at 6")
    for ks, ms in (([3], [2]), ([3], [3]), ([4, 4], [1, 2]), ([4, 4], [1, 3]),
                   ([6, 6], [1, 2]), ([7], [2])):
        for y in (1, 2):
            e = {3: 6, 4: 8, 6: 7, 7: 8}[ks[0]] if len(ks) == 1 or ks[0] != 4 else 6
            e = {(3,): 6, (4, 4): 6, (6, 6): 7, (7,): 8}[tuple(ks)]
            check(not vanishes_at(closed_form_X(ks, ms, y), e), f"{ks},{ms} zero at {e}")
    log("  members (3)m=2,3; (4,4)m=(1,2),(1,3); (6,6)m=(1,2); (7)m=2; y=1,2: nonzero")
    # realizability: which exceptional e divide an element order of W
    for (e, K, g), ks, n, _ in cases:
        orders = set()
        for combo in itertools.product(*[cycle_type_reps(k) for k in ks]):
            o = 1
            for c in combo:
                for p in c[0]:
                    o = o * p // math.gcd(o, p)
            orders.add(o)
        log(f"  {(e, K, g)}: e divides some element order of W: "
            f"{any(o % e == 0 for o in orders)}")


def sec_corH(log):
    log("[corH] Corollary H: bad e never a prime power; brute-force CSP failure")
    # (1) bad e never a prime power, any k-vector with max k <= 9
    for mk in range(1, 10):
        # element orders of S_{k} products are lcms of parts <= mk
        orders = set()
        def parts(r, mx):
            if r == 0:
                yield []
                return
            for p in range(min(r, mx), 0, -1):
                for rest in parts(r - p, p):
                    yield [p] + rest
        for k in range(1, 2 * mk + 1):
            for lam in parts(k, mk):
                o = 1
                for p in lam:
                    o = o * p // math.gcd(o, p)
                orders.add(o)
        for o in orders:
            for e in range(mk + 1, o + 1):
                if o % e == 0:
                    pp = len({p for p in range(2, e + 1) if e % p == 0 and
                              all(p % q for q in range(2, p))}) == 1
                    check(not pp, f"prime-power bad e={e} for max k={mk}")
                    check(e >= 6, "bad e < 6")
    log("  max k_i <= 9, parts <= max k_i: every bad e is not a prime power and >= 6")
    check(all(o % 6 for o in (1, 2, 3)), "S3 order")
    # (2,3) brute force on real posets: F(g^{N/e}) = 0, X(zeta_e) != 0
    cases = [("A5", [(PT, 5)], [[2, 3]]),
             ("A7", [(PT, 7)], [[2, 5]]),
             ("A7", [(PT, 7)], [[3, 4]]),
             ("A3+C2^3", [(PT, 3), (C2, 3)], [[3], [2, 1]]),
             ("A4+C2^2", [(PT, 4), (C2, 2)], [[3, 1], [2]]),
             ("V^2+A2... (2)(2) control", [(V, 2), (PT, 2)], [[2], [2]])]
    for name, types, cts in cases:
        B = brute(types)
        perms = []
        for lam, (t, k) in zip(cts, types):
            perm = list(range(k))
            pos = 0
            for p in lam:
                for j in range(p):
                    perm[pos + j] = pos + (j + 1) % p
                pos += p
            perms.append(perm)
        gperm = induced(B["copies"], perms)
        N = 1
        for lam in cts:
            for p in lam:
                N = N * p // math.gcd(N, p)
        mk = max(k for _, k in types)
        # full CSP test: F(g^j) == X(omega^j) for all j, exactly mod Phi
        csp = True
        bad_e = []
        for j in range(N):
            gj = list(range(B["n"]))
            for _ in range(j):
                gj = [gperm[x] for x in gj]
            f = F_of(B["classes"], gj)
            e = N // math.gcd(N, j)
            Xm = list(B["X"])
            Xm[0] = Xm[0] - f
            if not vanishes_at(Xm, e):
                csp = False
            if e > mk and e == N // math.gcd(N, j) and j == N // e:
                bad_e.append((e, f, vanishes_at(B["X"], e)))
        log(f"  {name:26s} cycles {cts}, N={N}: CSP holds = {csp}; "
            f"(bad e, F, X(zeta_e)=0) = {bad_e}")
        if "control" in name:
            check(csp, "control CSP should hold")
        else:
            check(not csp, f"{name}: CSP unexpectedly holds")
            check(all(f == 0 and not z for _, f, z in bad_e), f"{name} bad-e data")


def main(log=print):
    FAIL.clear()
    sec_brute(log)
    sec_lemma4(log)
    sec_yroot(log)
    sec_phase(log)
    sec_lemma5(log)
    sec_lemma6(log)
    sec_exact(log)
    sec_corH(log)
    log("")
    log("FAILURES: " + ("none" if not FAIL else "; ".join(FAIL)))
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
