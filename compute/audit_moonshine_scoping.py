"""Independent audit of notes/moonshine_scoping.md.

Self-contained: imports nothing from the other scripts of compute/ (in
particular nothing from moonshine_scoping.py or moonshine_lookup.py).
Exact integer / rational arithmetic, except the numerical cusp asymptotics
of [D], which use floats and are checked against closed-form limits.

Checks
  [W]   Witt layer: naturally labeled posets a_n (n <= 8) by own recursion;
        b_n, c_n, c_n^-; the d^m traces; A = prod (1-q^n)^(-c_n); the
        bipartite bound a_n >= 2^(floor(n/2) ceil(n/2)); c_n = c_n^- unless
        n = 2 mod 4.
  [H]   sub-Hopf monoids and the relation bigrading: naturally labeled
        matchings = involutions (telephone numbers); a_{n,r} >= binomial
        bound; height <= 2 already reaches 2^(n^2/4).
  [P]   quotient formula for g-fixed P-partitions, own brute force, 9 (P, g)
        pairs; leading pole at q = 1.
  [I]   infinite posets: chain_m x N (m = 1..3), N x N and its transpose,
        brute force against the product formulas; a_{4n}(sym) >= pp(n).
  [D]   Lemma D (log-derivative): y^3 Dlog F(iy) tends to 2 zeta(3)/(2 pi)^3
        (MacMahon) and zeta(3)/(4 (2 pi)^3) (symmetric), y^3 E_2(iy) -> 0;
        positive control: y^2 Dlog(1/eta-type) stays bounded.
  [F]   Frame shapes of Lie_n (n = 4..7) from the classical character;
        the note's sample shapes; T_g = prod (q^t; q^t)^(-r_t) as series;
        odd-g sign twist rule; Lie_n restricted to S_{n-1} is regular
        (n <= 9); eta(5t)^5/eta(t) coefficient identity to q^200.
  [A]   A_5: Lie_5 splits as 1*3 + 1*3' + ..., Fock traces on the 3-isotypic
        piece differ at the two classes of 5-cycles (A_n-specific, not
        rational, Siegel-type).

Usage:  python3 audit_moonshine_scoping.py [--W|--H|--P|--I|--D|--F|--A]
Exit status 0 iff every check passes.
"""

import cmath
import itertools
import math
import sys
from fractions import Fraction

CHECKS = []


def check(tag, ok, msg):
    CHECKS.append((tag, bool(ok)))
    print(f"[{tag}] {'ok  ' if ok else 'FAIL'} {msg}")


# ---------------------------------------------------------------- series ---

def mul(a, b, N):
    c = [0] * (N + 1)
    for i, x in enumerate(a[:N + 1]):
        if x:
            for j, y in enumerate(b[:N + 1 - i]):
                c[i + j] += x * y
    return c


def inv_one_minus_power(t, e, N):
    """(1 - q^t)^(-e) for integer e (either sign), to order N."""
    s = [0] * (N + 1)
    s[0] = 1
    if e >= 0:
        for _ in range(e):
            for i in range(t, N + 1):
                s[i] += s[i - t]
    else:
        for _ in range(-e):
            for i in range(N, t - 1, -1):
                s[i] -= s[i - t]
    return s


def euler_product(expo, N):
    """prod_{n>=1} (1-q^n)^(-expo[n])."""
    s = [1] + [0] * N
    for n in range(1, N + 1):
        if expo.get(n, 0):
            s = mul(s, inv_one_minus_power(n, expo[n], N), N)
    return s


def mobius(n):
    r, p, m = 1, 2, n
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            r = -r
        p += 1
    return -r if m > 1 else r


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


# ------------------------------------------------------- [W] Witt layer ---

def natural_posets(nmax):
    """All naturally labeled posets on [n], n <= nmax.

    A poset is a tuple D with D[i] the bitmask of the strict down-set of i.
    Element n is added as a maximal label: its strict down-set must be an
    order ideal of the poset on [n].  Returns {n: list of posets}.
    """
    out = {0: [()]}
    for n in range(1, nmax + 1):
        new = []
        for D in out[n - 1]:
            m = n - 1
            for S in range(1 << m):
                ok = True
                T = S
                while T:
                    i = (T & -T).bit_length() - 1
                    T &= T - 1
                    if D[i] & ~S:
                        ok = False
                        break
                if ok:
                    new.append(D + (S,))
        out[n] = new
    return out


def log_coeffs(A, N):
    """b_n = n [x^n] log A for A = 1 + ..., exact integers."""
    # n b'_n relation: x A'/A = sum b_n x^n
    xA = [n * A[n] for n in range(N + 1)]
    b = [0] * (N + 1)
    for n in range(1, N + 1):
        b[n] = xA[n] - sum(b[k] * A[n - k] for k in range(1, n))
    return b


def run_W():
    N = 8
    P = natural_posets(N)
    a = [len(P[n]) for n in range(N + 1)]
    A006455 = [1, 1, 2, 7, 40, 357, 4824, 96428, 2800472]
    check("W", a == A006455, f"a_n by own recursion = A006455 for n<=8: {a}")
    b = log_coeffs(a, N)
    note_b = [1, 3, 16, 131, 1561, 26532, 637890, 21580043]
    check("W", b[1:] == note_b, f"b_n = n[x^n]log A: {b[1:]}")
    c = [0] * (N + 1)
    cm = [0] * (N + 1)
    for n in range(1, N + 1):
        tot = Fraction(0)
        totm = Fraction(0)
        for d in divisors(n):
            m = n // d
            coef = Fraction(mobius(d) * b[m], d * m)  # coeff of p_d^m
            tot += coef  # <p_d^m, h_n> = 1
            totm += coef * (-1) ** ((d - 1) * m)  # <p_d^m, e_n> = sgn
        assert tot.denominator == 1 and totm.denominator == 1
        c[n], cm[n] = int(tot), int(totm)
    check("W", c[1:] == [1, 1, 5, 32, 312, 4419, 91127, 2697489],
          f"c_n = <ch V_n, h_n>: {c[1:]}")
    check("W", cm[1:] == [1, 2, 5, 32, 312, 4424, 91127, 2697489],
          f"c_n^- = <ch V_n, e_n>: {cm[1:]}")
    check("W", all((c[n] == cm[n]) == (n % 4 != 2) for n in range(1, N + 1)),
          "c_n = c_n^- exactly when n != 2 mod 4 (n <= 8)")
    check("W", euler_product({n: c[n] for n in range(1, N + 1)}, N) == a,
          "A(q) = prod (1-q^n)^(-c_n) through q^8")
    tr2 = [mobius(2) * 2 ** (m - 1) * math.factorial(m - 1) * b[m]
           for m in range(1, 5)]
    check("W", tr2 == [-1, -6, -128, -6288], f"trace of 2^m on V_2m: {tr2}")
    # trace d^m for non-squarefree d is identically zero (note says |.| = d^{m-1} dim V_m)
    check("W", mobius(4) == 0,
          "d = 4: the d^m trace series is identically 0 (the note's "
          "'|trace| = d^(m-1) dim V_m' needs mu(d) != 0)")
    bound = all(a[n] >= 2 ** ((n // 2) * ((n + 1) // 2)) for n in range(N + 1))
    check("W", bound, "a_n >= 2^(floor(n/2) ceil(n/2)), n <= 8")
    dims = [math.factorial(n - 1) * b[n] for n in range(3, 7)]
    check("W", dims == [32, 786, 37464, 3183840], f"dim V_n = (n-1)! b_n: {dims}")
    # c_n / a_n -> 1 (informational: the note's '>= 2^(n^2/4)' is proved for a_n only)
    print("      c_n/a_n:", [round(c[n] / a[n], 4) for n in range(1, N + 1)])
    return P


# ---------------------------------------- [H] sub-Hopf monoids, bigrading ---

def run_H(P=None):
    N = 8
    if P is None:
        P = natural_posets(N)

    def nrel(D):
        return sum(bin(x).count("1") for x in D)

    def height_le2(D):
        return all(D[j] == 0 for D_ in [D] for i in range(len(D))
                   for j in range(len(D)) if (D[i] >> j) & 1)

    def is_matching(D):
        # disjoint union of 2-chains and points: every element is in <= 1 relation
        n = len(D)
        deg = [0] * n
        for i in range(n):
            for j in range(n):
                if (D[i] >> j) & 1:
                    deg[i] += 1
                    deg[j] += 1
        return all(x <= 1 for x in deg)

    tel = [1, 1]
    for n in range(2, N + 1):
        tel.append(tel[-1] + (n - 1) * tel[-2])
    mt = [sum(1 for D in P[n] if is_matching(D)) for n in range(N + 1)]
    check("H", mt == tel, f"naturally labeled 2-chain matchings = involutions: {mt}")
    # positive control: involution numbers are superexponential, ratio grows
    check("H", tel[8] / tel[7] > tel[5] / tel[4],
          "telephone ratios increase (superexponential)")
    h2 = [sum(1 for D in P[n] if height_le2(D)) for n in range(N + 1)]
    check("H", all(h2[n] >= 2 ** ((n // 2) * ((n + 1) // 2)) for n in range(N + 1)),
          f"height <= 2 sub-monoid already >= 2^(n^2/4): {h2}")
    ok = True
    for n in range(N + 1):
        cnt = {}
        for D in P[n]:
            r = nrel(D)
            cnt[r] = cnt.get(r, 0) + 1
        k = (n // 2) * ((n + 1) // 2)
        for r in range(k + 1):
            if cnt.get(r, 0) < math.comb(k, r):
                ok = False
    check("H", ok, "a_{n,r} >= C(floor(n/2)ceil(n/2), r) for all n <= 8, r")


# ------------------------------------------ [P] quotient formula, finite ---

def ppartitions_fixed(n, rel, g, W):
    """Brute force: order-reversing sigma: [n] -> N, sigma o g = sigma, by weight <= W."""
    out = [0] * (W + 1)
    orbits = []
    seen = set()
    for x in range(n):
        if x in seen:
            continue
        o = [x]
        y = g[x]
        while y != x:
            o.append(y)
            y = g[y]
        seen.update(o)
        orbits.append(o)
    rep = {x: i for i, o in enumerate(orbits) for x in o}
    m = len(orbits)
    sizes = [len(o) for o in orbits]

    def rec(i, vals, w):
        if i == m:
            for (x, y) in rel:  # x < y  =>  sigma(x) >= sigma(y)
                if vals[rep[x]] < vals[rep[y]]:
                    return
            out[w] += 1
            return
        v = 0
        while w + v * sizes[i] <= W:
            vals.append(v)
            rec(i + 1, vals, w + v * sizes[i])
            vals.pop()
            v += 1

    rec(0, [], 0)
    return out


def quotient_formula(n, rel, g, W):
    orbits, seen = [], set()
    for x in range(n):
        if x in seen:
            continue
        o = [x]
        y = g[x]
        while y != x:
            o.append(y)
            y = g[y]
        seen.update(o)
        orbits.append(o)
    rep = {x: i for i, o in enumerate(orbits) for x in o}
    m = len(orbits)
    qrel = set()
    for (x, y) in rel:
        qrel.add((rep[x], rep[y]))
    # transitive closure on Q
    changed = True
    while changed:
        changed = False
        for (a, b) in list(qrel):
            for (c, d) in list(qrel):
                if b == c and (a, d) not in qrel:
                    qrel.add((a, d))
                    changed = True
    assert all((a, a) not in qrel for a in range(m)), "quotient not a poset"
    # natural labelling of Q: topological order
    order = []
    left = set(range(m))
    while left:
        mins = sorted(a for a in left if not any((b, a) in qrel for b in left))
        order.append(mins[0])
        left.remove(mins[0])
    lab = {a: i for i, a in enumerate(order)}
    sizes = [len(o) for o in orbits]
    total = [0] * (W + 1)
    lin = 0
    lead = Fraction(0)
    for w in itertools.permutations(range(m)):
        pos = {a: i for i, a in enumerate(w)}
        if any(pos[a] > pos[b] for (a, b) in qrel):
            continue
        lin += 1
        S = list(itertools.accumulate(sizes[a] for a in w))
        num = sum(S[j] for j in range(m - 1) if lab[w[j]] > lab[w[j + 1]])
        s = [0] * (W + 1)
        if num <= W:
            s[num] = 1
        for Sj in S:
            s = mul(s, inv_one_minus_power(Sj, 1, W), W)
        total = [x + y for x, y in zip(total, s)]
        lead += Fraction(1, math.prod(S))
    return total, lin, lead


def run_P():
    W = 16
    cases = [
        ("antichain4, (12)(34)", 4, [], [1, 0, 3, 2]),
        ("antichain4, 4-cycle (odd)", 4, [], [1, 2, 3, 0]),
        ("2+2, swap", 4, [(0, 1), (2, 3)], [2, 3, 0, 1]),
        ("bowtie, (01)(23)", 4, [(0, 2), (0, 3), (1, 2), (1, 3)], [1, 0, 3, 2]),
        ("bowtie, (01)", 4, [(0, 2), (0, 3), (1, 2), (1, 3)], [1, 0, 2, 3]),
        ("3+3, swap (odd)", 6, [(0, 1), (1, 2), (3, 4), (4, 5)], [3, 4, 5, 0, 1, 2]),
        ("2+2+2, 3-cycle", 6, [(0, 1), (2, 3), (4, 5)], [2, 3, 4, 5, 0, 1]),
        ("claw 1<{2,3,4}, 3-cycle", 4, [(0, 1), (0, 2), (0, 3)], [0, 2, 3, 1]),
        ("crown 6, rotation", 6, [(0, 3), (0, 4), (1, 4), (1, 5), (2, 5), (2, 3)],
         [1, 2, 0, 4, 5, 3]),
    ]
    for name, n, rel, g in cases:
        bf = ppartitions_fixed(n, rel, g, W)
        qf, lin, lead = quotient_formula(n, rel, g, W)
        check("P", bf == qf, f"{name}: brute force = prefix-sum formula to q^{W}"
              f" (|Lin Q| = {lin}, leading pole coeff {lead})")
    # negative control: the suffix-sum variant must fail somewhere
    n, rel, g = 4, [(0, 1), (2, 3)], [2, 3, 0, 1]
    bf = ppartitions_fixed(n, rel, [0, 1, 2, 3], W)
    # suffix sums with g = 1 on 2+2: weight sum_j delta_j*(n - j + 1)
    tot = [0] * (W + 1)
    for w in itertools.permutations(range(4)):
        pos = {a: i for i, a in enumerate(w)}
        if any(pos[a] > pos[b] for (a, b) in rel):
            continue
        S = [4 - j for j in range(4)]
        num = sum(S[j] for j in range(3) if w[j] > w[j + 1])
        s = [0] * (W + 1)
        s[num] = 1
        for Sj in S:
            s = mul(s, inv_one_minus_power(Sj, 1, W), W)
        tot = [x + y for x, y in zip(tot, s)]
    check("P", tot != bf, "negative control: suffix-sum variant disagrees on 2+2")
    # leading pole at g = 1 is e(P)/n!
    _, lin, lead = quotient_formula(4, [(0, 1), (2, 3)], [0, 1, 2, 3], W)
    check("P", lead == Fraction(6, 24), "g = 1 on 2+2: leading coefficient e(P)/n! = 6/24")


# ------------------------------------------------ [I] infinite posets ---

def plane_partitions_rows(m, N):
    """Count plane partitions with <= m rows by weight (brute force)."""
    out = [0] * (N + 1)

    def partitions_le(n, maxpart, maxlen):
        # partitions of n with parts <= maxpart, length <= maxlen
        if n == 0:
            yield ()
            return
        if maxlen == 0:
            return
        for p in range(min(n, maxpart), 0, -1):
            for rest in partitions_le(n - p, p, maxlen - 1):
                yield (p,) + rest

    def rec(row, prev, w):
        out[w] += 1  # remaining rows empty
        if row == m:
            return
        for s in range(1, N - w + 1):
            for lam in partitions_le(s, prev[0] if prev else s, len(prev) if prev else s):
                if prev and any(lam[i] > prev[i] for i in range(len(lam))):
                    continue
                rec(row + 1, lam, w + s)

    rec(0, None, 0)
    return out


def symmetric_pp(N):
    """Symmetric plane partitions by weight, brute force over Young-diagram fillings."""
    out = [0] * (N + 1)

    def rows_gen(w):
        # generate plane partitions as list of rows, then test symmetry
        pass

    # enumerate plane partitions recursively, keep the symmetric ones
    def partitions_bounded(n, bound):
        # partitions of n dominated componentwise by bound (tuple), parts weakly decreasing
        res = []

        def r(i, left, prevpart, cur):
            if left == 0:
                res.append(tuple(cur))
                return
            if i >= len(bound):
                return
            for p in range(min(left, prevpart, bound[i]), 0, -1):
                cur.append(p)
                r(i + 1, left - p, p, cur)
                cur.pop()

        r(0, n, n, [])
        return res

    def rec(rows, w):
        # rows: list of tuples
        if is_sym(rows):
            out[w] += 1
        prev = rows[-1] if rows else tuple([N] * N)
        for s in range(1, N - w + 1):
            for lam in partitions_bounded(s, prev):
                rec(rows + [lam], w + s)

    def is_sym(rows):
        for i, r in enumerate(rows):
            for j, v in enumerate(r):
                if j >= len(rows) or i >= len(rows[j]) or rows[j][i] != v:
                    return False
        return True

    rec([], 0)
    return out


def run_I():
    N = 12
    for m in (1, 2, 3):
        bf = plane_partitions_rows(m, N)
        pf = euler_product({n: min(n, m) for n in range(1, N + 1)}, N)
        check("I", bf == pf, f"chain_{m} x N: brute force = prod (1-q^n)^-min(n,{m}) to q^{N}")
        poly = mul(pf, euler_product({n: -m for n in range(1, N + 1)}, N), N)
        nonconst = any(poly[1:])
        check("I", nonconst == (m >= 2),
              f"chain_{m} x N times (q;q)^{m} is {'non' if nonconst else ''}constant "
              f"polynomial {poly[:m * m]}")
    bf = plane_partitions_rows(N, N)
    mac = euler_product({n: n for n in range(1, N + 1)}, N)
    check("I", bf == mac, "N x N: brute force = MacMahon to q^12")
    sb = symmetric_pp(N)
    ex = {}
    for i in range(1, N + 1):
        if 2 * i - 1 <= N:
            ex[2 * i - 1] = ex.get(2 * i - 1, 0) + 1
        for j in range(i + 1, N + 1):
            t = 2 * (i + j - 1)
            if t <= N:
                ex[t] = ex.get(t, 0) + 1
    sf = euler_product(ex, N)
    check("I", sb == sf, f"transpose-fixed (symmetric) pp: brute = product to q^{N}: {sf}")
    # elementary lower bound replacing Meinardus: a_sym(N) >= pp(floor(N/4))
    M = 80
    ex = {}
    for i in range(1, M + 1):
        if 2 * i - 1 <= M:
            ex[2 * i - 1] = ex.get(2 * i - 1, 0) + 1
        for j in range(i + 1, M + 1):
            t = 2 * (i + j - 1)
            if t <= M:
                ex[t] = ex.get(t, 0) + 1
    sym = euler_product(ex, M)
    mac = euler_product({n: n for n in range(1, M + 1)}, M)
    check("I", all(sym[k] >= mac[k // 4] for k in range(M + 1)),
          "a_sym(N) >= pp(floor(N/4)) for N <= 80")
    # Meinardus hypothesis check: exponent Dirichlet series has a pole at s = 1
    # residue of sum_{odd} n^-s + sum_k floor(k/2) (2k)^-s at s = 1 is
    # 1/2 (odd part) - 1/8 (from -(1-(-1)^k)/4 term: -1/2 * 1/4 * ... ) = 3/8
    # numerically: sum_{n<=X} a(n) - X^2/16 ~ (3/8) log X ... we test the
    # partial sums of a(n)/n, which grow like (3/8) log X + X/8.
    X1, X2 = 10 ** 4, 10 ** 6

    def S(X):
        return sum((1 if n % 2 else (n // 2) // 2) / n for n in range(1, X + 1))

    resid = (S(X2) - S(X1) - (X2 - X1) / 8) / math.log(X2 / X1)
    check("I", abs(resid - 3 / 8) < 0.05,
          f"exponent Dirichlet series D(s) of the symmetric case has a pole at s=1 "
          f"(residue ~ {resid:.3f}, predicted 3/8): Meinardus' single-pole hypothesis fails")


# ------------------------------------------- [D] Lemma D (log-derivative) ---

def run_D():
    z3 = sum(1 / k ** 3 for k in range(1, 200000))

    def dlog(acoef, y, nmax):
        # Dlog prod (1-q^n)^(-a(n)) at q = e^{-2 pi y}: sum_n n a(n) q^n/(1-q^n)
        q = math.exp(-2 * math.pi * y)
        s = 0.0
        qn = 1.0
        for n in range(1, nmax + 1):
            qn *= q
            if qn < 1e-300:
                break
            s += n * acoef(n) * qn / (1 - qn)
        return s

    def E2(y):
        q = math.exp(-2 * math.pi * y)
        s = 0.0
        qn = 1.0
        for n in range(1, 400000):
            qn *= q
            if qn < 1e-300:
                break
            s += n * qn / (1 - qn)
        return 1 - 24 * s

    for y in (0.01, 0.003):
        v = y ** 3 * dlog(lambda n: n, y, 10 ** 6)
        check("D", abs(v / (2 * z3 / (2 * math.pi) ** 3) - 1) < 0.05,
              f"MacMahon: y^3 Dlog F(iy) at y={y}: {v:.6f} vs 2zeta(3)/(2pi)^3 = "
              f"{2 * z3 / (2 * math.pi) ** 3:.6f}")

    def asym(n):
        return 1 if n % 2 else (n // 2) // 2

    for y in (0.001, 0.0003):
        v = y ** 3 * dlog(asym, y, 10 ** 7)
        pred = z3 / (4 * (2 * math.pi) ** 3)
        check("D", abs(v / pred - 1) < 0.02,
              f"symmetric pp: y^3 Dlog F(iy) at y={y}: {v:.6f} vs zeta(3)/(4(2pi)^3)"
              f" = {pred:.6f}")
    for y in (0.01, 0.003):
        v = y ** 3 * E2(y)
        check("D", abs(v) < 0.02, f"y^3 E_2(iy) at y={y}: {v:.2e} (-> 0)")
    # positive control: 1/(q;q) (modular) has y^2 Dlog bounded, y^3 Dlog -> 0
    for y in (0.01, 0.003):
        v2 = y ** 2 * dlog(lambda n: 1, y, 10 ** 6)
        check("D", abs(v2 - 1 / 24) < 0.01,
              f"control 1/(q;q): y^2 Dlog = {v2:.5f} (bounded, -> 1/24)")
    # chain_m x N: a(n) bounded, so Lemma D is silent (Lemma R needed)
    v = 0.003 ** 3 * dlog(lambda n: min(n, 3), 0.003, 10 ** 6)
    check("D", abs(v) < 0.01, f"chain_3 x N: y^3 Dlog -> 0 ({v:.2e}); Lemma D silent")


# --------------------------------------------------- [F] Frame shapes ---

def partitions(n, maxp=None):
    if maxp is None:
        maxp = n
    if n == 0:
        yield ()
        return
    for p in range(min(n, maxp), 0, -1):
        for r in partitions(n - p, p):
            yield (p,) + r


def lie_char(n, ctype):
    """Classical character of Lie_n: mu(d) d^{m-1} (m-1)! on type d^m, else 0."""
    if len(set(ctype)) != 1:
        return 0
    d = ctype[0]
    m = len(ctype)
    return mobius(d) * d ** (m - 1) * math.factorial(m - 1)


def power_type(ctype, e):
    out = []
    for c in ctype:
        g = math.gcd(c, e)
        out += [c // g] * g
    return tuple(sorted(out, reverse=True))


def order_of(ctype):
    return math.lcm(*ctype)


def frame_shape(char_of_power, o):
    """r_t with t r_t = sum_{e|t} mu(t/e) chi(g^e), t | o."""
    r = {}
    for t in divisors(o):
        s = sum(mobius(t // e) * char_of_power(e) for e in divisors(t))
        assert s % t == 0, "non-integral Frame shape"
        if s:
            r[t] = s // t
    return r


def fock_series_from_chars(char_of_power, N):
    """exp sum_k sum_m chi(g^k) q^{mk}/k, exact rationals."""
    L = [Fraction(0)] * (N + 1)
    for k in range(1, N + 1):
        ck = char_of_power(k)
        for m in range(1, N // k + 1):
            L[m * k] += Fraction(ck, k)
    # exp via f' = L' f
    f = [Fraction(0)] * (N + 1)
    f[0] = Fraction(1)
    for n in range(1, N + 1):
        f[n] = sum(j * L[j] * f[n - j] for j in range(1, n + 1)) / n
    return f


def run_F():
    note = {
        (5, (5,)): {1: -1, 5: 5},
        (6, (2, 2, 2)): {1: -8, 2: 64},
        (6, (3, 3)): {1: -3, 3: 41},
        (6, (6,)): {1: 1, 2: -2, 3: -3, 6: 22},
        (7, (7,)): {1: -1, 7: 103},
    }
    for (n, ct), want in note.items():
        r = frame_shape(lambda e: lie_char(n, power_type(ct, e)), order_of(ct))
        check("F", r == want, f"Lie_{n} at {ct}: Frame shape {r}")
    N = 30
    ok = True
    twist_ok = True
    for n in range(4, 8):
        for ct in partitions(n):
            o = order_of(ct)
            chi = lambda e, ct=ct, n=n: lie_char(n, power_type(ct, e))
            r = frame_shape(chi, o)
            f = fock_series_from_chars(chi, N)
            eta = euler_product({}, N)
            for t, rt in r.items():
                for k in range(t, N + 1, t):  # (q^t; q^t)^(-r_t)
                    eta = mul(eta, inv_one_minus_power(k, rt, N), N)
            if [Fraction(x) for x in eta] != f:
                ok = False
            sg = (-1) ** sum(c - 1 for c in ct)
            if sg == -1:
                chim = lambda e, ct=ct, n=n: ((-1) ** (e * sum(c - 1 for c in ct))) * \
                    lie_char(n, power_type(ct, e))
                rm = frame_shape(chim, 2 * o)
                pred = {}
                for t, rt in r.items():
                    if t % 2:
                        pred[2 * t] = pred.get(2 * t, 0) + rt
                        pred[t] = pred.get(t, 0) - rt
                    else:
                        pred[t] = pred.get(t, 0) + rt
                pred = {t: v for t, v in pred.items() if v}
                if rm != pred:
                    twist_ok = False
    check("F", ok, "Lie_4..Lie_7, every class: Fock trace = prod (q^t;q^t)^(-r_t) to q^30")
    check("F", twist_ok, "odd g, sgn-twisted: t^r -> (2t)^r t^(-r) for odd t, even t fixed")
    reg = all(lie_char(n, ct + (1,)) == 0 for n in range(2, 10)
              for ct in partitions(n - 1) if ct != (1,) * (n - 1))
    check("F", reg and lie_char(5, (1,) * 5) == 24,
          "Lie_n restricted to S_{n-1} is the regular representation (n <= 9): "
          "the Reg(S_4) 'control' is Lie_5 itself")
    # Lie_5 classes and shapes: free off identity and 5-cycles
    shapes = {}
    for ct in partitions(5):
        shapes[ct] = frame_shape(lambda e, ct=ct: lie_char(5, power_type(ct, e)),
                                 order_of(ct))
    want = {(1,) * 5: {1: 24}, (2, 1, 1, 1): {2: 12}, (2, 2, 1): {2: 12},
            (3, 1, 1): {3: 8}, (3, 2): {6: 4}, (4, 1): {4: 6}, (5,): {1: -1, 5: 5}}
    check("F", shapes == want, f"Lie_5 shapes {sorted(shapes.values(), key=str)}")
    # eta(5t)^5/eta(t) = q prod (1-q^{5n})^5/(1-q^n) vs sum_{d|n} (n/d | 5) d
    N = 200
    s = mul(euler_product({5 * n: -5 for n in range(1, N // 5 + 1)}, N),
            euler_product({n: 1 for n in range(1, N + 1)}, N), N)
    lhs = [0] + s[:N]

    def leg5(a):
        a %= 5
        return 0 if a == 0 else (1 if a in (1, 4) else -1)

    rhs = [0] + [sum(leg5(n // d) * d for d in divisors(n)) for n in range(1, N + 1)]
    check("F", lhs[:N + 1] == rhs[:N + 1],
          "eta(5t)^5/eta(t) = sum_n sum_{d|n} (n/d | 5) d q^n through q^200")
    wrong = [0] + [sum(leg5(d) * d for d in divisors(n)) for n in range(1, N + 1)]
    check("F", lhs != wrong, "negative control: sum_{d|n} (d|5) d fails")


# ------------------------------------------------- [A] A_5 split classes ---

def run_A():
    phi = (1 + 5 ** 0.5) / 2
    # A_5 classes: 1, (12)(34), (123), 5a, 5b; sizes 1, 15, 20, 12, 12
    sizes = [1, 15, 20, 12, 12]
    chars = {
        "1": [1, 1, 1, 1, 1],
        "3": [3, -1, 0, phi, 1 - phi],
        "3'": [3, -1, 0, 1 - phi, phi],
        "4": [4, 0, 1, -1, -1],
        "5": [5, 1, -1, 0, 0],
    }
    lie5 = [24, 0, 0, -1, -1]
    mult = {k: sum(s * x * y for s, x, y in zip(sizes, v, lie5)) / 60 for k, v in chars.items()}
    want = {"1": 0, "3": 1, "3'": 1, "4": 2, "5": 2}
    check("A", all(abs(mult[k] - want[k]) < 1e-9 for k in want),
          f"Lie_5|A_5 = 3 + 3' + 2*4 + 2*5: {({k: round(v, 6) for k, v in mult.items()})}")
    # Fock trace on Sym(3 (x) tC[t]) at 5a (eigenvalues 1, z, z^-1) and 5b (1, z^2, z^-2)
    z = cmath.exp(2j * math.pi / 5)

    def fock(eigs, N):
        f = [0j] * (N + 1)
        f[0] = 1
        L = [0j] * (N + 1)
        for k in range(1, N + 1):
            ck = sum(e ** k for e in eigs)
            for m in range(1, N // k + 1):
                L[m * k] += ck / k
        for n in range(1, N + 1):
            f[n] = sum(j * L[j] * f[n - j] for j in range(1, n + 1)) / n
        return f

    fa = fock([1, z, z ** -1], 6)
    fb = fock([1, z ** 2, z ** -2], 6)
    check("A", abs(fa[1] - phi) < 1e-9 and abs(fb[1] - (1 - phi)) < 1e-9,
          f"q^1 coefficients phi vs 1-phi: {fa[1].real:.4f}, {fb[1].real:.4f}")
    check("A", all(abs(x.imag) < 1e-9 for x in fa + fb),
          "the two series are real (eigenvalues closed under inversion)")
    print("      5a:", [round(x.real, 4) for x in fa])
    print("      5b:", [round(x.real, 4) for x in fb])
    # on the full Lie_5 the two classes give the same series
    full_a = fock([1] * 0 + [z ** j for j in range(5) for _ in range(5)][1:] , 6)
    # Lie_5 at a 5-cycle has Frame shape 1^-1 5^5: eigenvalue multiset is
    # 5 copies of all 5th roots of unity minus one copy of 1
    full_b = fock([(z ** 2) ** j for j in range(5) for _ in range(5)][1:], 6)
    check("A", all(abs(x - y) < 1e-9 for x, y in zip(full_a, full_b)),
          "on the whole of Lie_5 (rational character) 5a and 5b give equal series")


SECTIONS = {"--W": run_W, "--H": run_H, "--P": run_P, "--I": run_I,
            "--D": run_D, "--F": run_F, "--A": run_A}


def main(argv):
    if len(argv) > 1:
        for a in argv[1:]:
            SECTIONS[a]()
    else:
        P = run_W()
        run_H(P)
        run_P()
        run_I()
        run_D()
        run_F()
        run_A()
    bad = [t for t, ok in CHECKS if not ok]
    print(f"\n{len(CHECKS) - len(bad)}/{len(CHECKS)} checks passed")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
