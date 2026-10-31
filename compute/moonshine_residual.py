"""Checks for notes/moonshine_residual.md (mg-be1f9).

The residual moonshine candidates left open by notes/audit_moonshine_scoping.md:
items 6(d), 8, 7 and 1 of its section 3.

Sections
  [U]  item 6(d): unlabeled component-closed classes of the poset monoid with
       exponentially growing connected counts.  Counts of rooted trees,
       oriented trees (Hasse diagram a tree), connected series-parallel
       (= N-free) posets and cycle-Hasse posets, each against a brute-force
       count over all unlabeled posets with n <= 6; the boundedness
       R(rho) <= 1, C_SP(rho) < 1.15 behind Lemma P; the singular exponent
       alpha of u_n ~ C rho^-n n^alpha (-3/2, -5/2, -3/2 against -1 for the
       necklace control); n u_n 2^-n -> 1/2 for the cycle-Hasse class.
  [E]  item 6(d), realizability: the exponents u_n of 1/E_6 are positive
       integers (n <= 150) with n u_n e^(-2 pi n) -> 1, and
       u_n <= 2^((10n-1)^2) / (20n)!  (a lower bound for connected unlabeled
       posets on 20n points), so 1/E_6(20 tau) is the type series of a
       component-closed class.
  [S]  item 7: P-partitions of the shifted quadrant against
       prod (1-q^n)^(-ceil(n/2)) (q^16), and y^3 Dlog F(iy) -> zeta(3)/(2 pi)^3.
  [B]  item 7: P-partitions of the infinite binary tree (root minimal):
       recursion against brute force (q^8), B_m(1/4) bounded, alpha -> -3/2.
  [G]  item 7: a Gamma_0(2)-invariant F, holomorphic on H and at infinity,
       nonnegative coefficients with log a_n of order n^(2/3) (growth does
       not exclude broad-sense modularity on groups with two cusps).
  [T]  item 1: twisted traces T_{g,h} on Sym(Lie(P) (x) tC[t]) from the joint
       character of (g, h); the S-, T- and Gamma(N)-laws checked numerically
       for antichains (Lie_4, Lie_5, Lie_6), 2+2 and the bowtie; negative
       controls (wrong S-partner, one line without its conjugate).

Exact integer / rational arithmetic, except [E] asymptotics, [G] growth and
[T], which use floats and complex floats against stated tolerances.

Run from compute/:  python3 moonshine_residual.py [--U|--E|--S|--B|--G|--T]
Exit status 0 iff every check passes.
"""

import cmath
import math
import sys
from fractions import Fraction

from poset_jks_check import transitive_closure, unlabeled_posets_by_extension
from poset_lie_structure import closed_formula

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


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


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


def phi(n):
    return sum(1 for k in range(1, n + 1) if math.gcd(k, n) == 1)


def euler_transform(u, N):
    """prod_{n>=1} (1-x^n)^(-u[n]) to order N (u[0] ignored), exact."""
    b = [0] + [sum(d * u[d] for d in divisors(n) if d < len(u)) for n in range(1, N + 1)]
    a = [1] + [0] * N
    for n in range(1, N + 1):
        s = sum(b[k] * a[n - k] for k in range(1, n + 1))
        assert s % n == 0
        a[n] = s // n
    return a


def product_exponents(a, N):
    """Inverse Euler transform: u with a = prod (1-x^n)^(-u_n), a[0] = 1."""
    xa = [n * a[n] for n in range(N + 1)]
    g = [0] * (N + 1)  # x a'/a
    for n in range(1, N + 1):
        g[n] = xa[n] - sum(g[k] * a[n - k] for k in range(1, n))
    u = [0] * (N + 1)
    for n in range(1, N + 1):
        s = sum(mobius(n // d) * g[d] for d in divisors(n))
        assert s % n == 0
        u[n] = s // n
    return u


def alpha_estimates(a, ns):
    """alpha_n = -(n-1)^2 (a_n a_{n-2} / a_{n-1}^2 - 1); tends to alpha when
    a_n ~ C rho^-n n^alpha (a single dominant singularity)."""
    return {n: float(-(n - 1) ** 2 * (Fraction(a[n] * a[n - 2], a[n - 1] ** 2) - 1))
            for n in ns}


# ------------------------------------------- [U] component-closed classes ---

def rooted_trees(N, c=1):
    """R = x Exp(c R): c = 1 rooted trees (A000081), c = 2 rooted oriented
    trees (A000151)."""
    R = [0] * (N + 1)
    for n in range(1, N + 1):
        R[n] = euler_transform([0] + [c * R[k] for k in range(1, n)], n - 1)[n - 1]
    return R


def sp_connected(N):
    """Connected series-parallel (N-free) posets.  C = x + sum_{k>=2} s^k with
    s = x + D the ordinally indecomposable ones and D = Exp(C) - 1 - C."""
    C = [0] * (N + 1)
    for n in range(1, N + 1):
        if n == 1:
            C[1] = 1
            continue
        E = euler_transform(C[:n], n - 1)  # uses C_1..C_{n-1}
        s = [0] * n
        s[1] = 1
        for k in range(2, n):
            s[k] = E[k] - C[k]
        tot, p = 0, s[:] + [0]
        for _ in range(2, n + 1):
            p = mul(p, s + [0], n)
            tot += p[n]
        C[n] = tot
    return C


def cycle_hasse_burnside(n):
    """Unlabeled posets whose Hasse diagram is an n-cycle: orbits of the
    dihedral group on valid edge-orientation words.  A word is valid iff it
    is not constant and is not two runs with a run of length 1 (those have a
    transitive edge).  Rotation k fixes the words of period gcd(n, k);
    reflections reverse the word and flip every sign."""
    def valid(w):
        if len(set(w)) == 1:
            return False
        runs = sum(1 for i in range(n) if w[i] != w[i - 1])
        if runs == 2:
            k = sum(w)
            return 1 < k < n - 1
        return True

    words = [tuple((m >> i) & 1 for i in range(n)) for m in range(1 << n)]
    tot = 0
    for w in words:
        if not valid(w):
            continue
        for k in range(n):
            if w[k:] + w[:k] == w:
                tot += 1
            rv = tuple(1 - x for x in reversed(w))
            if rv[k:] + rv[:k] == w:
                tot += 1
    assert tot % (2 * n) == 0
    return tot // (2 * n)


def cycle_hasse_rotation_part(n):
    """(1/2n) sum_{d|n} phi(n/d) 2^d: the necklace part of u_n."""
    return Fraction(sum(phi(n // d) * 2 ** d for d in divisors(n)), 2 * n)


def poset_features(rel, n):
    lt = [[(i, j) in rel for j in range(n)] for i in range(n)]
    covers = [(i, j) for i in range(n) for j in range(n)
              if lt[i][j] and not any(lt[i][k] and lt[k][j] for k in range(n))]
    # connectivity of the comparability graph
    adj = {i: set() for i in range(n)}
    for i, j in covers:
        adj[i].add(j)
        adj[j].add(i)
    seen, stack = {0}, [0]
    while stack:
        x = stack.pop()
        for y in adj[x] - seen:
            seen.add(y)
            stack.append(y)
    connected = len(seen) == n
    deg = [len(adj[i]) for i in range(n)]
    lower = [sum(1 for (i, j) in covers if j == x) for x in range(n)]
    nfree = True
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for d in range(n):
                    if len({a, b, c, d}) < 4:
                        continue
                    pairs = {(a, c), (b, c), (b, d)}
                    sub = {(x, y) for x in (a, b, c, d) for y in (a, b, c, d) if lt[x][y]}
                    if sub == pairs:
                        nfree = False
    return {
        "connected": connected,
        "tree": connected and len(covers) == n - 1,
        "rooted": connected and all(l <= 1 for l in lower),
        "cycle": connected and n >= 3 and len(covers) == n and all(x == 2 for x in deg),
        "nfree": nfree,
    }


def run_U():
    N = 120
    R = rooted_trees(N)
    Ro = rooted_trees(N, 2)
    T = [0] + [Ro[n] - sum(Ro[k] * Ro[n - k] for k in range(1, n)) for n in range(1, N + 1)]
    C = sp_connected(N)
    check("U", R[1:12] == [1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842],
          f"rooted trees R = x Exp(R): {R[1:12]} (A000081)")
    check("U", T[1:12] == [1, 1, 3, 8, 27, 91, 350, 1376, 5743, 24635, 108968],
          f"oriented trees T = R_o - R_o^2, R_o = x Exp(2 R_o): {T[1:12]} (A000238)")
    S = euler_transform(C, 11)
    check("U", S[1:12] == [1, 2, 5, 15, 48, 167, 602, 2256, 8660, 33958, 135292],
          f"series-parallel posets Exp(C) - 1: {S[1:12]} (A003430)")

    # brute force over all unlabeled posets n <= 6
    P = unlabeled_posets_by_extension(6)
    cnt = {k: [0] * 7 for k in ("rooted", "tree", "cycle", "nfree_conn")}
    for n in range(1, 7):
        for rel in P[n]:
            f = poset_features(rel, n)
            for k in ("rooted", "tree", "cycle"):
                cnt[k][n] += f[k]
            cnt["nfree_conn"][n] += f["nfree"] and f["connected"]
    check("U", cnt["rooted"][1:] == R[1:7],
          f"brute force: connected posets with <= 1 lower cover per element {cnt['rooted'][1:]}")
    check("U", cnt["tree"][1:] == T[1:7],
          f"brute force: Hasse diagram a tree {cnt['tree'][1:]} = oriented trees")
    check("U", cnt["nfree_conn"][1:] == C[1:7],
          f"brute force: connected N-free {cnt['nfree_conn'][1:]} = connected SP")
    cyc = [0, 0, 0, 0] + [cycle_hasse_burnside(n) for n in range(4, 7)]
    check("U", cnt["cycle"][1:] == cyc[1:7],
          f"brute force: Hasse diagram a cycle {cnt['cycle'][1:]} = dihedral Burnside count")

    # Lemma P inputs: boundedness at the radius.  rho estimated from the ratio,
    # partial sums at a point below rho stay under the proved bounds.
    for name, u, bound in (("rooted trees R", R, 1.0), ("connected SP C", C, 1.15)):
        x = (1 - 2 / N) * u[N - 1] / u[N]  # u_{n-1}/u_n ~ rho (1 + 3/(2n)) > rho
        ps = sum(u[n] * x ** n for n in range(1, N + 1))
        check("U", ps <= bound, f"{name}: sum u_n x^n = {ps:.4f} <= {bound} at x = {x:.5f}")
    # Lemma P for the oriented trees: T_n <= R_o,n <= n T_n and R_o <= 1/2
    check("U", all(T[n] <= Ro[n] <= n * T[n] for n in range(1, N + 1)),
          "T_n <= R_o,n <= n T_n (same radius, n <= 120)")
    x = (1 - 2 / N) * Ro[N - 1] / Ro[N]
    ps = sum(Ro[n] * x ** n for n in range(1, N + 1))
    check("U", ps <= 0.5, f"R_o: sum at x = {x:.5f} is {ps:.4f} <= 1/2")

    # singular exponents
    lyndon = [0] + [sum(mobius(d) * 2 ** (n // d) for d in divisors(n)) // n
                    for n in range(1, N + 1)]
    ns = (40, 80, 120)
    for name, u, target in (("rooted trees", R, -1.5), ("oriented trees", T, -2.5),
                            ("connected SP", C, -1.5),
                            ("necklace control (log type)", lyndon, -1.0)):
        al = alpha_estimates(u, ns)
        check("U", abs(al[120] - target) < 0.02,
              f"alpha({name}) at n = 40, 80, 120: "
              + ", ".join(f"{al[n]:.4f}" for n in ns) + f" -> {target}")

    # cycle-Hasse: exact decomposition u_n = necklace part - 2 + reflections/(2n)
    ok = True
    for n in range(4, 15):
        u = cycle_hasse_burnside(n)
        refl = (u - cycle_hasse_rotation_part(n) + 2) * 2 * n
        ok &= refl.denominator == 1 and 0 <= refl <= n * 2 ** (n // 2 + 1)
    check("U", ok, "cycle-Hasse u_n = (1/2n) sum phi(n/d) 2^d - 2 + Refl_n/(2n), "
                   "0 <= Refl_n <= n 2^(n/2+1) (4 <= n <= 14)")
    vals = [float(cycle_hasse_burnside(n) * n / 2 ** n) for n in (10, 14, 18)]
    check("U", abs(vals[-1] - 0.5) < 0.01,
          f"n u_n 2^-n at n = 10, 14, 18: {[round(v, 4) for v in vals]} -> 1/2 "
          "(log coefficient m = 1/2, not an integer)")


# --------------------------------------------- [E] 1/E_6 is realizable ---

def sigma(n, k):
    return sum(d ** k for d in divisors(n))


def run_E():
    N = 150
    E6 = [1] + [-504 * sigma(n, 5) for n in range(1, N + 1)]
    inv = [0] * (N + 1)  # 1/E6
    inv[0] = 1
    for n in range(1, N + 1):
        inv[n] = -sum(E6[k] * inv[n - k] for k in range(1, n + 1))
    u = product_exponents(inv, N)
    check("E", u[1:4] == [504, 143388, 51180024], f"1/E_6 = prod (1-q^n)^(-u_n), u = {u[1:4]} ...")
    check("E", all(x > 0 for x in u[1:]), "u_n > 0 for n <= 150")
    dev = max(abs(Fraction(n * u[n]) / Fraction(math.exp(2 * math.pi * n)) - 1)
              * math.exp(math.pi * n) for n in range(1, 11))
    check("E", dev < 10, f"|n u_n e^(-2 pi n) - 1| <= {dev:.2f} e^(-pi n) for n <= 10 "
                         "(simple pole at q = e^(-2 pi), log coefficient m = 1; next poles "
                         "at |q| = e^(-pi))")

    def log2_conn_lower(m):
        k = m // 2
        return (k - 1) * (m - k - 1) - math.lgamma(m + 1) / math.log(2)

    ok = all(math.log2(u[n]) <= log2_conn_lower(20 * n) for n in range(1, N + 1))
    check("E", ok, "u_n <= 2^((10n-1)^2) / (20n)! <= #connected unlabeled posets on 20n "
                   f"points (n <= 150; margin at n = 1: "
                   f"{log2_conn_lower(20) - math.log2(504):.1f} bits)")
    # the bound grows like 100 n^2 bits, u_n like 9.07 n bits: beyond n = 150
    check("E", all(log2_conn_lower(20 * n) - (2 * math.pi * n / math.log(2) + 1) > 0
                   for n in range(1, 2000)),
          "2^((10n-1)^2)/(20n)! > 2 e^(2 pi n) for n < 2000 (and the gap grows)")


# --------------------------------------------- [S] shifted quadrant ---

def partitions_bounded(s, bounds):
    """Weakly decreasing positive sequences of sum s, part i <= bounds[i]
    (bounds None: unbounded)."""
    out = []

    def r(i, left, prev, cur):
        if left == 0:
            out.append(tuple(cur))
            return
        b = prev
        if bounds is not None:
            if i >= len(bounds):
                return
            b = min(b, bounds[i])
        for p in range(min(b, left), 0, -1):
            cur.append(p)
            r(i + 1, left - p, p, cur)
            cur.pop()
    r(0, s, s if bounds is None else 10 ** 9, [])
    return out


def shifted_quadrant(W):
    """P-partitions of {(i, j): i <= j} (product order), by weight.  Row i is a
    partition rho_i (entries a_{i,i}, a_{i,i+1}, ...); the column condition is
    rho_{i+1}[m] <= rho_i[m+1]."""
    memo = {}

    def below(prev, w):
        key = (prev, w)
        if key in memo:
            return memo[key]
        res = [0] * (w + 1)
        res[0] = 1
        for s in range(1, w + 1):
            for r in partitions_bounded(s, list(prev[1:])):
                for i, x in enumerate(below(r, w - s)):
                    res[i + s] += x
        memo[key] = res
        return res

    tot = [0] * (W + 1)
    tot[0] = 1
    for s in range(1, W + 1):
        for r in partitions_bounded(s, None):
            for i, x in enumerate(below(r, W - s)):
                tot[i + s] += x
    return tot


def run_S():
    W = 16
    bf = shifted_quadrant(W)
    pred = euler_transform([0] + [(n + 1) // 2 for n in range(1, W + 1)], W)
    check("S", bf == pred, f"shifted quadrant = prod (1-q^n)^(-ceil(n/2)) through q^{W}: {bf[:10]}...")
    wrong = euler_transform([0] + [n // 2 for n in range(1, W + 1)], W)
    check("S", bf != wrong, "negative control: floor(n/2) exponents disagree")

    def G(y, nmax):
        return sum(sum(d * ((d + 1) // 2) for d in divisors(N)) * math.exp(-2 * math.pi * N * y)
                   for N in range(1, nmax))
    lim = 1.2020569031595942 / (2 * math.pi) ** 3
    vals = [(y, y ** 3 * G(y, int(12 / y))) for y in (0.01, 0.003)]
    check("S", all(abs(v / lim - 1) < 0.05 for _, v in vals),
          "y^3 Dlog F(iy) at y = 0.01, 0.003: "
          + ", ".join(f"{v:.6f}" for _, v in vals) + f" -> zeta(3)/(2 pi)^3 = {lim:.6f} "
          "(Lemma D violated)")


# --------------------------------------------- [B] infinite binary tree ---

def binary_tree_series(N):
    """B = lim B_m, B_m = B_{m-1} + q^m B_m^2: P-partitions of the infinite
    binary tree, root minimal, with root value <= m."""
    B = [1] + [0] * N
    for j in range(1, N + 1):
        Bj = B[:]
        while True:
            sq = mul(Bj, Bj, N)
            new = [B[n] + (sq[n - j] if n >= j else 0) for n in range(N + 1)]
            if new == Bj:
                break
            Bj = new
        B = Bj
    return B


def binary_tree_brute(W):
    """Order-reversing maps on the binary tree (nodes = binary words, root
    minimal), finite support, weight <= W, by direct search."""
    counts = [0] * (W + 1)

    def rec(frontier, w):
        # frontier: list of (parent value) for nodes still to decide, BFS order
        counts[w] += 1 if not frontier else 0
        if not frontier:
            return
        pv, rest = frontier[0], frontier[1:]
        for v in range(0, min(pv, W - w) + 1):
            if v == 0:
                rec(rest, w)
            else:
                rec(rest + [v, v], w + v)
    rec([W], 0)
    return counts


def run_B():
    W = 8
    B = binary_tree_series(200)
    bf = binary_tree_brute(W)
    check("B", B[:W + 1] == bf, f"binary tree: recursion = direct search through q^{W}: {bf}")
    vals = []
    b = 0.0
    for m in range(1, 60):
        x = 0.25 ** m
        prev = 1.0 if m == 1 else b
        b = 2 * prev / (1 + math.sqrt(1 - 4 * x * prev))  # root of x b^2 - b + prev
        vals.append(b)
    check("B", abs(vals[0] - 2) < 1e-12 and max(vals) < 2.70,
          f"B_m(1/4): B_1 = {vals[0]:.4f}, B_2 = {vals[1]:.4f}, sup over m < 60 = {max(vals):.6f} < 2.70")
    ps = sum(B[n] * 0.25 ** n for n in range(201))
    check("B", ps <= max(vals), f"partial sum of B at 1/4 (q^200) = {ps:.4f} <= sup B_m(1/4)")
    al = alpha_estimates(B, (50, 100, 200))
    check("B", abs(al[200] + 1.5) < 0.01,
          "alpha(binary tree) at n = 50, 100, 200: "
          + ", ".join(f"{al[n]:.4f}" for n in (50, 100, 200)) + " -> -3/2")


# ------------------------------------- [G] a Gamma_0(2) broad-sense example ---

def run_G():
    N = 200
    # f = q prod (1+q^n)^24 = (eta(2t)/eta(t))^24, nonnegative integer coefficients
    f = [0] * (N + 1)
    f[1] = 1
    for n in range(1, N + 1):
        for _ in range(24):
            for i in range(N, n - 1, -1):
                f[i] += f[i - n]
    ff = [float(x) for x in f]
    # F = prod_{j>=0} (1 + f/2^j) = sum_k f^k 2^(-k(k-1)/2) / prod_{i<=k} (1 - 2^-i)
    F = [0.0] * (N + 1)
    F[0] = 1.0
    pw = [1.0] + [0.0] * N
    coef = 1.0
    for k in range(1, N + 1):
        pw = mul(pw, ff, N)
        coef *= 2.0 ** (-(k - 1)) / (1 - 2.0 ** (-k))
        for n in range(k, N + 1):
            F[n] += coef * pw[n]
    check("G", all(x > 0 for x in F), "F = prod_j (1 + f/2^j): every q-coefficient > 0 (n <= 200)")

    def ev(series_f, tau):
        q = cmath.exp(2j * math.pi * tau)
        fv = q
        for n in range(1, 400):
            fv *= (1 + q ** n) ** 24
        val = 1.0
        for j in range(80):
            val *= 1 + fv / 2 ** j
        return val
    tau = complex(-0.5, 0.5)
    gt = tau / (2 * tau + 1)
    a, b = ev(None, tau), ev(None, gt)
    check("G", abs(a - b) < 1e-9 * abs(a),
          f"F(gamma tau) = F(tau) for gamma = [[1,0],[2,1]] at tau = {tau}: {a:.6e} vs {b:.6e}")
    r_sqrt = [math.log(F[n]) / math.sqrt(n) for n in (50, 100, 200)]
    r_23 = [math.log(F[n]) / n ** (2 / 3) for n in (50, 100, 200)]
    check("G", r_sqrt[0] < r_sqrt[1] < r_sqrt[2],
          f"log a_n / sqrt(n) at n = 50, 100, 200: {[round(x, 3) for x in r_sqrt]} (increasing: "
          "not weakly holomorphic)")
    print(f"      log a_n / n^(2/3) at n = 50, 100, 200: {[round(x, 3) for x in r_23]} "
          "(saddle-point prediction 3 (pi^4/(4 log 2))^(1/3) ~ 12.4)")


# ------------------------------------------------ [T] twisted traces ---

def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def ppow(p, e):
    r = tuple(range(len(p)))
    for _ in range(e):
        r = compose(p, r)
    return r


def porder(p):
    k, r = 1, p
    while r != tuple(range(len(p))):
        r = compose(p, r)
        k += 1
    return k


def from_cycles(n, cycles):
    p = list(range(n))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def joint_spectrum(rel, n, g, h):
    """{(s, r): multiplicity} with g = e^(2 pi i s), h = e^(2 pi i r) on
    Lie(P), s, r in [0, 1), from the character of <g, h>."""
    assert compose(g, h) == compose(h, g)
    og, oh = porder(g), porder(h)
    chi = {}
    for a in range(og):
        for b in range(oh):
            chi[a, b] = closed_formula(rel, n, compose(ppow(g, a), ppow(h, b)))
    spec = {}
    for j in range(og):
        for k in range(oh):
            m = sum(chi[a, b] * cmath.exp(-2j * math.pi * (a * j / og + b * k / oh))
                    for a in range(og) for b in range(oh)) / (og * oh)
            mi = round(m.real)
            assert abs(m - mi) < 1e-8, m
            if mi:
                spec[Fraction(j, og), Fraction(k, oh)] = mi
    return spec


def B2(x):
    return x * x - x + Fraction(1, 6)


def Z(spec, tau, nmax=None):
    """prod over eigenlines (s, r): q^(-B_2(r)/4) prod_{n>=0, n+r>0} (1 - e(s) q^(n+r))^(-1)."""
    if nmax is None:
        nmax = int(40 / (2 * math.pi * tau.imag)) + 5
    logz = 0
    for (s, r), m in spec.items():
        lam = cmath.exp(2j * math.pi * float(s))
        t = -float(B2(r)) / 4 * 2j * math.pi * tau
        for k in range(nmax):
            e = k + float(r)
            if e == 0:
                continue
            t -= cmath.log(1 - lam * cmath.exp(2j * math.pi * tau * e))
        logz += m * t
    return cmath.exp(logz)


def is_constant(vals, tol=1e-8):
    v0 = vals[0]
    return all(abs(v - v0) <= tol * abs(v0) for v in vals)


T_EXAMPLES = [
    ("Lie_4: (12)(34), (13)(24)", (frozenset(), 4), [[0, 1], [2, 3]], [[0, 2], [1, 3]]),
    ("Lie_4: (1234), (13)(24)", (frozenset(), 4), [[0, 1, 2, 3]], [[0, 2], [1, 3]]),
    ("Lie_5: (12345), (12345)^2", (frozenset(), 5), [[0, 1, 2, 3, 4]], [[0, 2, 4, 1, 3]]),
    ("Lie_6: (123)(456), (14)(25)(36)", (frozenset(), 6), [[0, 1, 2], [3, 4, 5]],
     [[0, 3], [1, 4], [2, 5]]),
    ("Lie_6: (12)(34)(56), (135)(246)", (frozenset(), 6), [[0, 1], [2, 3], [4, 5]],
     [[0, 2, 4], [1, 3, 5]]),
    ("2+2: swap, swap", (frozenset({(0, 1), (2, 3)}), 4), [[0, 2], [1, 3]], [[0, 2], [1, 3]]),
    ("bowtie: (12), (34)", (frozenset({(0, 2), (0, 3), (1, 2), (1, 3)}), 4), [[0, 1]], [[2, 3]]),
]


def run_T():
    taus = [complex(0.11, 0.93), complex(-0.23, 1.17), complex(0.31, 1.05)]
    for name, (rel, n), gc, hc in T_EXAMPLES:
        rel = transitive_closure(rel, n)
        g, h = from_cycles(n, gc), from_cycles(n, hc)
        spec = joint_spectrum(rel, n, g, h)
        dim = sum(spec.values())
        d0 = spec.get((Fraction(0), Fraction(0)), 0)
        hinv = ppow(h, porder(h) - 1)
        spec_S = joint_spectrum(rel, n, hinv, g)
        spec_T = joint_spectrum(rel, n, compose(g, h), h)
        # the joint spectrum is closed under (s, r) -> (-s, -r)
        closed = all(spec.get(((-s) % 1, (-r) % 1)) == m for (s, r), m in spec.items())
        # S: Z_{g,h}(-1/tau) = c (-i tau)^(-d0/2) Z_{h^-1, g}(tau)
        S_rat = [Z(spec, -1 / t) / ((-1j * t) ** (-d0 / 2) * Z(spec_S, t)) for t in taus]
        T_rat = [Z(spec, t + 1) / Z(spec_T, t) for t in taus]
        # Gamma(N): gamma = [[1+N, N], [-N, 1-N]], at points where both tau
        # and gamma tau have Im ~ 0.3
        N = math.lcm(porder(g), porder(h))
        a, b, c, d = 1 + N, N, -N, 1 - N
        pts = [complex(-d / c + e, 1 / (abs(c) * 1.8)) for e in (0.0, 0.01, -0.013)]
        G_rat = [Z(spec, (a * t + b) / (c * t + d)) / ((c * t + d) ** (-d0 / 2) * Z(spec, t))
                 for t in pts]
        ok = (closed and is_constant(S_rat) and is_constant(T_rat) and is_constant(G_rat, 1e-6)
              and abs(abs(G_rat[0]) - 1) < 1e-6 and abs(abs(T_rat[0]) - 1) < 1e-9)
        lines = len(spec)
        check("T", ok, f"{name}: dim {dim}, {lines} joint eigenlines, weight {-d0 / 2}; "
                       f"S-, T- and Gamma({N})-laws hold, |T-mult| = |Gamma(N)-mult| = 1, "
                       f"S-constant {abs(S_rat[0]):.4f}")
        print("      joint eigenlines (s, r): mult  "
              + ", ".join(f"({s}, {r}): {k}" for (s, r), k in sorted(spec.items())))
        # negative control: the partner (h, g) instead of (h^-1, g), where it differs
        spec_bad = joint_spectrum(rel, n, h, g)
        if spec_bad != spec_S:
            bad = [Z(spec, -1 / t) / ((-1j * t) ** (-d0 / 2) * Z(spec_bad, t)) for t in taus]
            check("T", not is_constant(bad), "      negative control: S-partner (h, g) fails")
    # negative control: a single eigenline without its conjugate is not modular
    lone = {(Fraction(1, 3), Fraction(1, 4)): 1}
    lone_S = {(Fraction(3, 4), Fraction(1, 3)): 1}
    bad = [Z(lone, -1 / t) / Z(lone_S, t) for t in taus]
    check("T", not is_constant(bad), "negative control: one eigenline (1/3, 1/4) without "
                                     "its conjugate fails the S-law")
    # Siegel identification: a conjugate pair (s, r), (-s, -r) with 0 < r < 1
    # equals -e(s(r-1)/2) / g_(r,s), g_a the Siegel function (Kubert-Lang)
    s, r = Fraction(1, 3), Fraction(1, 4)
    pair = {(s, r): 1, ((-s) % 1, (-r) % 1): 1}
    ok = True
    for t in taus:
        q = cmath.exp(2j * math.pi * t)
        qz = cmath.exp(2j * math.pi * (float(r) * t + float(s)))
        gs = -cmath.exp(2j * math.pi * t * float(B2(r)) / 2) \
            * cmath.exp(1j * math.pi * float(s) * (float(r) - 1)) * (1 - qz)
        for k in range(1, 200):
            gs *= (1 - q ** k * qz) * (1 - q ** k / qz)
        pred = -cmath.exp(1j * math.pi * float(s) * (float(r) - 1)) / gs
        ok &= abs(Z(pair, t) - pred) < 1e-10 * abs(pred)
    check("T", ok, "a conjugate pair of eigenlines is -e(s(r-1)/2)/g_(r,s) (Siegel function)")


SECTIONS = {"U": run_U, "E": run_E, "S": run_S, "B": run_B, "G": run_G, "T": run_T}


def main(argv):
    picked = [a[2:] for a in argv if a.startswith("--")]
    for key, fn in SECTIONS.items():
        if not picked or key in picked:
            print(f"== [{key}] ==")
            fn()
    bad = [t for t, ok in CHECKS if not ok]
    print(f"{len(CHECKS) - len(bad)}/{len(CHECKS)} checks passed")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
