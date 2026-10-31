"""Independent audit of Proposition E of notes/prior_art_cyclic_sieving_cyc_2.md.

Self-contained: plain Python 3, imports nothing from the other scripts of
compute/ (and nothing from the author's uncommitted check script).

Proposition E (as stated in the note).  G <= GL(V) a finite complex
reflection group with degrees d_1..d_n, chi a class function,
  f_chi(q) = prod_i (1 - q^{d_i}) |G|^{-1} sum_g chi(g) / det(1 - q g),
zeta a primitive e-th root of unity, A = {i : e | d_i}, a = |A|,
M = {g : dim V(g, zeta^{-1}) = a}.  Then
  f_chi(zeta) = |G|^{-1} prod_{i in A} d_i prod_{i not in A} (1 - zeta^{d_i})
                * sum_{g in M} chi(g) prod_{lambda != zeta^{-1}} (1 - zeta lambda)^{-1}.

How the left-hand side is computed here (independently of the proof).
f_chi is a polynomial for a class function chi.  We evaluate the defining
sum at K points q_j = R exp(2 pi i j / K) of the circle |q| = R < 1, where
det(1 - q g) has no zero, recover the coefficients by an inverse DFT, check
that the recovered polynomial reproduces the defining sum at an unrelated
point (so the degree bound is honest), and evaluate it at zeta.  The
determinant det(1 - q g) is computed from the matrix of g by Gaussian
elimination, not from eigenvalues.  For S_k the polynomial is also computed
exactly over Q by polynomial division.

The right-hand side uses eigenvalues as exact angles in Q/Z, computed from
the cycle structure of a monomial matrix; those angles are themselves
checked against the matrices (char. polynomial) on every element.

Checks (bracketed tags are line labels in the output)
  [eig]     eigen-angles of every element agree with det(1 - q g) from the matrix
  [sp34]    max_g dim V(g, zeta) = a(e) for every e <= max d_i + 2, for zeta
            and zeta^{-1}, regular or not (Springer 3.4(i)); regularity of e
            reported by brute force (eigenvector off every reflecting hyperplane)
  [propE]   Proposition E on G(m,p,n), random complex class functions
  [typeA]   the displayed S_k formula vs exact f_F(zeta), k = 2..8, every e in
            2..k+2 (including e > k, a = 0)
  [thmB]    Theorem B (i)/(ii) for W = S_k1 x S_k2 x ... with random F
            supported as Lemma 1 allows; and the a(e) = 0 prefactor remark
  [ctl]     positive controls: wrong variants that must FAIL
"""

import cmath
import itertools
import math
import random
import sys
from fractions import Fraction

FAIL = []
TOL = 1e-7


def log(s):
    print(s)


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
    return cond


def root(x):
    """exp(2 pi i x) for x in Q (Fraction or int)."""
    return cmath.exp(2j * math.pi * float(x))


# ---------------------------------------------------------------- groups

class Elt:
    """Monomial matrix g e_i = w^{c_i} e_{perm[i]}, w = exp(2 pi i / m)."""

    def __init__(self, perm, col, m):
        self.perm, self.col, self.m = tuple(perm), tuple(col), m

    def key(self):
        return (self.perm, self.col)

    def mul(self, other):
        # (self o other) e_i = self(w^{c'_i} e_{p'(i)}) = w^{c'_i + c_{p'(i)}} e_{p(p'(i))}
        n = len(self.perm)
        perm = [self.perm[other.perm[i]] for i in range(n)]
        col = [(other.col[i] + self.col[other.perm[i]]) % self.m for i in range(n)]
        return Elt(perm, col, self.m)

    def inv(self):
        n = len(self.perm)
        perm = [0] * n
        col = [0] * n
        for i in range(n):
            perm[self.perm[i]] = i
            col[self.perm[i]] = (-self.col[i]) % self.m
        return Elt(perm, col, self.m)

    def matrix(self):
        n = len(self.perm)
        A = [[0j] * n for _ in range(n)]
        for i in range(n):
            A[self.perm[i]][i] = root(Fraction(self.col[i], self.m))
        return A

    def angles(self):
        """Eigenvalues as angles in [0,1): a cycle of length l with colour sum s
        has eigenvalues the l-th roots of w^s."""
        n = len(self.perm)
        seen = [False] * n
        out = []
        for i in range(n):
            if seen[i]:
                continue
            j, l, s = i, 0, 0
            while not seen[j]:
                seen[j] = True
                s += self.col[j]
                j = self.perm[j]
                l += 1
            for t in range(l):
                out.append((Fraction(s, self.m) + t) / l % 1)
        return out


def G_mpn(m, p, n):
    """G(m,p,n): monomial n x n, entries m-th roots of unity, product of the
    entries an (m/p)-th root of unity.  Degrees m, 2m, ..., (n-1)m, nm/p."""
    els = []
    for perm in itertools.permutations(range(n)):
        for col in itertools.product(range(m), repeat=n):
            if sum(col) % p == 0:
                els.append(Elt(perm, col, m))
    degs = [m * i for i in range(1, n)] + [n * m // p]
    return els, degs


def det(A):
    n = len(A)
    A = [row[:] for row in A]
    d = 1 + 0j
    for c in range(n):
        piv = max(range(c, n), key=lambda r: abs(A[r][c]))
        if abs(A[piv][c]) < 1e-300:
            return 0j
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for k in range(c, n):
                A[r][k] -= f * A[c][k]
    return d


def det_one_minus_q(Amat, q):
    n = len(Amat)
    return det([[(1 if i == j else 0) - q * Amat[i][j] for j in range(n)] for i in range(n)])


def conj_classes(els):
    idx = {g.key(): i for i, g in enumerate(els)}
    cls = [-1] * len(els)
    c = 0
    for i, g in enumerate(els):
        if cls[i] >= 0:
            continue
        for h in els:
            x = h.mul(g).mul(h.inv())
            cls[idx[x.key()]] = c
        c += 1
    return cls, c


# ------------------------------------------------------- the two sides

def f_at_zeta_numeric(els, mats, degs, chi, e, R=0.6, K=None):
    """Left-hand side: f_chi as a polynomial via inverse DFT on |q| = R."""
    deg_bound = sum(degs)
    if K is None:
        K = deg_bound + 8
    order = len(els)

    def f(q):
        num = 1
        for d in degs:
            num *= 1 - q ** d
        s = sum(chi[i] / det_one_minus_q(mats[i], q) for i in range(order))
        return num * s / order

    vals = [f(R * root(Fraction(j, K))) for j in range(K)]
    coef = []
    for t in range(K):
        c = sum(vals[j] * root(Fraction(-j * t, K)) for j in range(K)) / K
        coef.append(c / R ** t)
    # honesty check of the degree bound: the tail must vanish and the
    # polynomial must reproduce f at an unrelated point
    tail = max(abs(c) for c in coef[deg_bound + 1:]) if K > deg_bound + 1 else 0
    q0 = 0.31 + 0.17j
    ok = tail < 1e-6 and abs(sum(c * q0 ** t for t, c in enumerate(coef)) - f(q0)) < 1e-6
    z = root(Fraction(1, e))
    return sum(c * z ** t for t, c in enumerate(coef)), ok


def rhs_propE(els, degs, chi, e, flip=False, drop_dA=False):
    """Right-hand side of Proposition E at zeta = exp(2 pi i / e).
    flip=True: the wrong orientation (the whole formula taken at zeta^{-1},
    i.e. M defined by the eigenvalue zeta).  drop_dA=True: omit prod_{i in A} d_i."""
    order = len(els)
    z = Fraction(-1 if flip else 1, e) % 1    # flip: evaluate the formula at zeta^{-1}
    target = (-z) % 1                         # angle of the eigenvalue counted in M
    A = [d for d in degs if d % e == 0]
    a = len(A)
    pref = 1 + 0j
    if not drop_dA:
        for d in A:
            pref *= d
    for d in degs:
        if d % e:
            pref *= 1 - root(z * d)
    s = 0j
    for i, g in enumerate(els):
        ang = g.angles()
        if sum(1 for x in ang if x == target) != a:
            continue
        prod = 1 + 0j
        for x in ang:
            if x == target:
                continue
            prod *= 1 - root(z + x)
        s += chi[i] / prod
    return pref * s / order


# ------------------------------------------------------------- checks

def eig_check(els, mats):
    bad = 0
    for g, A in zip(els, mats):
        for q in (0.37 - 0.21j, -0.5 + 0.4j):
            lhs = det_one_minus_q(A, q)
            rhs = 1
            for x in g.angles():
                rhs *= 1 - q * root(x)
            if abs(lhs - rhs) > 1e-9:
                bad += 1
    return bad


def is_regular(els, mats, e, n):
    """Brute force: some g has a zeta-eigenvector fixed by no reflection."""
    refl = [A for g, A in zip(els, mats) if sum(1 for x in g.angles() if x == 0) == n - 1]
    zeta = root(Fraction(1, e))
    rng = random.Random(7)
    for g, A in zip(els, mats):
        if Fraction(1, e) % 1 not in g.angles():
            continue
        # zeta-eigenvectors of a monomial matrix: solve (A - zeta) v = 0 by
        # Gaussian elimination and take a random combination of a null basis
        basis = null_space([[A[i][j] - (zeta if i == j else 0) for j in range(n)] for i in range(n)])
        v = [0j] * n
        for b in basis:
            c = complex(rng.random(), rng.random())
            v = [vi + c * bi for vi, bi in zip(v, b)]
        if all(max(abs(sum(r[i][j] * v[j] for j in range(n)) - v[i]) for i in range(n)) > 1e-8
               for r in refl):
            return True
    return False


def null_space(B):
    n = len(B)
    B = [row[:] for row in B]
    pivcols = []
    r = 0
    for c in range(n):
        piv = max(range(r, n), key=lambda i: abs(B[i][c])) if r < n else None
        if piv is None or abs(B[piv][c]) < 1e-9:
            continue
        B[r], B[piv] = B[piv], B[r]
        pv = B[r][c]
        B[r] = [x / pv for x in B[r]]
        for i in range(n):
            if i != r and abs(B[i][c]) > 0:
                f = B[i][c]
                B[i] = [x - f * y for x, y in zip(B[i], B[r])]
        pivcols.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivcols]
    basis = []
    for fc in free:
        v = [0j] * n
        v[fc] = 1
        for row, pc in zip(B, pivcols):
            v[pc] = -row[fc]
        basis.append(v)
    return basis


GROUPS = [(3, 1, 2), (4, 2, 2), (4, 1, 2), (6, 2, 2), (6, 3, 2), (5, 1, 2),
          (2, 1, 3), (3, 3, 3), (2, 2, 4), (3, 1, 3), (4, 4, 3),
          (4, 2, 3), (2, 1, 4), (2, 2, 5)]


def run_general(seed=1):
    rng = random.Random(seed)
    n_ok = n_tot = n_nonreg = n_nonreg_a = 0
    ctl_flip = ctl_dA = ctl_n = 0
    for (m, p, n) in GROUPS:
        els, degs = G_mpn(m, p, n)
        mats = [g.matrix() for g in els]
        bad = eig_check(els, mats)
        check(bad == 0, f"eig G({m},{p},{n})")
        log(f"[eig]   G({m},{p},{n}) |G|={len(els)} degrees={degs}: {len(els) - bad}/{len(els)} elements agree")
        cls, nc = conj_classes(els)
        sp_ok = True
        regs = []
        for e in range(1, max(degs) + 3):
            a = sum(1 for d in degs if d % e == 0)
            for t in (Fraction(1, e), Fraction(-1, e) % 1):
                mx = max(sum(1 for x in g.angles() if x == t % 1) for g in els)
                sp_ok &= check(mx == a, f"sp34 G({m},{p},{n}) e={e}")
            regs.append((e, is_regular(els, mats, e, n)))
        nonreg = [e for e, r in regs if not r]
        log(f"[sp34]  G({m},{p},{n}): max dim V(g,zeta^(+-1)) = a(e) for all e <= {max(degs) + 2}: "
            f"{'yes' if sp_ok else 'NO'}; non-regular e: {nonreg}")
        for e in range(2, max(degs) + 3):
            vals = [complex(rng.randint(-5, 5), rng.randint(-5, 5)) for _ in range(nc)]
            chi = [vals[cls[i]] for i in range(len(els))]
            lhs, okpoly = f_at_zeta_numeric(els, mats, degs, chi, e)
            check(okpoly, f"poly-recovery G({m},{p},{n}) e={e}")
            rhs = rhs_propE(els, degs, chi, e)
            good = abs(lhs - rhs) < TOL * (1 + abs(lhs))
            n_tot += 1
            n_ok += good
            n_nonreg += (e in nonreg)
            n_nonreg_a += (e in nonreg) and any(d % e == 0 for d in degs)
            check(good, f"propE G({m},{p},{n}) e={e}: {lhs} vs {rhs}")
            # controls: only counted where the variant differs in principle
            a = sum(1 for d in degs if d % e == 0)
            if a >= 1 and e >= 3:   # e = 2: zeta = zeta^{-1}, the flip is the identity
                ctl_n += 1
                r1 = rhs_propE(els, degs, chi, e, flip=True)
                r2 = rhs_propE(els, degs, chi, e, drop_dA=True)
                ctl_flip += abs(lhs - r1) > TOL * (1 + abs(lhs))
                ctl_dA += abs(lhs - r2) > TOL * (1 + abs(lhs))
    log(f"[propE] Proposition E: {n_ok}/{n_tot} (group, e) cases agree "
        f"({n_nonreg} at a non-regular e, {n_nonreg_a} of these with a(e) >= 1)")
    log(f"[ctl]   flipped orientation (zeta for zeta^-1): fails in {ctl_flip}/{ctl_n} cases with a >= 1, e >= 3")
    log(f"[ctl]   prod_(i in A) d_i omitted: fails in {ctl_dA}/{ctl_n} cases with a >= 1, e >= 3")
    check(n_ok == n_tot, "propE total")
    check(ctl_flip > 0 and ctl_dA == ctl_n, "controls (general) did not fire")
    return n_ok, n_tot, ctl_flip, ctl_dA, ctl_n


# ---------------------------------------------------------------- type A

def partitions(k, mx=None):
    if mx is None:
        mx = k
    if k == 0:
        yield ()
        return
    for p in range(min(k, mx), 0, -1):
        for rest in partitions(k - p, p):
            yield (p,) + rest


def z_lambda(lam):
    z = 1
    for p in set(lam):
        c = lam.count(p)
        z *= p ** c * math.factorial(c)
    return z


def pmul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def pdiv_exact(a, b):
    """a / b over Q, asserting zero remainder."""
    a = a[:]
    out = [Fraction(0)] * (len(a) - len(b) + 1)
    for i in range(len(out) - 1, -1, -1):
        c = a[i + len(b) - 1] / b[-1]
        out[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    assert all(x == 0 for x in a), "non-polynomial quotient"
    return out


def one_minus_qp(p):
    return [Fraction(1)] + [Fraction(0)] * (p - 1) + [Fraction(-1)]


def fake_poly_W(ks, F):
    """Exact X(q) = prod_i (q;q)_{k_i} (1/|W|) sum_w F(w)/det(1 - q w), W = prod S_{k_i},
    F a function of the tuple of cycle types."""
    num = [Fraction(1)]
    for k in ks:
        for j in range(1, k + 1):
            num = pmul(num, one_minus_qp(j))
    tot = [Fraction(0)] * len(num)
    for lams in itertools.product(*[list(partitions(k)) for k in ks]):
        val = F.get(lams, 0)
        if not val:
            continue
        den = [Fraction(1)]
        zz = 1
        for lam in lams:
            zz *= z_lambda(lam)
            for p in lam:
                den = pmul(den, one_minus_qp(p))
        T = pdiv_exact(num, den)
        for i, c in enumerate(T):
            tot[i] += Fraction(val, zz) * c
    return tot


def peval(poly, z):
    return sum(complex(c) * z ** i for i, c in enumerate(poly))


def typeA_formula(k, e, F, z, drop=False):
    """The note's displayed formula for W = S_k (F on partitions of k)."""
    a = k // e
    pre = 1 if drop else e ** a * math.factorial(a)
    for j in range(1, k + 1):
        if j % e:
            pre *= 1 - z ** j
    s = 0j
    for lam, val in F.items():
        if sum(1 for p in lam if p % e == 0) != a:
            continue
        den = 1 + 0j
        for p in lam:
            den *= p if p % e == 0 else (1 - z ** p)
        s += val / z_lambda(lam) / den
    return pre * s


def run_typeA(seed=2):
    rng = random.Random(seed)
    ok = tot = ctl = ctl2 = 0
    for k in range(2, 9):
        parts = list(partitions(k))
        for e in range(2, k + 3):
            F = {lam: rng.randint(-9, 9) for lam in parts}
            X = fake_poly_W([k], {(lam,): v for lam, v in F.items()})
            for r in range(1, e):
                if math.gcd(r, e) != 1:
                    continue
                z = root(Fraction(r, e))
                lhs = peval(X, z)
                rhs = typeA_formula(k, e, F, z)
                good = abs(lhs - rhs) < TOL * (1 + abs(lhs))
                tot += 1
                ok += good
                check(good, f"typeA k={k} e={e} r={r}")
                if k // e >= 1:
                    bad = typeA_formula(k, e, F, z, drop=True)
                    ctl2 += 1
                    ctl += abs(lhs - bad) > TOL * (1 + abs(lhs))
    log(f"[typeA] displayed S_k formula vs exact f_F(zeta), k=2..8, e=2..k+2, every primitive zeta: {ok}/{tot}")
    log(f"[ctl]   S_k formula without e^a a!: fails in {ctl}/{ctl2} cases with a >= 1")
    check(ok == tot, "typeA total")
    check(ctl == ctl2, "typeA control did not fire")


def run_thmB(seed=3):
    """Theorem B for W = prod S_{k_i}, F random on the support allowed by Lemma 1."""
    rng = random.Random(seed)
    cases = [(2,), (3,), (4,), (5,), (6,), (2, 2), (2, 4), (3, 3), (2, 3), (4, 6), (3, 6), (2, 2, 4), (6,), (5, 2)]
    nB = okB = 0
    nzero = 0
    pref_ok = 0
    pref_n = 0
    pref_diff = 0
    zero_cases = []
    for ks in cases:
        g = 0
        for k in ks:
            g = math.gcd(g, k)
        F = {}
        for d in range(1, g + 1):
            if g % d == 0:
                F[tuple(tuple([d] * (k // d)) for k in ks)] = rng.randint(1, 9)
        X = fake_poly_W(list(ks), F)
        for e in range(2, max(ks) + 3):
            z = root(Fraction(1, e))
            val = peval(X, z)
            if all(k % e == 0 for k in ks):
                want = F[tuple(tuple([e] * (k // e)) for k in ks)]
                good = abs(val - want) < TOL
                tag = "i"
            elif e <= max(ks):
                want = 0
                good = abs(val) < TOL
                tag = "ii"
            else:
                # a(e) = 0: the note's displayed expression
                # (1/|W|) sum_w F(w) prod (1 - zeta lambda)^{-1}, with and without
                # the prefactor prod_i prod_{j<=k_i} (1 - zeta^j)
                tag = "a0"
                good = True
                s = 0j
                for lams, v in F.items():
                    zz = 1
                    den = 1 + 0j
                    for lam in lams:
                        zz *= z_lambda(lam)
                        for p in lam:
                            den *= 1 - z ** p
                    s += v / zz / den
                pre = 1 + 0j
                for k in ks:
                    for j in range(1, k + 1):
                        pre *= 1 - z ** j
                pref_n += 1
                pref_ok += abs(val - pre * s) < TOL
                pref_diff += abs(val - s) > TOL
                if abs(val) < TOL:
                    nzero += 1
                    zero_cases.append((ks, e))
                continue
            nB += 1
            okB += good
            check(good, f"thmB({tag}) ks={ks} e={e}: {val} vs {want}")
    log(f"[thmB]  Theorem B (i)/(ii) with F on the Lemma-1 support: {okB}/{nB}")
    log(f"[thmB]  a(e) = 0 (e > max k_i): X(zeta) = prod(1-zeta^d_i) (1/|W|) sum F/det(1-zeta w) in "
        f"{pref_ok}/{pref_n}; the note's sum without the prefactor differs from X(zeta) in {pref_diff}/{pref_n}")
    log(f"[thmB]  a(e) = 0 with a random positive F on the Lemma-1 support: X(zeta) = 0 in "
        f"{nzero}/{pref_n} {zero_cases} (support alone does not decide clause (a))")
    check(okB == nB, "thmB total")
    check(pref_ok == pref_n, "a0 prefactor")
    check(pref_diff > 0, "a0 control: prefactor-free sum never differed")


def main():
    run_general()
    run_typeA()
    run_thmB()
    if FAIL:
        log(f"FAILURES ({len(FAIL)}):")
        for f in FAIL[:30]:
            log("  " + f)
        sys.exit(1)
    log("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
