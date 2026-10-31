"""Independent audit of notes/linear_extensions.md.

Self-contained: imports nothing from the other scripts of compute/.

Promotion is implemented twice:
  promote_jdt   Schuetzenberger's sliding definition, as restated verbatim in
                Stanley, "Promotion and evacuation", Sec. 2 (arXiv:0806.4717):
                remove label 1, slide the smallest label among the upper
                covers down, repeat until a maximal element, label it p+1,
                subtract 1 from every label.
  promote_tog   the toggle product tau_{n-1} ... tau_1 used by the note.
Every check below uses promote_jdt; the two are compared in [jdt].

Checks
  [gen]      unlabelled posets n <= 7 (1, 2, 5, 16, 63, 318, 2045)
  [jdt]      promote_jdt == promote_tog on every poset n <= 7
  [P]        Lemma P, every disconnected poset n <= 7, every w, every split
             A | B into unions of components
  [P1] [P2]  Corollaries P1 (all d <= n) and P2 (all cuts)
  [R]        Theorem R and the necessity of its hypothesis
  [O]        Proposition O on every poset n <= 7, every base component
  [E]        Proposition E on every poset n <= 7
  [D]        Proposition D: K_P computed as a kernel, partial(K_P) tested
             numerically, every poset n <= 7
  [F]        Proposition F and the cumulant formula, every poset n <= 7
  [RSW]      fixed patterns of rot_d on Pat(m) vs the q-multinomial at
             omega^d ([RSW] Prop. 4.4 / eq. (4.5)), all m with n <= 8
  [U]        Theorem U on every disconnected poset n <= 7 whose components
             carry a maj-CSP; fixed-point product formula on all 503
  [sweep]    maj-CSP sweep of every poset with partial^n = id, n <= 7
  [rh]       Rhoades rectangles, q-hook formula, negative control
  [stair]    promotion orders on staircases
  [M]        Theorem M: R_P built from its generators (rank mod p),
             homogeneity, every graded piece, B_P per piece, n <= 6
  [homog]    homogeneity of R_P for des / maj / blocks / jumps / first
             letter / random colouring; des and maj over EVERY natural
             labelling for n <= 5
  [descR]    partial(R_P) <= R_P

Usage:  python3 audit_linear_extensions.py [--quick]
  --quick  stops at n <= 5 (a few seconds); the full run takes minutes.
"""

import cmath
import itertools
import math
import random
import sys
from collections import Counter, defaultdict

PRIME = 2147483647

# ---------------------------------------------------------------------------
# posets


class Poset:
    """Poset on 0..n-1; up[a] = bitmask of b with a < b (transitive)."""

    def __init__(self, n, up):
        self.n = n
        self.up = list(up)
        self.down = [0] * n
        for a in range(n):
            for b in range(n):
                if up[a] >> b & 1:
                    self.down[b] |= 1 << a
        self._comp = None

    @classmethod
    def from_relations(cls, n, rels):
        up = [0] * n
        for a, b in rels:
            up[a] |= 1 << b
        changed = True
        while changed:
            changed = False
            for a in range(n):
                new = up[a]
                for b in range(n):
                    if up[a] >> b & 1:
                        new |= up[b]
                if new != up[a]:
                    up[a] = new
                    changed = True
        for a in range(n):
            assert not up[a] >> a & 1, "relations are not acyclic"
        return cls(n, up)

    def lt(self, a, b):
        return self.up[a] >> b & 1 == 1

    def comparable(self, a, b):
        return self.lt(a, b) or self.lt(b, a)

    def components(self):
        if self._comp is None:
            comp = [-1] * self.n
            k = 0
            for s in range(self.n):
                if comp[s] >= 0:
                    continue
                stack = [s]
                comp[s] = k
                while stack:
                    x = stack.pop()
                    for y in range(self.n):
                        if comp[y] < 0 and self.comparable(x, y):
                            comp[y] = k
                            stack.append(y)
                k += 1
            self._comp = comp
        return self._comp

    def comp_sets(self):
        comp = self.components()
        k = max(comp) + 1 if comp else 0
        return [[x for x in range(self.n) if comp[x] == i] for i in range(k)]

    def relations(self):
        return [(a, b) for a in range(self.n) for b in range(self.n) if self.lt(a, b)]


def lin_ext(P, letters=None):
    """All linear extensions of P restricted to `letters`, as tuples."""
    if letters is None:
        letters = list(range(P.n))
    letters = list(letters)
    mask = 0
    for x in letters:
        mask |= 1 << x
    out = []

    def rec(rem, word):
        if not rem:
            out.append(tuple(word))
            return
        for x in letters:
            if rem >> x & 1 and not (P.down[x] & rem & mask):
                word.append(x)
                rec(rem & ~(1 << x), word)
                word.pop()

    rec(mask, [])
    return out


def ideals(P):
    out = []
    for S in range(1 << P.n):
        if all(not (S >> x & 1) or (P.down[x] & ~S) == 0 for x in range(P.n)):
            out.append(S)
    return out


def canon(P):
    n = P.n
    inv0 = [(bin(P.down[x]).count("1"), bin(P.up[x]).count("1")) for x in range(n)]
    inv = [
        (inv0[x],
         tuple(sorted(inv0[y] for y in range(n) if P.lt(y, x))),
         tuple(sorted(inv0[y] for y in range(n) if P.lt(x, y))))
        for x in range(n)
    ]
    groups = defaultdict(list)
    for x in range(n):
        groups[inv[x]].append(x)
    keys = sorted(groups)
    best = None
    for perms in itertools.product(*(itertools.permutations(groups[k]) for k in keys)):
        order = [x for p in perms for x in p]  # new position -> old element
        pos = {x: i for i, x in enumerate(order)}
        code = tuple(sorted((pos[a], pos[b]) for a, b in P.relations()))
        if best is None or code < best:
            best = code
    return best


def all_posets(nmax):
    """Unlabelled posets by size: dict n -> list of Poset (canonical labels)."""
    res = {1: [Poset(1, [0])]}
    for n in range(2, nmax + 1):
        seen = {}
        for Q in res[n - 1]:
            for S in ideals(Q):
                up = list(Q.up) + [0]
                for x in range(n - 1):
                    if S >> x & 1:
                        up[x] |= 1 << (n - 1)
                P = Poset(n, up)
                c = canon(P)
                if c not in seen:
                    seen[c] = Poset.from_relations(n, c)
        res[n] = list(seen.values())
    return res


# ---------------------------------------------------------------------------
# promotion


def promote_jdt(P, w):
    """Schuetzenberger promotion of the linear extension w of P|_{set(w)}.

    The labelling is f(w_i) = i (1-based); the result is the word of f.partial.
    Covers are those of the induced subposet on set(w)."""
    L = set(w)
    f = {x: i + 1 for i, x in enumerate(w)}
    t = w[0]
    chain = [t]
    while True:
        above = [c for c in L if P.lt(t, c)]
        covers = [c for c in above if not any(P.lt(t, u) and P.lt(u, c) for u in L)]
        if not covers:
            break
        t = min(covers, key=lambda c: f[c])
        chain.append(t)
    g = dict(f)
    del g[chain[0]]
    for i in range(len(chain) - 1):
        g[chain[i]] = f[chain[i + 1]]
    g[chain[-1]] = len(w) + 1
    g = {x: v - 1 for x, v in g.items()}
    return tuple(sorted(L, key=lambda x: g[x]))


def promote_tog(P, w):
    w = list(w)
    for i in range(len(w) - 1):
        if not P.comparable(w[i], w[i + 1]):
            w[i], w[i + 1] = w[i + 1], w[i]
    return tuple(w)


promote = promote_jdt


def promote_power(P, w, d):
    for _ in range(d):
        w = promote(P, w)
    return w


def orbits(P, lin):
    seen = set()
    out = []
    for w in lin:
        if w in seen:
            continue
        orb = [w]
        seen.add(w)
        x = promote(P, w)
        while x != w:
            orb.append(x)
            seen.add(x)
            x = promote(P, x)
        out.append(orb)
    return out


def promotion_order(P, lin):
    o = 1
    for orb in orbits(P, lin):
        o = o * len(orb) // math.gcd(o, len(orb))
    return o


# ---------------------------------------------------------------------------
# cuts, classes, patterns


def rot(w, k):
    return tuple(w[k:]) + tuple(w[:k])


def is_union(P, letters):
    comp = P.components()
    S = set(letters)
    return all((comp[x] == comp[y]) <= (y in S) for x in S for y in range(P.n) if comp[x] == comp[y])


def cuts(P, w):
    comp = P.components()
    size = Counter(comp)
    cnt = Counter()
    out = [0]
    for k in range(1, len(w)):
        cnt[comp[w[k - 1]]] += 1
        if all(cnt[c] in (0, size[c]) for c in size):
            out.append(k)
    return out


def class_key(w):
    return min(rot(w, k) for k in range(len(w)))


def classes(P, lin):
    cl = defaultdict(list)
    for w in lin:
        cl[class_key(w)].append(w)
    return list(cl.values())


def pattern(P, w):
    comp = P.components()
    return tuple(comp[x] for x in w)


def restrictions(P, w):
    return tuple(tuple(x for x in w if x in set(T)) for T in P.comp_sets())


def disjoint_union(*Ps):
    up = []
    off = 0
    for Q in Ps:
        up += [m << off for m in Q.up]
        off += Q.n
    return Poset(off, up)


def chain(m):
    return Poset.from_relations(m, [(i, i + 1) for i in range(m - 1)])


def antichain(n):
    return Poset(n, [0] * n)


def is_chain(P):
    return all(P.comparable(a, b) for a in range(P.n) for b in range(a + 1, P.n))


def is_antichain(P):
    return all(u == 0 for u in P.up)


# ---------------------------------------------------------------------------
# [jdt], [P], [P1], [P2]


def check_jdt(P, lin):
    return all(promote_jdt(P, w) == promote_tog(P, w) for w in lin)


def check_lemma_P(P, lin):
    """Lemma P for every split A | B into nonempty unions of components."""
    cs = P.comp_sets()
    k = len(cs)
    nchecks = 0
    for r in range(1, k):
        for idx in itertools.combinations(range(k), r):
            A = set(x for i in idx for x in cs[i])
            for w in lin:
                pw = promote(P, w)
                p = tuple(x in A for x in w)
                q = tuple(x in A for x in pw)
                if q != rot(p, 1):
                    return False, ("pattern", w)
                wA = tuple(x for x in w if x in A)
                wB = tuple(x for x in w if x not in A)
                pA = tuple(x for x in pw if x in A)
                pB = tuple(x for x in pw if x not in A)
                if w[0] in A:
                    ok = pA == promote(P, wA) and pB == wB
                else:
                    ok = pB == promote(P, wB) and pA == wA
                if not ok:
                    return False, ("restriction", w)
                nchecks += 1
    return True, nchecks


def check_P1(P, lin):
    cs = P.comp_sets()
    comp = P.components()
    n = P.n
    for w in lin:
        p = pattern(P, w)
        res = restrictions(P, w)
        x = w
        for d in range(1, n + 1):
            x = promote(P, x)
            a = Counter(p[:d])
            if pattern(P, x) != rot(p, d % n):
                return False
            for i, T in enumerate(cs):
                if restrictions(P, x)[i] != (promote_power(P, res[i], a[i]) if res[i] else ()):
                    return False
    return True


def check_P2(P, lin):
    for w in lin:
        for k in cuts(P, w):
            if k == 0:
                continue
            A = w[:k]
            lhs = promote_power(P, w, k)
            rhs = tuple(w[k:]) + promote_power(P, tuple(A), len(A))
            if lhs != rhs:
                return False
    return True


# ---------------------------------------------------------------------------
# [R], [O], [E]


def hypothesis_R(P):
    for T in P.comp_sets():
        for u in lin_ext(P, T):
            if promote_power(P, u, len(T)) != u:
                return False
    return True


def refinement(P, lin):
    orbit_of = {}
    for i, orb in enumerate(orbits(P, lin)):
        for w in orb:
            orbit_of[w] = i
    return all(len({orbit_of[w] for w in C}) == 1 for C in classes(P, lin))


def check_O(P, lin):
    orbs = orbits(P, lin)
    eC = len(classes(P, lin))
    if len(orbs) > eC:
        return False
    for T in P.comp_sets():
        Ts = set(T)
        if not all(any(w[0] in Ts for w in orb) for orb in orbs):
            return False
        # B_P with base component T has e_C elements
        if count_BP(P, lin, Ts) != eC:
            return False
    return True


def first_block(P, w):
    c = cuts(P, w)
    end = c[1] if len(c) > 1 else len(w)
    return set(w[:end])


def count_BP(P, lin, base):
    return sum(1 for w in lin if base <= first_block(P, w))


def orbits_equal_classes(P, lin):
    a = sorted(sorted(o) for o in orbits(P, lin))
    b = sorted(sorted(c) for c in classes(P, lin))
    return a == b


# ---------------------------------------------------------------------------
# [D]: K_P as a kernel, tested numerically


def e_zeta_image(vec, n):
    """vec: dict word -> complex coeff.  Returns the element sum c_w w e_zeta of
    C[S_n], with e_zeta = (1/n) sum_j zeta^{-j} gamma^j, as dict perm -> coeff."""
    z = cmath.exp(2j * math.pi / n)
    out = defaultdict(complex)
    for w, c in vec.items():
        for j in range(n):
            out[rot(w, j)] += c * z ** (-j) / n
    return out


def check_eigen(lin, n):
    """w gamma^k e_zeta = zeta^k w e_zeta (the fact Prop. D starts from)."""
    z = cmath.exp(2j * math.pi / n)
    for w in lin[:5]:
        for k in range(n):
            a = e_zeta_image({rot(w, k): 1}, n)
            b = e_zeta_image({w: z ** k}, n)
            if any(abs(a[x] - b[x]) > 1e-9 for x in set(a) | set(b)):
                return False
    return True


def kernel_basis(P, lin):
    """Kernel of C[Lin P] -> C[S_n], w -> w e_zeta, computed per coset by
    numerical linear algebra (the images of the words of one coset are
    vectors on that coset)."""
    n = P.n
    basis = []
    for C in classes(P, lin):
        # images of the words of C, as vectors indexed by the n rotations
        ref = C[0]
        imgs = []
        for w in C:
            im = e_zeta_image({w: 1}, n)
            imgs.append([im[rot(ref, j)] for j in range(n)])
        # they are all multiples of imgs[0]; kernel vectors w - lambda * ref
        v0 = imgs[0]
        piv = max(range(n), key=lambda j: abs(v0[j]))
        for w, v in zip(C[1:], imgs[1:]):
            lam = v[piv] / v0[piv]
            if any(abs(v[j] - lam * v0[j]) > 1e-9 for j in range(n)):
                raise AssertionError("images on a coset are not proportional")
            basis.append({w: 1, ref: -lam})
    return basis


def promotion_preserves_kernel(P, lin):
    n = P.n
    for v in kernel_basis(P, lin):
        pv = defaultdict(complex)
        for w, c in v.items():
            pv[promote(P, w)] += c
        im = e_zeta_image(pv, n)
        if any(abs(c) > 1e-8 for c in im.values()):
            return False
    return True


# ---------------------------------------------------------------------------
# [F]


def eC(P, lin=None):
    if lin is None:
        lin = lin_ext(P)
    return len({class_key(w) for w in lin})


def check_F(P, lin):
    cs = P.comp_sets()
    prod = 1
    for T in cs:
        prod *= len(lin_ext(P, T))
    chains = disjoint_union(*[chain(len(T)) for T in cs])
    return eC(P, lin) == prod * eC(chains)


def cumulant(P):
    cs = P.comp_sets()
    k = len(cs)
    eT = [len(lin_ext(P, T)) for T in cs]
    m = [len(T) for T in cs]
    total = 0
    for part in set_partitions(list(range(k))):
        term = (-1) ** (len(part) - 1) * math.factorial(len(part) - 1)
        for block in part:
            sz = sum(m[i] for i in block)
            mult = math.factorial(sz)
            for i in block:
                mult //= math.factorial(m[i])
            for i in block:
                mult *= eT[i]
            term *= mult
        total += term
    return total


def set_partitions(xs):
    if not xs:
        yield []
        return
    first, rest = xs[0], xs[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


# ---------------------------------------------------------------------------
# polynomials (lists of ints, index = exponent)


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def pdiv_exact(a, b):
    a = list(a)
    q = [0] * (len(a) - len(b) + 1)
    for i in range(len(q) - 1, -1, -1):
        c = a[i + len(b) - 1]
        assert c % b[-1] == 0
        c //= b[-1]
        q[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    assert all(x == 0 for x in a), "inexact division"
    return q


def qint(k):
    return [1] * k


def qfact(k):
    out = [1]
    for i in range(1, k + 1):
        out = pmul(out, qint(i))
    return out


def qmultinomial(m):
    num = qfact(sum(m))
    den = [1]
    for x in m:
        den = pmul(den, qfact(x))
    return pdiv_exact(num, den)


def peval(a, z):
    return sum(c * z ** i for i, c in enumerate(a))


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def natural_labelling(P):
    w = lin_ext(P)[0]
    return {x: i for i, x in enumerate(w)}


def maj(w, lab):
    return sum(i + 1 for i in range(len(w) - 1) if lab[w[i]] > lab[w[i + 1]])


def des(w, lab):
    return sum(1 for i in range(len(w) - 1) if lab[w[i]] > lab[w[i + 1]])


def shifted_maj_poly(P, lin, lab=None):
    if lab is None:
        lab = natural_labelling(P)
    ms = [maj(w, lab) for w in lin]
    lo = min(ms)
    out = [0] * (max(ms) - lo + 1)
    for x in ms:
        out[x - lo] += 1
    return out


def csp_holds(P, lin, X, n=None):
    """(Lin P, <promote>, X) with C_n, n = |P|: requires promote^n = id."""
    if n is None:
        n = P.n
    z = cmath.exp(2j * math.pi / n)
    if any(promote_power(P, w, n) != w for w in lin):
        return False
    x = list(lin)
    for d in range(n):
        fix = sum(1 for w, y in zip(lin, x) if w == y)
        val = peval(X, z ** d)
        if abs(val - fix) > 1e-6:
            return False
        x = [promote(P, y) for y in x]
    return True


# ---------------------------------------------------------------------------
# [RSW]


def compositions_all(n):
    for k in range(1, n + 1):
        for c in itertools.product(range(1, n + 1), repeat=k):
            if sum(c) == n:
                yield c


def check_rsw(nmax):
    count = 0
    for n in range(1, nmax + 1):
        z = cmath.exp(2j * math.pi / n)
        for m in compositions_all(n):
            if math.factorial(n) // math.prod(math.factorial(x) for x in m) > 50000:
                continue
            letters = [i for i, x in enumerate(m) for _ in range(x)]
            words = set(itertools.permutations(letters))
            X = qmultinomial(m)
            for d in range(n):
                fix = sum(1 for p in words if rot(p, d) == p)
                if abs(peval(X, z ** d) - fix) > 1e-6:
                    return False, (m, d)
            count += 1
    return True, count


# ---------------------------------------------------------------------------
# [U], [sweep]


def fixed_point_product(P, lin):
    """|Fix partial^d| = #{p : rot_d p = p} * prod_i |Fix partial_T^{d m_i/n}|."""
    n = P.n
    cs = P.comp_sets()
    m = [len(T) for T in cs]
    letters = [i for i, x in enumerate(m) for _ in range(x)]
    pats = set(itertools.permutations(letters))
    x = list(lin)
    for d in range(n):
        fix = sum(1 for w, y in zip(lin, x) if w == y)
        nfixp = sum(1 for p in pats if rot(p, d) == p)
        if nfixp:
            prod = 1
            for i, T in enumerate(cs):
                assert (d * m[i]) % n == 0
                e = d * m[i] // n
                prod *= sum(1 for u in lin_ext(P, T) if promote_power(P, u, e) == u)
            rhs = nfixp * prod
        else:
            rhs = 0
        if fix != rhs:
            return False
        x = [promote(P, y) for y in x]
    return True


def theorem_U(P, lin):
    """None if P does not qualify, else (CSP for X, X == shifted maj of P)."""
    cs = P.comp_sets()
    X = qmultinomial([len(T) for T in cs])
    for T in cs:
        Q = Poset.from_relations(len(T), [(T.index(a), T.index(b)) for a in T for b in T if P.lt(a, b)])
        ql = lin_ext(Q)
        XT = shifted_maj_poly(Q, ql)
        if not csp_holds(Q, ql, XT):
            return None
        X = pmul(X, XT)
    X = trim(X)
    return csp_holds(P, lin, X), X == trim(shifted_maj_poly(P, lin))


# ---------------------------------------------------------------------------
# [rh], [stair]


def shape_poset(cells):
    idx = {c: i for i, c in enumerate(cells)}
    rels = []
    for (i, j) in cells:
        for (a, b) in ((i + 1, j), (i, j + 1)):
            if (a, b) in idx:
                rels.append((idx[(i, j)], idx[(a, b)]))
    return Poset.from_relations(len(cells), rels)


def young(shape):
    return [(i, j) for i, r in enumerate(shape) for j in range(r)]


def shifted(shape):
    return [(i, i + j) for i, r in enumerate(shape) for j in range(r)]


def q_hook(shape):
    n = sum(shape)
    num = qfact(n)
    den = [1]
    conj = [sum(1 for r in shape if r > j) for j in range(shape[0])]
    for i, r in enumerate(shape):
        for j in range(r):
            h = (r - j - 1) + (conj[j] - i - 1) + 1
            den = pmul(den, qint(h))
    return pdiv_exact(num, den)


# ---------------------------------------------------------------------------
# linear algebra mod PRIME: echelon spans of sparse vectors


class Span:
    """Row-echelon span over GF(PRIME); vectors are dicts index -> int."""

    def __init__(self):
        self.rows = {}  # pivot -> normalised row (pivot coeff 1)

    def reduce(self, v):
        v = {k: x % PRIME for k, x in v.items() if x % PRIME}
        while v:
            p = min(v)
            if p not in self.rows:
                return v
            c = v[p]
            for k, x in self.rows[p].items():
                nv = (v.get(k, 0) - c * x) % PRIME
                if nv:
                    v[k] = nv
                else:
                    v.pop(k, None)
        return v

    def add(self, v):
        r = self.reduce(v)
        if not r:
            return False
        p = min(r)
        inv = pow(r[p], PRIME - 2, PRIME)
        self.rows[p] = {k: x * inv % PRIME for k, x in r.items()}
        return True

    def contains(self, v):
        return not self.reduce(v)

    def dim(self):
        return len(self.rows)


def shuffles(u, v):
    a, b = len(u), len(v)
    for S in itertools.combinations(range(a + b), a):
        Sset = set(S)
        w = []
        iu = iv = 0
        for i in range(a + b):
            if i in Sset:
                w.append(u[iu])
                iu += 1
            else:
                w.append(v[iv])
                iv += 1
        yield tuple(w)


def RP_generators(P):
    """s shuffle t, S a nonempty proper union of components (definition in
    [Thm] Sec. on the explicit basis), as dicts word -> coefficient."""
    cs = P.comp_sets()
    k = len(cs)
    gens = []
    for r in range(1, k):
        for idx in itertools.combinations(range(k), r):
            S = [x for i in idx for x in cs[i]]
            Sc = [x for x in range(P.n) if x not in set(S)]
            for s in lin_ext(P, S):
                for t in lin_ext(P, Sc):
                    g = Counter(shuffles(s, t))
                    gens.append(dict(g))
    return gens


def RP_span(P, lin):
    index = {w: i for i, w in enumerate(lin)}
    sp = Span()
    gens = RP_generators(P)
    target = len(lin) - eC(P, lin)
    for g in gens:
        sp.add({index[w]: c for w, c in g.items()})
    return sp, gens, index


def homogeneous(sp, gens, index, stat):
    """R homogeneous for stat iff every stat-piece of every generator is in R."""
    for g in gens:
        pieces = defaultdict(dict)
        for w, c in g.items():
            pieces[stat(w)][index[w]] = c
        if len(pieces) > 1:
            for v in pieces.values():
                if not sp.contains(v):
                    return False
    return True


def piece_quotient_dims(P, lin, sp, gens, index):
    """dim of each restriction-tuple piece of C[Lin P]/R_P, computed from the
    span of the generators that live in that piece."""
    by_piece = defaultdict(list)
    for w in lin:
        by_piece[restrictions(P, w)].append(w)
    span_piece = defaultdict(Span)
    for g in gens:
        keys = {restrictions(P, w) for w in g}
        assert len(keys) == 1
        span_piece[keys.pop()].add({index[w]: c for w, c in g.items()})
    return {x: len(ws) - span_piece[x].dim() for x, ws in by_piece.items()}, span_piece, by_piece


# ---------------------------------------------------------------------------
# driver


def run(nmax_lin=7, nmax_M=6, quick=False):
    if quick:
        nmax_lin, nmax_M = 5, 5
    report = {}
    posets = all_posets(nmax_lin)
    report["gen"] = [len(posets[n]) for n in range(1, nmax_lin + 1)]
    print("[gen] unlabelled posets by n:", report["gen"])

    allP = [P for n in range(1, nmax_lin + 1) for P in posets[n]]
    disc = [P for P in allP if max(P.components()) > 0]
    print("      total", len(allP), "disconnected", len(disc))
    lins = {id(P): lin_ext(P) for P in allP}

    ok = all(check_jdt(P, lins[id(P)]) for P in allP)
    print("[jdt] jdt == toggles on all", len(allP), "posets:", ok)
    report["jdt"] = ok

    tot = 0
    okP = ok1 = ok2 = True
    for P in disc:
        r, c = check_lemma_P(P, lins[id(P)])
        okP &= r
        if r:
            tot += c
        ok1 &= check_P1(P, lins[id(P)])
        ok2 &= check_P2(P, lins[id(P)])
    print("[P] Lemma P on", len(disc), "disconnected posets,", tot, "(w, split) pairs:", okP)
    print("[P1]", ok1, "[P2]", ok2)
    report.update(P=okP, P1=ok1, P2=ok2)

    hyp = [P for P in disc if hypothesis_R(P)]
    nohyp = [P for P in disc if not hypothesis_R(P)]
    r_hyp = all(refinement(P, lins[id(P)]) for P in hyp)
    fails = [P for P in nohyp if not refinement(P, lins[id(P)])]
    print("[R] hypothesis holds on", len(hyp), "; refinement on all of them:", r_hyp)
    print("    hypothesis fails on", len(nohyp), "; refinement fails on", len(fails))
    for P in sorted(fails, key=lambda Q: Q.n)[:6]:
        print("      n=%d rels=%s" % (P.n, P.relations()))
    report.update(R_hyp=len(hyp), R_ok=r_hyp, R_nohyp=len(nohyp), R_fail=len(fails))

    okO = all(check_O(P, lins[id(P)]) for P in allP)
    print("[O] Proposition O on all", len(allP), "posets, every base component:", okO)
    report["O"] = okO

    okE = all(orbits_equal_classes(P, lins[id(P)]) == (is_chain(P) or is_antichain(P)) for P in allP)
    nE = sum(1 for P in allP if orbits_equal_classes(P, lins[id(P)]))
    print("[E] orbits == classes iff chain or antichain:", okE, "(", nE, "posets with equality )")
    report["E"] = okE

    okEig = all(check_eigen(lins[id(P)], P.n) for P in allP if P.n >= 2)
    okD = True
    nD = 0
    for P in allP:
        pres = promotion_preserves_kernel(P, lins[id(P)])
        expect = max(P.components()) == 0 or is_antichain(P)
        okD &= pres == expect
        nD += pres and max(P.components()) > 0
    print("[D] eigen-relation:", okEig, "; descends iff connected or antichain:", okD,
          "(", nD, "disconnected posets where it descends )")
    report["D"] = okD and okEig

    okF = all(check_F(P, lins[id(P)]) for P in allP)
    okCum = all(cumulant(P) == eC(P, lins[id(P)]) for P in allP)
    print("[F] Proposition F on", len(allP), "posets:", okF, "; cumulant formula:", okCum)
    report.update(F=okF, cumulant=okCum)

    r, c = check_rsw(8)
    print("[RSW] fixed patterns = q-multinomial at roots of unity:", r, "(", c, "compositions )")
    report["RSW"] = r

    okfp = all(fixed_point_product(P, lins[id(P)]) for P in disc)
    qual = 0
    okU = okUmaj = True
    for P in disc:
        res = theorem_U(P, lins[id(P)])
        if res is None:
            continue
        qual += 1
        okU &= res[0]
        okUmaj &= res[1]
    print("[U] fixed-point product formula on all", len(disc), ":", okfp)
    print("    qualifying:", qual, "; CSP holds:", okU, "; X == shifted maj:", okUmaj)
    report.update(U_fp=okfp, U_qual=qual, U=okU, U_maj=okUmaj)

    sweep = {}
    fail4 = []
    for n in range(3, nmax_lin + 1):
        row = [len(posets[n]), 0, 0, 0]
        for P in posets[n]:
            lin = lins[id(P)]
            if n % promotion_order(P, lin):
                row[1] += 1
                continue
            if csp_holds(P, lin, shifted_maj_poly(P, lin)):
                row[2] += 1
            else:
                row[3] += 1
                if n == 4:
                    fail4.append(P.relations())
        sweep[n] = row
        print("[sweep] n=%d posets=%d order-not-dividing=%d hold=%d fail=%d" % (n, *row))
    print("        n=4 failures:", fail4)
    report["sweep"] = sweep

    rh_ok = True
    for shape in [(2, 2), (3, 3), (4, 4), (3, 3, 3), (5, 5), (4, 4, 4), (6, 6)]:
        P = shape_poset(young(shape))
        lin = lin_ext(P)
        X = trim(q_hook(shape))
        same = X == trim(shifted_maj_poly(P, lin))
        pos = csp_holds(P, lin, X)
        neg = csp_holds(P, lin, [0] + X)
        rh_ok &= same and pos and not neg
        print("[rh] %s: q-hook == shifted maj %s, CSP %s, q*X rejected %s" % (shape, same, pos, not neg))
    report["rh"] = rh_ok

    orders = {}
    for name, cells in [("(3,2,1)", young((3, 2, 1))), ("(4,3,2,1)", young((4, 3, 2, 1))),
                        ("shifted 3", shifted((2, 1))), ("shifted 6", shifted((3, 2, 1))),
                        ("shifted 10", shifted((4, 3, 2, 1)))]:
        P = shape_poset(cells)
        orders[name] = promotion_order(P, lin_ext(P))
    print("[stair] promotion orders:", orders)
    report["stair"] = orders

    # Theorem M, homogeneity, descent of R_P
    discM = [P for P in disc if P.n <= nmax_M]
    okM = True
    hom = Counter()
    descR = []
    rng = random.Random(20261031)
    nat_all = {"des": 0, "maj": 0, "tested": 0}
    for P in discM:
        lin = lins[id(P)]
        sp, gens, index = RP_span(P, lin)
        e, ec = len(lin), eC(P, lin)
        if sp.dim() != e - ec:
            okM = False
        dims, span_piece, by_piece = piece_quotient_dims(P, lin, sp, gens, index)
        cs = P.comp_sets()
        q = eC(disjoint_union(*[chain(len(T)) for T in cs]))
        if set(dims.values()) != {q} or sum(dims.values()) != ec:
            okM = False
        # B_P restricted to each piece is a basis of the piece modulo R_P
        base = set(cs[0])
        for x, ws in by_piece.items():
            B = [w for w in ws if base <= first_block(P, w)]
            s2 = Span()
            for r in span_piece[x].rows.values():
                s2.add(r)
            if len(B) != q or not all(s2.add({index[w]: 1}) for w in B):
                okM = False
        lab = natural_labelling(P)
        colour = {w: rng.randrange(2) for w in lin}
        stats = {
            "restriction tuple": lambda w: restrictions(P, w),
            "number of blocks": lambda w: len(cuts(P, w)),
            "jumps": lambda w: sum(1 for i in range(len(w) - 1) if not P.comparable(w[i], w[i + 1])),
            "des": lambda w: des(w, lab),
            "maj": lambda w: maj(w, lab),
            "first letter": lambda w: w[0],
            "random colouring": lambda w: colour[w],
        }
        for name, f in stats.items():
            if homogeneous(sp, gens, index, f):
                hom[name] += 1
        if P.n <= 5:
            # every natural labelling
            for L in lin:
                labL = {x: i for i, x in enumerate(L)}
                nat_all["tested"] += 1
                nat_all["des"] += homogeneous(sp, gens, index, lambda w: des(w, labL))
                nat_all["maj"] += homogeneous(sp, gens, index, lambda w: maj(w, labL))
        if all(sp.contains({index[promote(P, w)]: c for w, c in g.items()}) for g in gens):
            descR.append([len(T) for T in cs] if all(is_chain_set(P, T) for T in cs) else P.relations())
    print("[M] Theorem M on", len(discM), "disconnected posets n <=", nmax_M, ":", okM)
    print("[homog]", dict(hom), "of", len(discM))
    print("        every natural labelling, n <= 5:", nat_all)
    print("[descR] partial(R_P) <= R_P on", len(descR), ":", descR)
    q222 = eC(disjoint_union(chain(2), chain(2), chain(2)))
    print("        e_C(C2+C2+C2) =", q222)
    report.update(M=okM, homog=dict(hom), nat_all=nat_all, descR=descR, q222=q222)

    # table of section 2
    V = Poset.from_relations(3, [(0, 1), (0, 2)])
    rect22 = shape_poset(young((2, 2)))
    rect23 = shape_poset(young((3, 3)))
    rows = [("A3", antichain(3)), ("C2+C1", disjoint_union(chain(2), chain(1))),
            ("C2+C2", disjoint_union(chain(2), chain(2))),
            ("C2+C2+C2", disjoint_union(chain(2), chain(2), chain(2))),
            ("(2x2)+C1", disjoint_union(rect22, chain(1))), ("V+V", disjoint_union(V, V)),
            ("2x3", rect23)]
    table = {}
    for name, P in rows:
        lin = lin_ext(P)
        orbs = orbits(P, lin)
        table[name] = (len(lin), eC(P, lin), len(orbs), sorted(len(o) for o in orbs), refinement(P, lin))
        print("[table]", name, table[name])
    report["table"] = table
    return report


def is_chain_set(P, T):
    return all(P.comparable(a, b) for a in T for b in T if a != b)


if __name__ == "__main__":
    run(quick="--quick" in sys.argv)
