#!/usr/bin/env python3
"""Independent audit of the two homology-free proofs of
mu(OP(P)) = (-1)^{n-1} e_C(P)  (notes/audit_mu_op_elementary.md).

Plain Python 3, no dependencies.  Imports nothing from this repository; in
particular not mu_op_elementary.py.

A poset on {0..n-1} is a tuple `up` of bitmasks: up[x] = {y : x < y}.
A set partition is a sorted tuple of block bitmasks.  OP(P) is the set of
partitions whose quotient digraph is acyclic, ordered by refinement.

Checks (all posets up to isomorphism with n <= NMAX, generated here):
  [gen]     isomorphism-class counts 1, 2, 5, 16, 63, 318, 2045 (A000112).
  [pos-mu]  mu(Pi_n) = (-1)^{n-1}(n-1)! and mu(OP(chain)) = (-1)^{n-1}
            (positive controls for the Moebius routine).
  [A]       mu(OP(P)) = (-1)^{n-1} e_C(P)                    (Theorem A).
  [conn]    P connected => e_C(P) = e(P); disconnected => e_C < e  (Fact 0).
  [Mclose]  OP(P) is closed under the partition meet        (Lemma M(a)).
  [Mb]      a minimal or maximal: pi_a in OP, pi_a a coatom, and
            {x in OP : x meet pi_a = 0} = {0} u {pi_ab in OP}  (Lemma M(b)).
  [Wdual]   dual Weisner at c = pi_a, mu(x, 1) computed in OP(P) itself
            (Lemma D before Lemma U is applied).
  [U]       mu_OP(P)(pi, 1) = mu(OP(Q_pi)) for every pi in OP(P), Q_pi built
            as a transitive closure and its OP built from scratch  (Lemma U).
  [D]       mu(OP(P)) = -sum_b mu(OP(P/pi_ab)), a minimal     (Lemma D).
  [pab]     for a minimal: pi_ab in OP  <=>  a || b or b covers a.
  [C]       e_C(P) = sum_b e_C(P/pi_ab), a minimal            (Lemma C).
  [Cbij]    the necklace map Phi is a bijection onto the disjoint union.
  [W]       sum over compatible compositions of (-1)^k = (-1)^m [antichain],
            by brute force over ordered set partitions, and independently
            as mu of the lattice J(Q) of order ideals        (Lemma W).
  [F]       sum_{sigma >= pi in OP} (-1)^|sigma| e(Q_sigma)
            = (-1)^|pi| [pi >= kappa]                         (Lemma F).
  [Z]       (-1)^n e(P) = sum_{sigma >= kappa} (-1)^|sigma| mu(0, sigma)
                                                              (Prop. Z).
  [prod]    sigma >= kappa: mu(0, sigma) = prod_B mu(OP(P|_B)).
  [comp]    e(P) = sum_{sigma in Pi(K)} prod_B e_C(P|_B)   ([GT] Lemma 1.3).

Negative controls (each must fail somewhere):
  [neg:A-e]        Theorem A with e(P) in place of e_C(P);
  [neg:C-e]        Lemma C with e in place of e_C;
  [neg:C-mid]      Lemma C at an element with something above and below;
  [neg:D-mid]      Lemma D at such an element;
  [neg:Wdual-top]  dual Weisner with c = 1 (hypothesis c != 1 violated);
  [neg:W-strict]   Lemma W with strict compatibility (x < y => F(x) < F(y));
  [neg:F-nokappa]  Lemma F without the factor [pi >= kappa].

Run (from compute/):  python3 audit_mu_op_elementary.py            (n <= 6 full, n = 7 Theorem A, C, D, W)
                      python3 audit_mu_op_elementary.py --nmax 5   (seconds)
Exit status 0 iff every asserted check passes and every control fires.
"""

import argparse
import itertools
import sys
import time
from collections import defaultdict
from math import factorial

FAIL = []


class Stats:
    def __init__(self):
        self.c = defaultdict(lambda: [0, 0])  # name -> [fails, checks]

    def check(self, name, ok, info=None):
        self.c[name][1] += 1
        if not ok:
            self.c[name][0] += 1
            if not name.startswith("neg:") and len(FAIL) < 20:
                FAIL.append((name, info))


# ---------------------------------------------------------------- posets

def bits(m):
    while m:
        low = m & -m
        yield low.bit_length() - 1
        m ^= low


def popcount(m):
    return bin(m).count("1")


def down_of(up):
    n = len(up)
    dn = [0] * n
    for x in range(n):
        for y in bits(up[x]):
            dn[y] |= 1 << x
    return dn


def closure(n, edges):
    """Transitive closure of a digraph on range(n) given as up-masks.
    Returns None if there is a directed cycle."""
    up = list(edges)
    changed = True
    while changed:
        changed = False
        for x in range(n):
            m = up[x]
            for y in bits(up[x]):
                m |= up[y]
            if m != up[x]:
                up[x] = m
                changed = True
    if any(up[x] >> x & 1 for x in range(n)):
        return None
    return tuple(up)


def canon(up):
    """Canonical form of a poset under relabelling: colour refinement, then
    brute force over orderings inside colour classes."""
    n = len(up)
    dn = down_of(up)
    col = [(popcount(dn[x]), popcount(up[x])) for x in range(n)]
    for _ in range(n):
        new = [(col[x], tuple(sorted(col[y] for y in bits(dn[x]))),
                tuple(sorted(col[y] for y in bits(up[x])))) for x in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    classes = defaultdict(list)
    for x in range(n):
        classes[col[x]].append(x)
    groups = [classes[k] for k in sorted(classes)]
    best = None
    for parts in itertools.product(*(itertools.permutations(g) for g in groups)):
        order = [x for p in parts for x in p]
        pos = {x: i for i, x in enumerate(order)}
        code = tuple(sum(1 << pos[y] for y in bits(up[x])) for x in order)
        if best is None or code < best:
            best = code
    return best


def all_posets(n):
    """One poset per isomorphism class on n points (natural labellings,
    each new point a maximal element over an order ideal, deduplicated)."""
    level = {()}
    for k in range(n):
        nxt = set()
        for up in level:
            dn = down_of(up) if k else []
            for D in range(1 << k):
                if any((dn[x] & ~D) for x in bits(D)):
                    continue  # D not down-closed
                new = list(up) + [0]
                for x in bits(D):
                    new[x] |= 1 << k
                nxt.add(canon(tuple(new)))
        level = nxt
    return sorted(level)


def components(up):
    n = len(up)
    dn = down_of(up)
    seen, comps = 0, []
    for s in range(n):
        if seen >> s & 1:
            continue
        comp, frontier = 1 << s, 1 << s
        while frontier:
            nb = 0
            for x in bits(frontier):
                nb |= up[x] | dn[x]
            frontier = nb & ~comp
            comp |= nb
        seen |= comp
        comps.append(comp)
    return comps


def restrict(up, mask):
    els = list(bits(mask))
    idx = {x: i for i, x in enumerate(els)}
    return tuple(sum(1 << idx[y] for y in bits(up[x] & mask)) for x in els)


def quotient(up, blocks):
    """Q_pi: transitive closure of the quotient digraph; None if cyclic."""
    k = len(blocks)
    where = {}
    for i, B in enumerate(blocks):
        for x in bits(B):
            where[x] = i
    edges = [0] * k
    for x in range(len(up)):
        for y in bits(up[x]):
            i, j = where[x], where[y]
            if i != j:
                edges[i] |= 1 << j
    return closure(k, edges)


# ---------------------------------------------------- linear extensions

def lin_exts(up):
    n = len(up)
    dn = down_of(up)
    out = []

    def rec(placed, word):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not placed >> x & 1 and dn[x] & ~placed == 0:
                word.append(x)
                rec(placed | 1 << x, word)
                word.pop()

    rec(0, [])
    return out


def necklace(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


def e_count(up):
    """e(P) by DP over order ideals (independent of lin_exts)."""
    n = len(up)
    dn = down_of(up)
    cnt = {0: 1}
    for _ in range(n):
        nxt = defaultdict(int)
        for I, c in cnt.items():
            for x in range(n):
                if not I >> x & 1 and dn[x] & ~I == 0:
                    nxt[I | 1 << x] += c
        cnt = nxt
    return cnt[(1 << n) - 1]


def e_C(up):
    return len({necklace(w) for w in lin_exts(up)})


# ------------------------------------------------- partitions and mu

_SP = {}


def set_partitions(items):
    """Set partitions of a list of distinct ints, each a list of lists."""
    items = tuple(items)
    if items in _SP:
        return _SP[items]
    if not items:
        res = [[]]
    else:
        first, rest = items[0], items[1:]
        res = []
        for p in set_partitions(rest):
            res.append([[first]] + p)
            for i in range(len(p)):
                res.append(p[:i] + [[first] + p[i]] + p[i + 1:])
    _SP[items] = res
    return res


def is_op(up, blocks):
    return quotient(up, blocks) is not None


def mu_above(up, pi):
    """mu_{OP(P)}(pi, z) for every z >= pi in OP(P), computed inside OP(P)
    (no quotient poset).  pi is a tuple of block masks in OP(P).  Returns a
    dict z -> mu(pi, z)."""
    k = len(pi)
    # every coarsening of pi: a set partition of the block indices
    coarse = []
    for p in set_partitions(range(k)):
        z = tuple(sorted(sum(pi[i] for i in B) for B in p))
        if is_op(up, z):
            coarse.append((len(p), [sum(1 << i for i in B) for B in p], z))
    coarse.sort(key=lambda t: -t[0])  # finer first
    mu = {}
    for _, idxblocks, z in coarse:
        if z == pi:
            mu[z] = 1
            continue
        s = 0
        # every y with pi <= y < z: refine each z-block (as index sets)
        per_block = [set_partitions(list(bits(ib))) for ib in idxblocks]
        for choice in itertools.product(*per_block):
            y = tuple(sorted(sum(pi[i] for i in B) for part in choice for B in part))
            if y != z and y in mu:
                s += mu[y]
        mu[z] = -s
    return mu


def discrete(n):
    return tuple(sorted(1 << x for x in range(n)))


def mu_OP(up):
    n = len(up)
    if n == 0:
        return 1
    return mu_above(up, discrete(n))[((1 << n) - 1,)]


def meet(x, y):
    return tuple(sorted(a & b for a in x for b in y if a & b))


def finer_eq(x, y):
    """x <= y in refinement order."""
    return all(any(a & ~b == 0 for b in y) for a in x)


# -------------------------------------------- compatible compositions

def compositions_bruteforce(up, strict=False):
    """sum of (-1)^k over surjections F: Q -> [k] with x<y => F(x)<=F(y)
    (or < if strict), by enumerating ordered set partitions."""
    n = len(up)
    s = 0
    for p in set_partitions(range(n)):
        for order in itertools.permutations(p):
            F = {}
            for i, B in enumerate(order):
                for x in B:
                    F[x] = i
            ok = all((F[x] < F[y]) if strict else (F[x] <= F[y])
                     for x in range(n) for y in bits(up[x]))
            if ok:
                s += (-1) ** len(order)
    return s


def compositions_ideals(up):
    """the same sum as signed strict chains of order ideals 0 = D_0 < ... < D_k = Q,
    i.e. mu_{J(Q)}(empty, Q)."""
    n = len(up)
    dn = down_of(up)
    ideals = [I for I in range(1 << n) if all(dn[x] & ~I == 0 for x in bits(I))]
    ideals.sort(key=popcount)
    mu = {}
    for I in ideals:
        mu[I] = 1 if I == 0 else -sum(mu[J] for J in ideals if J != I and J & ~I == 0 and J in mu)
    return mu[(1 << n) - 1]


def is_antichain(up):
    return all(u == 0 for u in up)


# ---------------------------------------------------------- the checks

class Ctx:
    def __init__(self):
        self.mu = {}
        self.eC = {}

    def mu_of(self, up):
        key = canon(up) if up else ()
        if key not in self.mu:
            self.mu[key] = mu_OP(up)
        return self.mu[key]

    def eC_of(self, up):
        key = canon(up) if up else ()
        if key not in self.eC:
            self.eC[key] = e_C(up) if up else 1
        return self.eC[key]


def minimal(up, a):
    return all(not (up[x] >> a & 1) for x in range(len(up)))


def maximal(up, a):
    return up[a] == 0


def merged(n, a, b):
    return tuple(sorted([(1 << a) | (1 << b)] + [1 << x for x in range(n) if x not in (a, b)]))


def check_poset(up, st, ctx, full):
    n = len(up)
    N = (1 << n) - 1
    sgn = (-1) ** (n - 1)
    lin = lin_exts(up)
    e = len(lin)
    st.check("e-dp", e == e_count(up), up)
    eC = len({necklace(w) for w in lin})
    comps = components(up)
    connected = len(comps) == 1

    # Theorem A
    m = ctx.mu_of(up)
    st.check("A", m == sgn * eC, (up, m, eC))
    st.check("neg:A-e", m == sgn * e)
    st.check("conn", (eC == e) if connected else (eC < e), up)

    # Lemma W on P itself (Q_pi are themselves posets with <= n points)
    if n <= 7:
        sJ = compositions_ideals(up)
        st.check("W(J)", sJ == (-1) ** n * is_antichain(up), up)
    if full:
        sB = compositions_bruteforce(up)
        st.check("W", sB == (-1) ** n * is_antichain(up), up)
        st.check("neg:W-strict", compositions_bruteforce(up, strict=True)
                 == (-1) ** n * is_antichain(up))

    # Lemmas C, D, M(b), dual Weisner, pi_ab criterion, at every point a
    for a in range(n):
        isminl, ismaxl = minimal(up, a), maximal(up, a)
        mid = not isminl and not ismaxl
        bs = [b for b in range(n) if b != a and is_op(up, merged(n, a, b))]
        if n >= 2 and isminl:
            for b in range(n):
                if b == a:
                    continue
                inc = not (up[a] >> b & 1) and not (up[b] >> a & 1)
                covers = (up[a] >> b & 1) and not any(up[a] >> c & 1 and up[c] >> b & 1
                                                      for c in range(n))
                st.check("pab", (b in bs) == bool(inc or covers), (up, a, b))
        quots = {b: quotient(up, merged(n, a, b)) for b in bs}
        rhsC = sum(ctx.eC_of(quots[b]) for b in bs)
        rhsD = -sum(ctx.mu_of(quots[b]) for b in bs)
        if n >= 2 and isminl:
            st.check("C", eC == rhsC, (up, a))
            st.check("neg:C-e", e == sum(len(lin_exts(quots[b])) for b in bs))
            st.check("D", m == rhsD, (up, a))
            check_phi(up, a, lin, bs, quots, st)
        if mid:
            st.check("neg:C-mid", eC == rhsC)
            st.check("neg:D-mid", m == rhsD)
            pia = tuple(sorted([1 << a, N & ~(1 << a)]))
            st.check("pia-notOP-mid", not is_op(up, pia), (up, a))
        if full and n >= 2 and (isminl or ismaxl):
            pia = tuple(sorted([1 << a, N & ~(1 << a)]))
            st.check("Mb-in", is_op(up, pia), (up, a))
            ops = all_op(up)
            above = [x for x in ops if finer_eq(pia, x)]
            st.check("Mb-coatom", sorted(above) == sorted([pia, (N,)]), (up, a))
            zero = discrete(n)
            S = {x for x in ops if meet(x, pia) == zero}
            st.check("Mb", S == {zero} | {merged(n, a, b) for b in bs}, (up, a))
            # dual Weisner at pi_a, mu(x, 1) computed in OP(P) itself
            tot = sum(mu_above(up, x)[(N,)] for x in S)
            st.check("Wdual", tot == 0, (up, a))
    if n >= 1 and full:
        zero = discrete(n)
        st.check("neg:Wdual-top", mu_above(up, zero)[(N,)] == 0)

    if not full:
        return

    ops = all_op(up)
    # Lemma M(a)
    opset = set(ops)
    if n <= 5:
        for x in ops:
            for y in ops:
                st.check("Mclose", meet(x, y) in opset, (up, x, y))
    # Lemma U at every pi
    mu0 = mu_above(up, discrete(n))
    for pi in ops:
        Q = quotient(up, pi)
        st.check("U", mu_above(up, pi)[(N,)] == ctx.mu_of(Q), (up, pi))
    # Lemma F at every pi
    eQ = {s: e_count(quotient(up, s)) for s in ops}
    kappa = tuple(sorted(comps))
    for pi in ops:
        lhs = sum((-1) ** len(s) * eQ[s] for s in ops if finer_eq(pi, s))
        geq = finer_eq(kappa, pi)
        st.check("F", lhs == (-1) ** len(pi) * geq, (up, pi))
        st.check("neg:F-nokappa", lhs == (-1) ** len(pi))
    # Prop. Z, products, [GT] Lemma 1.3
    K = len(comps)
    rhsZ = 0
    rhsComp = 0
    for p in set_partitions(range(K)):
        sigma = tuple(sorted(sum(comps[i] for i in B) for B in p))
        st.check("Z-op", sigma in opset, (up, sigma))
        rhsZ += (-1) ** len(sigma) * mu0[sigma]
        prod_mu, prod_eC = 1, 1
        for blk in sigma:
            R = restrict(up, blk)
            prod_mu *= ctx.mu_of(R)
            prod_eC *= ctx.eC_of(R)
        st.check("prod", mu0[sigma] == prod_mu, (up, sigma))
        rhsComp += prod_eC
    st.check("Z", (-1) ** n * e == rhsZ, up)
    st.check("comp", e == rhsComp, up)


_OPS = {}


def all_op(up):
    if up not in _OPS:
        n = len(up)
        _OPS.clear()
        _OPS[up] = [tuple(sorted(sum(1 << x for x in B) for B in p))
                    for p in set_partitions(range(n))
                    if is_op(up, tuple(sorted(sum(1 << x for x in B) for B in p)))]
    return _OPS[up]


def check_phi(up, a, lin, bs, quots, st):
    """Lemma C at the level of the maps: Phi(N) = (successor b of a, N with
    a b merged) is a bijection from the necklaces of P meeting Lin(P) onto
    the disjoint union of the necklaces of P/pi_ab meeting Lin(P/pi_ab)."""
    n = len(up)
    necks = {necklace(w) for w in lin}
    image = set()
    for N in necks:
        i = N.index(a)
        b = N[(i + 1) % n]
        # merged necklace, as a cyclic word over the blocks of pi_ab,
        # blocks named by the index in sorted(merged(n, a, b))
        blocks = merged(n, a, b)
        name = {x: j for j, B in enumerate(blocks) for x in bits(B)}
        rot = N[i:] + N[:i]  # starts a b ...
        word = tuple(name[x] for x in rot[1:])  # drop a, keep b as the block
        if b not in bs:
            st.check("Cbij", False, ("successor not in OP", up, a, N))
            continue
        target = {necklace(w) for w in lin_exts(quots[b])}
        st.check("Cbij", necklace(word) in target, (up, a, N))
        image.add((b, necklace(word)))
    total = sum(len({necklace(w) for w in lin_exts(quots[b])}) for b in bs)
    st.check("Cbij", len(image) == len(necks) == total, (up, a))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--full-max", type=int, default=6,
                    help="run every check up to this n; above it only A, C, D, W(J)")
    args = ap.parse_args()
    out = []

    def log(*s):
        line = " ".join(str(x) for x in s)
        print(line, flush=True)
        out.append(line)

    st = Stats()
    ctx = Ctx()
    log("audit_mu_op_elementary.py: mu(OP(P)) = (-1)^{n-1} e_C(P), Proofs W and Z")
    expected = [1, 1, 2, 5, 16, 63, 318, 2045]
    # positive controls for the Moebius routine
    for n in range(1, min(args.nmax, 6) + 1):
        anti = tuple([0] * n)
        chain = tuple(sum(1 << y for y in range(x + 1, n)) for x in range(n))
        st.check("pos-mu", mu_OP(anti) == (-1) ** (n - 1) * factorial(n - 1), n)
        st.check("pos-mu", mu_OP(chain) == (-1) ** (n - 1), n)
        st.check("pos-mu", len(all_op(anti)) == len(set_partitions(range(n))), n)
        st.check("pos-mu", len(all_op(chain)) == 2 ** (n - 1), n)
    small = []
    for n in range(1, args.nmax + 1):
        t0 = time.time()
        ps = all_posets(n)
        st.check("gen", len(ps) == expected[n], (n, len(ps)))
        full = n <= args.full_max
        for up in ps:
            check_poset(up, st, ctx, full)
            if n <= 3:
                small.append((n, up, ctx.mu_of(up), len(lin_exts(up)), ctx.eC_of(up),
                              len(components(up))))
        log(f"  n = {n}: {len(ps)} posets, {'all checks' if full else 'A, C, D, W(J), Cbij'}, "
            f"{time.time() - t0:.1f} s")
    log("")
    log("small cases: n, up-masks, mu(OP), e, e_C, #components")
    for row in small:
        log("  ", *row)
    log("")
    log("check                      fails / checks")
    ok = True
    for name in sorted(st.c):
        f, k = st.c[name]
        log(f"  {name:22s} {f:9d} / {k}")
        if name.startswith("neg:"):
            if f == 0:
                ok = False
                log(f"NEGATIVE CONTROL DID NOT FIRE: {name}")
        elif f or k == 0:
            ok = False
    for x in FAIL:
        log("FAIL", x)
    log("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
