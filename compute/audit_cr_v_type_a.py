"""Independent audit of notes/cr_v_type_a.md (Theorem TA-CR, Lemmas K_A and C).

Written from the statements in the note only; imports nothing from the other
scripts of this repository (in particular not compute/cr_v_type_a.py).

Model.  P is a poset on [n] given by up[i] = bitmask of the j with i <_P j.
M = OP(P)^tau = tau-stable set partitions of [n] whose quotient digraph is
acyclic, ordered by refinement.  A partition is a sorted tuple of block
bitmasks; its "pair mask" has bit i*n+j set when i < j share a block, so
refinement is inclusion of pair masks and the common refinement is AND.

Parts:
  [CTL]   controls: poset counts (OEIS A000112), mu(Pi_n), Pi_4^(1234),
          the F6 join example, the fast join against a brute-force lub;
  [SWEEP] every poset with 3 <= n <= NMAX up to isomorphism, every
          tau in Aut(P) (sign +) and every anti-automorphism (sign -) up to
          conjugacy by Aut(P): mu(M), the full complement relation of M,
          CR_V, the zero criteria ([Thm] for +w, (TA1)-(TA4) for -tau),
          the table-W witness (in M? uncomplemented?), S4 via exact linear
          algebra for every power g^k, Lemma K_A for every w <= cl(Fix g),
          Lemma C against the lattice for every orbit partition cyc(tau^k);
  [NEG]   positive controls that MUST fail: witness cl(Fix g) everywhere,
          criterion without (TA4), k = 2 always in row W-1, plain partition
          join instead of the acyclic closure;
  [LC]    Lemma C by brute force, without posets, every cycle type n <= 7
          and every sigma-stable kappa, every h | o;
  [BIG]   the W-1 branch Lambda = {m, 2m}, m odd not squarefree, both
          lengths present: tau = (9)(18) on 27 points (and 9, 18, 25, 50
          single-length analogues), by exhaustive search over the
          tau-stable partitions meeting W trivially, with complemented
          positive controls;
  [COUNT] the number of lattices OP(P)^{+-tau}, n <= 6, without conjugacy
          reduction (the "5,063 vs 3,576" question).
"""

import argparse
import itertools
import math
import sys
import time
from fractions import Fraction

# ---------------------------------------------------------------- basics


def popcount(x):
    return bin(x).count("1")


def bits(x):
    out = []
    i = 0
    while x:
        if x & 1:
            out.append(i)
        x >>= 1
        i += 1
    return out


def set_partitions(n):
    """All set partitions of range(n), as sorted tuples of block bitmasks."""
    res = []

    def rec(i, blocks):
        if i == n:
            res.append(tuple(sorted(blocks)))
            return
        for b in range(len(blocks)):
            blocks[b] |= 1 << i
            rec(i + 1, blocks)
            blocks[b] &= ~(1 << i)
        blocks.append(1 << i)
        rec(i + 1, blocks)
        blocks.pop()

    rec(0, [])
    return res


def pairmask(part, n):
    m = 0
    for b in part:
        el = bits(b)
        for a in range(len(el)):
            for c in range(a + 1, len(el)):
                m |= 1 << (el[a] * n + el[c])
    return m


def map_mask(mask, perm):
    out = 0
    for i in bits(mask):
        out |= 1 << perm[i]
    return out


def map_part(part, perm):
    return tuple(sorted(map_mask(b, perm) for b in part))


def compose(p, q):  # (p o q)(i) = p[q[i]]
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    inv = [0] * len(p)
    for i, x in enumerate(p):
        inv[x] = i
    return tuple(inv)


def power(p, k):
    n = len(p)
    r = tuple(range(n))
    for _ in range(k):
        r = compose(p, r)
    return r


def cycles(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i not in seen:
            c, j = [], i
            while j not in seen:
                seen.add(j)
                c.append(j)
                j = p[j]
            out.append(c)
    return out


def order(p):
    o = 1
    for c in cycles(p):
        o = o * len(c) // math.gcd(o, len(c))
    return o


def squarefree(m):
    d = 2
    while d * d <= m:
        if m % (d * d) == 0:
            return False
        d += 1
    return True


def least_square_prime(m):
    d = 2
    while d * d <= m:
        if m % (d * d) == 0 and all(d % e for e in range(2, d)):
            return d
        d += 1
    return None


def cyc_part(p):
    return tuple(sorted(sum(1 << i for i in c) for c in cycles(p)))


# ---------------------------------------------------------------- posets


def close(n, up):
    up = list(up)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            new = up[i]
            for j in bits(up[i]):
                new |= up[j]
            if new != up[i]:
                up[i] = new
                changed = True
    return up


def is_poset(n, up):
    for i in range(n):
        if up[i] >> i & 1:
            return False
        for j in bits(up[i]):
            if up[j] >> i & 1:
                return False
            if up[j] & ~up[i]:
                return False
    return True


def down_of(n, up):
    dn = [0] * n
    for i in range(n):
        for j in bits(up[i]):
            dn[j] |= 1 << i
    return dn


def refine_colors(n, up, dn):
    col = [(popcount(up[i]), popcount(dn[i])) for i in range(n)]
    for _ in range(n):
        new = [(col[i], tuple(sorted(col[j] for j in bits(up[i]))),
                tuple(sorted(col[j] for j in bits(dn[i])))) for i in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    keys = sorted(set(col))
    return [keys.index(c) for c in col]


def canon(n, up):
    """Canonical form: lexicographically least relation key over all
    relabelings that respect a refined invariant colouring (colour classes
    are placed in increasing colour order)."""
    dn = down_of(n, up)
    col = refine_colors(n, up, dn)
    classes = {}
    for i in range(n):
        classes.setdefault(col[i], []).append(i)
    order_cls = [classes[c] for c in sorted(classes)]
    best = None
    for choice in itertools.product(*[itertools.permutations(c) for c in order_cls]):
        seq = [x for grp in choice for x in grp]  # seq[newlabel] = old
        pos = [0] * n
        for new, old in enumerate(seq):
            pos[old] = new
        key = tuple(sorted((pos[i], pos[j]) for i in range(n) for j in bits(up[i])))
        if best is None or key < best:
            best = key
    return best


def from_key(n, key):
    up = [0] * n
    for i, j in key:
        up[i] |= 1 << j
    return up


def posets_upto_iso(nmax):
    """reps[n] = list of up-arrays, one per isomorphism class.  Generated by
    adding a new maximal element over an order ideal of each smaller rep."""
    reps = {0: [[]]}
    keys0 = {0: [()]}
    for n in range(1, nmax + 1):
        seen = set()
        out = []
        for up in reps[n - 1]:
            m = n - 1
            dn = down_of(m, up) if m else []
            for D in range(1 << m):
                # D must be an order ideal (closed downward)
                ok = all((dn[j] & ~D) == 0 for j in bits(D))
                if not ok:
                    continue
                new = list(up) + [0]
                for j in bits(D):
                    new[j] |= 1 << m
                new = close(n, new)
                k = canon(n, new)
                if k not in seen:
                    seen.add(k)
                    out.append(from_key(n, k))
        reps[n] = out
    return reps


def automorphisms(n, up, anti):
    """All tau with i<j iff tau i < tau j (anti=False) or tau j < tau i."""
    dn = down_of(n, up)
    res = []
    rel = [[bool(up[i] >> j & 1) for j in range(n)] for i in range(n)]
    sig = [(popcount(up[i]), popcount(dn[i])) for i in range(n)]
    perm = [None] * n
    used = [False] * n

    def rec(i):
        if i == n:
            res.append(tuple(perm))
            return
        for v in range(n):
            if used[v]:
                continue
            want = sig[i] if not anti else (sig[i][1], sig[i][0])
            if sig[v] != want:
                continue
            ok = True
            for j in range(i):
                a, b = perm[j], v
                if not anti:
                    if rel[j][i] != rel[a][b] or rel[i][j] != rel[b][a]:
                        ok = False
                        break
                else:
                    if rel[j][i] != rel[b][a] or rel[i][j] != rel[a][b]:
                        ok = False
                        break
            if ok:
                perm[i] = v
                used[v] = True
                rec(i + 1)
                used[v] = False
                perm[i] = None

    rec(0)
    return res


def conj_reps(auts, taus):
    """Representatives of taus up to conjugation by the group auts."""
    seen = set()
    reps = []
    for t in taus:
        if t in seen:
            continue
        reps.append(t)
        for s in auts:
            seen.add(compose(compose(s, t), inverse(s)))
    return reps


def components(n, up):
    dn = down_of(n, up)
    seen = 0
    comps = []
    for i in range(n):
        if seen >> i & 1:
            continue
        comp, frontier = 1 << i, 1 << i
        while frontier:
            nxt = 0
            for j in bits(frontier):
                nxt |= up[j] | dn[j]
            frontier = nxt & ~comp
            comp |= nxt
        seen |= comp
        comps.append(comp)
    return tuple(sorted(comps))


# ---------------------------------------------------------------- lattice M


def quotient_edges(part, up):
    r = len(part)
    upset = []
    for b in part:
        u = 0
        for i in bits(b):
            u |= up[i]
        upset.append(u)
    return [[a != c and bool(upset[a] & part[c]) for c in range(r)] for a in range(r)]


def is_acyclic(part, up):
    E = quotient_edges(part, up)
    r = len(part)
    alive = set(range(r))
    while alive:
        src = [a for a in alive if not any(E[b][a] for b in alive)]
        if not src:
            return False
        alive -= set(src)
    return True


def sccs(E):
    r = len(E)
    reach = [[E[a][c] or a == c for c in range(r)] for a in range(r)]
    for k in range(r):
        for a in range(r):
            if reach[a][k]:
                for c in range(r):
                    if reach[k][c]:
                        reach[a][c] = True
    comp = [-1] * r
    out = []
    for a in range(r):
        if comp[a] < 0:
            grp = [c for c in range(r) if reach[a][c] and reach[c][a]]
            for c in grp:
                comp[c] = len(out)
            out.append(grp)
    return out


def partition_join(x, y):
    blocks = list(x)
    for b in y:
        merged = b
        rest = []
        for a in blocks:
            if a & merged:
                merged |= a
            else:
                rest.append(a)
        # merging may connect further blocks; repeat until stable
        changed = True
        while changed:
            changed = False
            rest2 = []
            for a in rest:
                if a & merged:
                    merged |= a
                    changed = True
                else:
                    rest2.append(a)
            rest = rest2
        blocks = rest + [merged]
    return tuple(sorted(blocks))


def acyclic_closure(part, up):
    """Merge strong components of the quotient, repeatedly, until acyclic
    (S2 says once suffices; we iterate so as not to rely on it)."""
    while True:
        E = quotient_edges(part, up)
        groups = sccs(E)
        if len(groups) == len(part):
            return part
        part = tuple(sorted(sum(part[a] for a in g) for g in groups))


def join_M(x, y, up):
    j = partition_join(x, y)
    if len(j) == 1:
        return j
    return acyclic_closure(j, up)


class Lat:
    def __init__(self, n, up, elems, joinf=None):
        self.n, self.up = n, up
        self.el = sorted(elems, key=lambda p: -len(p))  # finest first
        self.pm = [pairmask(p, n) for p in self.el]
        self.idx = {p: i for i, p in enumerate(self.el)}
        self.top = (1 << n) - 1
        self.joinf = joinf or (lambda a, b: join_M(a, b, up))
        self._comp = None

    def leq(self, a, b):
        return self.pm[a] & ~self.pm[b] == 0

    def mu(self):
        N = len(self.el)
        mu = [0] * N
        mu[0] = 1
        assert len(self.el[0]) == self.n  # bottom = discrete
        for i in range(1, N):
            s = 0
            pi = self.pm[i]
            for j in range(i):
                if self.pm[j] & ~pi == 0:
                    s += mu[j]
            mu[i] = -s
        assert self.el[-1] == (self.top,)
        return mu[-1]

    def complements(self):
        """comp[i] = list of j with el[j] ^ el[i] = bottom and join = top."""
        if self._comp is not None:
            return self._comp
        N = len(self.el)
        comp = [[] for _ in range(N)]
        topt = (self.top,)
        for i in range(N):
            for j in range(i, N):
                if self.pm[i] & self.pm[j]:
                    continue
                if self.joinf(self.el[i], self.el[j]) == topt:
                    comp[i].append(j)
                    if j != i:
                        comp[j].append(i)
        self._comp = comp
        return comp

    def uncomplemented(self):
        return [i for i, c in enumerate(self.complements()) if not c]


def stable_parts(allparts, perm):
    return [p for p in allparts if map_part(p, perm) == p]


def build_M(n, up, tau, allparts):
    return [p for p in stable_parts(allparts, tau) if is_acyclic(p, up)]


# ---------------------------------------------------------------- cl(Fix h)


def nullspace(rows, n):
    """Basis of {x in Q^n : rows x = 0} (exact)."""
    A = [[Fraction(v) for v in r] for r in rows]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        A[r] = [v / A[r][c] for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * n
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -A[i][f]
        basis.append(v)
    return basis


def clfix(eps, perm, n):
    """cl(Fix h) for h = eps*perm acting by (hx)_{perm i} = eps x_i on R^n_0."""
    rows = []
    for i in range(n):
        r = [0] * n
        r[perm[i]] += 1
        r[i] -= eps
        rows.append(r)
    rows.append([1] * n)
    B = nullspace(rows, n)
    blocks = []
    assigned = [False] * n
    for i in range(n):
        if assigned[i]:
            continue
        b = 0
        for j in range(n):
            if not assigned[j] and all(v[i] == v[j] for v in B):
                b |= 1 << j
                assigned[j] = True
        blocks.append(b)
    return tuple(sorted(blocks))


def clfix_formula_minus(perm):
    """The explicit form of S4 for cl(Fix(-perm)): one block of all points on
    odd cycles, two parity classes per even cycle."""
    odd = 0
    blocks = []
    for c in cycles(perm):
        if len(c) % 2:
            for i in c:
                odd |= 1 << i
        else:
            blocks.append(sum(1 << c[t] for t in range(0, len(c), 2)))
            blocks.append(sum(1 << c[t] for t in range(1, len(c), 2)))
    if odd:
        blocks.append(odd)
    return tuple(sorted(blocks))


# ---------------------------------------------------------------- criteria


def orbit_len_of_block(K, tau):
    s, C = 1, map_mask(K, tau)
    while C != K:
        C = map_mask(C, tau)
        s += 1
    return s


def zero_plus(n, up, tau):
    o = order(tau)
    kap = components(n, up)
    free = all(orbit_len_of_block(K, tau) == o for K in kap)
    return (not squarefree(o)) or (not free)


def ta_status(n, up, tau):
    """Return the first failing condition among 'TA1'..'TA4', or None."""
    cs = cycles(tau)
    lam = sorted(set(len(c) for c in cs))
    m = next((m for m in range(1, n + 1, 2) if all(l in (m, 2 * m) for l in lam)), None)
    if m is None or not squarefree(m):
        return "TA1"
    kap = components(n, up)
    if any(orbit_len_of_block(K, tau) not in (m, 2 * m) for K in kap):
        return "TA2"
    O = sum(1 << i for c in cs if len(c) % 2 for i in c)
    tm = power(tau, m)
    for K in kap:
        if popcount((K | map_mask(K, tm)) & O) > 1:
            return "TA3"
    has_even = any(len(c) % 2 == 0 for c in cs)
    if O and has_even:
        iso = sum(K for K in kap if popcount(K) == 1)
        if not any(len(c) % 2 and any(not (iso >> i & 1) for i in c) for c in cs):
            return "TA4"
    return None


def ta_status_no_ta4(n, up, tau):
    s = ta_status(n, up, tau)
    return None if s == "TA4" else s


def odd_m(lam):
    return next((m for m in range(1, 2 * max(lam) + 1, 2) if all(l in (m, 2 * m) for l in lam)), None)


def witness(n, up, eps, tau, variant="table"):
    """Table W of the note, implemented from its text.  Returns (row, W)."""
    if eps == +1:
        o = order(tau)
        kap = components(n, up)
        free = all(orbit_len_of_block(K, tau) == o for K in kap)
        if not free:
            return "W+1", cyc_part(tau)
        if not squarefree(o):
            if variant == "clfix":
                return "W+2", clfix(+1, tau, n)
            p = least_square_prime(o)
            return "W+2", cyc_part(power(tau, o // p))
        return None, None
    st = ta_status(n, up, tau)
    if st is None:
        return None, None
    c = clfix(-1, tau, n)
    if variant == "clfix" and st != "TA4":
        return "W-" + st[-1], c
    if st == "TA1":
        lam = sorted(set(len(cy) for cy in cycles(tau)))
        m = odd_m(lam)
        if m is not None and variant != "k2":
            k = 2 * m // least_square_prime(m)
        else:
            k = 2
        return "W-1", cyc_part(power(tau, k))
    if st in ("TA2", "TA3"):
        return "W-" + st[-1], c
    # TA4
    O = sum(1 << i for cy in cycles(tau) if len(cy) % 2 for i in cy)
    Q = ((1 << n) - 1) & ~O
    if variant == "clfix":
        return "W-4", c
    return "W-4", tuple(sorted([Q] + [1 << i for i in bits(O)]))


def lemma_c_ii(cyclens, lams, h):
    for s in range(1, max(cyclens) + 1):
        if math.gcd(s, h) == 1 and all(L % s == 0 for L in lams) and \
                all(l // math.gcd(l, h) == s for l in cyclens):
            return True
    return False


# ---------------------------------------------------------------- sweep


def analyse_pair(n, up, eps, tau, allparts, stats, fails, kafull=True, variant="table",
                 crit_no_ta4=False, joinf=None):
    elems = build_M(n, up, tau, allparts)
    L = Lat(n, up, elems, joinf)
    mu = L.mu()
    comp = L.complements()
    unc = [i for i, c in enumerate(comp) if not c]
    key = "+" if eps == 1 else "-"
    stats["pairs" + key] += 1
    zero = (mu == 0)
    stats["zeros" + key] += zero
    tag = f"n={n} {key}{tau} P={[(i, j) for i in range(n) for j in bits(up[i])]}"
    # CR_V, both directions
    if zero != bool(unc):
        fails.append("CR_V " + tag + f" mu={mu} unc={len(unc)}")
    # criterion
    if eps == 1:
        crit = zero_plus(n, up, tau)
    else:
        crit = (ta_status_no_ta4 if crit_no_ta4 else ta_status)(n, up, tau) is not None
    if crit != zero:
        fails.append("CRIT " + tag + f" mu={mu}")
    # witness
    row, W = witness(n, up, eps, tau, variant)
    if zero:
        if row is None:
            fails.append("NOROW " + tag)
        else:
            stats["row " + row] += 1
            if W not in L.idx:
                fails.append("W_NOT_IN_M " + row + " " + tag)
            elif comp[L.idx[W]]:
                fails.append("W_COMPLEMENTED " + row + " " + tag)
            c = clfix(eps, tau, n)
            if comp[L.idx[c]]:
                stats["clfix complemented on zero, " + row] += 1
    elif row is not None:
        fails.append("ROW_ON_NONZERO " + tag)
    if variant != "table" or crit_no_ta4 or joinf is not None:
        return
    # S4: every power g^k, exact linear algebra
    kap = components(n, up)
    kapm = pairmask(kap, n)
    o = order(tau)
    c = clfix(eps, tau, n)
    if eps == -1 and c != clfix_formula_minus(tau):
        fails.append("S4_FORMULA " + tag)
    for k in range(1, 2 * o + 1):
        e = eps ** k
        tk = power(tau, k)
        ck = clfix(e, tk, n)
        if e == 1 and ck != cyc_part(tk):
            fails.append(f"S4_CYC k={k} " + tag)
        if ck not in L.idx:
            fails.append(f"S4_NOT_IN_M k={k} " + tag)
            continue
        if any(up[i] & b for b in ck for i in bits(b)):
            fails.append(f"S4_RELATION k={k} " + tag)
        ci = L.idx[ck]
        if pairmask(ck, n) & ~pairmask(c, n):
            fails.append(f"S4_NOT_BELOW_C k={k} " + tag)
        # Lemma C against the lattice, for orbit partitions
        if e == 1:
            h = math.gcd(k, o)
            lams = [orbit_len_of_block(K, tau) for K in kap]
            pred = lemma_c_ii([len(cy) for cy in cycles(tau)], lams, h)
            got = bool(comp[ci])
            stats["lemmaC checks"] += 1
            stats["lemmaC complemented"] += got
            if pred != got:
                fails.append(f"LEMMA_C k={k} pred={pred} got={got} " + tag)
    # Lemma K_A: complements of every w <= c (or of the cl(Fix g^k) only)
    cm = pairmask(c, n)
    targets = range(len(L.el)) if kafull else \
        [L.idx[clfix(eps ** k, power(tau, k), n)] for k in range(1, 2 * o + 1)]
    for wi in targets:
        if L.pm[wi] & ~cm:
            continue
        for xi in comp[wi]:
            stats["K_A complements checked"] += 1
            if kapm & ~L.pm[xi]:
                fails.append("K_A " + tag + f" w={L.el[wi]} x={L.el[xi]}")
            j = partition_join(L.el[xi], L.el[wi])
            if j != (L.top,):
                fails.append("K_A_JOIN " + tag)


def sweep(nmin, nmax, reps, budget, kafull_nmax, variant="table", crit_no_ta4=False,
          joinf_name=None, verbose=True):
    from collections import Counter
    t0 = time.time()
    total_fails = []
    per_n = {}
    unrun = False
    for n in range(nmin, nmax + 1):
        allparts = set_partitions(n)
        stats = Counter()
        fails = []
        for up in reps[n]:
            if time.time() - t0 > budget:
                unrun = True
                break
            auts = automorphisms(n, up, False)
            antis = automorphisms(n, up, True)
            joinf = None
            if joinf_name == "plain":
                joinf = partition_join
            for eps, taus in ((+1, auts), (-1, antis)):
                for tau in conj_reps(auts, taus):
                    analyse_pair(n, up, eps, tau, allparts, stats, fails,
                                 kafull=(n <= kafull_nmax), variant=variant,
                                 crit_no_ta4=crit_no_ta4, joinf=joinf)
        per_n[n] = (stats, fails)
        total_fails += fails
        if verbose:
            rows = " / ".join(str(stats["row " + r]) for r in
                              ("W+1", "W+2", "W-1", "W-2", "W-3", "W-4"))
            cl = {k[len("clfix complemented on zero, "):]: v for k, v in stats.items()
                  if k.startswith("clfix complemented")}
            print(f"  n={n}: posets {len(reps[n])}; pairs +{stats['pairs+']} -{stats['pairs-']}; "
                  f"zeros +{stats['zeros+']} -{stats['zeros-']}; rows W+1/W+2/W-1/W-2/W-3/W-4 = {rows}; "
                  f"cl(Fix g) complemented on zeros {sum(cl.values())} {dict(sorted(cl.items()))}; "
                  f"LemmaC {stats['lemmaC checks']} ({stats['lemmaC complemented']} complemented); "
                  f"K_A complements {stats['K_A complements checked']} "
                  f"({'all w <= c' if n <= kafull_nmax else 'w = cl(Fix g^k)'}); "
                  f"failures {len(fails)}  [{time.time() - t0:.0f}s]")
            for f in fails[:5]:
                print("    " + f)
            sys.stdout.flush()
        if unrun:
            print(f"  UNRUN: budget exhausted during n={n}")
            break
    return per_n, total_fails, unrun


# ---------------------------------------------------------------- [LC]


def lemma_c_bruteforce(nmax):
    """Lemma C (i) <=> (ii) without posets: every cycle type, every
    sigma-stable kappa, every h | o; (i) by direct search."""
    checks = agree = pos = 0
    for n in range(1, nmax + 1):
        allparts = set_partitions(n)
        pms = {p: pairmask(p, n) for p in allparts}
        top = ((1 << n) - 1,)
        for lam in partitions_int(n):
            sigma, start = [], 0
            for l in lam:
                sigma += [start + (t + 1) % l for t in range(l)]
                start += l
            sigma = tuple(sigma)
            o = order(sigma)
            stab = stable_parts(allparts, sigma)
            for kap in stab:
                km = pms[kap]
                lams = [orbit_len_of_block(K, sigma) for K in kap]
                above = [x for x in stab if km & ~pms[x] == 0]
                for h in [d for d in range(1, o + 1) if o % d == 0]:
                    w = cyc_part(power(sigma, h))
                    wm = pms[w]
                    direct = any(pms[x] & wm == 0 and partition_join(x, w) == top for x in above)
                    pred = lemma_c_ii(list(lam), lams, h)
                    checks += 1
                    agree += (direct == pred)
                    pos += direct
                    if direct != pred:
                        print(f"    LEMMA C MISMATCH sigma={lam} kappa={kap} h={h} direct={direct}")
    return checks, agree, pos


def partitions_int(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions_int(n - k, k):
            yield (k,) + rest


# ---------------------------------------------------------------- [BIG]


def perm_from_cycle_type(lam):
    sigma, start = [], 0
    for l in lam:
        sigma += [start + (t + 1) % l for t in range(l)]
        start += l
    return tuple(sigma)


def complement_search_antichain(lam, k, max_states=2_000_000):
    """Antichain on n = sum(lam) points, tau of cycle type lam (any sign:
    for the antichain M = all tau-stable partitions, and by S2 the join is
    the partition join).  W = cyc(tau^k).  Enumerate every tau-stable
    partition x with x ^ W = 0 (BFS over joins with the partitions generated
    by a single <tau>-orbit of pairs; any tau-stable partition is the join of
    the orbit-partitions of its pairs, and x ^ W = 0 is inherited downward,
    so pruning is exact).  Return (#states, #complements found)."""
    n = sum(lam)
    tau = perm_from_cycle_type(lam)
    W = cyc_part(power(tau, k))
    Wblock = [0] * n
    for bi, b in enumerate(W):
        for i in bits(b):
            Wblock[i] = bi
    # orbits of tau on unordered pairs
    seen = set()
    atoms = []
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in seen:
                continue
            orb = []
            a, b = i, j
            while (min(a, b), max(a, b)) not in seen:
                seen.add((min(a, b), max(a, b)))
                orb.append((min(a, b), max(a, b)))
                a, b = tau[a], tau[b]
            if any(Wblock[a] == Wblock[b] for a, b in orb):
                continue  # this orbit already meets W
            atoms.append(orb)

    def join_pairs(part, pairs):
        parent = {}
        lab = [0] * n
        for bi, b in enumerate(part):
            for i in bits(b):
                lab[i] = bi
        par = list(range(len(part)))

        def f(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for a, b in pairs:
            ra, rb = f(lab[a]), f(lab[b])
            if ra != rb:
                par[ra] = rb
        merged = {}
        for bi, b in enumerate(part):
            r = f(bi)
            merged[r] = merged.get(r, 0) | b
        return tuple(sorted(merged.values()))

    def meets_W_trivially(part):
        for b in part:
            ws = [Wblock[i] for i in bits(b)]
            if len(ws) != len(set(ws)):
                return False
        return True

    bottom = tuple(sorted(1 << i for i in range(n)))
    states = {bottom}
    frontier = [bottom]
    while frontier:
        nxt = []
        for x in frontier:
            for orb in atoms:
                y = join_pairs(x, orb)
                if y not in states and meets_W_trivially(y):
                    states.add(y)
                    nxt.append(y)
                    if len(states) > max_states:
                        raise RuntimeError("state budget exceeded")
        frontier = nxt
    topt = ((1 << n) - 1,)
    found = sum(1 for x in states if partition_join(x, W) == topt)
    stable = all(map_part(x, tau) == x for x in states)
    return len(states), found, stable, W


# ---------------------------------------------------------------- [CTL]


def controls(reps):
    ok = True
    want = [1, 1, 2, 5, 16, 63, 318, 2045]
    got = [len(reps[n]) for n in range(len(reps))]
    c1 = got == want[:len(got)]
    print(f"  poset counts n=0..{len(got) - 1}: {got} (OEIS A000112 {want[:len(got)]}): {c1}")
    ok &= c1
    # Pi_n: mu = (-1)^{n-1} (n-1)!
    for n in range(1, 7):
        anti = [0] * n
        L = Lat(n, anti, set_partitions(n))
        c = L.mu() == (-1) ** (n - 1) * math.factorial(n - 1)
        ok &= c
    print(f"  mu(Pi_n) = (-1)^(n-1)(n-1)! for n = 1..6: {ok}")
    # Pi_4^(1234): chain 0 < 13|24 < 1, mu = 0, middle uncomplemented
    tau = (1, 2, 3, 0)
    L = Lat(4, [0] * 4, stable_parts(set_partitions(4), tau))
    els = sorted(L.el, key=lambda p: -len(p))
    c2 = len(els) == 3 and L.mu() == 0 and L.uncomplemented() == [1] and els[1] == (0b0101, 0b1010)
    print(f"  Pi_4^(1234) = chain 0 < 13|24 < 1, mu 0, middle uncomplemented: {c2}")
    ok &= c2
    # Pi_4 complemented
    L = Lat(4, [0] * 4, set_partitions(4))
    c3 = len(L.el) == 15 and L.mu() == -6 and L.uncomplemented() == []
    print(f"  Pi_4: 15 elements, mu -6, complemented: {c3}")
    ok &= c3
    # 3-chain: OP = B_2, mu 1
    up = close(3, [0b010, 0b100, 0])
    L = Lat(3, up, build_M(3, up, (0, 1, 2), set_partitions(3)))
    c4 = len(L.el) == 4 and L.mu() == 1
    print(f"  OP(3-chain) has 4 elements, mu 1: {c4}")
    ok &= c4
    # F6: P = {0<2, 1<3}: join of 03|1|2 and 12|0|3 is 1, partition join 03|12 is cyclic
    up = [0b0100, 0b1000, 0, 0]
    x = tuple(sorted([0b1001, 0b0010, 0b0100]))
    y = tuple(sorted([0b0110, 0b0001, 0b1000]))
    c5 = join_M(x, y, up) == (0b1111,) and partition_join(x, y) == tuple(sorted([0b1001, 0b0110]))
    print(f"  F6 example: acyclic join is 1, partition join is 03|12: {c5}")
    ok &= c5
    # fast join = brute-force least upper bound in M, every pair, every (P, tau), n <= 5
    nb = bad = 0
    for n in range(3, 6):
        allp = set_partitions(n)
        for up in reps[n]:
            auts = automorphisms(n, up, False)
            antis = automorphisms(n, up, True)
            for tau in conj_reps(auts, auts) + conj_reps(auts, antis):
                L = Lat(n, up, build_M(n, up, tau, allp))
                N = len(L.el)
                for a in range(N):
                    for b in range(a, N):
                        ubs = [z for z in range(N) if L.leq(a, z) and L.leq(b, z)]
                        lub = [z for z in ubs if all(L.leq(z, u) for u in ubs)]
                        nb += 1
                        if len(lub) != 1 or L.el[lub[0]] != join_M(L.el[a], L.el[b], up):
                            bad += 1
                        # meet is the common refinement and lies in M
                        lbs = [z for z in range(N) if L.leq(z, a) and L.leq(z, b)]
                        glb = [z for z in lbs if all(L.leq(u, z) for u in lbs)]
                        if len(glb) != 1 or L.pm[glb[0]] != L.pm[a] & L.pm[b]:
                            bad += 1
    c6 = bad == 0
    print(f"  fast join / meet = brute-force lub / glb on {nb} pairs of elements, n <= 5: {c6} ({bad} bad)")
    ok &= c6
    return ok


# ---------------------------------------------------------------- [COUNT]


def count_unreduced(reps, nmax):
    tot = 0
    for n in range(3, nmax + 1):
        a = b = 0
        for up in reps[n]:
            a += len(automorphisms(n, up, False))
            b += len(automorphisms(n, up, True))
        print(f"  n={n}: automorphism pairs {a}, anti-automorphism pairs {b}, total {a + b}")
        tot += a + b
    print(f"  total n=3..{nmax}: {tot}")
    return tot


# ---------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--kafull-nmax", type=int, default=6)
    ap.add_argument("--budget", type=float, default=3600)
    ap.add_argument("--skip-big", action="store_true")
    args = ap.parse_args()
    ok = True
    t0 = time.time()
    reps = posets_upto_iso(args.nmax)
    print("[CTL]")
    ok &= controls(reps)

    print("[COUNT] lattices OP(P)^{+-tau}, all tau (no conjugacy reduction), posets up to iso")
    tot6 = count_unreduced(reps, min(6, args.nmax))

    print("[SWEEP]")
    per_n, fails, unrun = sweep(3, args.nmax, reps, args.budget, args.kafull_nmax)
    ok &= not fails and not unrun
    tot = {k: sum(per_n[n][0][k] for n in per_n) for k in ("pairs+", "pairs-", "zeros+", "zeros-")}
    print(f"  totals: {tot}; failures {len(fails)}")

    print("[NEG] positive controls: each MUST report failures")
    nneg = min(args.nmax, 6)
    for label, kw in (("witness cl(Fix g) in every row", dict(variant="clfix")),
                      ("criterion without (TA4)", dict(crit_no_ta4=True)),
                      ("plain partition join", dict(joinf_name="plain"))):
        _, f, _ = sweep(3, nneg, reps, 1e9, 0, verbose=False, **kw)
        kinds = sorted(set(x.split()[0] for x in f))
        print(f"  {label}: {len(f)} failures {kinds} -> control {'fires' if f else 'DID NOT FIRE'}")
        ok &= bool(f)
    # k = 2 vs k = 6 on the antichain of 9 with tau a 9-cycle (the "k = 2 always
    # in row W-1" control cannot fire at n <= 7: no odd non-squarefree m fits)
    for k, want_comp in ((2, True), (6, False)):
        st, found, stable, W = complement_search_antichain((9,), k)
        print(f"  antichain 9, tau=(9), W=cyc(tau^{k}) ({len(W)} blocks): {st} candidate x, "
              f"{found} complements (expect {'>0' if want_comp else '0'})")
        ok &= (found > 0) == want_comp and stable

    print("[LC] Lemma C by brute force, no posets, n <= 7")
    checks, agree, pos = lemma_c_bruteforce(7)
    print(f"  {checks} (sigma, kappa, h) triples, {agree} agree, {pos} complemented")
    ok &= checks == agree

    if not args.skip_big:
        print("[BIG] row W-1 with m odd not squarefree (antichain; covers every P with this tau, see note)")
        cases = [((9,), 6, False), ((18,), 6, False), ((9, 18), 6, False),
                 ((9, 18), 2, True), ((9, 9, 18), 6, False), ((25,), 10, False)]
        for lam, k, expect in cases:
            ta = ta_status(sum(lam), [0] * sum(lam), perm_from_cycle_type(lam))
            o = order(perm_from_cycle_type(lam))
            h = math.gcd(k, o)
            pred = lemma_c_ii(list(lam), list(lam), h)  # antichain: lambda_K = cycle lengths
            t1 = time.time()
            try:
                st, found, stable, W = complement_search_antichain(lam, k)
            except RuntimeError as e:
                print(f"  tau={lam} k={k}: {e}")
                ok = False
                continue
            line = (f"  tau={lam} (n={sum(lam)}, {ta} fails) k={k} h={h}: W has {len(W)} blocks; "
                    f"{st} tau-stable x with x^W=0; {found} complements; Lemma C(ii) predicts "
                    f"{'complemented' if pred else 'uncomplemented'} [{time.time() - t1:.1f}s]")
            print(line)
            good = stable and ((found > 0) == pred)
            if expect is not None:
                good &= (found > 0) == expect
            ok &= good

    print(f"[time] {time.time() - t0:.0f}s")
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
