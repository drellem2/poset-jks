"""Independent audit of notes/promotion_on_R_P.md.

Imports nothing from the rest of compute/.  Standard library only.

Two independent ways of deciding whether promotion d preserves R_P on a
disconnected poset P:

  [def]  membership straight from the definition
           R_P = span{ s sh t : S a nonempty proper union of components,
                                s in Lin(P|S), t in Lin(P|S^c) },
         by sparse Gaussian elimination modulo two primes, one graded piece
         (restriction tuple) at a time.  Every generator r of R_P is tested
         (or until the first failure), in this script's own order.  Run where
         the graded pieces are small enough (dimension <= --dim-limit).

  [cert] the note's explicit generator r and Lie-bracket functional, with
         the vanishing on R_P checked against EVERY defining generator s sh t
         (no appeal to Ree's theorem), and the value on d r computed from
         promotion by toggles.  Rigorous over Z.  Run on every poset.

Posets are generated up to isomorphism by adding a new MINIMAL element whose
up-set is an order filter, with a refined-partition canonical form.
"""

import argparse
import itertools
import random
import sys
from collections import defaultdict

# ---------------------------------------------------------------- posets

def closure(n, rel):
    lt = [[False] * n for _ in range(n)]
    for a, b in rel:
        lt[a][b] = True
    for k in range(n):
        for i in range(n):
            if lt[i][k]:
                for j in range(n):
                    if lt[k][j]:
                        lt[i][j] = True
    return lt


def canon(n, lt):
    """Canonical form: lexicographically least relation string over all
    relabellings that respect a refined invariant partition."""
    inv = [(sum(lt[j][i] for j in range(n)), sum(lt[i][j] for j in range(n)))
           for i in range(n)]
    keys = sorted(set(inv))
    inv = [keys.index(x) for x in inv]
    for _ in range(n):
        new = [(inv[i], tuple(sorted(inv[j] for j in range(n) if lt[j][i])),
                tuple(sorted(inv[j] for j in range(n) if lt[i][j])))
               for i in range(n)]
        keys = sorted(set(new))
        new = [keys.index(x) for x in new]
        done = len(keys) == len(set(inv))
        inv = new
        if done:
            break
    classes = defaultdict(list)
    for i in range(n):
        classes[inv[i]].append(i)
    blocks = [classes[c] for c in sorted(classes)]
    best = None
    for choice in itertools.product(*[itertools.permutations(b) for b in blocks]):
        order = [x for blk in choice for x in blk]
        code = tuple(lt[order[i]][order[j]] for i in range(n) for j in range(n))
        if best is None or code < best:
            best = code
    return best


def from_code(n, code):
    return [[code[i * n + j] for j in range(n)] for i in range(n)]


def all_posets(nmax):
    """dict n -> list of canonical codes, all posets up to iso."""
    res = {1: [canon(1, [[False]])]}
    for n in range(1, nmax):
        seen = set()
        for code in res[n]:
            lt = from_code(n, code)
            # order filters (up-closed sets) of the old poset
            for mask in range(1 << n):
                U = [i for i in range(n) if mask >> i & 1]
                if any(lt[u][j] and not mask >> j & 1 for u in U for j in range(n)):
                    continue
                m = n + 1
                new = [[False] * m for _ in range(m)]
                for i in range(n):
                    for j in range(n):
                        new[i + 1][j + 1] = lt[i][j]
                for u in U:
                    new[0][u + 1] = True
                seen.add(canon(m, new))
        res[n + 1] = sorted(seen)
    return res


def is_connected(n, lt):
    seen = {0}
    stack = [0]
    while stack:
        a = stack.pop()
        for b in range(n):
            if b not in seen and (lt[a][b] or lt[b][a]):
                seen.add(b)
                stack.append(b)
    return len(seen) == n


def is_chain(n, lt):
    return all(lt[i][j] or lt[j][i] for i in range(n) for j in range(i + 1, n))


def disconnected_posets(conn, n):
    """Multisets of >= 2 connected posets (codes) of total size n.
    conn: dict size -> sorted list of codes.  Yields list of (size, code)."""
    items = [(s, c) for s in sorted(conn) for c in conn[s]]
    out = []

    def rec(start, remaining, acc):
        if remaining == 0:
            if len(acc) >= 2:
                out.append(list(acc))
            return
        for idx in range(start, len(items)):
            s, c = items[idx]
            if s <= remaining:
                acc.append((s, c))
                rec(idx, remaining - s, acc)
                acc.pop()
    rec(0, n, [])
    return out


class Poset:
    """Disjoint union of components, labelled 0..n-1 consecutively."""

    def __init__(self, comps):
        self.n = sum(s for s, _ in comps)
        n = self.n
        self.lt = [[False] * n for _ in range(n)]
        self.comps = []
        self.chain = []
        off = 0
        for s, code in comps:
            lt = from_code(s, code)
            for i in range(s):
                for j in range(s):
                    self.lt[off + i][off + j] = lt[i][j]
            self.comps.append(tuple(range(off, off + s)))
            self.chain.append(is_chain(s, lt))
            off += s
        self.comp_of = {}
        for ci, T in enumerate(self.comps):
            for x in T:
                self.comp_of[x] = ci
        self.sizes = tuple(s for s, _ in comps)

    def lin(self, letters):
        letters = tuple(letters)
        out = []

        def rec(rem, acc):
            if not rem:
                out.append(tuple(acc))
                return
            for x in rem:
                if not any(self.lt[y][x] for y in rem if y != x):
                    acc.append(x)
                    rec(tuple(y for y in rem if y != x), acc)
                    acc.pop()
        rec(letters, [])
        return out

    def promote(self, w):
        w = list(w)
        for i in range(len(w) - 1):
            a, b = w[i], w[i + 1]
            if not self.lt[a][b] and not self.lt[b][a]:
                w[i], w[i + 1] = b, a
        return tuple(w)

    def is_lin(self, w):
        pos = {x: i for i, x in enumerate(w)}
        return all(not self.lt[a][b] or pos[a] < pos[b]
                   for a in w for b in w)

    def unions(self):
        k = len(self.comps)
        for mask in range(1, (1 << k) - 1):
            S = tuple(x for ci in range(k) if mask >> ci & 1 for x in self.comps[ci])
            yield mask, S


def shuffle(s, t):
    """s sh t as a list of words (all distinct: disjoint letters)."""
    n = len(s) + len(t)
    out = []
    for pos in itertools.combinations(range(n), len(s)):
        w = [None] * n
        ps = set(pos)
        i = j = 0
        for p in range(n):
            if p in ps:
                w[p] = s[i]; i += 1
            else:
                w[p] = t[j]; j += 1
        out.append(tuple(w))
    return out


def restrict(w, S):
    S = set(S)
    return tuple(x for x in w if x in S)


def rho(c):
    """right-normed bracket [c1,[c2,...[c_{m-1},c_m]]] expanded, dict word->coef."""
    cur = {(c[-1],): 1}
    for x in reversed(c[:-1]):
        new = defaultdict(int)
        for u, a in cur.items():
            new[(x,) + u] += a
            new[u + (x,)] -= a
        cur = {u: a for u, a in new.items() if a}
    return cur


def promote_vec(P, vec):
    out = defaultdict(int)
    for w, a in vec.items():
        out[P.promote(w)] += a
    return {w: a for w, a in out.items() if a}


def pair(f, vec):
    return sum(a * vec.get(w, 0) for w, a in f.items())

# ------------------------------------------------------------ [def] method

PRIMES = (2147483647, 1000000007)


class Echelon:
    def __init__(self, p):
        self.p = p
        self.rows = {}  # pivot -> row dict (pivot coefficient 1)

    def reduce(self, v):
        p = self.p
        v = {k: a % p for k, a in v.items() if a % p}
        while v:
            piv = min(v)
            if piv not in self.rows:
                return v, piv
            a = v[piv]
            for k, b in self.rows[piv].items():
                v[k] = (v.get(k, 0) - a * b) % p
                if not v[k]:
                    del v[k]
        return v, None

    def add(self, v):
        r, piv = self.reduce(v)
        if piv is None:
            return False
        inv = pow(r[piv], self.p - 2, self.p)
        self.rows[piv] = {k: a * inv % self.p for k, a in r.items()}
        return True


def grade(P, w):
    return tuple(restrict(w, T) for T in P.comps)


def grade_generators(P, g):
    """All defining generators of R_P whose words have restriction tuple g
    (and, as a check, every generator is homogeneous)."""
    k = len(P.comps)
    gens = []
    for mask, S in P.unions():
        Sc = tuple(x for x in range(P.n) if x not in set(S))
        xs = [g[ci] for ci in range(k) if mask >> ci & 1]
        xt = [g[ci] for ci in range(k) if not mask >> ci & 1]
        for s in multishuffle(xs):
            for t in multishuffle(xt):
                gens.append(shuffle(s, t))
    return gens


def multishuffle(words):
    acc = [()]
    for u in words:
        acc = [w for v in acc for w in shuffle(v, u)]
    return acc


def multinomial(sizes):
    from math import factorial
    r = factorial(sum(sizes))
    for s in sizes:
        r //= factorial(s)
    return r


class DefMembership:
    def __init__(self, P):
        self.P = P
        self.cache = {}

    def ech(self, g):
        if g not in self.cache:
            gens = grade_generators(self.P, g)
            idx = {}
            for gen in gens:
                for w in gen:
                    assert grade(self.P, w) == g  # homogeneity
            words = sorted({w for gen in gens for w in gen} |
                           set(multishuffle(list(g))))
            idx = {w: i for i, w in enumerate(words)}
            echs = []
            for p in PRIMES:
                E = Echelon(p)
                for gen in gens:
                    E.add({idx[w]: 1 for w in gen})
                echs.append(E)
            self.cache[g] = (idx, echs)
        return self.cache[g]

    def contains(self, vec):
        """True iff vec in R_P modulo both primes (they must agree)."""
        by = defaultdict(dict)
        for w, a in vec.items():
            by[grade(self.P, w)][w] = a
        ans = True
        for g, piece in by.items():
            idx, echs = self.ech(g)
            res = [E.reduce({idx[w]: a for w, a in piece.items()})[1] is None
                   for E in echs]
            assert res[0] == res[1], "primes disagree"
            ans = ans and res[0]
        return ans


def generators(P):
    for mask, S in P.unions():
        Sc = tuple(x for x in range(P.n) if x not in set(S))
        for s in P.lin(S):
            for t in P.lin(Sc):
                yield {w: 1 for w in shuffle(s, t)}


def def_preserves(P):
    D = DefMembership(P)
    for r in generators(P):
        if not D.contains(promote_vec(P, r)):
            return False
    return True

# ----------------------------------------------------------- [cert] method

def annihilates_RP(P, f):
    """f (dict word->coef, supported anywhere) restricted to Lin P pairs to 0
    with every defining generator s sh t.  Checked from the definition:
    <f, s sh t> = sum of f(w) over w in Lin P with w|S = s and w|S^c = t."""
    supp = {w: a for w, a in f.items() if P.is_lin(w)}
    for mask, S in P.unions():
        Sc = tuple(x for x in range(P.n) if x not in set(S))
        tot = defaultdict(int)
        for w, a in supp.items():
            tot[(restrict(w, S), restrict(w, Sc))] += a
        if any(tot.values()):
            return False
    return True


def certificate(P, ci, s, t):
    """The note's r = s sh t with T = comps[ci], and its functional.
    Returns (case, r, f) with f a dict word->coef."""
    T = P.comps[ci]
    B = tuple(x for x in range(P.n) if x not in set(T))
    r = {w: 1 for w in shuffle(s, t)}
    if not P.chain[ci]:
        dTs = P.promote(s)  # toggles on s alone = promotion of P|T
        s2, z = dTs[:-1], dTs[-1]
        f = rho(s2 + t + (z,))
        # restrict to the graded piece  T-part = d_T(s)
        f = {w: a for w, a in f.items() if restrict(w, T) == dTs}
        return 'A', r, f
    f = rho(s[:-1] + t + (s[-1],))
    return 'B', r, f


def cert_check(P, ci, s, t):
    case, r, f = certificate(P, ci, s, t)
    val = pair(f, promote_vec(P, r))
    return case, annihilates_RP(P, f), val

# ------------------------------------------------------------------ driver

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=8)
    ap.add_argument('--dim-limit', type=int, default=1680)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    ok = True

    def check(tag, cond, msg):
        nonlocal ok
        print(f'[{tag}] {"ok  " if cond else "FAIL"} {msg}')
        ok = ok and cond

    allp = all_posets(max(1, min(a.nmax - 1, 7)))
    A000112 = [1, 1, 2, 5, 16, 63, 318, 2045, 16999]
    A000608 = [0, 1, 1, 3, 10, 44, 238, 1650, 14512]
    conn = {}
    for n, codes in allp.items():
        conn[n] = [c for c in codes if is_connected(n, from_code(n, c))]
        check('count', len(codes) == A000112[n] and len(conn[n]) == A000608[n],
              f'n={n}: {len(codes)} posets, {len(conn[n])} connected (OEIS A000112, A000608)')

    # Ree / triangularity sanity, n <= 5, from the definition of shuffles
    for n in range(2, 6):
        good = True
        for c in itertools.permutations(range(n)):
            f = rho(c)
            # Lemma 2 triangularity: words ending in c[-1]
            ends = {w: a for w, a in f.items() if w[-1] == c[-1]}
            good &= ends == {c: 1}
            for j in range(1, n):
                for S in itertools.combinations(range(n), j):
                    Sc = tuple(x for x in range(n) if x not in S)
                    for s in [S, S[::-1]]:
                        for t in [Sc, Sc[::-1]]:
                            good &= pair(f, {w: 1 for w in shuffle(s, t)}) == 0
        check('ree', good, f'n={n}: rho(c) has the single word c ending in c_n, and kills sampled shuffles')

    total = fam_total = 0
    nA = nB = 0
    cum6 = [0, 0]
    def_cover = 0
    def_yes = defaultdict(int)
    def_no = defaultdict(int)
    for n in range(2, a.nmax + 1):
        posets = disconnected_posets(conn, n)
        fam = 0
        fam_sizes = []
        bad = []
        for comps in posets:
            P = Poset(comps)
            two_chains = len(P.comps) == 2 and all(P.chain)
            # [def] decision where the graded pieces are small
            if multinomial(P.sizes) <= a.dim_limit:
                def_cover += 1
                pres = def_preserves(P)
                def_yes[n] += pres
                def_no[n] += not pres
                if pres != two_chains:
                    bad.append(('def', comps))
            # [cert] for every poset outside the family
            if two_chains:
                fam += 1
                fam_sizes.append(tuple(sorted(P.sizes)))
                # 'if' from the definition: R_P is the line through sum Lin P
                lin = P.lin(range(n))
                vecs = {tuple(sorted(r)) for r in generators(P)}
                if vecs != {tuple(sorted(lin))}:
                    bad.append(('if', comps))
                continue
            nonchain = [ci for ci in range(len(P.comps)) if not P.chain[ci]]
            cis = nonchain if nonchain else list(range(len(P.comps)))
            exhaustive = n <= 6
            for ci in (cis if exhaustive else [rng.choice(cis)]):
                T = P.comps[ci]
                B = tuple(x for x in range(n) if x not in set(T))
                LT, LB = P.lin(T), P.lin(B)
                pairs = ([(s, t) for s in LT for t in LB] if exhaustive
                         else [(rng.choice(LT), rng.choice(LB)) for _ in range(2)])
                for s, t in pairs:
                    case, ann, val = cert_check(P, ci, s, t)
                    if not (ann and val == 1):
                        bad.append(('cert', comps, s, t, ann, val))
            if nonchain:
                nA += 1
            else:
                nB += 1
        total += len(posets)
        fam_total += fam
        if n <= 6:
            cum6[0] += def_yes[n] + def_no[n]; cum6[1] += def_yes[n]
        check('sweep', not bad,
              f'n={n}: {len(posets)} disconnected, {fam} two-chain, sizes {sorted(set(fam_sizes))}; '
              f'[def] decided {def_yes[n] + def_no[n]}: {def_yes[n]} preserve; failures {bad[:3]}')
    check('total', True, f'{total} disconnected posets n<= {a.nmax}; {fam_total} two-chain; '
          f'certificates: case A {nA}, case B {nB}; [def] decided {def_cover}')
    check('control', cum6 == [108, 9], f'n<=6, [def] from the definition: {cum6[1]} of {cum6[0]} preserve R_P (expect 9 of 108)')

    # negative control: certificate checker must reject a functional that
    # does not vanish on R_P (a plain word), and [def] must reject Sh-violators
    P = Poset([(1, canon(1, [[False]]))] * 3)
    check('ctl', not annihilates_RP(P, {(0, 1, 2): 1}), 'a single word does not annihilate R_{A_3}')
    D = DefMembership(P)
    check('ctl', D.contains({w: 1 for w in shuffle((0,), (1, 2))}) and
          not D.contains({(0, 1, 2): 1}), '[def] accepts a generator and rejects a single word')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
