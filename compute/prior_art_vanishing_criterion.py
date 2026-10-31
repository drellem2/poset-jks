"""Checks behind notes/prior_art_vanishing_criterion.md.

Two statements of the prior-art note are checked by set partitions, with
exact integer arithmetic and no imports from other scripts.

(H) Hanlon's hinge.  For w in S_n acting on the braid arrangement, the
    index set Z*(w) of Formula Z on all chambers is the set of complements
    of the cycle partition cyc (Hanlon's hinge h) in the fixed lattice
    Pi_n^w.  With r = number of cycles of w and every m_X = (r-1)!, Formula Z
    on all chambers reads

        mu(Pi_n^w) = (-1)^(r-1) (r-1)! * sum_{c complement of h} mu_{Pi_n^w}(c, 1).

    Hanlon (Pacific J. Math. 96 (1981), Lemmas 5, 6 and Theorem 4) counts
    j^(m-1) complements, each with mu(c, 1) = mu(j).  The script checks the
    identity, the count o^(r-1), and the value mu(o), for every w with n <= 8.

(D) The -w rule is not the all-chambers rule.  L(A)^{-w} = L(A)^w, so the
    all-chambers value at -w is (-1)^(n-1) times the value at w, and it is
    nonzero iff all cycles of w have one length o with mu(o) != 0 (Stanley
    1982, Lemma 7.1).  Theorem S at -w ("some X in Z*(-w) has mu != 0") is
    computed here from the definition of Z*(-w) in vanishing_criterion.md
    section 4, and compared with both rules.

Order convention: partitions are ordered by refinement, finest = 0, as in
Hanlon and Stanley.  The flat lattice L(A)^g is the dual order, so
mu_{L(A)^g}(0, X_pi) = mu_{Pi^w}(pi, 1).
"""

import sys
from functools import lru_cache
from math import factorial


def num_mobius(k):
    r, p = 1, 2
    while p * p <= k:
        if k % p == 0:
            k //= p
            if k % p == 0:
                return 0
            r = -r
        p += 1
    return -r if k > 1 else r


def set_partitions(elems):
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | {first}] + p[i + 1:]
        yield p + [frozenset([first])]


def canon(p):
    return frozenset(frozenset(b) for b in p)


def perm_of_type(ct):
    w, start = {}, 0
    for k in ct:
        for i in range(k):
            w[start + i] = start + (i + 1) % k
        start += k
    return w


def cycles(w):
    seen, out = set(), []
    for i in sorted(w):
        if i not in seen:
            c, j = [], i
            while j not in seen:
                seen.add(j)
                c.append(j)
                j = w[j]
            out.append(c)
    return out


def partitions_of(n):
    out, ct = [], []

    def rec(rem, mx):
        if rem == 0:
            out.append(list(ct))
            return
        for k in range(min(rem, mx), 0, -1):
            ct.append(k)
            rec(rem - k, k)
            ct.pop()

    rec(n, n)
    return out


class FixedLattice:
    """Pi_n^w: the w-stable set partitions of [n], ordered by refinement."""

    def __init__(self, w):
        n = len(w)
        self.w = w
        self.elems = []
        for p in set_partitions(list(range(n))):
            P = canon(p)
            if canon(frozenset(w[i] for i in b) for b in P) == P:
                self.elems.append(P)
        self.top = canon([frozenset(range(n))])
        self.bot = canon([frozenset([i]) for i in range(n)])
        self.block_of = {P: {i: b for b in P for i in b} for P in self.elems}

    def leq(self, P, Q):  # P finer than Q
        bq = self.block_of[Q]
        return all(len({bq[i] for i in b}) == 1 for b in P)

    def mu_to_top(self, P):
        """mu(P, 1) in Pi_n^w, by the recursion over [P, 1]."""
        up = [Q for Q in self.elems if self.leq(P, Q)]
        up.sort(key=len)  # coarser first: fewer blocks
        mu = {}
        for Q in up:
            if Q == self.top:
                mu[Q] = 1
            else:
                mu[Q] = -sum(mu[R] for R in mu if self.leq(Q, R))
        return mu[P]


def join_is_top(P, Q, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for part in (P, Q):
        for b in part:
            b = sorted(b)
            for x in b[1:]:
                parent[find(x)] = find(b[0])
    return len({find(i) for i in range(n)}) == 1


def meet_is_bottom(P, Q):
    return all(len(a & b) <= 1 for a in P for b in Q)


def check_hanlon(ct):
    """(H) for w of cycle type ct.  Returns (ok, n_complements, mus)."""
    n = sum(ct)
    w = perm_of_type(ct)
    L = FixedLattice(w)
    cyc = canon(frozenset(c) for c in cycles(w))
    r = len(ct)
    comps = [P for P in L.elems if join_is_top(P, cyc, n) and meet_is_bottom(P, cyc)]
    mus = [L.mu_to_top(P) for P in comps]
    lhs = L.mu_to_top(L.bot)
    rhs = (-1) ** (r - 1) * factorial(r - 1) * sum(mus)
    return lhs == rhs, len(comps), mus, lhs


def check_hanlon_wrong_index(ct):
    """Negative control: drop the meet condition (keep only 'join = 1')."""
    n = sum(ct)
    w = perm_of_type(ct)
    L = FixedLattice(w)
    cyc = canon(frozenset(c) for c in cycles(w))
    r = len(ct)
    idx = [P for P in L.elems if join_is_top(P, cyc, n)]
    rhs = (-1) ** (r - 1) * factorial(r - 1) * sum(L.mu_to_top(P) for P in idx)
    return L.mu_to_top(L.bot) == rhs


def zstar_minus(ct):
    """Z*(-w) of vanishing_criterion.md section 4, as set partitions."""
    n = sum(ct)
    w = perm_of_type(ct)
    L = FixedLattice(w)
    cyc = cycles(w)
    odd_pts = {i for c in cyc if len(c) % 2 == 1 for i in c}
    pos = {}
    for c in cyc:
        for k, i in enumerate(c):
            pos[i] = (id(c), k, len(c))

    def tight(i, j):
        if i in odd_pts and j in odd_pts:
            return True
        (ci, ki, li), (cj, kj, _) = pos[i], pos[j]
        return ci == cj and li % 2 == 0 and (ki - kj) % 2 == 0

    out = []
    for P in L.elems:
        # every w-bar orbit of blocks has odd length
        bo = L.block_of[P]
        seen, ok = set(), True
        for b in P:
            if b in seen:
                continue
            k, x = 0, b
            while True:
                seen.add(x)
                k += 1
                x = bo[w[next(iter(x))]]
                if x == b:
                    break
            if k % 2 == 0:
                ok = False
                break
        if not ok:
            continue
        if any(tight(i, j) for b in P for i in b for j in b if i < j):
            continue
        out.append(P)
    return L, out


def some_cone_minus(ct):
    L, Z = zstar_minus(ct)
    return any(L.mu_to_top(P) != 0 for P in Z)


def rule_minus(ct):
    """(A-): cycle lengths in {m, 2m}, m odd squarefree."""
    m = min(k if k % 2 else k // 2 for k in ct)
    return m % 2 == 1 and num_mobius(m) != 0 and all(k in (m, 2 * m) for k in ct)


def rule_all_chambers(ct):
    """Stanley 1982 Lemma 7.1 / Hanlon Thm 4: mu(Pi_n^w) != 0."""
    return len(set(ct)) == 1 and num_mobius(ct[0]) != 0


def main(nmax):
    fails = 0
    print("(H) Formula Z on all chambers, g = w in S_n, vs Hanlon's complements of the hinge")
    for n in range(2, nmax + 1):
        for ct in partitions_of(n):
            ok, nc, mus, lhs = check_hanlon(ct)
            equal = len(set(ct)) == 1
            o, r = ct[0], len(ct)
            if equal:
                shape_ok = nc == o ** (r - 1) and all(m == num_mobius(o) for m in mus)
            else:
                shape_ok = all(m == 0 for m in mus)
            neg = check_hanlon_wrong_index(ct)
            flag = ok and shape_ok
            fails += not flag
            print(f"  w={ct}: mu(Pi^w)={lhs}, #complements={nc}, mu(c,1) values={sorted(set(mus))},"
                  f" identity {'OK' if ok else 'FAIL'}, Hanlon shape {'OK' if shape_ok else 'FAIL'};"
                  f" control without meet condition: {'holds' if neg else 'fails'}")
    print()
    print("(D) -w: Theorem S (from Z*(-w)) vs rule (A-) vs the all-chambers rule")
    extra = []
    for n in range(3, min(nmax, 7) + 1):
        for ct in partitions_of(n):
            s = some_cone_minus(ct)
            a = rule_minus(ct)
            f = rule_all_chambers(ct)
            fails += s != a
            if s and not f:
                extra.append(ct)
            print(f"  -w, w={ct}: Theorem S {int(s)}, rule (A-) {int(a)}, all chambers {int(f)}"
                  f"{'' if s == a else '  FAIL'}")
    print()
    print(f"-w classes nonzero on some cone but zero on all chambers: {len(extra)}: {extra}")
    print()
    print("ALL CHECKS PASSED" if fails == 0 else f"{fails} FAILURES")
    return fails


if __name__ == "__main__":
    nmax = 8
    if "--quick" in sys.argv:
        nmax = 6
    sys.exit(1 if main(nmax) else 0)
