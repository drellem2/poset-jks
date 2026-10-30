#!/usr/bin/env python3
"""Independent audit of notes/literature_novelty_jks_maps.md (mg-350d5).

Written from scratch; shares no code with splitting_cycles.py or
poset_jks_check.py.  Plain Python 3, no dependencies.

Conventions.  A word w = (w_1, ..., w_n) is the permutation i -> w_i.
Left multiplication g*w relabels letters, right multiplication w*s permutes
positions, gamma = (2, 3, ..., n, 1), so w*gamma is w rotated left by one.
Set partitions are frozensets of frozensets.  A top simplex of the order
complex of the proper part of Pi_n is a tuple of n-2 partitions, finest first.

Checks (each prints PASS/FAIL; exit status 0 iff all pass):
  phi      Signed shuffle relations among splitting cycles hold exactly at
           chain level, and rank{rho_s} + rank Sh_n = n!, so
           rho_s -> sgn(s) s  mod Sh_n is an isomorphism (Prop. Phi), n <= NPHI.
  ree      Left-normed brackets are orthogonal to Sh_n and have rank (n-1)!.
  propC    O(P) = O(P^op); Sh_n e_zeta != 0 (explicit witness) and
           Sh_n kappa_n != 0, so no S_n-equivariant J, even one chosen for
           the single chain, satisfies eq. (restrictionlemma).
  conjS    For every unlabeled poset with n <= NS: Lemma D, and
           rank_p{rho_w : w in Lin P} = dim_p ker(boundary) = e_C(P),
           which forces span{rho_w} = H_P and dim H_P = e_C(P) over Q.
  free     For connected P with n <= NS and g != 1 in Aut(P):
           mu(O(P)^g) = 0 (the S2' criterion).
  ex109    Counts of non-chain posets whose chamber sum is not in Sh_n.

Run from compute/:  python3 audit_jks_maps.py > output/audit_jks_maps.txt  (~40 s)
"""

import argparse
import cmath
import itertools
import sys
from math import factorial

PRIME = 2147483647


# ---------------------------------------------------------------- permutations

def sign(w):
    s = 1
    n = len(w)
    for i in range(n):
        for j in range(i + 1, n):
            if w[i] > w[j]:
                s = -s
    return s


def perms(n):
    return list(itertools.permutations(range(1, n + 1)))


def relabel(g, w):
    """Left multiplication: letters of w relabelled by g."""
    return tuple(g[x - 1] for x in w)


def rotate_left(w, j):
    j %= len(w)
    return w[j:] + w[:j]


# ---------------------------------------------------------------- partitions

def segments(w, cuts):
    """Partition of the letters of w obtained by cutting after positions in cuts."""
    blocks, cur = [], []
    for i, x in enumerate(w, start=1):
        cur.append(x)
        if i in cuts or i == len(w):
            blocks.append(frozenset(cur))
            cur = []
    return frozenset(blocks)


def set_partitions(elems):
    elems = list(elems)
    if not elems:
        yield []
        return
    first, rest = elems[0], elems[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | {first}] + p[i + 1:]
        yield p + [frozenset([first])]


def splitting_cycle(w):
    """rho_w as {top simplex: coefficient}, normalised so that m_w has +1.

    Maximal chains of Pi_w <-> orders tau in which the n-1 cuts are removed
    (bottom-up).  The fundamental cycle is sum sgn(tau) c_tau.  m_w (the chain
    whose k-block partition is w_1|...|w_{k-1}|rest) removes cuts
    n-1, n-2, ..., 1 in that order.
    """
    n = len(w)
    m_order = tuple(range(n - 1, 0, -1))
    eps = sign(m_order)
    rho = {}
    for tau in itertools.permutations(range(1, n)):
        present = set(range(1, n))
        chain = []
        for k in range(n - 2):
            present.discard(tau[k])
            chain.append(segments(w, present))
        rho[tuple(chain)] = sign(tau) * eps
    return rho


def m_chain(w):
    n = len(w)
    return tuple(segments(w, set(range(1, k + 1))) for k in range(n - 2, 0, -1))


def boundary(vec):
    out = {}
    for simplex, c in vec.items():
        for i in range(len(simplex)):
            face = simplex[:i] + simplex[i + 1:]
            out[face] = out.get(face, 0) + (-1) ** i * c
    return {f: c for f, c in out.items() if c}


def act_on_chain(g, chain):
    return tuple(frozenset(frozenset(g[x - 1] for x in b) for b in p) for p in chain)


def add_into(acc, vec, scale):
    for k, v in vec.items():
        acc[k] = acc.get(k, 0) + scale * v


# ---------------------------------------------------------------- linear algebra mod p

class Echelon:
    """Incremental row echelon form mod PRIME over sparse dict vectors."""

    def __init__(self):
        self.pivots = {}  # pivot key -> row (dict), row[pivot] == 1
        self.order = {}

    def _key(self, k):
        if k not in self.order:
            self.order[k] = len(self.order)
        return self.order[k]

    def reduce(self, vec):
        v = {k: c % PRIME for k, c in vec.items() if c % PRIME}
        while v:
            k = min(v, key=self._key)
            if k not in self.pivots:
                return v, k
            row = self.pivots[k]
            c = v[k]
            for kk, rc in row.items():
                nv = (v.get(kk, 0) - c * rc) % PRIME
                if nv:
                    v[kk] = nv
                else:
                    v.pop(kk, None)
        return v, None

    def add(self, vec):
        v, k = self.reduce(vec)
        if k is None:
            return False
        inv = pow(v[k], PRIME - 2, PRIME)
        self.pivots[k] = {kk: c * inv % PRIME for kk, c in v.items()}
        return True

    @property
    def rank(self):
        return len(self.pivots)


def rank_mod_p(vectors):
    e = Echelon()
    for v in vectors:
        e.add(v)
    return e.rank


# ---------------------------------------------------------------- shuffles and Lie

def shuffle_words(u, v):
    if not u:
        return [v]
    if not v:
        return [u]
    return [(u[0],) + x for x in shuffle_words(u[1:], v)] + \
           [(v[0],) + x for x in shuffle_words(u, v[1:])]


def proper_shuffles(n):
    """One representative u ш v per unordered pair {u, v} (A contains 1)."""
    out = []
    rest = list(range(2, n + 1))
    for k in range(0, n - 1):
        for extra in itertools.combinations(rest, k):
            A = (1,) + extra
            B = tuple(x for x in range(1, n + 1) if x not in A)
            for u in itertools.permutations(A):
                for v in itertools.permutations(B):
                    out.append(shuffle_words(u, v))
    return out


def bracket(a, b):
    out = {}
    for x, cx in a.items():
        for y, cy in b.items():
            out[x + y] = out.get(x + y, 0) + cx * cy
            out[y + x] = out.get(y + x, 0) - cx * cy
    return {k: c for k, c in out.items() if c}


def left_normed(w):
    cur = {(w[0],): 1}
    for x in w[1:]:
        cur = bracket(cur, {(x,): 1})
    return cur


def lie_basis(n):
    return [left_normed((1,) + p) for p in itertools.permutations(range(2, n + 1))]


# ---------------------------------------------------------------- posets

def natural_posets(n):
    """All naturally labelled posets on [n] as tuples down[j] (frozensets of i <_P j)."""
    if n == 0:
        return [()]
    out = []
    for P in natural_posets(n - 1):
        m = n - 1
        for k in range(m + 1):
            for I in itertools.combinations(range(1, m + 1), k):
                I = frozenset(I)
                if all(P[j - 1] <= I for j in I):
                    out.append(P + (I,))
    return out


def relations(P):
    return frozenset((i, j + 1) for j, d in enumerate(P) for i in d)


def canonical(P, n, allperms):
    rel = relations(P)
    best = None
    for g in allperms:
        key = tuple(sorted((g[i - 1], g[j - 1]) for i, j in rel))
        if best is None or key < best:
            best = key
    return best


def unlabeled_posets(n):
    allperms = perms(n)
    seen = {}
    for P in natural_posets(n):
        c = canonical(P, n, allperms)
        if c not in seen:
            seen[c] = relations(P)
    return list(seen.values())


def linear_extensions(rel, n):
    down = {j: {i for i, jj in rel if jj == j} for j in range(1, n + 1)}
    out = []

    def rec(prefix, used):
        if len(prefix) == n:
            out.append(tuple(prefix))
            return
        for x in range(1, n + 1):
            if x not in used and down[x] <= used:
                prefix.append(x)
                used.add(x)
                rec(prefix, used)
                used.discard(x)
                prefix.pop()
    rec([], set())
    return out


def is_order_preserving(partition, rel):
    block = {}
    for b in partition:
        for x in b:
            block[x] = b
    succ = {b: set() for b in partition}
    for i, j in rel:
        if block[i] != block[j]:
            succ[block[i]].add(block[j])
    # acyclicity by DFS
    state = {}

    def dfs(b):
        state[b] = 1
        for c in succ[b]:
            if state.get(c) == 1:
                return False
            if c not in state and not dfs(c):
                return False
        state[b] = 2
        return True
    return all(dfs(b) for b in partition if b not in state)


def op_lattice(rel, n):
    return [frozenset(p) for p in set_partitions(range(1, n + 1))
            if is_order_preserving(frozenset(p), rel)]


def refines(p, q):
    return all(any(b <= c for c in q) for b in p)


def top_chains(elements, n):
    """Chains of n-2 elements of the proper part, finest first (block counts n-1..2)."""
    by_size = {}
    for p in elements:
        by_size.setdefault(len(p), []).append(p)
    chains = [(p,) for p in by_size.get(n - 1, [])]
    for size in range(n - 2, 1, -1):
        chains = [c + (q,) for c in chains for q in by_size.get(size, []) if refines(c[-1], q)]
    return chains


def mobius_bottom_top(elements):
    """mu(0,1) of a finite bounded poset of partitions under refinement."""
    els = sorted(elements, key=lambda p: -len(p))
    bottom, top = els[0], els[-1]
    mu = {}
    for x in els:
        if x == bottom:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in mu if y != x and refines(y, x))
    return mu[top]


def cyclic_classes(lin):
    seen = set()
    count = 0
    for w in lin:
        if w not in seen:
            count += 1
            for j in range(len(w)):
                seen.add(rotate_left(w, j))
    return count


def automorphisms(rel, n):
    return [g for g in perms(n)
            if frozenset((g[i - 1], g[j - 1]) for i, j in rel) == rel]


def connected(rel, n):
    adj = {i: set() for i in range(1, n + 1)}
    for i, j in rel:
        adj[i].add(j)
        adj[j].add(i)
    seen, stack = {1}, [1]
    while stack:
        x = stack.pop()
        for y in adj[x] - seen:
            seen.add(y)
            stack.append(y)
    return len(seen) == n


# ---------------------------------------------------------------- checks

RESULTS = []


def report(name, ok, detail=""):
    RESULTS.append(ok)
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ""))


def check_phi(nmax):
    print("== Prop. Phi: splitting cycles vs signed shuffles ==")
    for n in range(3, nmax + 1):
        P = perms(n)
        rho = {w: splitting_cycle(w) for w in P}
        cyc = all(not boundary(rho[w]) for w in P)
        mnorm = all(rho[w][m_chain(w)] == 1 for w in P)
        g = tuple(list(range(2, n + 1)) + [1])
        equiv = all(rho[relabel(g, w)] == {act_on_chain(g, c): v for c, v in rho[w].items()}
                    for w in P)
        shuffles = proper_shuffles(n)
        signed_ok, unsigned_fail = True, 0
        for s in shuffles:
            acc, acc_u = {}, {}
            for w in s:
                add_into(acc, rho[w], sign(w))
                add_into(acc_u, rho[w], 1)
            if any(acc.values()):
                signed_ok = False
            if any(acc_u.values()):
                unsigned_fail += 1
        r_rho = rank_mod_p(rho[w] for w in P)
        r_sh = rank_mod_p({w: 1 for w in s} for s in shuffles)
        r_first = rank_mod_p(rho[w] for w in P if w[0] == 1)
        report(f"n={n} rho_w are cycles, m_w coefficient +1, g.rho_w = rho_gw", cyc and mnorm and equiv)
        report(f"n={n} the (n-1)! rho_w with w_1 = 1 are independent (Sec. 3.5 item 3)",
               r_first == factorial(n - 1))
        report(f"n={n} signed shuffle relation exact on all {len(shuffles)} shuffles", signed_ok)
        report(f"n={n} positive control: unsigned relation fails", unsigned_fail > 0,
               f"{unsigned_fail}/{len(shuffles)} unsigned sums nonzero")
        report(f"n={n} rank_p rho = {r_rho}, rank_p Sh = {r_sh}, sum = n! = {factorial(n)}",
               r_rho + r_sh == factorial(n) and r_rho == factorial(n - 1))


def check_ree(nmax):
    print("== Ree: Lie_n orthogonal to Sh_n ==")
    for n in range(3, nmax + 1):
        L = lie_basis(n)
        shuffles = proper_shuffles(n)
        orth = all(sum(l.get(w, 0) for w in s) == 0 for l in L for s in shuffles)
        report(f"n={n} left-normed brackets orthogonal to Sh_n, rank_p = {rank_mod_p(L)}",
               orth and rank_mod_p(L) == factorial(n - 1))


def right_mult_coeff(x, a, n):
    """x * a for dict elements of C[S_n] (words), product (u*v)_i = u_{v_i}."""
    out = {}
    for u, cu in x.items():
        for v, cv in a.items():
            uv = tuple(u[i - 1] for i in v)
            out[uv] = out.get(uv, 0) + cu * cv
    return out


def maj(w):
    return sum(i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def check_propC(nmax_le, nmax_op):
    print("== Prop. C / Lemma B ==")
    # Lemma B on every labelled poset (natural labelling suffices: relabelling commutes)
    for n in range(3, nmax_op + 1):
        ok = True
        for P in natural_posets(n):
            rel = relations(P)
            op = frozenset((j, i) for i, j in rel)
            if set(op_lattice(rel, n)) != set(op_lattice(op, n)):
                ok = False
        report(f"n={n} O(P) = O(P^op) for all naturally labelled P", ok)
    for n in range(3, nmax_le + 1):
        z = cmath.exp(2j * cmath.pi / n)
        gamma = tuple(list(range(2, n + 1)) + [1])
        e = {}
        for j in range(n):
            gj = tuple(range(1, n + 1))
            for _ in range(j):
                gj = tuple(gj[i - 1] for i in gamma)
            e[gj] = e.get(gj, 0) + z ** (-j) / n
        # witness: s = 1 ш (2..n); coefficient of identity in s*e_zeta is (1+zeta)/n
        s = {w: 1 for w in shuffle_words((1,), tuple(range(2, n + 1)))}
        se = right_mult_coeff(s, e, n)
        ident = tuple(range(1, n + 1))
        report(f"n={n} witness (1 ш 2..n) e_zeta has identity coefficient (1+zeta)/n != 0",
               abs(se.get(ident, 0) - (1 + z) / n) < 1e-9 and abs(1 + z) > 1e-9)
        # Klyachko kappa_n = (1/n) sum zeta^{maj s} s; find the convention that is Lie
        kap = {w: z ** maj(w) / n for w in perms(n)}
        k2 = right_mult_coeff(kap, kap, n)
        idem = all(abs(k2.get(w, 0) - kap[w]) < 1e-9 for w in kap)
        shuffles = proper_shuffles(n)
        lie = all(abs(sum(kap[w] for w in sh)) < 1e-9 for sh in shuffles)
        sk = max(max((abs(c) for c in right_mult_coeff({w: 1 for w in sh}, kap, n).values()),
                     default=0) for sh in shuffles)
        w0 = tuple(range(n, 0, -1))
        a = kap
        b = right_mult_coeff({w0: 1}, kap, n)
        # proportional iff 2x2 minors vanish
        keys = list(a)
        ref = max(keys, key=lambda k: abs(a[k]))
        lam = b.get(ref, 0) / a[ref]
        prop = all(abs(b.get(k, 0) - lam * a[k]) < 1e-9 for k in keys)
        report(f"n={n} kappa_n idempotent and Lie; Sh_n kappa_n != 0; kappa, w0.kappa not proportional",
               idem and lie and sk > 1e-6 and not prop)


def check_conjS(nmax, direct_max):
    print("== Lemma D, Conjecture S, dim H_P ==")
    for n in range(3, nmax + 1):
        posets = unlabeled_posets(n)
        allS = True
        lemmaD = True
        details = []
        rho_cache = {}
        for rel in posets:
            lin = linear_extensions(rel, n)
            eC = cyclic_classes(lin)
            ops = set(op_lattice(rel, n))
            for w in lin:
                if w not in rho_cache:
                    rho_cache[w] = splitting_cycle(w)
                if not all(p in ops for c in rho_cache[w] for p in c):
                    lemmaD = False
            r = rank_mod_p(rho_cache[w] for w in lin)
            if n <= direct_max:
                chains = top_chains(ops, n)
                rb = rank_mod_p(boundary({c: 1}) for c in chains)
                dimker_p = len(chains) - rb
                ok = (r == eC == dimker_p)
            else:
                dimker_p = None
                ok = (r == eC)
            if not ok:
                allS = False
                details.append((sorted(rel), r, eC, dimker_p))
        report(f"n={n} Lemma D on all {len(posets)} unlabeled posets", lemmaD)
        if n == 3:
            # positive controls: rho_213 is not supported in O(chain 1<2<3);
            # V-poset 1<2, 1<3 (connected, Lin = {123, 132}): one rho_w is short.
            chain = frozenset({(1, 2), (2, 3), (1, 3)})
            ops = set(op_lattice(chain, n))
            outside = not all(p in ops for c in splitting_cycle((2, 1, 3)) for p in c)
            vee = frozenset({(1, 2), (1, 3)})
            short = rank_mod_p([splitting_cycle((1, 2, 3))]) < cyclic_classes(linear_extensions(vee, n))
            report("positive controls: rho_213 leaves O(chain); one rho_w short of e_C(V)", outside and short)
        how = "rank_p rho_w = dim_p ker d = e_C" if n <= direct_max else "rank_p rho_w = e_C"
        report(f"n={n} Conjecture S ({how}) on all {len(posets)} unlabeled posets", allS,
               "" if allS else str(details[:3]))


def fixed_sublattice(ops, g):
    def act(p):
        return frozenset(frozenset(g[x - 1] for x in b) for b in p)
    return [p for p in ops if act(p) == p]


def check_free(nmax):
    print("== S2': mu(O(P)^g) = 0 for g != 1, P connected ==")
    for n in range(3, nmax + 1):
        bad, tested = 0, 0
        for rel in unlabeled_posets(n):
            if not connected(rel, n):
                continue
            auts = automorphisms(rel, n)
            if len(auts) == 1:
                continue
            ops = op_lattice(rel, n)
            for g in auts:
                if g == tuple(range(1, n + 1)):
                    continue
                tested += 1
                if mobius_bottom_top(fixed_sublattice(ops, g)) != 0:
                    bad += 1
        report(f"n={n} connected P, {tested} nontrivial automorphisms, mu(O(P)^g) = 0", bad == 0,
               f"{bad} nonzero")
        # positive control: the antichain (disconnected) has g with mu != 0
    n = 3
    anti = frozenset()
    g = (2, 3, 1)
    mu = mobius_bottom_top(fixed_sublattice(op_lattice(anti, n), g))
    report("positive control: antichain n=3, g=(123): mu(O^g) != 0", mu != 0, f"mu = {mu}")


def check_ex109(nmax):
    print("== Topics Ex. 10.9 (top-cone version) ==")
    n = 3
    lie = bracket({(2,): 1}, bracket({(1,): 1}, {(3,): 1}))
    expect = {(2, 1, 3): 1, (2, 3, 1): -1, (1, 3, 2): -1, (3, 1, 2): 1}
    cone_sum = lie.get((1, 2, 3), 0) + lie.get((1, 3, 2), 0)
    report("n=3 [2,[1,3]] = 213-231-132+312, coefficient sum on {123,132} = -1",
           lie == expect and cone_sum == -1)
    for n in range(3, nmax + 1):
        L = lie_basis(n)
        tot = bad = 0
        for rel in unlabeled_posets(n):
            lin = linear_extensions(rel, n)
            if len(lin) == 1:
                continue
            tot += 1
            linset = set(lin)
            if any(sum(c for w, c in l.items() if w in linset) for l in L):
                bad += 1
        print(f"     n={n}: {bad}/{tot} non-chain posets have chamber sum outside Sh_n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nphi", type=int, default=6)
    ap.add_argument("--ns", type=int, default=6)
    ap.add_argument("--direct", type=int, default=6)
    args = ap.parse_args()
    check_phi(args.nphi)
    check_ree(args.nphi)
    check_propC(5, 5)
    check_conjS(args.ns, args.direct)
    check_free(args.ns)
    check_ex109(5)
    ok = all(RESULTS)
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
