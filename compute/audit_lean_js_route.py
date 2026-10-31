"""Independent audit of notes/lean_js_route.md, Section 3 (Route C).

Self-contained: imports nothing from the other scripts of compute/.
All ranks are exact ranks over Q (sparse Gaussian elimination in Fraction
arithmetic). A rank mod 2 is implemented only for a positive control.

Conventions (those of lean/PosetJKS/OrderComplex.lean): a chain is an
increasing tuple, d-chains have d + 1 elements, the empty chain is in degree
-1, and  bd(c) = sum_i (-1)^i (c minus its i-th element).

Checks, for every unlabelled poset P with n <= NMAX:
  [gen]   poset counts 1, 2, 5, 16, 63, 318 (OEIS A000112)
  [JS]    reduced Betti numbers over Q of the proper part of OP(P):
          beta_d = 0 for d != n - 3 and beta_{n-3} = e_C(P) (n >= 3);
          all beta_d = 0 for d >= 0 when n <= 2
and for every minimal a of P (n >= 3):
  [M]     {x in OP(P) : x meet pi_a = 0^} = {0^} u {pi_ab in OP(P)}
  [Pz]    the hypotheses of Lemma K for Q = Lbar \\ A, t = pi_a,
          p(x) = x meet pi_a: p maps Q to Q, monotone, p <= id, p <= t,
          p = id below t, t in Q
  [K]     the chain-homotopy identity of Lemma K, signs as in the note:
          (bd s + s bd)(c) - c lies in F_{k-1}, and is 0 when k = 0,
          for every chain c of Q (empty chain included)
  [Qac]   Q has all reduced Betti numbers 0 over Q (degree -1 included)
  [U]     sigma -> sigma / pi_ab is an order isomorphism from the open
          interval (pi_ab, 1^) of OP(P) onto the proper part of OP(P/pi_ab)
  [rel]   beta_d(Lbar) = sum_b beta_{d-1}((pi_ab, 1^)) for every d >= 0,
          with beta_{-1}(empty) = 1 (the full long exact sequence form)
Positive controls (each must fire):
  [ctl-rank]  rank code: crown + point (beta_0 = beta_1 = 1); S^2 + S^1
              (beta_0 = beta_1 = beta_2 = 1); RP^2 face poset, which is
              acyclic over Q but has beta_1 = beta_2 = 1 mod 2
  [ctl-sign]  s with the opposite sign fails [K] on some poset
  [ctl-Q]     Q replaced by Lbar fails [Qac] on some poset
  [ctl-tau]   tau(c) = p(max c) fails the [K] identity on some poset

Usage:  python3 audit_lean_js_route.py [--nmax N] [--procs K]
"""

import argparse
import itertools
import os
import sys
from fractions import Fraction
from multiprocessing import Pool


# ---------------------------------------------------------------- posets

class Poset:
    """A poset on range(n), given by the strict relation lt[i][j] (i < j)."""

    def __init__(self, n, lt):
        self.n = n
        self.lt = lt

    @staticmethod
    def from_relations(n, rels):
        lt = [[False] * n for _ in range(n)]
        for i, j in rels:
            lt[i][j] = True
        for k in range(n):
            for i in range(n):
                if lt[i][k]:
                    for j in range(n):
                        if lt[k][j]:
                            lt[i][j] = True
        for i in range(n):
            assert not lt[i][i], "relation has a cycle"
        return Poset(n, lt)

    def le(self, i, j):
        return i == j or self.lt[i][j]

    def minimal(self):
        return [a for a in range(self.n)
                if not any(self.lt[b][a] for b in range(self.n))]


def canon(n, lt):
    best = None
    for perm in itertools.permutations(range(n)):
        key = tuple(lt[perm[i]][perm[j]] for i in range(n) for j in range(n))
        if best is None or key < best:
            best = key
    return best


def all_posets(nmax):
    """Unlabelled posets by n: add a maximal element above a down-set."""
    out = {0: [Poset(0, [])]}
    for n in range(1, nmax + 1):
        seen = {}
        for P in out[n - 1]:
            m = n - 1
            for mask in range(1 << m):
                below = [i for i in range(m) if mask >> i & 1]
                if any(P.lt[j][i] and not (mask >> j & 1)
                       for i in below for j in range(m)):
                    continue  # not a down-set
                lt = [row[:] + [False] for row in P.lt] + [[False] * n]
                for i in below:
                    lt[i][m] = True
                key = canon(n, lt)
                if key not in seen:
                    seen[key] = Poset(n, lt)
        out[n] = list(seen.values())
    return out


def linear_extensions(P):
    res = []

    def rec(word, used):
        if len(word) == P.n:
            res.append(tuple(word))
            return
        for x in range(P.n):
            if not used >> x & 1 and all(used >> y & 1 for y in range(P.n)
                                         if P.lt[y][x]):
                word.append(x)
                rec(word, used | 1 << x)
                word.pop()

    rec([], 0)
    return res


def e_C(P):
    """Number of rotation classes of words that contain a linear extension."""
    return len({min(w[k:] + w[:k] for k in range(len(w)))
                for w in linear_extensions(P)})


# ---------------------------------------------------------------- OP(P)

def set_partitions(n):
    """Partitions of range(n) as tuples of block labels (restricted growth)."""
    def rec(prefix, m):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for v in range(m + 1):
            yield from rec(prefix + [v], max(m, v + 1))
    yield from rec([], 0)


def normal(blocklabels):
    seen = {}
    return tuple(seen.setdefault(v, len(seen)) for v in blocklabels)


def is_op(P, part):
    """The quotient digraph P/part is acyclic."""
    k = max(part) + 1 if part else 0
    edges = {(part[i], part[j]) for i in range(P.n) for j in range(P.n)
             if P.lt[i][j] and part[i] != part[j]}
    reach = [[False] * k for _ in range(k)]
    for u, v in edges:
        reach[u][v] = True
    for w in range(k):
        for u in range(k):
            if reach[u][w]:
                for v in range(k):
                    if reach[w][v]:
                        reach[u][v] = True
    return not any(reach[u][u] for u in range(k))


def refines(x, y):
    """x <= y in the refinement order."""
    return all(y[i] == y[j] for i in range(len(x)) for j in range(len(x))
               if x[i] == x[j])


def meet(x, y):
    return normal([(x[i], y[i]) for i in range(len(x))])


def OP(P):
    return [s for s in set_partitions(P.n) if is_op(P, s)]


def bot(n):
    return tuple(range(n))


def top(n):
    return tuple([0] * n)


def proper_part(P):
    if P.n == 0:
        return []
    return [s for s in OP(P) if s != bot(P.n) and s != top(P.n)]


def pi_a(n, a):
    return normal([0 if i == a else 1 for i in range(n)])


def pi_ab(n, a, b):
    return normal([a if i == b else i for i in range(n)])


def quotient(P, a, b):
    """P / pi_ab: identify b with a, transitive closure. Points are
    range(n) minus b, renumbered in order."""
    pts = [i for i in range(P.n) if i != b]
    idx = {v: k for k, v in enumerate(pts)}
    cls = lambda i: idx[a] if i == b else idx[i]
    rels = {(cls(i), cls(j)) for i in range(P.n) for j in range(P.n)
            if P.lt[i][j] and cls(i) != cls(j)}
    return Poset.from_relations(len(pts), rels), cls


# ---------------------------------------------------------------- chains

def chains(elems, less):
    """All chains (increasing tuples) of the finite poset (elems, less),
    by number of elements: res[m] = list of m-element chains."""
    up = {x: [y for y in elems if less(x, y)] for x in elems}
    res = [[()]]

    def rec(c):
        m = len(c)
        while len(res) <= m:
            res.append([])
        res[m].append(c)
        for y in up[c[-1]]:
            rec(c + (y,))

    for x in elems:
        rec((x,))
    return res


def bd(c):
    """Boundary of one chain, as a dict chain -> int."""
    out = {}
    for i in range(len(c)):
        f = c[:i] + c[i + 1:]
        out[f] = out.get(f, 0) + (-1) ** i
    return {f: v for f, v in out.items() if v}


def rank_Q(rows):
    """Exact rank over Q of a list of sparse rows (dict col -> int)."""
    pivots = {}
    r = 0
    for row in rows:
        row = {k: Fraction(v) for k, v in row.items() if v}
        while row:
            c = min(row)
            if c in pivots:
                f = row[c]
                for k, v in pivots[c].items():
                    nv = row.get(k, 0) - f * v
                    if nv:
                        row[k] = nv
                    else:
                        row.pop(k, None)
            else:
                f = row[c]
                pivots[c] = {k: v / f for k, v in row.items()}
                r += 1
                break
    return r


def rank_F2(rows):
    pivots = {}
    r = 0
    for row in rows:
        s = {k for k, v in row.items() if v % 2}
        while s:
            c = min(s)
            if c in pivots:
                s ^= pivots[c]
            else:
                pivots[c] = s
                r += 1
                break
    return r


def reduced_betti(elems, less, rank=rank_Q):
    """Reduced Betti numbers beta_d, d = -1, 0, 1, ...; returned as a dict.
    Augmented complex: the empty chain is the basis of C_{-1}."""
    ch = chains(elems, less)
    index = [{c: i for i, c in enumerate(cm)} for cm in ch]
    # rk[m] = rank of bd from m-element chains to (m-1)-element chains
    rk = [0] * (len(ch) + 1)
    for m in range(1, len(ch)):
        rows = [{index[m - 1][f]: v for f, v in bd(c).items()} for c in ch[m]]
        rk[m] = rank(rows)
    return {m - 1: len(ch[m]) - rk[m] - rk[m + 1] for m in range(len(ch))}


# ---------------------------------------------------------------- Lemma K

def lemma_k_check(Q, less, t, p, sign=1, tau_rule="min_high"):
    """Check the Claim of Section 3.1 on every chain of (Q, less).
    Returns (ok, number of chains checked)."""
    leq = lambda x, y: x == y or less(x, y)

    def high(c):
        return [x for x in c if not leq(x, t)]

    def tau(c):
        h = high(c)
        if not h:
            return t
        if tau_rule == "min_high":
            return p(h[0])          # chains are increasing: h[0] = min c_>
        return p(c[-1])             # control: p(max c)

    def s(c):
        tc = tau(c)
        if tc in c:
            return {}
        j = len(c) - len(high(c))   # |c_<=|
        if tau_rule != "min_high":
            # control: insert where the order puts it, if c u {tc} is a chain
            if not all(leq(x, tc) or leq(tc, x) for x in c):
                return None
            j = sum(1 for x in c if less(x, tc))
        new = c[:j] + (tc,) + c[j:]
        for x, y in zip(new, new[1:]):
            if not less(x, y):
                return None
        return {new: sign * (-1) ** j}

    def add(acc, d, coef=1):
        for k, v in d.items():
            nv = acc.get(k, 0) + coef * v
            if nv:
                acc[k] = nv
            else:
                acc.pop(k, None)

    ch = chains(Q, less)
    count = 0
    for cm in ch:
        for c in cm:
            count += 1
            k = len(high(c))
            acc = {}
            sc = s(c)
            if sc is None:
                return False, count
            for cc, v in sc.items():
                add(acc, bd(cc), v)
            for f, v in bd(c).items():
                sf = s(f)
                if sf is None:
                    return False, count
                add(acc, sf, v)
            add(acc, {c: 1}, -1)
            if k == 0:
                if acc:
                    return False, count
            elif any(len(high(x)) > k - 1 for x in acc):
                return False, count
    return True, count


# ---------------------------------------------------------------- per poset

def check_poset(P):
    n = P.n
    less = lambda x, y: x != y and refines(x, y)
    L = proper_part(P)
    res = {"n": n, "eC": e_C(P) if n else 0}
    beta = reduced_betti(L, less)
    res["beta"] = beta
    if n <= 2:
        res["JS"] = all(v == 0 for d, v in beta.items() if d >= 0)
    else:
        res["JS"] = all((v == 0) if d != n - 3 else (v == res["eC"])
                        for d, v in beta.items() if d >= 0)
    res.update(M=True, Pz=True, K=True, Qac=True, U=True, rel=True,
               pairs=0, kchains=0, ctl_sign=False, ctl_Q=False, ctl_tau=False)
    if n < 3:
        return res
    ops = OP(P)
    Lset = set(L)
    for a in P.minimal():
        res["pairs"] += 1
        t = pi_a(n, a)
        A = [pi_ab(n, a, b) for b in range(n) if b != a
             and pi_ab(n, a, b) in Lset]
        bs = [b for b in range(n) if b != a and pi_ab(n, a, b) in Lset]
        # [M]
        mc = {x for x in ops if meet(x, t) == bot(n)}
        if mc != {bot(n)} | set(A):
            res["M"] = False
        # [Pz]
        Q = [x for x in L if x not in set(A)]
        Qs = set(Q)
        p = lambda x: meet(x, t)
        leq = lambda x, y: refines(x, y)
        ok = t in Qs
        for x in Q:
            ok &= p(x) in Qs and leq(p(x), x) and leq(p(x), t)
            if leq(x, t):
                ok &= p(x) == x
            for y in Q:
                if leq(x, y):
                    ok &= leq(p(x), p(y))
        res["Pz"] &= ok
        # [K] and controls
        okK, cnt = lemma_k_check(Q, less, t, p)
        res["K"] &= okK
        res["kchains"] += cnt
        if not lemma_k_check(Q, less, t, p, sign=-1)[0]:
            res["ctl_sign"] = True
        if not lemma_k_check(Q, less, t, p, tau_rule="max")[0]:
            res["ctl_tau"] = True
        # [Qac]
        bQ = reduced_betti(Q, less)
        res["Qac"] &= all(v == 0 for v in bQ.values())
        if any(v != 0 for v in beta.values()):
            res["ctl_Q"] = True  # Lbar itself is not acyclic
        # [U] and [rel]
        interval_betti = []
        for b in bs:
            pab = pi_ab(n, a, b)
            I = [x for x in L if less(pab, x)]
            P2, cls = quotient(P, a, b)
            L2 = proper_part(P2)

            def down(x):
                lab = {}
                for i in range(n):
                    lab[cls(i)] = x[i]
                return normal([lab[k] for k in range(P2.n)])

            img = [down(x) for x in I]
            okU = len(set(img)) == len(I) and set(img) == set(L2)
            for x, y in itertools.product(I, I):
                okU &= refines(x, y) == refines(down(x), down(y))
            res["U"] &= okU
            bI = reduced_betti(I, less)
            b2 = reduced_betti(L2, less)
            res["U"] &= ({d: v for d, v in bI.items() if v} ==
                         {d: v for d, v in b2.items() if v})
            interval_betti.append(bI)
        for d in range(0, n):
            lhs = beta.get(d, 0)
            rhs = sum(bI.get(d - 1, 0) for bI in interval_betti)
            if lhs != rhs:
                res["rel"] = False
    return res


# ---------------------------------------------------------------- controls

def control_complexes():
    """Face posets (ordered by inclusion) with known homology."""
    def face_poset(facets):
        faces = set()
        for f in facets:
            for r in range(1, len(f) + 1):
                faces.update(frozenset(s) for s in itertools.combinations(f, r))
        return list(faces), lambda x, y: x < y

    out = {}
    # crown (a, b < c, d): a circle; plus an isolated point
    crown = Poset.from_relations(5, [(0, 2), (0, 3), (1, 2), (1, 3)])
    out["crown+point"] = (list(range(5)), lambda x, y: crown.lt[x][y],
                          {0: 1, 1: 1})
    # boundary of a tetrahedron (S^2) disjoint from a triangle boundary (S^1)
    s2 = [tuple(sorted(set(range(4)) - {i})) for i in range(4)]
    s1 = [(4, 5), (5, 6), (4, 6)]
    el, lt = face_poset(s2 + s1)
    out["S2+S1"] = (el, lt, {0: 1, 1: 1, 2: 1})
    # 6-vertex RP^2
    rp2 = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5),
           (1, 2, 4), (2, 3, 5), (1, 3, 4), (1, 3, 5), (2, 4, 5)]
    el, lt = face_poset(rp2)
    out["RP2"] = (el, lt, {})
    return out


def run_controls():
    ok = True
    for name, (el, lt, expect) in control_complexes().items():
        b = {d: v for d, v in reduced_betti(el, lt).items() if v}
        print(f"[ctl-rank] {name}: beta over Q = {b} (expected {expect})")
        ok &= b == expect
    el, lt, _ = control_complexes()["RP2"]
    b2 = {d: v for d, v in reduced_betti(el, lt, rank=rank_F2).items() if v}
    print(f"[ctl-rank] RP2: beta mod 2 = {b2} (expected {{1: 1, 2: 1}})")
    ok &= b2 == {1: 1, 2: 1}
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--procs", type=int,
                    default=int(os.environ.get("POGO_WORKER_CORES", "1")))
    args = ap.parse_args()

    allok = run_controls()
    posets = all_posets(args.nmax)
    counts = [len(posets[n]) for n in range(1, args.nmax + 1)]
    print(f"[gen] posets n = 1..{args.nmax}: {counts}")
    allok &= counts == [1, 2, 5, 16, 63, 318, 2045][:args.nmax]
    flat = [P for n in range(1, args.nmax + 1) for P in posets[n]]
    with Pool(args.procs) as pool:
        results = pool.map(check_poset, flat, chunksize=1)
    keys = ["JS", "M", "Pz", "K", "Qac", "U", "rel"]
    tot = len(results)
    for k in keys:
        good = sum(1 for r in results if r[k])
        print(f"[{k}] holds on {good}/{tot}")
        allok &= good == tot
    print(f"pairs (P, a minimal), n >= 3: {sum(r['pairs'] for r in results)}")
    print(f"chains checked in [K]: {sum(r['kchains'] for r in results)}")
    for k in ["ctl_sign", "ctl_Q", "ctl_tau"]:
        fired = sum(1 for r in results if r[k])
        print(f"[{k}] fires on {fired} posets")
        allok &= fired > 0
    for n in range(3, args.nmax + 1):
        rs = [r for r in results if r["n"] == n]
        tops = sorted({r["beta"].get(n - 3, 0) for r in rs})
        print(f"n = {n}: {len(rs)} posets, top Betti numbers {tops}, "
              f"top chain degree {max(max(r['beta']) for r in rs)}")
    print("ALL CHECKS PASS" if allok else "SOME CHECK FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
