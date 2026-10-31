#!/usr/bin/env python3
"""Quasisymmetric refinement of Theorem H: the T-anchored P-partition
enumerator K_{C,T}(P) is a sum of one fundamental F_D per cyclic class.

Companion to ../notes/qsym_refinement_omega_c.md.  Self-contained: it does
not import any other module of this repository.  The poset enumeration and
the Moebius computation of Omega_C are copied from h_vector_omega_c.py so
that this file stands alone.

K_{C,T}(P) := sum of x^f over order-preserving f : P -> {1,2,...} such that
every nonempty upper level set f^{-1}[v, oo) that is a union of components
contains T.  It is computed here from its DEFINITION, by chains of order
ideals (one monomial quasisymmetric M_alpha per chain), and then converted
to Gessel's fundamental basis F_J.  No linear extension is used for it.

Claims checked (PASS/FAIL, bracketed tags):

  [T-dep]      K_{C,T}(P) depends on T for some P (so "K_C(P)" needs T);
  [Fpos-all-T] K_{C,T}(P) is F-positive for every P and every component T;
  [spec]       its principal specialisation is Omega_C(P, m) computed from
               the Moebius definition (n <= SPECMAX);
  [thmQ]       Theorem Q: for every natural labelling satisfying (E_T)
               (every maximal element of a non-singleton component, and T if
               T is an isolated point, is labelled above every minimal
               element of P - T), K_{C,T}(P) = sum over classes kappa of
               F_{Des R_T(kappa)}, R_T = the rotation whose last piece is T's;
  [thmQ-iff]   for every natural labelling (n <= LMAX) the identity holds
               iff (X'_T): every w whose last piece misses T has a descent
               at some cut after T's piece; and (E_T) => (X_T) => (X'_T),
               (X_T) = the junction leaving T's piece is always a descent;
  [lamT]       the labelling lambda_T (lambda_0 with T's maxima last) is
               natural, separated and satisfies (E_T), and under it
               |Des R_T(kappa)| = cdes(kappa) - 1 (n >= 2): Theorem H;
  [bij]        brute force, n <= BIJMAX, m <= 3: under (E_T), an
               order-preserving f is T-anchored iff its Stanley word has
               T's piece last;
  [E*]         (E*_T) (see satisfies_Estar) is equivalent to (X_T);
  [perclass-X'] under (X'_T) every class contributes exactly one F;

COMPUTED / CONTROLS (must be refuted somewhere):
  [ctl-perclass-sep] Lemma 1 lifted: under a SEPARATED labelling each class
               contributes a single F_D (sum over its rotations of the
               inclusion-exclusion expansion), every T;
  [ctl-perclass-Fpos] the same contribution is at least F-positive;
  [ctl-mindes]  K_{C,T} = sum_kappa F_{Des(lex-first min-des rotation)}
               under lambda_0, every T;
  [ctl-anyrep]  K_{C,T} = sum_kappa F_{Des(first listed rotation)} under
               lambda_T;
  [ctl-Mneg]    M_(2) = F_{} - F_{1} is flagged as not F-positive.

Run from compute/:

    python3 qsym_refinement_omega_c.py --nmax 7 --lmax 6 > output/qsym_refinement_omega_c.txt

Plain Python 3, no dependencies, one core.  Exit status 0 iff every claim
holds and every control is refuted somewhere.
"""

import argparse
import itertools
import sys
from collections import Counter
from math import comb as _comb

FAILS = []


def comb(a, b):
    return _comb(a, b) if a >= 0 and b >= 0 else 0


def check(ok, label):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        FAILS.append(label)


def control(failures, total, label):
    ok = failures > 0
    print(("PASS " if ok else "FAIL ") + "CONTROL " + label
          + f" (refuted on {failures} of {total})")
    if not ok:
        FAILS.append("CONTROL " + label)


# ---------------------------------------------------------------------------
# Posets: rel = frozenset of pairs (a, b) meaning a < b, transitively closed.


def cells(rel, n):
    down = [[a for a in range(n) if (a, x) in rel] for x in range(n)]
    up = [[b for b in range(n) if (x, b) in rel] for x in range(n)]
    col = [(len(down[x]), len(up[x])) for x in range(n)]
    while True:
        new = [(col[x], tuple(sorted(col[a] for a in down[x])),
                tuple(sorted(col[b] for b in up[x]))) for x in range(n)]
        keys = sorted(set(new))
        new = [keys.index(c) for c in new]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    out = {}
    for x in range(n):
        out.setdefault(col[x], []).append(x)
    return [out[k] for k in sorted(out)]


def canonical(rel, n):
    cs = cells(rel, n)
    best = None
    for parts in itertools.product(*[itertools.permutations(c) for c in cs]):
        order = [x for p in parts for x in p]
        pos = {x: i for i, x in enumerate(order)}
        code = tuple(sorted((pos[a], pos[b]) for a, b in rel))
        if best is None or code < best:
            best = code
    return frozenset(best)


def ideal_masks(rel, n):
    out = []
    for mask in range(1 << n):
        if all((mask >> a & 1) for (a, b) in rel if mask >> b & 1):
            out.append(mask)
    return out


def unlabeled_posets(nmax):
    by_n = {1: [frozenset()]}
    for n in range(2, nmax + 1):
        seen = set()
        for rel in by_n[n - 1]:
            for I in ideal_masks(rel, n - 1):
                new = set(rel) | {(a, n - 1) for a in range(n - 1) if I >> a & 1}
                seen.add(canonical(frozenset(new), n))
        by_n[n] = sorted(seen, key=lambda r: sorted(r))
    return by_n


def linexts(rel, n):
    below = [0] * n
    for a, b in rel:
        below[b] |= 1 << a
    out = []

    def rec(word, used):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not used >> x & 1 and below[x] & ~used == 0:
                word.append(x)
                rec(word, used | 1 << x)
                word.pop()
    rec([], 0)
    return out


def components(rel, n):
    """List of component bitmasks, sorted by least element."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in rel:
        parent[find(a)] = find(b)
    comp = {}
    for x in range(n):
        comp[find(x)] = comp.get(find(x), 0) | 1 << x
    return sorted(comp.values(), key=lambda m: (m & -m))


def relabel(rel, w):
    """Natural labelling from the linear extension w: w_i gets label i."""
    lab = {x: i for i, x in enumerate(w)}
    return frozenset((lab[a], lab[b]) for a, b in rel), lab


def relabel_mask(mask, lab):
    out = 0
    for x, i in lab.items():
        if mask >> x & 1:
            out |= 1 << i
    return out


def kinds(rel, n):
    hasdown = [False] * n
    hasup = [False] * n
    for a, b in rel:
        hasup[a] = True
        hasdown[b] = True
    mins = [x for x in range(n) if not hasdown[x] and hasup[x]]
    maxs = [x for x in range(n) if hasdown[x] and not hasup[x]]
    iso = [x for x in range(n) if not hasdown[x] and not hasup[x]]
    mid = [x for x in range(n) if hasdown[x] and hasup[x]]
    return mins, mid, iso, maxs


def is_separated(rel, n):
    mins, _, _, maxs = kinds(rel, n)
    return all(a < b for a in mins for b in maxs)


def satisfies_ET(rel, n, T):
    """(E_T): every maximal element of a non-singleton component, and T
    itself if T is an isolated point, is labelled above every minimal
    element of P - T (isolated points count as minimal)."""
    mins, mid, iso, maxs = kinds(rel, n)
    tops = maxs + [x for x in iso if T >> x & 1]
    minO = [x for x in mins + iso if not T >> x & 1]
    return all(a > b for a in tops for b in minO)


def satisfies_Estar(rel, n, comps, T):
    """(E*_T), the exact criterion: a > b whenever a is a maximal element of
    a non-singleton component V and b is a minimal element of a component
    U not in {T, V}; and, if T = {t} is an isolated point, t > b for every
    minimal element b outside T."""
    below = set(rel)
    compof = {}
    for i, c in enumerate(comps):
        for x in range(n):
            if c >> x & 1:
                compof[x] = i
    tidx = compof[(T & -T).bit_length() - 1]
    ismax = [not any((x, y) in below for y in range(n)) for x in range(n)]
    ismin = [not any((y, x) in below for y in range(n)) for x in range(n)]
    size = [bin(c).count("1") for c in comps]
    for a in range(n):
        if not ismax[a] or size[compof[a]] < 2:
            continue
        for b in range(n):
            if ismin[b] and compof[b] not in (tidx, compof[a]) and a < b:
                return False
    if size[tidx] == 1:
        t = (T & -T).bit_length() - 1
        if any(ismin[b] and b != t and t < b for b in range(n)):
            return False
    return True


def lin_closed(words, n):
    """Is the set of words exactly Lin of the poset 'a before b in every
    word'?"""
    words = set(words)
    pos = [{x: i for i, x in enumerate(w)} for w in words]
    rel = frozenset((a, b) for a in range(n) for b in range(n) if a != b
                    and all(p[a] < p[b] for p in pos))
    return set(linexts(rel, n)) == words


def exit_conditions(lin, comps, T):
    """(X_T): in every w whose last piece does not contain T, the junction
    leaving T's piece is a descent.  (X'_T): in every such w, SOME cut after
    T's piece is a descent, i.e. C_T(w) meets Des(w)."""
    X = Xp = True
    for w in lin:
        C = CT(w, comps, T)
        if not C:
            continue
        D = Des(w)
        if C[0] not in D:
            X = False
        if not any(p in D for p in C):
            Xp = False
    return X, Xp


def lambda_T_extension(rel, n, T):
    """lambda_0 of h_vector_omega_c.md with T's maxima (or T itself, if T is
    an isolated point) moved to the very end: non-isolated minima, middle
    elements (by down-set size), isolated points other than T, maxima not in
    T, then T's maxima / T."""
    mins, mid, iso, maxs = kinds(rel, n)
    dsz = [sum(1 for y in range(n) if (y, x) in rel) for x in range(n)]
    mid.sort(key=lambda x: dsz[x])
    isoT = [x for x in iso if T >> x & 1]
    isoO = [x for x in iso if not T >> x & 1]
    maxT = [x for x in maxs if T >> x & 1]
    maxO = [x for x in maxs if not T >> x & 1]
    return mins + mid + isoO + maxO + maxT + isoT


def lambda_0_extension(rel, n):
    mins, mid, iso, maxs = kinds(rel, n)
    dsz = [sum(1 for y in range(n) if (y, x) in rel) for x in range(n)]
    mid.sort(key=lambda x: dsz[x])
    return mins + mid + iso + maxs


def is_linext(rel, w):
    pos = {x: i for i, x in enumerate(w)}
    return all(pos[a] < pos[b] for a, b in rel)


# ---------------------------------------------------------------------------
# Omega_C from the Moebius definition (copied from h_vector_omega_c.py)


def set_partitions_rgs(k):
    out = []

    def rec(s, mx):
        if len(s) == k:
            out.append(tuple(s))
            return
        for v in range(mx + 2):
            s.append(v)
            rec(s, max(mx, v))
            s.pop()
    rec([], -1)
    return out


RGS = {}


def rgs(k):
    if k not in RGS:
        RGS[k] = set_partitions_rgs(k)
    return RGS[k]


def acyclic_quotient(blk, rel, nb):
    edges = {(blk[a], blk[b]) for a, b in rel if blk[a] != blk[b]}
    indeg = [0] * nb
    adj = [[] for _ in range(nb)]
    for u, v in edges:
        adj[u].append(v)
        indeg[v] += 1
    stack = [u for u in range(nb) if indeg[u] == 0]
    seen = 0
    while stack:
        u = stack.pop()
        seen += 1
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                stack.append(v)
    return seen == nb


def normalise(blk):
    m = {}
    return tuple(m.setdefault(b, len(m)) for b in blk)


def omega_c_coeffs(rel, n):
    """a[k] = sum_{|pi|=k} (-1)^{k-1} mu(pi, 1), so that
    Omega_C(P, m) = sum_k a[k] C(m, k)."""
    OP = [p for p in rgs(n) if acyclic_quotient(p, rel, max(p) + 1)]
    OPset = set(OP)
    nblocks = {p: max(p) + 1 for p in OP}
    mu = {}
    for p in sorted(OP, key=lambda p: nblocks[p]):
        k = nblocks[p]
        if k == 1:
            mu[p] = 1
            continue
        s = 0
        for q in rgs(k):
            if max(q) + 1 == k:
                continue
            sigma = normalise(tuple(q[b] for b in p))
            if sigma in OPset:
                s += mu[sigma]
        mu[p] = -s
    a = [0] * (n + 1)
    for p in OP:
        k = nblocks[p]
        a[k] += (-1) ** (k - 1) * mu[p]
    return a


# ---------------------------------------------------------------------------
# Quasisymmetric functions of degree n, stored as Counter {frozenset J: c},
# J a subset of [n-1] (descent-set / partial-sum-set indexing).


def KCT_M(rel, n, comps, T):
    """K_{C,T}(P) in the monomial basis, from the definition.  An
    order-preserving f with image {v_1 < ... < v_k} gives the chain of order
    ideals I_j = f^{-1}[1, v_j] and contributes to M_alpha, alpha =
    (|I_1|, |I_2 - I_1|, ...).  f is T-anchored iff every I_j with j < k that
    is a union of components is disjoint from T."""
    full = (1 << n) - 1
    ids = ideal_masks(rel, n)

    def union(I):
        return all((I & c) in (0, c) for c in comps)
    ok = {I: I == full or not union(I) or (I & T) == 0 for I in ids}
    ids.sort(key=lambda m: bin(m).count("1"))
    # paths[I] = Counter of partial-sum sets of chains 0 < ... < I
    paths = {0: Counter({frozenset(): 1})}
    for I in ids:
        if I not in paths or I == full or (I != 0 and not ok[I]):
            continue
        sI = bin(I).count("1")
        for J in ids:
            if J != I and J & I == I:
                tgt = paths.setdefault(J, Counter())
                for S, c in paths[I].items():
                    tgt[S | {sI} if sI > 0 else S] += c
    return Counter({S: c for S, c in paths.get(full, Counter()).items() if c})


def m_to_f(n, mc):
    """M_J = sum_{K >= J} (-1)^{|K - J|} F_K."""
    f = Counter()
    for J, c in mc.items():
        free = [i for i in range(1, n) if i not in J]
        for r in range(len(free) + 1):
            for add in itertools.combinations(free, r):
                f[J | frozenset(add)] += c * (-1) ** r
    return Counter({K: v for K, v in f.items() if v})


def principal(n, fc, m):
    """F_J(1^m) = C(m + n - 1 - |J|, n)."""
    return sum(c * comb(m + n - 1 - len(J), n) for J, c in fc.items())


# ---------------------------------------------------------------------------
# Words, cuts, pieces, classes (labels = the integers of the word)


def Des(w):
    return frozenset(i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def cdes(w):
    return len(Des(w)) + (1 if w[-1] > w[0] else 0)


def cuts(w, comps):
    out, mask = [], 0
    for p in range(1, len(w)):
        mask |= 1 << w[p - 1]
        if all((mask & c) in (0, c) for c in comps):
            out.append(p)
    return out


def classes(lin, comps):
    seen = set()
    out = []
    for w in lin:
        if w in seen:
            continue
        cl = [w] + [w[p:] + w[:p] for p in cuts(w, comps)]
        seen.update(cl)
        out.append(cl)
    return out


def last_piece_has_T(w, comps, T):
    c = cuts(w, comps)
    start = c[-1] if c else 0
    return any(T >> x & 1 for x in w[start:])


def CT(w, comps, T):
    pos = {x: i for i, x in enumerate(w)}
    tl = max(pos[x] for x in range(len(w)) if T >> x & 1)
    return [p for p in cuts(w, comps) if p > tl]


def G_T(w, comps, T):
    """Generating function of the T-anchored f whose Stanley word is w:
    weakly increasing along w, strict at Des(w), equal at C_T(w).
    Inclusion-exclusion over the forced equalities."""
    D = Des(w)
    C = CT(w, comps, T)
    if any(p in D for p in C):
        return Counter()
    out = Counter()
    for r in range(len(C) + 1):
        for S in itertools.combinations(C, r):
            out[D | frozenset(S)] += (-1) ** r
    return Counter({K: v for K, v in out.items() if v})


def add(a, b):
    c = Counter(a)
    for k, v in b.items():
        c[k] += v
    return Counter({k: v for k, v in c.items() if v})


def F_sum_of_reps(reps):
    return Counter(Des(w) for w in reps)


def fmt(fc):
    return " + ".join(f"{c}*F{sorted(J)}" for J, c in
                      sorted(fc.items(), key=lambda t: (len(t[0]), sorted(t[0]))))


# ---------------------------------------------------------------------------
# Brute force of the bijective statement


def stanley_word(f, n):
    return tuple(sorted(range(n), key=lambda x: (f[x], x)))


def anchored(f, n, comps, T):
    for v in sorted(set(f)):
        U = sum(1 << x for x in range(n) if f[x] >= v)
        if all((U & c) in (0, c) for c in comps) and (U & T) != T:
            return False
    return True


# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--lmax", type=int, default=6,
                    help="largest n at which every natural labelling is tried")
    ap.add_argument("--specmax", type=int, default=7,
                    help="largest n for the Moebius specialisation check")
    ap.add_argument("--bijmax", type=int, default=5)
    args = ap.parse_args(argv)

    by_n = unlabeled_posets(args.nmax)
    st = Counter()
    first = {}

    def note(key, ex):
        st[key] += 1
        if key not in first:
            first[key] = ex

    for n in range(1, args.nmax + 1):
        for rel0 in by_n[n]:
            st["posets"] += 1
            comps0 = components(rel0, n)
            # ---- K_{C,T} from the definition, every T (labelling-free)
            Ks = []
            for T0 in comps0:
                st["pairs"] += 1
                K = m_to_f(n, KCT_M(rel0, n, comps0, T0))
                Ks.append(K)
                if any(v < 0 for v in K.values()):
                    note("Fneg", (sorted(rel0), T0))
            if len({frozenset(K.items()) for K in Ks}) > 1:
                note("Tdep", (n, sorted(rel0), [fmt(K) for K in Ks]))
            # ---- specialisation against the Moebius definition
            if n <= args.specmax:
                a = omega_c_coeffs(rel0, n)
                for K in Ks:
                    for m in range(n + 2):
                        if principal(n, K, m) != sum(a[k] * comb(m, k)
                                                     for k in range(n + 1)):
                            note("spec-bad", sorted(rel0))
                            break
                st["spec-pairs"] += len(Ks)

            # ---- labellings: lambda_T for every T; all natural ones for n<=lmax
            labellings = {}
            for T0 in comps0:
                w = lambda_T_extension(rel0, n, T0)
                labellings.setdefault(("lamT", T0), w)
            labellings[("lam0", None)] = lambda_0_extension(rel0, n)
            if n <= args.lmax:
                for w in linexts(rel0, n):
                    labellings.setdefault(("all", w), w)
            seen_lab = set()
            for (kind, tag), w in labellings.items():
                assert is_linext(rel0, w)
                rel, lab = relabel(rel0, w)
                comps = components(rel, n)
                lin = linexts(rel, n)
                cls = classes(lin, comps)
                sep = is_separated(rel, n)
                for T0, K in zip(comps0, Ks):
                    T = relabel_mask(T0, lab)
                    ET = satisfies_ET(rel, n, T)
                    X, Xp = exit_conditions(lin, comps, T) if kind == "all" \
                        else (None, None)
                    key = (rel, T)
                    reps = []
                    for cl in cls:
                        r = [u for u in cl if last_piece_has_T(u, comps, T)]
                        assert len(r) == 1
                        reps.append(r[0])
                    rhs = F_sum_of_reps(reps)
                    holds = rhs == K
                    if kind == "lamT" and tag == T0:
                        st["lamT"] += 1
                        if not (sep and ET):
                            note("lamT-bad", sorted(rel0))
                        if n >= 2 and any(len(Des(r)) != cdes(r) - 1
                                          for r in reps):
                            note("lamT-cdes-bad", sorted(rel0))
                        if not holds:
                            note("lamT-thm-bad", sorted(rel0))
                        if lin_closed([u for u in lin
                                       if last_piece_has_T(u, comps, T)], n):
                            st["linP"] += 1
                        else:
                            note("notlinP", (sorted(rel), T))
                        # control: arbitrary representative
                        st["anyrep"] += 1
                        if F_sum_of_reps([cl[0] for cl in cls]) != K:
                            note("anyrep-fail", (sorted(rel), T, fmt(K)))
                    if kind == "lam0":
                        st["mindes"] += 1
                        mreps = [min(cl, key=lambda u: (len(Des(u)), u))
                                 for cl in cls]
                        if F_sum_of_reps(mreps) != K:
                            note("mindes-fail", (sorted(rel), T))
                    if kind != "all" or key in seen_lab:
                        continue
                    seen_lab.add(key)
                    st["lab-pairs"] += 1
                    if satisfies_Estar(rel, n, comps, T) != X:
                        note("Estar-bad", (sorted(rel), T))
                    if ET:
                        st["ET"] += 1
                        if not X:
                            note("ET-not-X", (sorted(rel), T))
                    if X:
                        st["X"] += 1
                    if X and not Xp:
                        note("X-not-Xp", (sorted(rel), T))
                    if Xp:
                        st["Xp"] += 1
                        for cl in cls:
                            st["pc-Xp"] += 1
                            g = Counter()
                            for u in cl:
                                g = add(g, G_T(u, comps, T))
                            if not (len(g) == 1 and list(g.values()) == [1]):
                                note("pc-Xp-bad", (sorted(rel), T, cl))
                    if holds != Xp:
                        note("iff-bad", (sorted(rel), T, holds, Xp))
                    if not Xp:
                        st["notXp"] += 1
                    if ET and not holds:
                        note("thmQ-bad", (sorted(rel), T))
                    # per-class qsym lift of Lemma 1, separated labellings
                    if sep:
                        st["pc-sep-pairs"] += 1
                        tot = Counter()
                        single = fpos = True
                        for cl in cls:
                            g = Counter()
                            for u in cl:
                                g = add(g, G_T(u, comps, T))
                            tot = add(tot, g)
                            st["pc-sep-classes"] += 1
                            if not (len(g) == 1 and list(g.values()) == [1]):
                                single = False
                                st["pc-sep-notsingle"] += 1
                                if any(v < 0 for v in g.values()):
                                    fpos = False
                                    st["pc-sep-notFpos"] += 1
                                    if "pc-neg-ex" not in first:
                                        first["pc-neg-ex"] = (sorted(rel), T,
                                                              cl, fmt(g))
                        if tot != K:
                            note("propD-qsym-bad", (sorted(rel), T))
                        if not single:
                            note("pc-sep-pair-notsingle", (sorted(rel), T))
                        if not fpos:
                            note("pc-sep-pair-notFpos", (sorted(rel), T))

            # ---- bijective statement, brute force
            if n <= args.bijmax:
                for T0 in comps0:
                    w = lambda_T_extension(rel0, n, T0)
                    rel, lab = relabel(rel0, w)
                    comps = components(rel, n)
                    T = relabel_mask(T0, lab)
                    for f in itertools.product(range(1, 4), repeat=n):
                        if any(f[a] > f[b] for a, b in rel):
                            continue
                        st["bij"] += 1
                        sw = stanley_word(f, n)
                        if anchored(f, n, comps, T) != last_piece_has_T(sw, comps, T):
                            note("bij-bad", (sorted(rel), T, f))
        print(f"# n = {n} done: posets {len(by_n[n])}", flush=True)

    print(f"# posets {st['posets']}, (P, T) pairs {st['pairs']}")
    print(f"# K_(C,T) depends on T for {st['Tdep']} posets; first: "
          f"{first.get('Tdep')}")
    check(st["Tdep"] > 0, "[T-dep] K_(C,T)(P) depends on T for some P "
          f"({st['Tdep']} posets)")
    check(st["Fneg"] == 0, f"[Fpos-all-T] K_(C,T)(P) F-positive for all "
          f"{st['pairs']} pairs (P, T), n <= {args.nmax}")
    check(st["spec-bad"] == 0, f"[spec] principal specialisation = Omega_C "
          f"from Moebius, m = 0..n+1, {st['spec-pairs']} pairs")
    check(st["lamT-bad"] == 0 and st["lamT-cdes-bad"] == 0,
          f"[lamT] lambda_T natural, separated, (E_T); |Des R_T| = cdes - 1 "
          f"({st['lamT']} pairs)")
    check(st["lamT-thm-bad"] == 0, f"[thmQ] lambda_T: K_(C,T) = sum_kappa "
          f"F_Des(R_T kappa) on all {st['lamT']} pairs (P, T), n <= {args.nmax}")
    check(st["ET-not-X"] == 0 and st["X-not-Xp"] == 0,
          f"[E=>X=>X'] (E_T) implies (X_T) implies (X'_T), n <= {args.lmax}: "
          f"{st['lab-pairs']} labelled pairs; E {st['ET']}, X {st['X']}, "
          f"X' {st['Xp']}")
    print(f"#  X' but not X: {st['Xp'] - st['X']} labelled pairs; "
          f"X but not E: {st['X'] - st['ET']}")
    check(st["Estar-bad"] == 0, f"[E*] (E*_T) iff (X_T) on all "
          f"{st['lab-pairs']} labelled pairs, n <= {args.lmax}")
    print(f"# under lambda_T, L_T(P) = Lin(P') for a poset P' on "
          f"{st['linP']} of {st['lamT']} pairs; first exception "
          f"{first.get('notlinP')}")
    check(st["thmQ-bad"] == 0, f"[thmQ] every natural labelling with (E_T), "
          f"n <= {args.lmax}: {st['ET']} labelled pairs")
    check(st["iff-bad"] == 0, f"[thmQ-iff] identity holds iff (X'_T), every "
          f"natural labelling n <= {args.lmax}: holds on {st['Xp']}, fails on "
          f"{st['notXp']} labelled pairs")
    check(st["pc-Xp-bad"] == 0, f"[perclass-X'] under (X'_T) each class "
          f"contributes one F: {st['pc-Xp']} classes")
    check(st["propD-qsym-bad"] == 0, f"[propD-qsym] sum_w G_T(w) = K_(C,T), "
          f"{st['pc-sep-pairs']} separated labelled pairs")
    check(st["bij-bad"] == 0, f"[bij] T-anchored iff Stanley word has T's "
          f"piece last, lambda_T, n <= {args.bijmax}, m = 3: {st['bij']} maps")
    print(f"# separated labelled pairs {st['pc-sep-pairs']}: classes "
          f"{st['pc-sep-classes']}, not a single F {st['pc-sep-notsingle']}, "
          f"not F-positive {st['pc-sep-notFpos']}")
    print(f"#  first non-F-positive class: {first.get('pc-neg-ex')}")
    control(st["pc-sep-pair-notsingle"], st["pc-sep-pairs"],
            "[ctl-perclass-sep] each class contributes a single F, "
            "separated labelling, every T")
    control(st["pc-sep-pair-notFpos"], st["pc-sep-pairs"],
            "[ctl-perclass-Fpos] each class contribution is F-positive, "
            "separated labelling, every T")
    control(st["mindes-fail"], st["mindes"],
            "[ctl-mindes] sum_kappa F_Des(lex-first min-des rotation), "
            "lambda_0, every T")
    print(f"#  first: {first.get('mindes-fail')}")
    control(st["anyrep-fail"], st["anyrep"],
            "[ctl-anyrep] sum_kappa F_Des(first listed rotation), lambda_T")
    print(f"#  first: {first.get('anyrep-fail')}")
    control(int(any(v < 0 for v in m_to_f(2, Counter({frozenset(): 1})).values())),
            1, "[ctl-Mneg] M_(2) is F-positive")
    if FAILS:
        print("FAILED:", FAILS)
        return 1
    print("ALL CLAIMS HOLD")
    return 0


if __name__ == "__main__":
    sys.exit(main())
