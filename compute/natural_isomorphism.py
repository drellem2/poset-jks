#!/usr/bin/env python3
"""Checks for notes/natural_isomorphism.md: which naturality of
H_P (x) sgn ~= Lie(P) holds.

Models (P a poset on {0..n-1}, W_P = C{Lin P}):
  M_P = W_P / R_P  (= image of W_P in C[S_n]/Sh_n;  ~= H_P (x) sgn)
  L_P = W_P e_zeta (= C[Lin P] / (W_P cap K_zeta); the e_zeta model)

Sections (each prints one line per n and a verdict):
  [ext]   R_P e_zeta = 0  <=>  P connected or n <= 2   (Thm 1 of the note)
  [wit]   the witness coefficient: u = t_1 s t_2..t_b has coefficient 1/n
          in (s ш t) e_zeta                                   (Thm 1 proof)
  [lie]   Lie_n cap K_zeta = 0, i.e. x -> x e_zeta is injective on Lie_n
  [sum]   phi_Sigma = sum over components i of phi_i is an Aut(P)-iso
          M_P -> L_P  (phi_i: good word b w.r.t. base component i -> b e_zeta)
  [cop]   candidate e_zeta-side structure maps L_{P+Q} -> L_P (x) L_Q do not
          descend (restriction, deconcatenation, cobracket); the cobracket
          does descend on the M side (control)

Arithmetic is mod primes p = 1 (mod 420), with zeta an n-th root of unity
mod p.  Full rank mod p implies full rank over Q(zeta) (reduction mod a
prime of Z[zeta] is a ring map); a vanishing mod p of a fixed integer
combination is only evidence, so every "fails" is witnessed at two primes.

Run from compute/:
    python3 natural_isomorphism.py --nmax 6 > output/natural_isomorphism.txt
"""

import argparse
import itertools
import sys
from collections import defaultdict

import poset_jks_check as pj
from conjecture_s import L as L_a, components, R_generators
from splitting_cycles import prime_1_mod, right_comb, root_of_unity, shuffles

P1 = prime_1_mod(420, 10**9)  # = 1 mod lcm(1..7), so zeta_n exists for n <= 7
P2 = prime_1_mod(420, 2 * 10**9)

# ---------------------------------------------------------------------------
# Linear algebra mod p (dense rows)


def rank_dense(rows, p):
    rows = [list(r) for r in rows]
    rank, ncol = 0, len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rank, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [x * inv % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def solve_rows(basis, targets, p):
    """Coefficients X with targets[r] = sum_d X[r][d] basis[d] (rows, mod p).
    Raises if a target is not in the span or the basis is dependent."""
    e, m = len(basis), len(basis[0])
    # augmented: columns of the system are the m coordinates
    # solve basis^T x = target^T  via elimination on [basis^T | targets^T]
    A = [[basis[d][c] % p for d in range(e)] + [t[c] % p for t in targets] for c in range(m)]
    rank = 0
    pivcols = []
    for c in range(e):
        piv = next((i for i in range(rank, m) if A[i][c]), None)
        if piv is None:
            raise ValueError("basis dependent")
        A[rank], A[piv] = A[piv], A[rank]
        inv = pow(A[rank][c], p - 2, p)
        A[rank] = [x * inv % p for x in A[rank]]
        for i in range(m):
            if i != rank and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rank])]
        pivcols.append(c)
        rank += 1
    for i in range(rank, m):
        if any(A[i][e:]):
            raise ValueError("target not in span")
    return [[A[d][e + r] for d in range(e)] for r in range(len(targets))]


# ---------------------------------------------------------------------------
# e_zeta model coordinates


def times_e_zeta(vec, n, z, p):
    """(sum_w c_w w) e_zeta = (1/n) sum_w sum_j zeta^{-j} c_w (w gamma^j)."""
    inv_n, zinv = pow(n, p - 2, p), pow(z, p - 2, p)
    out = defaultdict(int)
    for w, c in vec.items():
        for j in range(n):
            out[pj.rot(w, j)] = (out[pj.rot(w, j)] + c * pow(zinv, j, p) * inv_n) % p
    return {k: v for k, v in out.items() if v}


class EModel:
    """L_P with basis {rep_C e_zeta}; w = rep gamma^j gives w e_zeta = zeta^j rep e_zeta."""

    def __init__(self, lin, n, z, p):
        self.reps = pj.cyclic_classes(lin)
        self.index = {r: i for i, r in enumerate(self.reps)}
        self.n, self.z, self.p = n, z, p

    def coord(self, w):
        for j in range(self.n):
            r = pj.rot(w, -j)  # w = rot(r, j)
            if r in self.index:
                return self.index[r], pow(self.z, j, self.p)
        raise KeyError(w)


# ---------------------------------------------------------------------------
# M-model coordinates: kappa = L_0 (kernel exactly Sh_n), restricted to W_P


def good_words(lin, comps, base):
    comp_of = {y: c for c in comps for y in c}
    out = []
    for w in lin:
        seen = set()
        for y in w:
            seen.add(y)
            if all(comp_of[x] <= seen for x in seen):
                if base <= seen:
                    out.append(w)
                break
    return out


def kappa_rows(words, n, colindex):
    rows = []
    for w in words:
        v = L_a(w, 0) if n > 1 else {(): 1}
        r = [0] * len(colindex)
        for t, c in v.items():
            r[colindex[t]] += c
        rows.append(r)
    return rows


# ---------------------------------------------------------------------------
# [ext], [wit]


def is_connected_or_small(rel, n):
    return n <= 2 or len(components(rel, n)) == 1


def check_ext(posets, nmax, out):
    ok = True
    for n in range(1, nmax + 1):
        z = {p: root_of_unity(n, p) for p in (P1, P2)}
        cnt = agree = disc = 0
        for rel in posets[n]:
            cnt += 1
            lin = pj.linear_extensions(rel, n)
            gens = R_generators(rel, n, lin) if len(components(rel, n)) > 1 else []
            disc += len(components(rel, n)) > 1
            zero = {p: all(not times_e_zeta(g, n, z[p], p) for g in gens) for p in (P1, P2)}
            # R_P e_zeta = 0 is a statement about a fixed element; nonzero at
            # one prime proves nonzero.  Predicted: zero iff connected or n <= 2.
            pred = is_connected_or_small(rel, n)
            agree += (zero[P1] and zero[P2]) == pred if pred else (not zero[P1])
        line = agree == cnt
        ok &= line
        out.append(f"[ext] n={n}: {cnt} posets ({disc} disconnected): "
                   f"R_P e_zeta = 0 <=> (connected or n<=2): {agree}/{cnt}: {line}")
    return ok


def check_witness(posets, nmax, out):
    """For every disconnected P (n>=3), every proper union S of components,
    every s in Lin P|S, t in Lin P|T with |t| >= 2: the coefficient of
    u = t_1 s t_2...t_b in (s ш t) e_zeta is exactly 1/n."""
    ok = True
    for n in range(3, nmax + 1):
        p, z = P1, root_of_unity(n, P1)
        inv_n = pow(n, p - 2, p)
        cnt = good = 0
        for rel in posets[n]:
            comps = components(rel, n)
            if len(comps) == 1:
                continue
            lin = pj.linear_extensions(rel, n)
            for r in range(1, len(comps)):
                for Sc in itertools.combinations(comps, r):
                    S = frozenset().union(*Sc)
                    pairs = {(tuple(y for y in w if y in S), tuple(y for y in w if y not in S)) for w in lin}
                    for s, t in pairs:
                        if len(t) < 2:
                            continue
                        cnt += 1
                        u = (t[0],) + s + t[1:]
                        v = times_e_zeta({x: 1 for x in shuffles(s, t)}, n, z, p)
                        good += v.get(u, 0) == inv_n
        line = good == cnt
        ok &= line
        out.append(f"[wit] n={n}: (P,S,s,t) cases with |t|>=2: {cnt}; coefficient of u in "
                   f"(s ш t) e_zeta equals 1/n: {good}/{cnt}: {line}")
    return ok


# ---------------------------------------------------------------------------
# [lie]


def check_lie(nmax, out):
    ok = True
    for n in range(2, nmax + 1):
        p, z = P1, root_of_unity(n, P1)
        taus = [t + (n - 1,) for t in itertools.permutations(range(n - 1))]
        perms = list(itertools.permutations(range(n)))
        idx = {w: i for i, w in enumerate(perms)}
        rows = []
        for tau in taus:
            v = times_e_zeta(right_comb(tau), n, z, p)
            r = [0] * len(perms)
            for w, c in v.items():
                r[idx[w]] = c
            rows.append(r)
        rk = rank_dense(rows, p)
        line = rk == len(taus)
        ok &= line
        out.append(f"[lie] n={n}: rank of Lie_n e_zeta = {rk}, (n-1)! = {len(taus)}: {line}")
    return ok


# ---------------------------------------------------------------------------
# [sum]


def phi_matrices(rel, n, p, z):
    """Return (comps, Bs, Phi_i matrices, M-coord fn, L-coord fn, e).

    M_P basis: kappa(B_0) (B_0 = good words for the first component, ordered by
    class).  Phi_i[c] = L-coordinates (length e) of phi_i(B_0[c])."""
    lin = pj.linear_extensions(rel, n)
    comps = components(rel, n)
    em = EModel(lin, n, z, p)
    e = len(em.reps)
    cols = sorted({t for w in lin for t in L_a(w, 0)})
    colindex = {t: i for i, t in enumerate(cols)}
    Bs = []
    for comp in comps:
        B = good_words(lin, comps, comp)
        B.sort(key=lambda w: em.coord(w)[0])
        assert [em.coord(w)[0] for w in B] == list(range(e))
        Bs.append(B)
    K = [kappa_rows(B, n, colindex) for B in Bs]
    Phis = []
    for i, B in enumerate(Bs):
        X = solve_rows(K[i], K[0], p)  # kappa(B_0[c]) = sum_d X[c][d] kappa(B_i[d])
        D = [em.coord(b)[1] for b in B]
        Phis.append([[X[c][d] * D[d] % p for d in range(e)] for c in range(e)])

    def mcoord(w):
        return solve_rows(K[0], kappa_rows([w], n, colindex), p)[0]

    def lcoord(w):
        c, s = em.coord(w)
        v = [0] * e
        v[c] = s
        return v

    return comps, Bs, Phis, mcoord, lcoord, e, em


def apply_mat(vec, M, p):
    e = len(M[0])
    return [sum(vec[c] * M[c][d] for c in range(len(vec))) % p for d in range(e)]


def equivariant(rel, n, Phi, mcoord, lcoord, em, Bs, p):
    """Phi(g . b) = g . Phi(b) for all g in Aut P and b in B_0."""
    for g in pj.automorphisms(rel, n):
        for b in Bs[0]:
            lhs = apply_mat(mcoord(pj.compose(g, b)), Phi, p)
            phib = apply_mat(mcoord(b), Phi, p)
            rhs = [0] * len(phib)
            for c, rep in enumerate(em.reps):
                if phib[c]:
                    v = lcoord(pj.compose(g, rep))
                    rhs = [(x + phib[c] * y) % p for x, y in zip(rhs, v)]
            if lhs != rhs:
                return False
    return True


def check_sum(posets, nmax, out):
    ok = True
    for n in range(2, nmax + 1):
        cnt = inv_sum = inv_wt = eq_sum = 0
        single_fail = single_tested = 0
        bad = []
        for rel in posets[n]:
            if len(components(rel, n)) == 1:
                continue
            cnt += 1
            res = {}
            for p in (P1,):
                z = root_of_unity(n, p)
                comps, Bs, Phis, mcoord, lcoord, e, em = phi_matrices(rel, n, p, z)
                S = [[sum(Ph[c][d] for Ph in Phis) % p for d in range(e)] for c in range(e)]
                W = [[sum(len(comps[i]) * Phis[i][c][d] for i in range(len(Phis))) % p
                      for d in range(e)] for c in range(e)]
                res = (rank_dense(S, p) == e, rank_dense(W, p) == e)
                if n <= 5:
                    eq_sum += equivariant(rel, n, S, mcoord, lcoord, em, Bs, p)
                    # positive control: a single phi_0 is not equivariant
                    # whenever Aut(P) moves the base component
                    G = pj.automorphisms(rel, n)
                    if n > 2 and any(frozenset(g[y] for y in comps[0]) != comps[0] for g in G):
                        single_tested += 1
                        single_fail += not equivariant(rel, n, Phis[0], mcoord, lcoord, em, Bs, p)
            inv_sum += res[0]
            inv_wt += res[1]
            if not res[0]:
                bad.append(sorted(rel))
        line = inv_sum == cnt and (n > 5 or (eq_sum == cnt and single_fail == single_tested))
        ok &= line
        eqs = f"Aut-equivariant {eq_sum}/{cnt}; control: phi_0 alone non-equivariant {single_fail}/{single_tested}; " if n <= 5 else ""
        out.append(f"[sum] n={n}: disconnected posets {cnt}: {eqs}"
                   f"sum_i phi_i invertible {inv_sum}/{cnt}; size-weighted invertible {inv_wt}/{cnt}: {line}")
        for b in bad[:5]:
            out.append(f"      singular sum_i phi_i: P = {b}")
    return ok


# ---------------------------------------------------------------------------
# [cop]


def restrict_relabel(w, S):
    """w|S, relabelled order-preservingly onto 0..|S|-1."""
    order = sorted(S)
    m = {x: i for i, x in enumerate(order)}
    return tuple(m[y] for y in w if y in S)


def candidate_maps(w, S, T):
    """Yield (name, list of (coef, u, v)) for the three candidate maps."""
    u, v = restrict_relabel(w, S), restrict_relabel(w, T)
    k = len(S)
    pre_S = set(w[:k]) == S
    pre_T = set(w[:len(T)]) == T
    yield "restriction", [(1, u, v)]
    yield "deconcatenation", [(1, u, v)] if pre_S else []
    yield "cobracket", ([(1, u, v)] if pre_S else []) + ([(-1, u, v)] if pre_T else [])


def check_coproducts(posets, nmax, out):
    """P on {0..a-1}, Q on {a..n-1}, n <= nmax.  Each candidate map
    f: C[Lin(P+Q)] -> L_P (x) L_Q descends to L_{P+Q} iff it kills every
    w' - zeta^j w with w' = w gamma^j in Lin(P+Q)."""
    ok = True
    for n in range(2, nmax + 1):
        p = P1
        zn = root_of_unity(n, p)
        tested = 0
        fails = defaultdict(int)
        m_ok = m_tested = 0
        npred = cob_agree = 0
        for a in range(1, n):
            for relP in posets[a]:
                for relQ in posets[n - a]:
                    rel = set(relP) | {(x + a, y + a) for x, y in relQ}
                    S, T = frozenset(range(a)), frozenset(range(a, n))
                    lin = pj.linear_extensions(rel, n)
                    linP, linQ = pj.linear_extensions(relP, a), pj.linear_extensions(relQ, n - a)
                    eP = EModel(linP, a, root_of_unity(a, p), p)
                    eQ = EModel(linQ, n - a, root_of_unity(n - a, p), p)
                    linset = set(lin)
                    rels = []
                    for w in lin:
                        for j in range(1, n):
                            if pj.rot(w, j) in linset:
                                rels.append((w, j))
                    tested += 1
                    # predicted: the cobracket descends iff P, Q connected and |P| = |Q|
                    pred_cob = (len(components(relP, a)) == 1 and len(components(relQ, n - a)) == 1
                                and 2 * a == n)
                    npred += pred_cob
                    for name in ("restriction", "deconcatenation", "cobracket"):
                        def f(word):
                            acc = defaultdict(int)
                            for nm, terms in candidate_maps(word, S, T):
                                if nm != name:
                                    continue
                                for c, u, v in terms:
                                    cu, su = eP.coord(u)
                                    cv, sv = eQ.coord(v)
                                    acc[(cu, cv)] = (acc[(cu, cv)] + c * su * sv) % p
                            return acc
                        bad = False
                        for w, j in rels:
                            fw, fw2 = f(w), f(pj.rot(w, j))
                            zj = pow(zn, j, p)
                            keys = set(fw) | set(fw2)
                            if any((fw2.get(k, 0) - zj * fw.get(k, 0)) % p for k in keys):
                                bad = True
                                break
                        fails[name] += bad
                        if name == "cobracket":
                            cob_agree += bad != pred_cob
                    # control: the cobracket kills R_{P+Q} on the M side
                    # (kappa_S (x) kappa_T, kernel Sh_S (x) . + . (x) Sh_T)
                    m_tested += 1
                    good = True
                    for g in R_generators(rel, n, lin):
                        acc = defaultdict(int)
                        for word in g:
                            for nm, terms in candidate_maps(word, S, T):
                                if nm != "cobracket":
                                    continue
                                for c, u, v in terms:
                                    lu = L_a(u, 0) if a > 1 else {(): 1}
                                    lv = L_a(v, 0) if n - a > 1 else {(): 1}
                                    for x, cx in lu.items():
                                        for y, cy in lv.items():
                                            acc[(x, y)] += c * cx * cy
                        if any(acc.values()):
                            good = False
                            break
                    m_ok += good
        line = (fails["restriction"] == fails["deconcatenation"] == tested
                and cob_agree == tested and m_ok == m_tested)
        ok &= line
        out.append(f"[cop] n={n}: pairs (P,Q) {tested}: do NOT descend to L: "
                   + ", ".join(f"{nm} {fails[nm]}/{tested}" for nm in ("restriction", "deconcatenation", "cobracket"))
                   + f"; cobracket descends <=> (P,Q connected, |P|=|Q|) {cob_agree}/{tested} "
                   f"({npred} such pairs); control: cobracket descends on M {m_ok}/{m_tested}: {line}")
    return ok


# ---------------------------------------------------------------------------
# [psi]  psi_P : L_P -> M_P,  y |-> pr_P(y) mod R_P  (truncate support to Lin P)


def check_psi(posets, nmax, out):
    """psi_P(rep_C e_zeta) = (1/n) sum_{w in C} zeta^{-j(w)} w  (w = rep gamma^j).
    psi_P is an iso iff these e_C(P) elements are independent mod Sh_n."""
    ok = True
    for n in range(2, nmax + 1):
        p, z = P1, root_of_unity(n, P1)
        zinv = pow(z, p - 2, p)
        cnt = good = disc = 0
        for rel in posets[n]:
            cnt += 1
            disc += len(components(rel, n)) > 1
            lin = pj.linear_extensions(rel, n)
            em = EModel(lin, n, z, p)
            byclass = defaultdict(lambda: defaultdict(int))
            for w in lin:
                c, _ = em.coord(w)
                j = next(j for j in range(n) if pj.rot(em.reps[c], j) == w)
                for t, x in L_a(w, 0).items():
                    byclass[c][t] = (byclass[c][t] + x * pow(zinv, j, p)) % p
            cols = sorted({t for v in byclass.values() for t in v})
            ci = {t: i for i, t in enumerate(cols)}
            rows = []
            for c in range(len(em.reps)):
                r = [0] * len(cols)
                for t, x in byclass[c].items():
                    r[ci[t]] = x
                rows.append(r)
            good += rank_dense(rows, p) == len(em.reps)
        line = good == cnt
        ok &= line
        out.append(f"[psi] n={n}: {cnt} posets ({disc} disconnected): truncation map "
                   f"psi_P: L_P -> M_P is an isomorphism: {good}/{cnt}: {line}")
    return ok


# ---------------------------------------------------------------------------
# [dyn]  antichain: sum_i phi_i is x |-> x theta_n^* e_zeta up to a scalar


def check_dynkin(nmax, out):
    from splitting_cycles import dynkin_left
    ok = True
    for n in range(2, nmax + 1):
        p, z = P1, root_of_unity(n, P1)
        rel = frozenset()
        comps, Bs, Phis, mcoord, lcoord, e, em = phi_matrices(rel, n, p, z)
        S = [[sum(Ph[c][d] for Ph in Phis) % p for d in range(e)] for c in range(e)]
        theta = dynkin_left(n)
        theta_star = {pj.inverse(t): c for t, c in theta.items()}
        ratio = None
        good = True
        for b in itertools.permutations(range(n)):
            lhs = apply_mat(mcoord(b), S, p)
            y = times_e_zeta({pj.compose(b, t): c for t, c in theta_star.items()}, n, z, p)
            rhs = [n * y.get(r, 0) % p for r in em.reps]
            for x, yv in zip(lhs, rhs):
                if yv and ratio is None:
                    ratio = x * pow(yv, p - 2, p) % p
                if (x - (ratio or 0) * yv) % p:
                    good = False
        good &= ratio is not None and ratio != 0
        # identify the scalar as a small integer
        lab = next((str(k) for k in range(-50, 51) if k and (k - ratio) % p == 0), str(ratio))
        ok &= good
        out.append(f"[dyn] n={n}: antichain: sum_i phi_i(x) = c * (x theta_n^* e_zeta) for all words x: "
                   f"{good}, c = {lab}")
    return ok


# ---------------------------------------------------------------------------
# [wgt]  Theorem Psi in its weighted form (the form the induction proves)


def union_prefix_cuts(w, comps):
    comp_of = {y: c for c in comps for y in c}
    seen, cuts = set(), [0]
    for i, y in enumerate(w):
        seen.add(y)
        if i + 1 < len(w) and all(comp_of[x] <= seen for x in seen):
            cuts.append(i + 1)
    return cuts


def lin_class_reps(lin):
    """One member of Lin P per cyclic class: the least word of C cap Lin P.

    pj.cyclic_classes returns the least rotation, which need not lie in
    Lin P; s_lam(C) must be built from a word of Lin P (audit section 5)."""
    reps = {}
    for w in sorted(lin):
        reps.setdefault(pj.class_rep(w), w)
    return [reps[c] for c in sorted(reps)]


def weighted_rank(rel, n, lam, p, reps_fn=lin_class_reps):
    """Rank mod Sh of { s(w_C) = sum_{cuts k} lam(w_1..w_k)^{-1} rot(w_C, k) },
    w_C in C cap Lin P.  reps_fn is a hook for the positive-control test."""
    lin = pj.linear_extensions(rel, n)
    comps = components(rel, n)
    reps = reps_fn(lin)
    rows, colindex = [], {}
    for r in reps:
        acc = defaultdict(int)
        for k in union_prefix_cuts(r, comps):
            ph = 1
            for y in r[:k]:
                ph = ph * lam[y] % p
            phinv = pow(ph, p - 2, p)
            for t, x in L_a(pj.rot(r, k), 0).items():
                acc[t] = (acc[t] + x * phinv) % p
        rows.append(acc)
    cols = sorted({t for a in rows for t in a})
    ci = {t: i for i, t in enumerate(cols)}
    dense = []
    for a in rows:
        d = [0] * len(cols)
        for t, x in a.items():
            d[ci[t]] = x
        dense.append(d)
    return (rank_dense(dense, p) if cols else 0), len(reps)


def check_weights(posets, nmax, out, seed=1, reps_fn=lin_class_reps):
    import random
    rng = random.Random(seed)
    ok = True
    p = P1
    for n in range(2, nmax + 1):
        cnt = good = ctl_tested = ctl_drop = 0
        anti_drop = False
        for rel in posets[n]:
            comps = components(rel, n)
            unions = [frozenset().union(*c) for r in range(1, len(comps))
                      for c in itertools.combinations(comps, r)]
            for _ in range(2):
                while True:
                    lam = [rng.randrange(1, p) for _ in range(n - 1)]
                    prod = 1
                    for x in lam:
                        prod = prod * x % p
                    lam.append(pow(prod, p - 2, p))
                    if all(_prod(lam, U, p) != 1 for U in unions):
                        break
                cnt += 1
                rk, e = weighted_rank(rel, n, lam, p, reps_fn)
                good += rk == e
            if len(comps) > 1:
                # lam = 1 violates the hypothesis; for antichains the rank
                # must drop (cyclic sums of words lie in Sh_n): positive control
                ctl_tested += 1
                rk, e = weighted_rank(rel, n, [1] * n, p, reps_fn)
                ctl_drop += rk < e
                if not rel:
                    anti_drop = rk < e
        # lam = 1 always drops for disconnected P (PROVEN, audit section 5):
        # sum_C s_1(C) = sum_{w in Lin P} w lies in Sh_n
        line = good == cnt and anti_drop and ctl_drop == ctl_tested
        ok &= line
        out.append(f"[wgt] n={n}: random admissible weights: independent {good}/{cnt}; "
                   f"lam=1 (inadmissible): rank drops for {ctl_drop}/{ctl_tested} disconnected P, "
                   f"incl. the antichain (control): {anti_drop}: {line}")
    return ok


def _prod(lam, U, p):
    r = 1
    for y in U:
        r = r * lam[y] % p
    return r


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=5)
    ap.add_argument("--cop-nmax", type=int, default=5)
    ap.add_argument("--only", default="ext,wit,lie,sum,psi,wgt,dyn,cop",
                    help="comma-separated sections to run")
    args = ap.parse_args(argv)
    only = set(args.only.split(","))
    posets = pj.unlabeled_posets_by_extension(args.nmax)
    out = []
    ok = True
    sections = [
        ("ext", lambda: check_ext(posets, args.nmax, out)),
        ("wit", lambda: check_witness(posets, args.nmax, out)),
        ("lie", lambda: check_lie(args.nmax, out)),
        ("sum", lambda: check_sum(posets, args.nmax, out)),
        ("psi", lambda: check_psi(posets, args.nmax, out)),
        ("wgt", lambda: check_weights(posets, args.nmax, out)),
        ("dyn", lambda: check_dynkin(min(args.nmax, 5), out)),
        ("cop", lambda: check_coproducts(posets, min(args.nmax, args.cop_nmax), out)),
    ]
    for name, fn in sections:
        if name in only:
            ok &= fn()
    out.append("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    print("\n".join(out))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
