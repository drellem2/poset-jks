#!/usr/bin/env python3
"""Checks for notes/general_theory.md (mg-2858d).  Plain Python 3.

Part I (cones of real arrangements; reuses cone_lie.py).  For every top-cone
V of each arrangement, with L = lin V (the flats Z with Z >= S_max(V), as zero
sets) and Lambda(V) the supports of the faces of V:
  [flatL] every flat Z >= S_max lies in Lambda(V).
  [zas]   #V = sum_{flats Z >= S_max} m(V_Z),
          m(V_Z) := (-1)^{rank Z} mu_{Lambda(V)}(Z, top)        (Theorem 2).
  [wedge] reduced homology of the proper part of Lambda(V) is concentrated
          in degree d-2, of rank m(V) := m(V_bottom)              (Theorem 1).
  [brown] sum_{Z >= S_max} mu_L(bottom, Z) c_Z = m(V), where c_Z is the
          number of chambers of V above a face of support Z     (Prop. 3).
  [q=m]   q(V) = dim Gamma_V/(Gamma_V cap Lune) equals m(V)    (Conj. G).
  [eq]    for the stabiliser of V in the symmetry group W:
          tr(g | H~_{d-2}(Lambda(V))) = det(g) tr(g | (Gamma_V+Lune)/Lune),
          with the left side computed as (-1)^d mu(Lambda(V)^g)  (Conj. G-eq).
  Control: for types B and D the same identity without det must fail on
  some cone.  For A2, A3, A4 it cannot: there sgn (x) M ~ M for every cone
  (n = 3, 4, 5; cf. the n = 6 twist in poset_jks_theorem.tex, Prop. frob),
  so the untwisted count is reported only.

Part II (posets, n <= NMAX):
  [foata] the Foata map from linear extensions (as sequences of irreducible
          pieces) to sets of cycles of pieces is injective, and its image
          has size sum_{sigma in Pi(K)} prod_B e_C(P|_B) = |Lin P|  (Lemma 5).
  [pbw]   shuffle products of first-block bases over sigma in Pi(K) have
          rank |Lin P| and there are exactly |Lin P| of them     (Theorem 6).
  [prim]  dim of the primitives of Q' in degree P equals e_C(P)  (Theorem 7).
  [pbw-eq] for every g in Aut(P): the character of C[Lin P] (|Lin P| at 1,
          0 elsewhere) equals sum over g-stable sigma of the tensor-induced
          character of the Lie(P|_B), computed from fixed cyclic classes.

Exit status 0 iff every asserted check passes.

Run from compute/:  python3 general_theory.py [--quick]
"""

import argparse
import cmath
import itertools
import sys
from collections import defaultdict

import cone_lie as cl
import poset_jks_check as pj

P = cl.P


# ---------------------------------------------------------------------------
# Part I: cones


def symmetry_group(name, vecs, covs):
    """Elements as (perm, signs, det): (g x)_{perm[e]} = signs[e] * x_e."""
    m = len(vecs)
    d = len(vecs[0])
    out = []
    if name.startswith("A"):
        n = d + 1
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        idx = {p: k for k, p in enumerate(pairs)}
        for g in itertools.permutations(range(n)):
            perm, signs = [0] * m, [0] * m
            for k, (i, j) in enumerate(pairs):
                a, b = g[i], g[j]
                perm[k] = idx[(min(a, b), max(a, b))]
                signs[k] = 1 if a < b else -1
            out.append((tuple(perm), tuple(signs), pj.sign(g)))
    elif name.startswith(("B", "D")):
        vidx = {v: k for k, v in enumerate(vecs)}
        for g in itertools.permutations(range(d)):
            for eps in itertools.product((1, -1), repeat=d):
                # M e_i = eps_i e_{g(i)}; (Mx)_f = sgn<M^T v_f, p>.
                # Equivalently map normals forward: M v_e = c v_f.
                perm, signs = [0] * m, [0] * m
                for e, v in enumerate(vecs):
                    w = [0] * d
                    for i in range(d):
                        w[g[i]] += eps[i] * v[i]
                    w = tuple(w)
                    if w in vidx:
                        perm[e], signs[e] = vidx[w], 1
                    else:
                        perm[e] = vidx[tuple(-x for x in w)]
                        signs[e] = -1
                det = pj.sign(g)
                for x in eps:
                    det *= x
                out.append((tuple(perm), tuple(signs), det))
    else:
        return None
    covset = set(covs)
    for perm, signs, _ in out:  # sanity: the action preserves covectors
        for x in covs[:50]:
            assert act_cov(perm, signs, x) in covset
    return out


def act_cov(perm, signs, x):
    y = [0] * len(x)
    for e, a in enumerate(x):
        y[perm[e]] = signs[e] * a
    return tuple(y)


def mobius_up(elems, Z, less):
    """mu(Z, y) for y >= Z; elems sorted bottom-first."""
    mu = {Z: 1}
    start = elems.index(Z)
    for y in elems[start + 1:]:
        if less(Z, y):
            mu[y] = -sum(mu[w] for w in mu if w != y and less(w, y))
    return mu


def trace_mod_lune(Vs, res, act_tope):
    """tr(g | span{res[i] : i in V}); act_tope: i -> g(i). Integer result."""
    basis, pivrows = [], {}
    # echelon form; each pivot row is recorded as a combination of res[b],
    # b in basis
    for i in Vs:
        v = dict(res[i])
        comb = {i: 1}
        for c, (r, rc) in sorted(pivrows.items()):
            if c in v:
                f = v[c]
                for cc, x in r.items():
                    v[cc] = (v.get(cc, 0) - f * x) % P
                    if v[cc] == 0:
                        del v[cc]
                for cc, x in rc.items():
                    comb[cc] = (comb.get(cc, 0) - f * x) % P
        if v:
            c = min(v)
            inv = pow(v[c], P - 2, P)
            pivrows[c] = ({k: x * inv % P for k, x in v.items()},
                          {k: x * inv % P for k, x in comb.items()})
            basis.append(i)
    # coordinates of a vector in terms of the basis residues
    def coords(y):
        y = dict(y)
        out = defaultdict(int)
        for c, (r, rc) in sorted(pivrows.items()):
            if c in y:
                f = y[c]
                for cc, x in r.items():
                    y[cc] = (y.get(cc, 0) - f * x) % P
                    if y[cc] == 0:
                        del y[cc]
                for k, x in rc.items():
                    out[k] = (out[k] + f * x) % P
        assert not y, "vector not in span"
        return out

    tr = 0
    for b in basis:
        cb = coords(res[act_tope(b)])
        assert set(k for k, x in cb.items() if x) <= set(basis)
        tr = (tr + cb.get(b, 0)) % P
    return tr if tr < P // 2 else tr - P


def run_cones(name, vecs, cones, samples, homology, eq, out):
    covs, cc = cl.covectors(vecs)
    m, d = len(vecs), len(vecs[0])
    topes = [x for x in covs if all(x)]
    tindex = {t: i for i, t in enumerate(topes)}
    flats = sorted({cl.zeros(x) for x in covs}, key=lambda Z: -len(Z))
    rank = {Z: cl.rank_q([vecs[e] for e in Z]) if Z else 0 for Z in flats}
    E = frozenset(range(m))
    flats_max = sorted({cl.zeros(c) for c in cc}, key=sorted)
    less = lambda a, b: a > b
    mu_full = cl.moebius_from_bottom(flats, less)[frozenset()]
    piv, res = cl.lune_quotient(topes, flats_max, len(topes) - abs(mu_full))
    assert len(piv) == len(topes) - abs(mu_full)
    G = symmetry_group(name, vecs, covs) if eq else None
    if G is not None:
        assert len({(p, s) for p, s, _ in G}) == len(G)
        tperm = [[tindex[act_cov(p, s, t)] for t in topes] for p, s, _ in G]
    conelist = (cl.all_top_cones(topes, m) if cones == "all"
                else cl.sampled_top_cones(topes, m, samples, 2))
    st = defaultdict(int)
    for V in conelist:
        st["n"] += 1
        Vs = sorted(V)
        Vt = [topes[i] for i in Vs]
        Smax = {}
        for e in range(m):
            s = {t[e] for t in Vt}
            if len(s) == 1:
                Smax[e] = s.pop()
        Sk = frozenset(Smax)
        faces = [x for x in covs if all(x[e] in (0, s) for e, s in Smax.items())]
        sup = sorted({cl.zeros(x) for x in faces}, key=lambda Z: -len(Z))
        supset = set(sup)
        Lflats = [Z for Z in flats if Z >= Sk]
        st["flatL"] += all(Z in supset for Z in Lflats)
        mvals = {}
        for Z in Lflats:
            muZ = mobius_up(sup, Z, less)
            mvals[Z] = (-1) ** rank[Z] * muZ[frozenset()]
        mV = mvals[E]
        st["zas"] += sum(mvals.values()) == len(V)
        # Brown multiplicity for the lineality face monoid acting on V
        muL = cl.moebius_from_bottom(Lflats, less)
        cZ = {}
        okc = True
        for x in faces:
            Z = cl.zeros(x)
            if Z >= Sk:
                c = sum(1 for i in Vs if cl.leq_face(x, topes[i]))
                if cZ.setdefault(Z, c) != c:
                    okc = False
        st["brown"] += okc and sum(muL[Z] * cZ[Z] for Z in Lflats) == mV
        q = cl.rank_mod_p([res[i] for i in Vs])
        st["q=m"] += q == mV
        if homology:
            b = cl.reduced_betti(sup[1:-1], less)
            st["wedge"] += (set(b) <= {d - 2}) and b.get(d - 2, 0) == mV
        if G is not None:
            okt = oku = True
            stab = [k for k, tp in enumerate(tperm) if all(tp[i] in V for i in Vs)]
            st["stab"] += len(stab)
            for k in stab:
                perm, signs, det = G[k]
                fixed = [Z for Z in sup
                         if frozenset(perm[e] for e in Z) == Z]
                chiH = (-1) ** d * cl.moebius_from_bottom(fixed, less)[frozenset()]
                chiQ = trace_mod_lune(Vs, res, tperm[k].__getitem__)
                okt &= chiH == det * chiQ
                oku &= chiH == chiQ
            st["eq"] += okt
            st["eq_untwisted"] += oku
    n = st["n"]
    print(f"[{name}] d={d} m={m} topes={len(topes)} cones={n} ({cones})", file=out)
    keys = ["flatL", "zas", "brown", "q=m"] + (["wedge"] if homology else []) \
        + (["eq"] if G is not None else [])
    ok = True
    for k in keys:
        print(f"  [{k}] {st[k]}/{n}", file=out)
        ok &= st[k] == n
    if G is not None:
        print(f"  [eq] |W|={len(G)}, sum of stabiliser orders {st['stab']}; "
              f"control (no det twist) holds on {st['eq_untwisted']}/{n} cones",
              file=out)
        if name.startswith(("B", "D")):
            ok &= st["eq_untwisted"] < n  # the twist must matter somewhere
    print(f"  => {'PASS' if ok else 'FAIL'}", file=out)
    return ok


ARR = [
    ("A2", cl.braid(3), "all", True, True),
    ("A3", cl.braid(4), "all", True, True),
    ("B2", cl.type_b(2), "all", True, True),
    ("B3", cl.type_b(3), "all", True, True),
    ("generic5 R^3", cl.random_arrangement(5, 3, 7), "all", True, False),
    ("random7 R^3", cl.random_arrangement(7, 3, 3, box=2), "all", True, False),
    ("random6 R^4", cl.random_arrangement(6, 4, 5, box=2), "all", True, False),
    ("A4", cl.braid(5), "all", False, True),
    ("D4", cl.type_d(4), "sample", False, True),
]


# ---------------------------------------------------------------------------
# Part II: posets


def comps_of(rel, n):
    adj = defaultdict(set)
    for a, b in rel:
        adj[a].add(b)
        adj[b].add(a)
    seen, out = set(), []
    for s in range(n):
        if s in seen:
            continue
        c, st = {s}, [s]
        seen.add(s)
        while st:
            y = st.pop()
            for z in adj[y] - seen:
                seen.add(z)
                c.add(z)
                st.append(z)
        out.append(frozenset(c))
    return out


def pieces(w, comps):
    """Split w at every cut (prefix that is a union of components)."""
    comp_of = {y: c for c in comps for y in c}
    out, cur, seen = [], [], set()
    for y in w:
        cur.append(y)
        seen.add(y)
        if all(comp_of[z] <= seen for z in seen):
            out.append(tuple(cur))
            cur = []
    assert not cur
    return out


def foata(seq):
    """Sequence of distinct pieces -> frozenset of cycles (canonical form:
    rotation starting at the piece with the largest label)."""
    key = lambda p: min(p)
    cycles, cur, best = [], [], None
    for p in seq:
        if best is None or key(p) > best:
            if cur:
                cycles.append(tuple(cur))
            cur, best = [p], key(p)
        else:
            cur.append(p)
    if cur:
        cycles.append(tuple(cur))
    return frozenset(cycles)


def restrict(rel, B):
    Bs = sorted(B)
    loc = {x: i for i, x in enumerate(Bs)}
    return frozenset((loc[a], loc[b]) for a, b in rel if a in B and b in B), Bs


def e_C(rel, n):
    return len(pj.cyclic_classes(pj.linear_extensions(rel, n)))


def partitions_of(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in partitions_of(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def shuffles(u, v):
    if not u:
        return [v]
    if not v:
        return [u]
    return [(u[0],) + w for w in shuffles(u[1:], v)] + \
           [(v[0],) + w for w in shuffles(u, v[1:])]


def lie_char(rel, n, h):
    """tr(h | Lie(Q)) = sum over h-fixed cyclic classes of zeta^r (integer)."""
    lin = pj.linear_extensions(rel, n)
    tot = 0
    zeta = cmath.exp(2j * cmath.pi / n)
    for c in pj.cyclic_classes(lin):
        w = next(x for x in lin if pj.class_rep(x) == c)
        r = pj.rotation_amount(h, w)
        if r is not None:
            tot += zeta ** r
    v = round(tot.real)
    assert abs(tot - v) < 1e-6
    return v


def run_posets(nmax, out):
    ok = True
    allp = pj.unlabeled_posets_by_extension(nmax)
    for n in range(1, nmax + 1):
        st = defaultdict(int)
        for rel in allp[n]:
            st["n"] += 1
            comps = comps_of(rel, n)
            lin = pj.linear_extensions(rel, n)
            # [foata]
            imgs = set()
            for w in lin:
                imgs.add(foata(pieces(w, comps)))
            pred = 0
            for sig in partitions_of(comps):
                prod = 1
                for blk in sig:
                    B = frozenset().union(*blk)
                    r, _ = restrict(rel, B)
                    prod *= e_C(r, len(B))
                pred += prod
            st["foata"] += len(imgs) == len(lin) == pred
            # [pbw]: shuffle products of first-block bases over sigma
            vecs, count = [], 0
            idx = {w: i for i, w in enumerate(lin)}
            for sig in partitions_of(comps):
                bases = []
                for blk in sig:
                    B = frozenset().union(*blk)
                    r, Bs = restrict(rel, B)
                    lc = comps_of(r, len(Bs))
                    base = [c for c in lc if 0 in c][0]
                    words = []
                    for u in pj.linear_extensions(r, len(Bs)):
                        pcs = pieces(u, lc)
                        if 0 in pcs[0] or set(base) <= set(pcs[0]):
                            words.append(tuple(Bs[i] for i in u))
                    bases.append(words)
                for combo in itertools.product(*bases):
                    acc = [combo[0]]
                    for wd in combo[1:]:
                        acc = [z for a in acc for z in shuffles(a, wd)]
                    v = {}
                    for z in acc:
                        v[idx[z]] = v.get(idx[z], 0) + 1
                    vecs.append(v)
                    count += 1
            st["pbw"] += count == len(lin) and cl.rank_mod_p(vecs) == len(lin)
            # [prim]: primitives of Q' in degree P = annihilator of R_P
            Rg = []
            for k in range(1, len(comps)):
                for S in itertools.combinations(comps, k):
                    S = frozenset().union(*S)
                    seen = set()
                    for w in lin:
                        s = tuple(y for y in w if y in S)
                        t = tuple(y for y in w if y not in S)
                        if (s, t) in seen:
                            continue
                        seen.add((s, t))
                        Rg.append({idx[z]: 1 for z in shuffles(s, t)})
            rR = cl.rank_mod_p(Rg) if Rg else 0
            st["prim"] += len(lin) - rR == e_C(rel, n)
            # [pbw-eq]
            okg = True
            for g in pj.automorphisms(rel, n):
                lhs = len(lin) if all(g[i] == i for i in range(n)) else 0
                rhs = 0
                for sig in partitions_of(comps):
                    blocks = [frozenset().union(*blk) for blk in sig]
                    bset = set(blocks)
                    if any(frozenset(g[x] for x in B) not in bset for B in blocks):
                        continue
                    term, done = 1, set()
                    for B in blocks:
                        if B in done:
                            continue
                        orbit, C = [], B
                        while C not in orbit:
                            orbit.append(C)
                            C = frozenset(g[x] for x in C)
                        done |= set(orbit)
                        k = len(orbit)
                        gk = list(range(n))
                        for _ in range(k):
                            gk = [g[x] for x in gk]
                        r, Bs = restrict(rel, B)
                        loc = {x: i for i, x in enumerate(Bs)}
                        h = tuple(loc[gk[x]] for x in Bs)
                        term *= lie_char(r, len(Bs), h)
                    rhs += term
                okg &= lhs == rhs
            st["pbw-eq"] += okg
        line = " ".join(f"[{k}] {st[k]}/{st['n']}" for k in
                        ("foata", "pbw", "prim", "pbw-eq"))
        print(f"[posets n={n}] {st['n']} posets: {line}", file=out)
        ok &= all(st[k] == st["n"] for k in ("foata", "pbw", "prim", "pbw-eq"))
    return ok


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="skip A4, D4 and use posets n <= 4")
    ap.add_argument("--nmax", type=int, default=6)
    args = ap.parse_args(argv)
    allok = True
    for name, vecs, mode, hom, eq in ARR:
        if args.quick and name in ("A4", "D4"):
            continue
        allok &= run_cones(name, vecs, mode, 150, hom, eq, sys.stdout)
        sys.stdout.flush()
    allok &= run_posets(4 if args.quick else args.nmax, sys.stdout)
    print("ALL CHECKS PASSED" if allok else "SOME CHECKS FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
