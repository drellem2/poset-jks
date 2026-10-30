#!/usr/bin/env python3
"""Cone/lune Lie theory for top-cones of real hyperplane arrangements (mg-3ab4a).

Companion to notes/cone_lune_lie_theory.md.  Plain Python 3, no dependencies.

An arrangement is a list of integer normal vectors in R^d (essential: rank d).
Everything is computed from its oriented matroid of covectors:
  * cocircuits = sign vectors of the lines (rank d-1 intersections),
  * covectors  = closure of {0} under right Tits product by cocircuits
                 (every covector is a composition of cocircuits),
  * topes (chambers) = covectors with no zero entry,
  * Tits product (XY)_e = X_e if X_e != 0 else Y_e,
  * support of X = its zero set z(X); flats ordered by reverse inclusion.

A top-cone V is a set of topes {C : C_e = s_e for e in S}; S_max(V) is the
set of all hyperplanes with V on one side.  Faces of V = covectors X with
X_e in {0, s_e} for e in S_max; lin(V) = faces with X_e = 0 on S_max.

Lunes (Aguiar-Mahajan top-lunes): for a flat Z != E (E = all hyperplanes) and
a tope D, the lune is {C : C|_Z = D|_Z}.  The lune span Lune is spanned by the
lunes of the maximal proper flats Z (zero sets of cocircuits), since a lune of
Z is a disjoint union of lunes of any Z' containing Z.

Checks, per arrangement and per top-cone V (each prints a line; exit 0 iff
all pass):
  [lrb]  the faces of V are closed under the Tits product and contain 0.
  [lin]  for every flat Z != E and tope D: lune(Z, D) is contained in V iff
         D in V and S_max(V) is contained in Z  (i.e. some face H with
         z(H) = Z, H <= D, lies in lin V).
  [q]    q(V) := dim (Gamma_V + Lune)/Lune  equals  dim H~_top(Lambda(V)),
         where Lambda(V) = supports of faces of V (bounded), and the
         reduced homology of its proper part is concentrated in top degree.
  [K]    Gamma_V cap Lune is spanned by the lunes contained in V.
  [full] for V = all topes: q = |mu(flat lattice)| (Aguiar-Mahajan, Zaslavsky).
Reported but not asserted:
  [brown] Brown's multiplicity of the bottom simple in the chamber module of
          the LRB F(V):  m = sum_{X in Lambda(V)} mu(bottom, X) c_X,
          c_X = number of topes of V above a face of V with support X.

Ranks are modulo the prime P; rank_p <= rank_Q.  The [q] comparison is made
rigorous as follows: Lune is computed until its p-rank reaches
#topes - |mu|, which is its rational dimension (CITED: Aguiar-Mahajan, Topics
Thm 14.32 / Prop. 14.25 and Lemma 10.7); a p-basis of that size is then a
Q-basis.  q_p = rank_p of the image of Gamma_V in the quotient coordinates is
<= q_Q, and q_Q <= dim H_top(Lambda(V)) is not known a priori in general, so
the equality q_p == h_top is reported as COMPUTED over F_p only (see notes).

Run:  python3 cone_lie.py [--quick]
"""

import argparse
import itertools
import random
import sys
from fractions import Fraction

P = 2_147_483_647  # prime 2^31 - 1


# ---------------------------------------------------------------------------
# Arrangements


def braid(n):
    """A_{n-1} essentialised in R^{n-1}: x_n = 0, normals e_i - e_j, e_i."""
    d = n - 1
    vecs = []
    for i in range(n):
        for j in range(i + 1, n):
            v = [0] * d
            v[i] = 1
            if j < d:
                v[j] = -1
            vecs.append(tuple(v))
    return vecs


def type_b(d):
    vecs = []
    for i in range(d):
        v = [0] * d
        v[i] = 1
        vecs.append(tuple(v))
    vecs += type_d(d)
    return vecs


def type_d(d):
    vecs = []
    for i in range(d):
        for j in range(i + 1, d):
            for s in (1, -1):
                v = [0] * d
                v[i] = 1
                v[j] = s
                vecs.append(tuple(v))
    return vecs


def random_arrangement(m, d, seed, box=4):
    """m random integer normals in R^d, rejecting repeated directions."""
    rng = random.Random(seed)
    vecs = []
    while len(vecs) < m:
        v = tuple(rng.randint(-box, box) for _ in range(d))
        if all(x == 0 for x in v):
            continue
        if any(rank_q([v, w]) < 2 for w in vecs):
            continue
        vecs.append(v)
    return vecs


# ---------------------------------------------------------------------------
# Exact linear algebra over Q (small matrices)


def rref_q(rows):
    m = [[Fraction(x) for x in r] for r in rows]
    piv = []
    r = 0
    ncols = len(m[0]) if m else 0
    for c in range(ncols):
        k = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if k is None:
            continue
        m[r], m[k] = m[k], m[r]
        inv = 1 / m[r][c]
        m[r] = [x * inv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(c)
        r += 1
    return m[:r], piv


def rank_q(rows):
    return len(rref_q(rows)[1])


def nullspace_q(rows, d):
    red, piv = rref_q(rows)
    free = [c for c in range(d) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * d
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -red[i][f]
        basis.append(v)
    return basis


def sgn(x):
    return (x > 0) - (x < 0)


# ---------------------------------------------------------------------------
# Oriented matroid of an arrangement


def cocircuits(vecs):
    d = len(vecs[0])
    assert rank_q(vecs) == d, "arrangement must be essential"
    out = set()
    for sub in itertools.combinations(range(len(vecs)), d - 1):
        ns = nullspace_q([vecs[i] for i in sub], d)
        if len(ns) != 1:
            continue
        v = ns[0]
        x = tuple(sgn(sum(a * b for a, b in zip(h, v))) for h in vecs)
        out.add(x)
        out.add(tuple(-t for t in x))
    return sorted(out)


def compose(x, y):
    return tuple(a if a else b for a, b in zip(x, y))


def covectors(vecs):
    cc = cocircuits(vecs)
    zero = tuple([0] * len(vecs))
    seen = {zero}
    frontier = [zero]
    while frontier:
        nxt = []
        for x in frontier:
            for c in cc:
                y = compose(x, c)
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return sorted(seen), cc


def zeros(x):
    return frozenset(i for i, a in enumerate(x) if a == 0)


def leq_face(h, d):
    """h <= d in the face order: h_e in {0, d_e}."""
    return all(a == 0 or a == b for a, b in zip(h, d))


# ---------------------------------------------------------------------------
# Posets: Moebius function and reduced homology of the proper part


def moebius_from_bottom(elems, less):
    """mu(bottom, x) for all x; elems sorted so that less(a, b) => a before b."""
    mu = {}
    for i, x in enumerate(elems):
        if i == 0:
            mu[x] = 1
        else:
            mu[x] = -sum(mu[y] for y in elems[:i] if less(y, x))
    return mu


def rank_mod_p(rows, p=P):
    """Rank of a list of sparse rows (dict col -> int) modulo p."""
    pivots = {}
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            c = min(r)
            if c in pivots:
                f = r[c]
                for cc, vv in pivots[c].items():
                    r[cc] = (r.get(cc, 0) - f * vv) % p
                    if r[cc] == 0:
                        del r[cc]
            else:
                inv = pow(r[c], p - 2, p)
                pivots[c] = {cc: vv * inv % p for cc, vv in r.items()}
                break
    return len(pivots)


def reduced_betti(elems, less):
    """Reduced Betti numbers (mod p) of the order complex of a finite poset."""
    if not elems:
        return {-1: 1}
    up = {x: [y for y in elems if less(x, y)] for x in elems}
    chains = {0: [(x,) for x in elems]}
    k = 0
    while chains[k]:
        chains[k + 1] = [c + (y,) for c in chains[k] for y in up[c[-1]]]
        k += 1
    top = k - 1
    index = {k: {c: i for i, c in enumerate(chains[k])} for k in chains}
    ranks = {}
    for k in range(1, top + 1):
        rows = []
        for c in chains[k]:
            r = {}
            for i in range(len(c)):
                f = c[:i] + c[i + 1:]
                r[index[k - 1][f]] = (-1) ** i
            rows.append(r)
        ranks[k] = rank_mod_p(rows)
    betti = {}
    for k in range(0, top + 1):
        dim_c = len(chains[k])
        z = dim_c - (ranks.get(k, 0))
        b = ranks.get(k + 1, 0)
        betti[k] = z - b
    betti[0] -= 1  # reduced
    return {k: v for k, v in betti.items() if v}


# ---------------------------------------------------------------------------
# Lunes and the quotient Gamma / Lune


def lune_classes(topes, Z):
    groups = {}
    for i, t in enumerate(topes):
        groups.setdefault(tuple(t[e] for e in sorted(Z)), []).append(i)
    return list(groups.values())


def lune_quotient(topes, flats_max, target_rank):
    """Echelon basis of Lune (dense rows mod P) and the residue map.

    Returns (pivot columns, residue vectors res[i] for every tope i, as a
    dict over non-pivot columns)."""
    n = len(topes)
    rows = {}  # pivot -> dense row, leading 1 at pivot

    def reduce(v):
        for c in sorted(rows):
            f = v[c]
            if f:
                r = rows[c]
                for j in range(c, n):
                    if r[j]:
                        v[j] = (v[j] - f * r[j]) % P
        return v

    done = False
    for Z in flats_max:
        for cls in lune_classes(topes, Z):
            if len(rows) >= target_rank:
                done = True
                break
            v = [0] * n
            for i in cls:
                v[i] = 1
            v = reduce(v)
            lead = next((j for j in range(n) if v[j]), None)
            if lead is None:
                continue
            inv = pow(v[lead], P - 2, P)
            rows[lead] = [x * inv % P for x in v]
        if done:
            break
    piv = set(rows)
    res = []
    for i in range(n):
        v = [0] * n
        v[i] = 1
        v = reduce(v)
        res.append({j: x for j, x in enumerate(v) if x})
    return piv, res


def kernel_mod_p(eqs, nvars, p=P):
    """Basis of {x : sum_j eq[j] x_j = 0 for all eq} mod p (eqs sparse)."""
    piv = {}  # pivot var -> row dict with 1 at pivot, zero at other pivots
    for r in eqs:
        r = {c: v % p for c, v in r.items() if v % p}
        for c in list(piv):
            if c in r:
                f = r[c]
                for cc, vv in piv[c].items():
                    r[cc] = (r.get(cc, 0) - f * vv) % p
                    if r[cc] == 0:
                        del r[cc]
        if not r:
            continue
        c = min(r)
        inv = pow(r[c], p - 2, p)
        r = {cc: vv * inv % p for cc, vv in r.items()}
        for c2 in piv:
            if c in piv[c2]:
                f = piv[c2][c]
                for cc, vv in r.items():
                    piv[c2][cc] = (piv[c2].get(cc, 0) - f * vv) % p
                    if piv[c2][cc] == 0:
                        del piv[c2][cc]
        piv[c] = r
    basis = []
    for fvar in range(nvars):
        if fvar in piv:
            continue
        v = {fvar: 1}
        for c, r in piv.items():
            if fvar in r:
                v[c] = (-r[fvar]) % p
        basis.append(v)
    return basis


def chamber_cycles(topes, covs, d):
    """rho_C: the fundamental cycle of the proper part of Lambda(C), as a
    sparse vector over a global index of maximal chains of flats."""
    m = len(topes[0])
    E = frozenset(range(m))
    gidx = {}
    rhos = []
    for C in topes:
        sup = {zeros(x) for x in covs if leq_face(x, C)} - {E, frozenset()}
        up = {Z: [W for W in sup if W < Z] for Z in sup}
        chains = [(Z,) for Z in sup]
        full = []
        stack = list(chains)
        while stack:
            c = stack.pop()
            nxt = up[c[-1]]
            if not nxt:
                full.append(c)
            for W in nxt:
                stack.append(c + (W,))
        full = [c for c in full if len(c) == d - 1]
        loc = {c: i for i, c in enumerate(full)}
        faces = {}
        for c in full:
            for i in range(len(c)):
                f = c[:i] + c[i + 1:]
                faces.setdefault(f, {})[loc[c]] = (-1) ** i
        ker = kernel_mod_p(list(faces.values()), len(full))
        assert len(ker) == 1, "Lambda(C) proper part should be a sphere"
        v = {}
        for i, x in ker[0].items():
            key = tuple(tuple(sorted(Z)) for Z in full[i])
            v[gidx.setdefault(key, len(gidx))] = x
        rhos.append(v)
    return rhos


def check_restriction(topes, covs, flats_proper, m):
    """Lemma E: E_h(lune(Z, D)) = D_h * [F : F|_Z = D|_Z, F chamber of A^h]
    if h in Z, and 0 otherwise; for every hyperplane h, flat Z != E, tope D."""
    covset = set(covs)
    for h in range(m):
        def E_h(C):
            F = C[:h] + (0,) + C[h + 1:]
            return (F, C[h]) if F in covset else None
        hch = [x for x in covs if zeros(x) == frozenset([h])]
        for Z in flats_proper:
            for cls in lune_classes(topes, Z):
                D = topes[cls[0]]
                img = {}
                for i in cls:
                    r = E_h(topes[i])
                    if r:
                        img[r[0]] = img.get(r[0], 0) + r[1]
                img = {F: v for F, v in img.items() if v}
                if h in Z:
                    pred = {F: D[h] for F in hch
                            if all(F[e] == D[e] for e in Z if e != h)}
                else:
                    pred = {}
                if img != pred:
                    return False
    return True


# ---------------------------------------------------------------------------
# Top-cones


def all_top_cones(topes, m):
    full = frozenset(range(len(topes)))
    half = {}
    for e in range(m):
        for s in (1, -1):
            half[(e, s)] = frozenset(i for i, t in enumerate(topes) if t[e] == s)
    seen = {full}
    frontier = [full]
    while frontier:
        nxt = []
        for V in frontier:
            for h in half.values():
                W = V & h
                if W and W not in seen:
                    seen.add(W)
                    nxt.append(W)
        frontier = nxt
    return sorted(seen, key=lambda V: (-len(V), sorted(V)))


def sampled_top_cones(topes, m, count, seed):
    rng = random.Random(seed)
    full = frozenset(range(len(topes)))
    seen = {full}
    tries = 0
    while len(seen) < count and tries < 50 * count:
        tries += 1
        D = topes[rng.randrange(len(topes))]
        S = [e for e in range(m) if rng.random() < rng.choice([0.15, 0.3, 0.5])]
        V = frozenset(i for i, t in enumerate(topes)
                      if all(t[e] == D[e] for e in S))
        seen.add(V)
    return sorted(seen, key=lambda V: (-len(V), sorted(V)))


def analyse_cone(V, topes, covs, m, res, flats_proper, want_homology=True,
                 rhos=None):
    """Return a dict of the per-cone data."""
    Vt = [topes[i] for i in sorted(V)]
    Smax = {}
    for e in range(m):
        signs = {t[e] for t in Vt}
        if len(signs) == 1:
            Smax[e] = signs.pop()
    faces = [x for x in covs if all(x[e] in (0, s) for e, s in Smax.items())]
    faceset = set(faces)
    out = {"n_topes": len(V), "n_faces": len(faces), "S": len(Smax)}
    # [lrb]
    out["lrb"] = all(compose(x, y) in faceset for x in faces for y in faces) \
        and tuple([0] * m) in faceset
    # supports Lambda(V)
    sup = sorted({zeros(x) for x in faces}, key=lambda Z: -len(Z))
    less = lambda a, b: a > b  # strictly larger zero set = lower flat
    mu = moebius_from_bottom(sup, less)
    out["mu"] = mu[sup[-1]]
    if want_homology:
        proper = sup[1:-1]
        out["betti"] = reduced_betti(proper, less)
    # [lin]
    Vset = set(V)
    lin_ok = True
    Sk = set(Smax)
    for Z in flats_proper:
        for cls in lune_classes(topes, Z):
            inside = all(i in Vset for i in cls)
            pred = (cls[0] in Vset) and Sk <= Z
            if inside != pred:
                lin_ok = False
    out["lin"] = lin_ok
    # q(V)
    q = rank_mod_p([res[i] for i in sorted(V)])
    out["q"] = q
    # [K] lunes inside V span Gamma_V cap Lune (dim |V| - q)
    lun = []
    for Z in flats_proper:
        if Sk <= Z:
            for cls in lune_classes(topes, Z):
                if cls[0] in Vset:
                    lun.append({i: 1 for i in cls})
    out["rank_lunes_in_V"] = rank_mod_p(lun) if lun else 0
    out["K"] = out["rank_lunes_in_V"] == len(V) - q
    # [brown]
    cX = {}
    for x in faces:
        Z = zeros(x)
        c = sum(1 for i in V if leq_face(x, topes[i]))
        cX.setdefault(Z, set()).add(c)
    out["brown_consistent"] = all(len(s) == 1 for s in cX.values())
    out["brown"] = sum(mu[Z] * next(iter(cX[Z])) for Z in sup)
    out["pointed"] = not any(Sk <= zeros(x) for x in covs if any(x))
    if rhos is not None:
        out["rank_rho"] = rank_mod_p([rhos[i] for i in sorted(V)])
    return out


def run_arrangement(name, vecs, cones="all", count=300, seed=1,
                    homology=True, out=sys.stdout):
    covs, cc = covectors(vecs)
    m = len(vecs)
    topes = [x for x in covs if all(x)]
    flats = sorted({zeros(x) for x in covs}, key=lambda Z: -len(Z))
    E = frozenset(range(m))
    flats_proper = [Z for Z in flats if Z != E]
    flats_max = sorted({zeros(c) for c in cc}, key=sorted)
    less = lambda a, b: a > b
    mu_full = moebius_from_bottom(flats, less)[frozenset()]
    target = len(topes) - abs(mu_full)
    piv, res = lune_quotient(topes, flats_max, target)
    lune_ok = len(piv) == target
    print(f"[{name}] m={m} d={len(vecs[0])} covectors={len(covs)} "
          f"topes={len(topes)} flats={len(flats)} |mu|={abs(mu_full)} "
          f"rank_p(Lune)={len(piv)} (target {target}): {lune_ok}", file=out)
    restr_ok = check_restriction(topes, covs, flats_proper, m)
    print(f"  [E_h] restriction maps lunes to lunes of A^h or 0: {restr_ok}",
          file=out)
    rhos = chamber_cycles(topes, covs, len(vecs[0])) if homology else None
    if cones == "all":
        cl = all_top_cones(topes, m)
    else:
        cl = sampled_top_cones(topes, m, count, seed)
    stats = dict(n=0, lrb=0, lin=0, K=0, q_eq_h=0, conc=0, q_eq_mu=0,
                 brown_eq=0, brown_cons=0, pointed=0, pointed_q_all=0, rho=0,
                 brown_zero=0)
    bad = []
    for V in cl:
        r = analyse_cone(V, topes, covs, m, res, flats_proper, homology, rhos)
        stats["n"] += 1
        stats["lrb"] += r["lrb"]
        stats["lin"] += r["lin"]
        stats["K"] += r["K"]
        stats["q_eq_mu"] += r["q"] == abs(r["mu"])
        stats["brown_eq"] += r["brown"] == r["q"]
        stats["brown_cons"] += r["brown_consistent"]
        stats["brown_zero"] += (r["brown"] == 0) or len(V) == len(topes)
        if r["pointed"]:
            stats["pointed"] += 1
            stats["pointed_q_all"] += r["q"] == r["n_topes"]
        if homology:
            b = r["betti"]
            top = len(vecs[0]) - 2
            conc = set(b) <= {top}
            stats["conc"] += conc
            stats["q_eq_h"] += r["q"] == b.get(top, 0)
            stats["rho"] += r["rank_rho"] == r["q"]
        if len(bad) < 5 and not (r["lrb"] and r["lin"] and r["K"]
                                 and (not homology or r["q"] == r["betti"].get(len(vecs[0]) - 2, 0))):
            bad.append((sorted(V), r))
    full = analyse_cone(frozenset(range(len(topes))), topes, covs, m, res,
                        flats_proper, False)
    full_ok = full["q"] == abs(mu_full)
    n = stats["n"]
    print(f"  cones ({cones}): {n}", file=out)
    print(f"  [lrb] faces of V closed under Tits product: {stats['lrb']}/{n}", file=out)
    print(f"  [lin] lune in V <=> D in V and S_max in Z: {stats['lin']}/{n}", file=out)
    print(f"  [K]   Gamma_V cap Lune = span(lunes in V): {stats['K']}/{n}", file=out)
    if homology:
        print(f"  [q]   q(V) = dim H~_top(Lambda(V)): {stats['q_eq_h']}/{n}; "
              f"homology concentrated in top degree: {stats['conc']}/{n}", file=out)
    if homology:
        print(f"  [rho] rank span(rho_C : C in V) = q(V): {stats['rho']}/{n}", file=out)
    print(f"  [q]   q(V) = |mu(Lambda(V))|: {stats['q_eq_mu']}/{n}", file=out)
    print(f"  [pointed] pointed cones: {stats['pointed']}; with q = #topes: "
          f"{stats['pointed_q_all']}/{stats['pointed']}", file=out)
    print(f"  [brown] c_X well defined: {stats['brown_cons']}/{n}; "
          f"Brown multiplicity m_bottom = q(V): {stats['brown_eq']}/{n}; "
          f"m_bottom = 0 or V = all: {stats['brown_zero']}/{n} (not asserted)",
          file=out)
    print(f"  [full] q(all topes) = |mu| : {full_ok}", file=out)
    for V, r in bad:
        print(f"  FAIL cone {V}: {r}", file=out)
    ok = lune_ok and full_ok and restr_ok and stats["lrb"] == n and stats["lin"] == n \
        and stats["K"] == n and stats["q_eq_mu"] == n \
        and (not homology or (stats["q_eq_h"] == n and stats["conc"] == n
                          and stats["rho"] == n)) \
        and stats["brown_cons"] == n and stats["pointed_q_all"] == stats["pointed"]
    return ok, stats


ARRANGEMENTS = [
    ("A2 (braid n=3)", braid(3), "all", True),
    ("A3 (braid n=4)", braid(4), "all", True),
    ("A4 (braid n=5)", braid(5), "all", True),
    ("B2", type_b(2), "all", True),
    ("B3", type_b(3), "all", True),
    ("D4", type_d(4), "sample", True),
    ("B4", type_b(4), "sample", False),
    ("generic5 R^3 seed 7", None, "all", True),
    ("generic6 R^3 seed 11", None, "all", True),
    ("random7 R^3 seed 3", None, "all", True),
    ("random6 R^4 seed 5", None, "all", True),
]


def build(name, vecs):
    if vecs is not None:
        return vecs
    if name.startswith("generic5"):
        return random_arrangement(5, 3, 7)
    if name.startswith("generic6"):
        return random_arrangement(6, 3, 11)
    if name.startswith("random7"):
        return random_arrangement(7, 3, 3, box=2)
    if name.startswith("random6"):
        return random_arrangement(6, 4, 5, box=2)
    raise ValueError(name)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="skip A4, D4, B4 (seconds instead of minutes)")
    ap.add_argument("--samples", type=int, default=150)
    args = ap.parse_args(argv)
    allok = True
    for name, vecs, mode, hom in ARRANGEMENTS:
        if args.quick and name[:2] in ("A4", "D4", "B4"):
            continue
        vecs = build(name, vecs)
        ok, _ = run_arrangement(name, vecs, mode, args.samples, seed=2,
                                homology=hom)
        print(f"  => {'PASS' if ok else 'FAIL'}")
        allok &= ok
    print("ALL CHECKS PASSED" if allok else "SOME CHECKS FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
