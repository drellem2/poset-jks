#!/usr/bin/env python3
"""What the poset Lie theory says about linear extensions.

Companion to ../notes/linear_extensions.md.  Sections (each prints PASS/FAIL
lines and tallies; the script exits 0 iff every check that is meant to hold
holds, and every positive control that is meant to fail fails):

  csp     cyclic sieving: positive controls (Rhoades rectangles, RSW
          q-binomial on two disjoint chains), a negative control (unshifted
          maj polynomial), a sweep over all posets with n <= NMAX whose
          promotion has order dividing n, and the disjoint-union theorem.
  promo   promotion vs. rotation classes: the toggle and jeu-de-taquin
          descriptions agree; Lemma P (promotion on A + B rotates the
          shuffle pattern); Corollary P2 (promotion to a cut); refinement of
          promotion orbits by cyclic classes; when promotion descends to
          PLie(P) and to C[Lin P]/R_P.
  count   counting: Jenca-Sarkoci contraction recursion (control: the
          standard e(P) = sum_a e(P - a)); the Weisner family of alternating
          identities; e_C over components; the factorisation
          e_C(P) = prod e(T) * e_C(chains); fixed classes and Burnside.
  struct  structure of C[Lin P]/R_P: homogeneity of R_P for several
          statistics (restriction to components, number of blocks, des,
          maj, jumps), dimension of each restriction-graded piece.

Run from compute/:

    python3 linear_extensions.py --nmax 7 --rnmax 6 > output/linear_extensions.txt

Plain Python 3, no dependencies.  Ranks are mod a large prime (valid as
lower bounds over Q; every rank used here is also matched against a value
known over Q, see the note).
"""

import argparse
import cmath
import itertools
import sys
from collections import Counter, defaultdict
from math import comb, factorial, gcd

import n7_sweep

PRIME = 2_147_483_647
FAILS = []


def check(ok, label):
    if not ok:
        FAILS.append(label)
    return ok


# ---------------------------------------------------------------------------
# Posets, linear extensions, components, cuts


def less_matrix(rel, n):
    m = [[False] * n for _ in range(n)]
    for a, b in rel:
        m[a][b] = True
    return m


def linexts(rel, n):
    """All linear extensions, as words w (w[i] = element in position i)."""
    down = [0] * n
    for a, b in rel:
        down[b] |= 1 << a
    out = []

    def rec(word, used):
        if len(word) == n:
            out.append(tuple(word))
            return
        for x in range(n):
            if not used >> x & 1 and down[x] & ~used == 0:
                word.append(x)
                rec(word, used | 1 << x)
                word.pop()
    rec([], 0)
    return out


def components(rel, n):
    comp = list(range(n))

    def find(x):
        while comp[x] != x:
            comp[x] = comp[comp[x]]
            x = comp[x]
        return x
    for a, b in rel:
        ra, rb = find(a), find(b)
        if ra != rb:
            comp[ra] = rb
    groups = defaultdict(list)
    for x in range(n):
        groups[find(x)].append(x)
    comps = sorted(groups.values())
    lab = [0] * n
    for i, c in enumerate(comps):
        for x in c:
            lab[x] = i
    return comps, lab


def restrict(rel, B):
    """Induced subposet on B, relabelled 0..|B|-1 in increasing order."""
    B = sorted(B)
    idx = {x: i for i, x in enumerate(B)}
    return frozenset((idx[a], idx[b]) for a, b in rel if a in idx and b in idx), B


def cuts(w, lab, comps):
    """k in 0..n-1 with {w_1..w_k} a union of components."""
    size = [len(c) for c in comps]
    seen = [0] * len(comps)
    open_ = 0
    out = [0]
    for k, x in enumerate(w[:-1], 1):
        c = lab[x]
        if seen[c] == 0:
            open_ += 1
        seen[c] += 1
        if seen[c] == size[c]:
            open_ -= 1
        if open_ == 0:
            out.append(k)
    return out


def rot(w, k):
    k %= len(w)
    return w[k:] + w[:k]


def cyclic_classes(lin, lab, comps):
    rep = {}
    for w in lin:
        if w in rep:
            continue
        cls = [rot(w, k) for k in cuts(w, lab, comps)]
        r = min(cls)
        for v in cls:
            rep[v] = r
    return rep


def e_C(rel, n):
    if n == 0:
        return 1
    comps, lab = components(rel, n)
    return len(set(cyclic_classes(linexts(rel, n), lab, comps).values()))


# ---------------------------------------------------------------------------
# Promotion


def promote(w, lt):
    """Toggle form: tau_{n-1} ... tau_1, tau_i swapping positions i, i+1 when
    the two letters are incomparable (tau_1 applied first)."""
    w = list(w)
    for i in range(len(w) - 1):
        a, b = w[i], w[i + 1]
        if not lt[a][b] and not lt[b][a]:
            w[i], w[i + 1] = b, a
    return tuple(w)


def promote_jdt(w, rel, n):
    """Jeu-de-taquin form: delete the element labelled 1, slide along the
    minimally labelled upper cover, put n at the end, subtract 1."""
    f = {x: i + 1 for i, x in enumerate(w)}
    cov = defaultdict(list)
    for a, b in rel:
        if not any((a, c) in rel and (c, b) in rel for c in range(n)):
            cov[a].append(b)
    x = w[0]
    path = [x]
    while cov[x]:
        x = min(cov[x], key=lambda y: f[y])
        path.append(x)
    g = {y: f[y] - 1 for y in f}
    for i in range(len(path) - 1):
        g[path[i]] = f[path[i + 1]] - 1
    g[path[-1]] = n
    word = [None] * n
    for y, v in g.items():
        word[v - 1] = y
    return tuple(word)


def orbits(perm_map):
    seen, out = set(), []
    for x in perm_map:
        if x in seen:
            continue
        orb, y = [], x
        while y not in seen:
            seen.add(y)
            orb.append(y)
            y = perm_map[y]
        out.append(orb)
    return out


def perm_order(perm_map):
    o = 1
    for orb in orbits(perm_map):
        o = o * len(orb) // gcd(o, len(orb))
    return o


# ---------------------------------------------------------------------------
# q-polynomials and cyclic sieving


def poly_mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def q_int(m):
    return [1] * m


def q_fact(m):
    p = [1]
    for i in range(1, m + 1):
        p = poly_mul(p, q_int(i))
    return p


def poly_div_exact(p, d):
    p = list(p)
    out = [0] * (len(p) - len(d) + 1)
    for i in range(len(out) - 1, -1, -1):
        c = p[i + len(d) - 1] // d[-1]
        out[i] = c
        for j, b in enumerate(d):
            p[i + j] -= c * b
    assert all(v == 0 for v in p), "not exact"
    return out


def q_multinomial(ms):
    num = q_fact(sum(ms))
    for m in ms:
        num = poly_div_exact(num, q_fact(m))
    return num


def poly_eval(p, z):
    return sum(c * z ** i for i, c in enumerate(p))


def csp_holds(fix_counts, X, N):
    """fix_counts[d] = |Fix(c^d)| for d = 0..N-1; X a polynomial."""
    for d in range(N):
        v = poly_eval(X, cmath.exp(2j * cmath.pi * d / N))
        if abs(v - fix_counts[d]) > 1e-6:
            return False
    return True


def fixed_counts(perm_map, N):
    out = []
    for d in range(N):
        cnt = 0
        for x in perm_map:
            y = x
            for _ in range(d):
                y = perm_map[y]
            cnt += (y == x)
        out.append(cnt)
    return out


def fixed_counts_fast(perm_map, N):
    """Same as fixed_counts, from the orbit sizes."""
    sizes = [len(o) for o in orbits(perm_map)]
    return [sum(s for s in sizes if d % s == 0) for d in range(N)]


def maj_poly(lin, n, shift=True):
    """sum_w q^maj(w) for the natural labelling given by the integer labels
    (requires a < b in P => a < b as integers); shifted by q^{-min maj}."""
    cnt = Counter(sum(i + 1 for i in range(n - 1) if w[i] > w[i + 1]) for w in lin)
    lo = min(cnt) if shift else 0
    p = [0] * (max(cnt) - lo + 1)
    for k, v in cnt.items():
        p[k - lo] += v
    return p


def is_natural(rel):
    return all(a < b for a, b in rel)


def rectangle(a, b):
    """[a] x [b]; element (i, j) -> i*b + j; natural labelling."""
    rel = set()
    for i in range(a):
        for j in range(b):
            for k in range(i, a):
                for l in range(j, b):
                    if (k, l) != (i, j):
                        rel.add((i * b + j, k * b + l))
    return frozenset(rel), a * b


def shape_poset(shape):
    """Young diagram poset of a partition shape (row-reading labels)."""
    cells = [(i, j) for i, r in enumerate(shape) for j in range(r)]
    idx = {c: k for k, c in enumerate(cells)}
    rel = set()
    for (i, j) in cells:
        for (k, l) in cells:
            if (k, l) != (i, j) and k >= i and l >= j:
                rel.add((idx[(i, j)], idx[(k, l)]))
    return frozenset(rel), len(cells)


def shifted_staircase_poset(m):
    cells = [(i, j) for i in range(m) for j in range(i, m)]
    idx = {c: k for k, c in enumerate(cells)}
    rel = set()
    for (i, j) in cells:
        for (k, l) in cells:
            if (k, l) != (i, j) and k >= i and l >= j:
                rel.add((idx[(i, j)], idx[(k, l)]))
    return frozenset(rel), len(cells)


def q_hook(shape):
    n = sum(shape)
    conj = [sum(1 for r in shape if r > j) for j in range(shape[0])]
    num = q_fact(n)
    for i, r in enumerate(shape):
        for j in range(r):
            num = poly_div_exact(num, q_int(r - j + conj[j] - i - 1))
    return num


def disjoint_union(*parts):
    rel, off = set(), 0
    for r, m in parts:
        rel |= {(a + off, b + off) for a, b in r}
        off += m
    return frozenset(rel), off


def chain(m):
    return frozenset((i, j) for i in range(m) for j in range(i + 1, m)), m


def section_csp(posets, out):
    print("== [csp] cyclic sieving", file=out)
    # Positive control 1: Rhoades, rectangles, polynomial = q-hook formula.
    for a, b in [(2, 2), (2, 3), (2, 4), (3, 3), (2, 5), (3, 4), (2, 6)]:
        rel, n = rectangle(a, b)
        lin = linexts(rel, n)
        lt = less_matrix(rel, n)
        pm = {w: promote(w, lt) for w in lin}
        Xh = q_hook([b] * a)
        Xm = maj_poly(lin, n)
        ok = (n % perm_order(pm) == 0 and Xh == Xm
              and csp_holds(fixed_counts_fast(pm, n), Xh, n))
        check(ok, f"rhoades {a}x{b}")
        # negative control: q * (q-hook) must fail
        neg = csp_holds(fixed_counts_fast(pm, n), [0] + Xh, n)
        check(not neg, f"rhoades {a}x{b} shifted control")
        print(f"  [ctl-rhoades] {a}x{b}: e={len(lin)} order={perm_order(pm)} "
              f"CSP(q-hook)={'PASS' if ok else 'FAIL'}  "
              f"CSP(q * q-hook)={'holds (control FAILED)' if neg else 'fails (control OK)'}",
              file=out)
    # Positive control 2: RSW, binary words = Lin(C_a + C_b), promotion =
    # rotation of the pattern, polynomial = q-binomial.
    for a, b in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3), (4, 2), (4, 3)]:
        rel, n = disjoint_union(chain(a), chain(b))
        lin = linexts(rel, n)
        lt = less_matrix(rel, n)
        pm = {w: promote(w, lt) for w in lin}
        ok = csp_holds(fixed_counts_fast(pm, n), q_multinomial([a, b]), n)
        check(ok, f"rsw C{a}+C{b}")
        print(f"  [ctl-rsw] C{a}+C{b}: e={len(lin)} CSP(q-binomial)={'PASS' if ok else 'FAIL'}",
              file=out)
    # Staircases (computed only; no claim from the literature is made here).
    for shape in [(2, 1), (3, 2, 1), (4, 3, 2, 1)]:
        rel, n = shape_poset(shape)
        lin = linexts(rel, n)
        lt = less_matrix(rel, n)
        pm = {w: promote(w, lt) for w in lin}
        o = perm_order(pm)
        res = csp_holds(fixed_counts_fast(pm, n), q_hook(list(shape)), n) if n % o == 0 else None
        print(f"  [staircase] shape {shape}: e={len(lin)} promotion order={o} (n={n}); "
              f"CSP with q-hook: {res}", file=out)
    for m in [2, 3, 4]:
        rel, n = shifted_staircase_poset(m)
        lin = linexts(rel, n)
        lt = less_matrix(rel, n)
        pm = {w: promote(w, lt) for w in lin}
        o = perm_order(pm)
        print(f"  [shifted-staircase] m={m}: e={len(lin)} promotion order={o} (n={n})", file=out)

    # Sweep.
    tally = Counter()
    fails_by_n = defaultdict(list)
    for n in sorted(posets):
        for rel in posets[n]:
            assert is_natural(rel)
            lin = linexts(rel, n)
            lt = less_matrix(rel, n)
            pm = {w: promote(w, lt) for w in lin}
            o = perm_order(pm)
            if n % o:
                tally[(n, "order does not divide n")] += 1
                continue
            ok = csp_holds(fixed_counts_fast(pm, n), maj_poly(lin, n), n)
            tally[(n, "CSP holds" if ok else "CSP fails")] += 1
            if not ok:
                fails_by_n[n].append(sorted(rel))
    print("  [sweep] (Lin P, promotion, q^{-min maj} sum q^maj), C_n acting:", file=out)
    for n in sorted(posets):
        row = {k[1]: v for k, v in tally.items() if k[0] == n}
        print(f"    n={n}: {len(posets[n])} posets; " +
              ", ".join(f"{k}: {row.get(k, 0)}" for k in
                        ["order does not divide n", "CSP holds", "CSP fails"]), file=out)
    for n in sorted(fails_by_n):
        for r in fails_by_n[n][:3]:
            print(f"    first CSP failures n={n}: covers {cover_list(r, n)}", file=out)

    # Disjoint-union theorem: components with promotion order | size and CSP
    # => P has CSP with q-multinomial * product.  Check on every disconnected
    # poset with n <= NMAX whose components qualify.
    good = {}
    tested = 0
    for n in sorted(posets):
        for rel in posets[n]:
            comps, lab = components(rel, n)
            if len(comps) == 1:
                continue
            Xs, qual = [], True
            for c in comps:
                r, _ = restrict(rel, c)
                key = (len(c), r)
                if key not in good:
                    lin_c = linexts(r, len(c))
                    lt_c = less_matrix(r, len(c))
                    pm_c = {w: promote(w, lt_c) for w in lin_c}
                    m = len(c)
                    if m % perm_order(pm_c):
                        good[key] = None
                    else:
                        Xc = maj_poly(lin_c, m)
                        good[key] = Xc if csp_holds(fixed_counts_fast(pm_c, m), Xc, m) else None
                if good[key] is None:
                    qual = False
                    break
                Xs.append(good[key])
            if not qual:
                continue
            X = q_multinomial([len(c) for c in comps])
            for Xc in Xs:
                X = poly_mul(X, Xc)
            lin = linexts(rel, n)
            lt = less_matrix(rel, n)
            pm = {w: promote(w, lt) for w in lin}
            ok = perm_order(pm) in [d for d in range(1, n + 1) if n % d == 0] and \
                csp_holds(fixed_counts_fast(pm, n), X, n)
            tested += 1
            check(ok, f"union theorem {sorted(rel)}")
            check(X == maj_poly(lin, n), f"union maj factorisation {sorted(rel)}")
    print(f"  [union] disjoint-union CSP theorem checked on {tested} disconnected posets "
          f"(all components qualify): {'PASS' if not [f for f in FAILS if f.startswith('union')] else 'FAIL'}",
          file=out)


def cover_list(rel, n):
    rel = set(map(tuple, rel))
    return [(a, b) for a, b in sorted(rel)
            if not any((a, c) in rel and (c, b) in rel for c in range(n))]


# ---------------------------------------------------------------------------
# Promotion vs. rotation classes


def pattern(w, lab):
    return tuple(lab[x] for x in w)


def restriction(w, c):
    s = set(c)
    return tuple(x for x in w if x in s)


def section_promo(posets, out, rnmax):
    print("== [promo] promotion vs rotation classes", file=out)
    t = Counter()
    refine_fail_examples = []
    descend_K, descend_R = [], []
    orbit_eq_class = []
    for n in sorted(posets):
        for rel in posets[n]:
            lin = linexts(rel, n)
            lt = less_matrix(rel, n)
            comps, lab = components(rel, n)
            pm = {w: promote(w, lt) for w in lin}
            # toggle == jdt
            if n <= 6:
                check(all(pm[w] == promote_jdt(w, rel, n) for w in lin), f"jdt {sorted(rel)}")
                t["jdt"] += 1
            cls = cyclic_classes(lin, lab, comps)
            orbs = orbits(pm)
            orb_of = {w: i for i, o in enumerate(orbs) for w in o}
            k = len(comps)
            # Lemma P: for each single component A, pattern rotates, A-part
            # promotes iff w_1 in A, other parts unchanged.
            if k > 1:
                promo_c = {}
                for ci, c in enumerate(comps):
                    r, B = restrict(rel, c)
                    ltc = less_matrix(r, len(c))
                    promo_c[ci] = (B, ltc)
                okP = True
                for w in lin:
                    v = pm[w]
                    if pattern(v, lab) != rot(pattern(w, lab), 1):
                        okP = False
                        break
                    for ci, c in enumerate(comps):
                        B, ltc = promo_c[ci]
                        idx = {x: i for i, x in enumerate(B)}
                        wc = tuple(idx[x] for x in restriction(w, c))
                        vc = tuple(idx[x] for x in restriction(v, c))
                        exp = promote(wc, ltc) if lab[w[0]] == ci else wc
                        if vc != exp:
                            okP = False
                            break
                check(okP, f"lemma P {sorted(rel)}")
                t["lemmaP"] += 1
                # Corollary P2: for a cut k with prefix A, promotion^k(w) is
                # w gamma^k with the A-part replaced by promotion_A^{|A|}.
                okP2 = True
                for w in lin:
                    for kk in cuts(w, lab, comps)[1:]:
                        v = w
                        for _ in range(kk):
                            v = pm[v]
                        A = sorted(w[:kk])
                        r, B = restrict(rel, A)
                        ltA = less_matrix(r, len(A))
                        idx = {x: i for i, x in enumerate(B)}
                        u = tuple(idx[x] for x in w[:kk])
                        for _ in range(kk):
                            u = promote(u, ltA)
                        expect = w[kk:] + tuple(B[i] for i in u)
                        if v != expect:
                            okP2 = False
                check(okP2, f"cor P2 {sorted(rel)}")
                t["corP2"] += 1
            # Refinement: every cyclic class inside one promotion orbit?
            refine = all(orb_of[w] == orb_of[cls[w]] for w in lin)
            comp_ok = True
            for c in comps:
                r, _ = restrict(rel, c)
                lc = linexts(r, len(c))
                ltc = less_matrix(r, len(c))
                pc = {w: promote(w, ltc) for w in lc}
                if len(c) % perm_order(pc):
                    comp_ok = False
            if k == 1:
                pass
            elif comp_ok:
                check(refine, f"refinement under hypothesis {sorted(rel)}")
                t["refine hyp"] += 1
            else:
                t["hyp fails"] += 1
                if refine:
                    t["hyp fails, refine holds"] += 1
                else:
                    t["hyp fails, refine fails"] += 1
                    if len(refine_fail_examples) < 3:
                        refine_fail_examples.append((n, cover_list(rel, n)))
            nclass = len(set(cls.values()))
            # Proposition O: every promotion orbit contains a word whose first
            # letter lies in the base component P_1 (= comps[0]); such a word
            # is in B_P, hence #orbits <= |B_P| = e_C(P).
            check(all(any(lab[v[0]] == 0 for v in o) for o in orbs), f"prop O {sorted(rel)}")
            check(len(orbs) <= nclass, f"orbit bound {sorted(rel)}")
            t["propO"] += 1
            if k > 1:
                t["disconnected"] += 1
                if len(orbs) <= nclass:
                    t["orbits <= e_C"] += 1
            if refine and len(orbs) == nclass:
                orbit_eq_class.append((n, cover_list(rel, n)))
            # Descent to PLie(P): promotion commutes with cut-rotations.
            dK = all(pm[rot(w, kk)] == rot(pm[w], kk)
                     for w in lin for kk in cuts(w, lab, comps))
            if k > 1 and dK:
                descend_K.append((n, cover_list(rel, n)))
            # Descent to C[Lin P]/R_P (n <= rnmax).
            if k > 1 and n <= rnmax:
                A, cols = lie_matrix_on(lin, n)
                Ap = [[row[cols[pm[w]]] for w in lin] for row in A]
                rA = rank_mod(A)
                rboth = rank_mod(A + Ap)
                if rA == rboth:
                    descend_R.append((n, cover_list(rel, n)))
                t["R tested"] += 1
    print(f"  [jdt] toggle form = jeu-de-taquin form on {t['jdt']} posets (n <= 6)", file=out)
    print(f"  [lemmaP] Lemma P checked on {t['lemmaP']} disconnected posets", file=out)
    print(f"  [corP2] Corollary P2 checked on {t['corP2']} disconnected posets", file=out)
    print(f"  [refine] disconnected posets whose components T all have promotion^|T| = id: {t['refine hyp']}, "
          f"cyclic classes refine promotion orbits on all of them", file=out)
    print(f"  [refine] disconnected posets with a component T where promotion^|T| != id: {t['hyp fails']} "
          f"(refinement still holds: {t['hyp fails, refine holds']}, fails: "
          f"{t['hyp fails, refine fails']})", file=out)
    for ex in refine_fail_examples:
        print(f"    refinement failure: n={ex[0]} covers {ex[1]}", file=out)
    print(f"  [propO] every promotion orbit meets {{w : w_1 in P_1}}, so #orbits <= e_C(P): "
          f"{t['propO']} posets", file=out)
    print(f"  [count] disconnected posets: {t['disconnected']}; with #promotion orbits <= e_C: "
          f"{t['orbits <= e_C']}", file=out)
    print(f"  [orbit=class] posets where promotion orbits = cyclic classes: {len(orbit_eq_class)}", file=out)
    for ex in orbit_eq_class[:12]:
        print(f"    n={ex[0]} covers {ex[1]}", file=out)
    print(f"  [descend-PLie] disconnected posets on which promotion commutes with every cut "
          f"rotation (= descends to PLie(P) = C[Lin P]/K_P): {len(descend_K)}", file=out)
    for ex in descend_K[:12]:
        print(f"    n={ex[0]} covers {ex[1]}", file=out)
    print(f"  [descend-R] disconnected posets, n <= {rnmax}, with promotion(R_P) inside R_P: "
          f"{len(descend_R)} of {t['R tested']}", file=out)
    for ex in descend_R[:12]:
        print(f"    n={ex[0]} covers {ex[1]}", file=out)
    return descend_K, descend_R


# ---------------------------------------------------------------------------
# Lie_n on Lin P (Ree: Sh_n = Lie_n^perp), ranks mod p


def lie_basis(n):
    """Left-normed brackets [..[0, s1], s2], ...] for s a permutation of
    1..n-1 (Dynkin basis of the multilinear part of Lie_n), as dicts."""
    out = []
    for s in itertools.permutations(range(1, n)):
        cur = {(0,): 1}
        for x in s:
            nxt = defaultdict(int)
            for wd, c in cur.items():
                nxt[wd + (x,)] += c
                nxt[(x,) + wd] -= c
            cur = nxt
        out.append(cur)
    return out


_LIE = {}


def lie_matrix_on(lin, n):
    if n not in _LIE:
        _LIE[n] = lie_basis(n)
    cols = {w: i for i, w in enumerate(lin)}
    A = [[ell.get(w, 0) % PRIME for w in lin] for ell in _LIE[n]]
    return A, cols


def rank_mod(rows, p=PRIME):
    rows = [list(r) for r in rows if any(r)]
    if not rows:
        return 0
    m = len(rows[0])
    rank = 0
    piv_rows = []
    for col in range(m):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i][col] % p:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        rows[rank] = [(v * inv) % p for v in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


# ---------------------------------------------------------------------------
# Counting


def quotient(rel, n, blocks):
    """Quotient poset Q_x (transitive closure of P/x), blocks indexed 0..k-1;
    None if not order-preserving."""
    bl = {}
    for i, B in enumerate(blocks):
        for x in B:
            bl[x] = i
    k = len(blocks)
    reach = [set() for _ in range(k)]
    for a, b in rel:
        if bl[a] != bl[b]:
            reach[bl[a]].add(bl[b])
    # transitive closure; detect cycles
    closure = [set() for _ in range(k)]
    for s in range(k):
        stack, seen = list(reach[s]), set()
        while stack:
            y = stack.pop()
            if y in seen:
                continue
            seen.add(y)
            stack.extend(reach[y])
        if s in seen:
            return None
        closure[s] = seen
    return frozenset((a, b) for a in range(k) for b in closure[a]), k


def set_partitions(items):
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def mobius_top(elems):
    """mu(0^, 1^) on a list of partitions (frozensets of frozensets)."""
    def refines(x, y):
        return all(any(B <= C for C in y) for B in x)
    elems = sorted(elems, key=lambda p: -len(p))
    mu = {}
    for x in elems:
        mu[x] = 1 if x is elems[0] else -sum(mu[y] for y in mu if len(y) > len(x) and refines(y, x))
    return mu[elems[-1]]


def mobius_num(m):
    r, p, mm = 1, 2, m
    while p * p <= mm:
        if mm % p == 0:
            mm //= p
            if mm % p == 0:
                return 0
            r = -r
        p += 1
    if mm > 1:
        r = -r
    return r


def euler_phi(m):
    return sum(1 for i in range(1, m + 1) if gcd(i, m) == 1)


def section_count(posets, out, wnmax):
    print("== [count] counting identities", file=out)
    t = Counter()
    ec_cache = {}

    def ec(rel, n):
        key = (n, rel)
        if key not in ec_cache:
            ec_cache[key] = e_C(rel, n)
        return ec_cache[key]

    for n in sorted(posets):
        for rel in posets[n]:
            lin = linexts(rel, n)
            e = len(lin)
            comps, lab = components(rel, n)
            eC = ec(rel, n)
            mins = [a for a in range(n) if not any((b, a) in rel for b in range(n))]
            # control: e(P) = sum over minimal a of e(P - a)
            if n >= 2:
                tot = 0
                for a in mins:
                    r, _ = restrict(rel, [x for x in range(n) if x != a])
                    tot += len(linexts(r, n - 1))
                check(tot == e, f"standard recursion {sorted(rel)}")
                t["std"] += 1
            # Jenca-Sarkoci contraction recursion, every minimal a.
            if n >= 2:
                for a in mins:
                    tot, tot_bad = 0, 0
                    for b in range(n):
                        if b == a:
                            continue
                        blocks = [[a, b]] + [[x] for x in range(n) if x not in (a, b)]
                        q = quotient(rel, n, blocks)
                        if q is None:
                            continue
                        v = ec(*q)
                        tot += v
                        if (a, b) not in rel:
                            tot_bad += v   # control: drop the covers b of a
                    check(tot == eC, f"JS recursion {sorted(rel)} a={a}")
                    if any((a, b) in rel for b in range(n)) and tot_bad == eC:
                        t["JS control not rejected"] += 1
                    t["JS"] += 1
            # e_C over components (cumulant) and the factorisation.
            sizes = [len(c) for c in comps]
            es = []
            for c in comps:
                r, _ = restrict(rel, c)
                es.append(len(linexts(r, len(c))))
            cum = 0
            for pi in set_partitions(range(len(comps))):
                term = (-1) ** (len(pi) - 1) * factorial(len(pi) - 1)
                for B in pi:
                    m = sum(sizes[i] for i in B)
                    mult = factorial(m)
                    for i in B:
                        mult = mult // factorial(sizes[i]) * es[i]
                    term *= mult
                cum += term
            check(cum == eC, f"cumulant {sorted(rel)}")
            ch_rel, ch_n = disjoint_union(*[chain(s) for s in sizes])
            prod = 1
            for v in es:
                prod *= v
            check(eC == prod * ec(ch_rel, ch_n), f"factorisation {sorted(rel)}")
            t["cumulant+factor"] += 1
            # bounds e/k <= e_C <= e
            check(e <= len(comps) * eC and eC <= e, f"bounds {sorted(rel)}")
            # Weisner family and mu(OP) = (-1)^{n-1} e_C.
            if n <= wnmax:
                OP = []
                for p in set_partitions(range(n)):
                    q = quotient(rel, n, p)
                    if q is not None:
                        OP.append((frozenset(frozenset(B) for B in p), q))
                vals = {x: (-1) ** len(x) * ec(*q) for x, q in OP}
                if n <= 6:
                    mu = mobius_top([x for x, _ in OP])
                    check(mu == (-1) ** (n - 1) * eC, f"mu(OP) {sorted(rel)}")
                    t["mu"] += 1
                top = frozenset([frozenset(range(n))])
                bottom = frozenset(frozenset([i]) for i in range(n))
                cs = [x for x, _ in OP] if (n <= 6 or len(OP) <= 120) else [bottom]
                for c in cs:
                    s = 0
                    for x, _ in OP:
                        # x meet c = discrete iff every block of x meets every block of c in <= 1
                        if all(len(B & C) <= 1 for B in x for C in c):
                            s += vals[x]
                    if c == top:
                        check(s != 0 or n == 1, f"weisner control {sorted(rel)}")
                        t["weisner control rejected"] += (s != 0)
                    elif n >= 2:
                        check(s == 0, f"weisner {sorted(rel)} c={sorted(map(sorted, c))}")
                        t["weisner"] += 1
    print(f"  [std-rec] e(P) = sum_(a minimal) e(P - a): {t['std']} posets (control)", file=out)
    print(f"  [JS-rec] e_C(P) = sum_b e_C(P/ab), every minimal a: {t['JS']} (poset, a) pairs; "
          f"wrong variant (covers dropped) accepted on {t['JS control not rejected']} pairs that have a cover", file=out)
    print(f"  [cumulant] e_C over components and e_C(P) = prod e(T) * e_C(chains): {t['cumulant+factor']} posets", file=out)
    print(f"  [mu] mu(OP(P)) = (-1)^(n-1) e_C(P): {t['mu']} posets (n <= 6)", file=out)
    print(f"  [weisner] sum_(x meet c = 0) (-1)^|x| e_C(Q_x) = 0: {t['weisner']} (poset, c) pairs "
          f"(n <= 6 all c; n = 7 all c when |OP| <= 120, else c = 0^); c = 1^ control rejected "
          f"{t['weisner control rejected']} times", file=out)


def section_burnside(posets, out):
    """#{C : gC = C} = phi(o) * S(g), S(g) = sum_{x in F(P,g)} e_C(P|B_0(x));
    Burnside count of Aut(P)-orbits on Cyc(P); integrality of PLie
    multiplicities on cyclic subgroups."""
    print("== [burnside] fixed classes and orbit counts", file=out)
    t = Counter()
    for n in sorted(posets):
        for rel in posets[n]:
            comps, lab = components(rel, n)
            lin = linexts(rel, n)
            cls = cyclic_classes(lin, lab, comps)
            reps = sorted(set(cls.values()))
            G = n7_sweep.automorphisms_fast(rel, n)
            S = {}
            for g in G:
                o = 1
                y = list(g)
                while y != list(range(n)):
                    y = [g[v] for v in y]
                    o += 1
                # fixed classes, direct
                fixed = sum(1 for w in reps if cls.get(tuple(g[x] for x in w)) == w)
                # F(P, g): partitions of the components into o blocks, each a
                # union of components, permuted cyclically by g.
                Sg = 0
                cmap = [lab[g[c[0]]] for c in comps]
                for pi in set_partitions(range(len(comps))):
                    if len(pi) != o:
                        continue
                    blocks = [frozenset(B) for B in pi]
                    img = [frozenset(cmap[i] for i in B) for B in blocks]
                    if set(img) != set(blocks):
                        continue
                    # cyclic: orbit of block 0 under g has size o
                    B0 = next(B for B in blocks if lab[0] in B)
                    orb, Bc = 1, frozenset(cmap[i] for i in B0)
                    while Bc != B0:
                        Bc = frozenset(cmap[i] for i in Bc)
                        orb += 1
                    if orb != o:
                        continue
                    elems = [x for i in B0 for x in comps[i]]
                    r, _ = restrict(rel, elems)
                    Sg += e_C(r, len(elems))
                S[g] = (o, Sg)
                check(fixed == euler_phi(o) * Sg, f"fixed classes {sorted(rel)} g={g}")
                t["pairs"] += 1
            burn = sum(euler_phi(o) * s for o, s in S.values())
            norb = len({frozenset(cls[tuple(g[x] for x in w)] for g in G) for w in reps})
            check(burn % len(G) == 0 and burn // len(G) == norb, f"burnside {sorted(rel)}")
            triv = sum(mobius_num(o) * s for o, s in S.values())
            check(triv % len(G) == 0 and triv >= 0, f"trivial multiplicity {sorted(rel)}")
            t["posets"] += 1
            if len(comps) > 1 and len(G) > 1:
                t["nontrivial"] += 1
    print(f"  [fixed] #{{C: gC = C}} = phi(o(g)) * sum_(x in F(P,g)) e_C(P|B0(x)): {t['pairs']} (P, g) pairs", file=out)
    print(f"  [burnside] #Aut-orbits on Cyc(P) by Burnside from the closed formula; "
          f"multiplicity of the trivial character in PLie(P) a nonnegative integer: {t['posets']} posets "
          f"({t['nontrivial']} disconnected with Aut != 1)", file=out)


# ---------------------------------------------------------------------------
# Structure of C[Lin P]/R_P


def stats(w, rel, lt, lab, comps, n):
    blocks = len(cuts(w, lab, comps))
    des = sum(1 for i in range(n - 1) if w[i] > w[i + 1])
    maj = sum(i + 1 for i in range(n - 1) if w[i] > w[i + 1])
    jumps = sum(1 for i in range(n - 1) if not lt[w[i]][w[i + 1]])
    restr = tuple(restriction(w, c) for c in comps)
    first_block_has_P1 = None
    return {"restriction": restr, "blocks": blocks, "des": des, "maj": maj, "jumps": jumps,
            "first letter": w[0], "random": hash((w, 7)) % 2}


def section_struct(posets, out, rnmax):
    print("== [struct] structure of C[Lin P]/R_P", file=out)
    names = ["restriction", "blocks", "des", "maj", "jumps", "first letter", "random"]
    homog = Counter()
    tested = 0
    piece_ok = True
    for n in sorted(posets):
        if n > rnmax or n < 2:
            continue
        for rel in posets[n]:
            comps, lab = components(rel, n)
            if len(comps) == 1:
                continue
            lin = linexts(rel, n)
            lt = less_matrix(rel, n)
            A, cols = lie_matrix_on(lin, n)
            eC = e_C(rel, n)
            rA = rank_mod(A)
            check(rA == eC, f"rank Lie|Lin = e_C {sorted(rel)}")
            st = {w: stats(w, rel, lt, lab, comps, n) for w in lin}
            ch_rel, ch_n = disjoint_union(*[chain(len(c)) for c in comps])
            ec_ch = e_C(ch_rel, ch_n)
            for nm in names:
                groups = defaultdict(list)
                for w in lin:
                    groups[st[w][nm]].append(cols[w])
                tot = 0
                for v, cl in groups.items():
                    r = rank_mod([[row[j] for j in cl] for row in A])
                    tot += r
                    if nm == "restriction" and r != ec_ch:
                        piece_ok = False
                if tot == eC:
                    homog[nm] += 1
            tested += 1
    check(homog["restriction"] == tested and piece_ok, "restriction grading")
    print(f"  [rank] rank of Lie_n restricted to Lin P = e_C(P) on all {tested} disconnected posets "
          f"with n <= {rnmax}", file=out)
    print(f"  [homog] R_P homogeneous for the statistic (number of the {tested} posets):", file=out)
    for nm in names:
        print(f"    {nm:13s}: {homog[nm]}", file=out)
    print(f"  [pieces] every restriction-graded piece has dimension e_C(disjoint chains of the "
          f"component sizes): {'PASS' if piece_ok else 'FAIL'}", file=out)


# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--rnmax", type=int, default=6,
                    help="max n for the R_P linear algebra")
    ap.add_argument("--wnmax", type=int, default=7,
                    help="max n for the Weisner-family identities")
    ap.add_argument("--sections", default="csp,promo,count,burnside,struct")
    args = ap.parse_args(argv)
    out = sys.stdout
    allp = n7_sweep.unlabeled_posets(args.nmax)
    posets = {n: allp[n] for n in range(1, args.nmax + 1)}
    print(f"posets per n: {[len(posets[n]) for n in posets]}", file=out)
    secs = args.sections.split(",")
    if "csp" in secs:
        section_csp(posets, out)
    if "promo" in secs:
        section_promo(posets, out, args.rnmax)
    if "count" in secs:
        section_count(posets, out, args.wnmax)
    if "burnside" in secs:
        section_burnside(posets, out)
    if "struct" in secs:
        section_struct(posets, out, args.rnmax)
    print(f"FAILED CHECKS: {len(FAILS)}", file=out)
    for f in FAILS[:30]:
        print("  " + f, file=out)
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
