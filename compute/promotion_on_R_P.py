#!/usr/bin/env python3
"""When does promotion preserve R_P?  Companion to ../notes/promotion_on_R_P.md.

For every disconnected poset P with n <= NMAX elements (up to isomorphism),
decide whether promotion maps R_P into itself, where

    R_P = span{ s sh t : S a nonempty proper union of components,
                         s in Lin(P|S), t in Lin(P|S^c) }.

Method (independent of linear_extensions.py; plain Python, exact integers):

  * Posets are generated up to isomorphism by adding a maximal element to
    each poset on n-1 points, with a brute-force canonical form.  Counts are
    checked against OEIS A000112 / A000608.
  * Promotion is computed by toggles, d = tau_{n-1} o ... o tau_1
    (tau_1 first), on words w = w_1 ... w_n.  Lemma P is NOT used.
  * Membership in R_P: by [Thm] Thm thm:S(b), W_P cap Sh_n = R_P, so for
    Y in W_P = C[Lin P],  Y in R_P  iff  Y in Sh_n  iff  Y is orthogonal to
    Lie_n (Ree).  Lie_n has basis rho(c n) = [c_1,[c_2,...,[c_{n-1}, n]]],
    c a word in [n-1], and <rho(c n), L n R> = (-1)^{|R|} [c in L sh rev(R)].
    So Y in Sh_n iff pi(Y) = 0, where
        pi(L n R) = (-1)^{|R|} (L sh rev(R))   in C[words of [n-1]].
    The pairing formula and "pi(Y)=0 iff Y in Sh_n" are checked for n <= 5
    by expanding the brackets and by ranks.
  * d(R_P) in R_P iff pi(d r) = 0 for every generator r = s sh t.  For a
    poset where this fails we record the first failing generator (a
    certificate: r in R_P and a word c with <rho(c n), d r> != 0).  For the
    posets where it holds, every generator is checked.
  * Theorem certificates: for every disconnected P outside the two-chain
    family, the specific r of the note's proof (case A: S = a non-chain
    component; case B: S = a chain component with P - S not a chain) is
    checked to satisfy pi(d r) != 0, and in case A the graded piece
    (s'' sh t) z alone is checked to be outside Sh_n.

Run from compute/:

    python3 promotion_on_R_P.py --nmax 8 > output/promotion_on_R_P.txt

Exit status 0 iff every check holds and every control behaves as intended.
"""

import argparse
import itertools
import sys
import time
from collections import defaultdict

FAILS = []
OEIS_POSETS = {1: 1, 2: 2, 3: 5, 4: 16, 5: 63, 6: 318, 7: 2045, 8: 16999}
OEIS_CONNECTED = {1: 1, 2: 1, 3: 3, 4: 10, 5: 44, 6: 238, 7: 1650, 8: 14512}


def check(ok, label):
    if not ok:
        FAILS.append(label)
    return ok


# ---------------------------------------------------------------------------
# Posets up to isomorphism.  A poset on [n] is a frozenset of strict pairs
# (a, b) meaning a < b, transitively closed.


def canonical(rel, n):
    """Lexicographically least relation set over relabellings that respect
    the (down-size, up-size) invariant."""
    down = [0] * n
    up = [0] * n
    for a, b in rel:
        down[b] += 1
        up[a] += 1
    key = sorted(range(n), key=lambda x: (down[x], up[x]))
    classes = []
    for x in key:
        if classes and (down[classes[-1][0]], up[classes[-1][0]]) == (down[x], up[x]):
            classes[-1].append(x)
        else:
            classes.append([x])
    best = None
    for perms in itertools.product(*[itertools.permutations(c) for c in classes]):
        order = [x for p in perms for x in p]
        new = {x: i for i, x in enumerate(order)}
        cand = tuple(sorted((new[a], new[b]) for a, b in rel))
        if best is None or cand < best:
            best = cand
    return frozenset(best)


def ideals(rel, n):
    """All down-closed subsets of [n], as bitmasks."""
    below = [0] * n
    for a, b in rel:
        below[b] |= 1 << a
    out = []
    for mask in range(1 << n):
        if all(below[x] & ~mask == 0 for x in range(n) if mask >> x & 1):
            out.append(mask)
    return out


def posets_up_to(nmax):
    """Dict n -> list of posets on [n] up to isomorphism."""
    res = {1: [frozenset()]}
    for n in range(2, nmax + 1):
        seen = set()
        for rel in res[n - 1]:
            for D in ideals(rel, n - 1):
                new = set(rel) | {(a, n - 1) for a in range(n - 1) if D >> a & 1}
                seen.add(canonical(new, n))
        res[n] = sorted(seen, key=lambda r: sorted(r))
    return res


def components(rel, n):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in rel:
        parent[find(a)] = find(b)
    groups = defaultdict(list)
    for x in range(n):
        groups[find(x)].append(x)
    return sorted((tuple(g) for g in groups.values()), key=lambda g: (len(g), g))


def is_chain(rel, elems):
    return all((a, b) in rel or (b, a) in rel for a, b in itertools.combinations(elems, 2))


def linexts(rel, elems):
    elems = list(elems)
    below = {x: {a for a, b in rel if b == x and a in elems} for x in elems}
    out = []

    def rec(word, used):
        if len(word) == len(elems):
            out.append(tuple(word))
            return
        for x in elems:
            if x not in used and below[x] <= used:
                word.append(x)
                used.add(x)
                rec(word, used)
                used.discard(x)
                word.pop()
    rec([], set())
    return out


def promote(w, rel):
    """d = tau_{n-1} o ... o tau_1 on a word (tau_i swaps positions i, i+1
    when the two letters are incomparable)."""
    w = list(w)
    for i in range(len(w) - 1):
        a, b = w[i], w[i + 1]
        if (a, b) not in rel and (b, a) not in rel:
            w[i], w[i + 1] = b, a
    return tuple(w)


# ---------------------------------------------------------------------------
# Shuffles, Lie brackets, and the membership test pi


def shuffle(u, v):
    if not u:
        return [tuple(v)]
    if not v:
        return [tuple(u)]
    return ([(u[0],) + x for x in shuffle(u[1:], v)] +
            [(v[0],) + x for x in shuffle(u, v[1:])])


def add(acc, vec, c=1):
    for k, x in vec.items():
        acc[k] = acc.get(k, 0) + c * x
    return acc


def clean(vec):
    return {k: x for k, x in vec.items() if x}


def shuffle_vec(u, v):
    out = {}
    for x in shuffle(u, v):
        out[x] = out.get(x, 0) + 1
    return out


def rho(c):
    """Right-normed bracket [c_1,[c_2,...,[c_{m-1}, c_m]]] as a dict."""
    vec = {(c[-1],): 1}
    for a in reversed(c[:-1]):
        new = {}
        for w, x in vec.items():
            new[(a,) + w] = new.get((a,) + w, 0) + x
            new[w + (a,)] = new.get(w + (a,), 0) - x
        vec = clean(new)
    return vec


def pi(Y, pivot):
    """pi(L pivot R) = (-1)^{|R|} (L sh rev R).  Y in Sh_n iff pi(Y) = 0."""
    out = {}
    for w, x in Y.items():
        if not x:
            continue
        p = w.index(pivot)
        L, R = w[:p], w[p + 1:]
        sgn = -1 if len(R) % 2 else 1
        for c in shuffle(L, tuple(reversed(R))):
            out[c] = out.get(c, 0) + sgn * x
    return clean(out)


def rank_q(rows):
    """Exact rank over Q of a list of dict-vectors."""
    from fractions import Fraction
    rows = [{k: Fraction(v) for k, v in r.items() if v} for r in rows]
    rank = 0
    pivots = {}
    for r in rows:
        while r:
            k = min(r)
            if k in pivots:
                pr = pivots[k]
                f = r[k] / pr[k]
                for kk, vv in pr.items():
                    nv = r.get(kk, 0) - f * vv
                    if nv:
                        r[kk] = nv
                    else:
                        r.pop(kk, None)
            else:
                pivots[k] = r
                rank += 1
                break
    return rank


def section_instrument(out):
    """Checks on the membership test itself (n <= 5)."""
    print("== instrument: pi and Ree", file=out)
    ok_pair = True
    for n in range(2, 6):
        pivot = n - 1
        for c in itertools.permutations(range(n - 1)):
            vec = rho(c + (pivot,))
            for w, x in vec.items():
                p = w.index(pivot)
                L, R = w[:p], w[p + 1:]
                want = (-1) ** len(R) * shuffle(L, tuple(reversed(R))).count(c)
                ok_pair &= (x == want)
            # words not in the bracket pair to zero
            for w in itertools.permutations(range(n)):
                if w not in vec:
                    p = w.index(pivot)
                    ok_pair &= c not in shuffle(w[:p], tuple(reversed(w[p + 1:])))
    check(ok_pair, "pairing formula")
    print(f"  [pair] <rho(c n), L n R> = (-1)^|R| [c in L sh rev R] for all c, all words, "
          f"n <= 5: {'PASS' if ok_pair else 'FAIL'}", file=out)
    ok_rank = True
    for n in range(2, 6):
        pivot = n - 1
        letters = tuple(range(n))
        shuf = []
        for k in range(1, n):
            for S in itertools.combinations(letters, k):
                Sc = tuple(x for x in letters if x not in S)
                for u in itertools.permutations(S):
                    for v in itertools.permutations(Sc):
                        shuf.append(shuffle_vec(u, v))
        r_sh = rank_q(shuf)
        killed = all(not pi(y, pivot) for y in shuf)
        images = [pi({w: 1}, pivot) for w in itertools.permutations(letters)]
        r_img = rank_q(images)
        from math import factorial
        good = killed and r_sh == factorial(n) - factorial(n - 1) and r_img == factorial(n - 1)
        ok_rank &= good
        print(f"  [ree] n={n}: dim Sh_n = {r_sh} (= n! - (n-1)!), pi kills every shuffle: {killed}, "
              f"rank pi = {r_img} (= (n-1)!): {'PASS' if good else 'FAIL'}", file=out)
    check(ok_rank, "Ree / pi rank")
    # Negative control: a nonzero vector supported on words ending in one
    # letter is not in Sh_n (the Lemma used in the note).
    neg = pi({(1, 0, 3, 2): 1, (0, 1, 3, 2): -1}, 3)
    check(bool(neg), "control: X z not in Sh")
    print(f"  [ctl] pi(1032 - 0132) != 0: {'PASS' if neg else 'FAIL'}", file=out)


# ---------------------------------------------------------------------------
# The main test


def generators(rel, n, comps):
    """Yield (S, s, t, r) for every generator r = s sh t of R_P."""
    k = len(comps)
    lin_cache = {}

    def lin(elems):
        if elems not in lin_cache:
            lin_cache[elems] = linexts(rel, elems)
        return lin_cache[elems]
    for mask in range(1, (1 << k) - 1):
        S = tuple(sorted(x for i in range(k) if mask >> i & 1 for x in comps[i]))
        Sc = tuple(sorted(x for x in range(n) if x not in S))
        for s in lin(S):
            for t in lin(Sc):
                yield S, s, t


def promote_vec(Y, rel):
    out = {}
    for w, x in Y.items():
        dw = promote(w, rel)
        out[dw] = out.get(dw, 0) + x
    return out


def preserves(rel, n, comps):
    """(holds, certificate or None, number of generators checked)."""
    count = 0
    for S, s, t in generators(rel, n, comps):
        count += 1
        r = shuffle_vec(s, t)
        img = pi(promote_vec(r, rel), n - 1)
        if img:
            c = min(img)
            return False, (S, s, t, c, img[c]), count
    return True, None, count


def proof_certificate(rel, n, comps):
    """The r of the note's proof.  Returns (case, ok)."""
    pivot = n - 1
    nonchain = [T for T in comps if not is_chain(rel, T)]
    if nonchain:
        T = nonchain[0]
        R = tuple(sorted(x for x in range(n) if x not in T))
        s = linexts(rel, T)[0]
        t = linexts(rel, R)[0]
        r = shuffle_vec(s, t)
        dr = promote_vec(r, rel)
        ds = promote(s, rel)
        z = ds[-1]
        # graded piece with T-part d_T(s) must equal (s'' sh t) z
        piece = {w: x for w, x in dr.items() if tuple(y for y in w if y in T) == ds}
        want = {w + (z,): x for w, x in shuffle_vec(ds[:-1], t).items()}
        ok = (ds != s and piece == want and bool(pi(piece, pivot)) and bool(pi(dr, pivot)))
        return "A", ok
    # all components chains: case B needs k >= 3
    T = comps[0]
    R = tuple(sorted(x for x in range(n) if x not in T))
    s = linexts(rel, T)[0]
    t = linexts(rel, R)[0]
    r = shuffle_vec(s, t)
    dr = promote_vec(r, rel)
    dt = promote(t, rel)
    # d r - s sh d(t)  ==  (s~ sh (t - d t)) sigma
    lhs = add(dict(dr), shuffle_vec(s, dt), -1)
    rhs = add({w + (s[-1],): x for w, x in shuffle_vec(s[:-1], t).items()},
              {w + (s[-1],): x for w, x in shuffle_vec(s[:-1], dt).items()}, -1)
    ok = (dt != t and clean(lhs) == clean(rhs) and bool(pi(dr, pivot)))
    return "B", ok


def two_chains(rel, comps):
    return len(comps) == 2 and all(is_chain(rel, T) for T in comps)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=8)
    args = ap.parse_args(argv)
    out = sys.stdout
    t0 = time.time()
    section_instrument(out)

    print(f"== posets up to isomorphism, n <= {args.nmax}", file=out)
    ps = posets_up_to(args.nmax)
    for n in range(1, args.nmax + 1):
        conn = sum(1 for rel in ps[n] if len(components(rel, n)) == 1)
        ok = len(ps[n]) == OEIS_POSETS[n] and conn == OEIS_CONNECTED[n]
        check(ok, f"poset count n={n}")
        print(f"  [count] n={n}: {len(ps[n])} posets (A000112: {OEIS_POSETS[n]}), "
              f"{conn} connected (A000608: {OEIS_CONNECTED[n]}), "
              f"{len(ps[n]) - conn} disconnected: {'PASS' if ok else 'FAIL'}", file=out)

    print("== does promotion preserve R_P?  (disconnected P)", file=out)
    cum_total = cum_pres = 0
    for n in range(2, args.nmax + 1):
        total = pres = 0
        pres_list = []
        mismatch = []
        cases = defaultdict(int)
        cert_ok = True
        gens = 0
        for rel in ps[n]:
            comps = components(rel, n)
            if len(comps) == 1:
                continue
            total += 1
            holds, cert, cnt = preserves(rel, n, comps)
            gens += cnt
            fam = two_chains(rel, comps)
            if holds:
                pres += 1
                pres_list.append(tuple(len(T) for T in comps))
            if holds != fam:
                mismatch.append(sorted(rel))
            if not fam:
                case, ok = proof_certificate(rel, n, comps)
                cases[case] += 1
                cert_ok &= ok
                if not ok:
                    print(f"    proof certificate FAILS on {sorted(rel)}", file=out)
        cum_total += total
        cum_pres += pres
        check(not mismatch, f"family n={n}")
        check(cert_ok, f"proof certificates n={n}")
        print(f"  [descend-R] n={n}: promotion preserves R_P on {pres} of {total} disconnected "
              f"posets; component sizes of those: {sorted(pres_list)}; "
              f"= the two-chain posets: {'PASS' if not mismatch else 'FAIL ' + str(mismatch[:3])}",
              file=out)
        print(f"  [proof]     n={n}: proof's r has d r not in R_P on all {total - pres} others "
              f"(case A, a non-chain component: {cases['A']}; case B, >= 3 chains: {cases['B']}): "
              f"{'PASS' if cert_ok else 'FAIL'}; generators examined: {gens}", file=out)
        if n == 6:
            ctl = cum_total == 108 and cum_pres == 9
            check(ctl, "positive control 9/108")
            print(f"  [control] n <= 6: {cum_pres} of {cum_total} "
                  f"(linear_extensions.md: 9 of 108): {'PASS' if ctl else 'FAIL'}", file=out)
    print(f"  [total] n <= {args.nmax}: {cum_pres} of {cum_total} disconnected posets", file=out)

    # One explicit certificate per smallest case, for the note.
    print("== smallest examples", file=out)
    examples = {
        "A_3 (three points)": (frozenset(), 3),
        "C_2 + C_1 + C_1": (frozenset({(0, 1)}), 4),
        "V + C_1 (V = 0<1, 0<2)": (frozenset({(0, 1), (0, 2)}), 4),
    }
    for name, (rel, n) in examples.items():
        comps = components(rel, n)
        holds, cert, _ = preserves(rel, n, comps)
        check(not holds, f"example {name}")
        S, s, t, c, val = cert
        print(f"  {name}: r = {''.join(map(str, s))} sh {''.join(map(str, t))}; "
              f"<rho({''.join(map(str, c))}{n - 1}), d r> = {val}", file=out)

    print(f"== {'ALL PASS' if not FAILS else 'FAILURES: ' + ', '.join(FAILS)}  "
          f"({time.time() - t0:.0f} s)", file=out)
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
