#!/usr/bin/env python3
"""Conjecture S: linear extensions modulo proper shuffles (mg-3de87).

Companion to notes/conjecture_s_splitting_cycles_span.md.  Plain Python 3, no
dependencies; reuses helpers from poset_jks_check.py and splitting_cycles.py.

Notation (0-based letters; a word is a tuple of distinct letters):
  * Sh(A) = span of proper shuffles u ш v, u, v nonempty, complementary
    letter sets with union A.  Membership is tested through the left-comb
    coordinates  L_a(w) = (-1)^{|u|} rev(u) ш v  for w = u a v  (a = the
    least letter); ker L_a = Sh(A) exactly (checked here for n <= 6, see
    check_La_kernel).
  * W_P = span Lin(P);  K_P = W_P ∩ Sh;  R_P = span of the shuffle sets
    s ш t with s in Lin(P|S), t in Lin(P|S^c), S a nonempty proper union of
    connected components of P.
  * E_{a,x}(w) = +(w minus x) if x immediately precedes a in w,
                 -(w minus x) if x immediately follows a, 0 otherwise.

Checks (each prints a line; the script exits 0 iff all pass):
  [E]   E_{a,x}(u ш v) equals the predicted element (u\\x) ш v, -(u\\x) ш v
        or 0, for every proper shuffle and every ordered pair (a, x), n <= NE.
  [La]  rank of L_a on all words is (n-1)! and L_a kills every proper
        shuffle (so ker L_a = Sh), n <= NE.
  [S]   for every unlabeled poset with n <= NMAX:
          dim K_P = |Lin P| - e_C(P)            (Conjecture S)
          dim R_P = dim K_P                       (K_P = R_P)
          connected P  =>  K_P = 0
  [B]   the words whose first block contains the component of a fixed
        element are independent modulo Sh and number e_C(P) (n <= NMAX).
  [rho] chain level, no use of Prop. Phi: the splitting cycles rho_w,
        w in B_P, are linearly independent and number e_C(P) (n <= NRHO).

Ranks are computed modulo the prime P from splitting_cycles; since
rank_p <= rank_Q, the comparisons are drawn in the rigorous direction (see
the notes file, section "Computations").

Run:  python3 conjecture_s.py [--nmax 6] [--ne 6] [--nrho 5] [--n7-connected]
"""

import argparse
import itertools
import sys
from collections import defaultdict
from math import factorial

import poset_jks_check as pj
from splitting_cycles import rank_mod_p, rho, shuffles


# ---------------------------------------------------------------------------
# Words and the operators E and L


def delete(w, x):
    return tuple(y for y in w if y != x)


def E(vec, a, x):
    """E_{a,x} applied to a dict word -> coefficient."""
    out = defaultdict(int)
    for w, c in vec.items():
        i = w.index(a)
        if i > 0 and w[i - 1] == x:
            out[delete(w, x)] += c
        elif i + 1 < len(w) and w[i + 1] == x:
            out[delete(w, x)] -= c
    return {k: v for k, v in out.items() if v}


def shuffle_vec(u, v, sign=1):
    return {s: sign for s in shuffles(tuple(u), tuple(v))}


def L(w, a):
    """L_a(w) = (-1)^{|u|} rev(u) ш v for w = u a v, as dict."""
    i = w.index(a)
    u, v = w[:i], w[i + 1:]
    return shuffle_vec(tuple(reversed(u)), v, (-1) ** len(u))


def L_rows(words, a):
    """Rows (dict word -> coefficient) of L_a on a list of words."""
    return [L(w, a) for w in words]


def rank_words(vecs):
    """Rank (mod p) of a list of dicts keyed by words."""
    index = {}
    rows = [{index.setdefault(k, len(index)): v for k, v in r.items()} for r in vecs]
    return rank_mod_p(rows)


def rank_mod_sh(words_or_vecs, letters):
    """Rank of a family of elements of C[words on letters] modulo Sh."""
    a = min(letters)
    rows = []
    for item in words_or_vecs:
        if isinstance(item, dict):
            acc = defaultdict(int)
            for w, c in item.items():
                for t, s in L(w, a).items():
                    acc[t] += c * s
            rows.append({k: v for k, v in acc.items() if v})
        else:
            rows.append(L(item, a))
    return rank_words(rows)


# ---------------------------------------------------------------------------
# [E] and [La]


def proper_shuffle_pairs(letters):
    letters = tuple(letters)
    n = len(letters)
    for k in range(1, n):
        for U in itertools.combinations(letters, k):
            V = [y for y in letters if y not in U]
            for u in itertools.permutations(U):
                for v in itertools.permutations(V):
                    yield u, v


def predicted_E(u, v, a, x):
    """The value of E_{a,x}(u ш v) claimed in the notes (Lemma 1)."""
    for s, t in ((u, v), (v, u)):
        if a in s and x in s:
            i, j = s.index(a), s.index(x)
            if j == i - 1:
                return shuffle_vec(delete(s, x), t, 1)
            if j == i + 1:
                return shuffle_vec(delete(s, x), t, -1)
            return {}
    return {}  # a and x in different factors: cancellation


def check_E(n, out):
    letters = range(n)
    bad = total = 0
    for u, v in proper_shuffle_pairs(letters):
        vec = shuffle_vec(u, v)
        for a in letters:
            for x in letters:
                if a == x:
                    continue
                total += 1
                if E(vec, a, x) != predicted_E(u, v, a, x):
                    bad += 1
    ok = bad == 0
    out.append(f"[E]  n={n}: E_(a,x)(u sh v) == predicted for {total} (shuffle, pair) cases: {ok}")
    return ok


def check_La_kernel(n, out):
    letters = range(n)
    words = list(itertools.permutations(letters))
    r = rank_words(L_rows(words, 0))
    killed = True
    for u, v in proper_shuffle_pairs(letters):
        acc = defaultdict(int)
        for w in shuffles(u, v):
            for t, s in L(w, 0).items():
                acc[t] += s
        if any(acc.values()):
            killed = False
            break
    ok = r == factorial(n - 1) and killed
    out.append(f"[La] n={n}: rank L_a = {r} (expect {factorial(n - 1)}), kills all proper shuffles: {killed}: {ok}")
    return ok


# ---------------------------------------------------------------------------
# Posets: components, R_P, blocks


def components(rel, n):
    adj = defaultdict(set)
    for a, b in rel:
        adj[a].add(b)
        adj[b].add(a)
    seen, comps = set(), []
    for s in range(n):
        if s in seen:
            continue
        comp, stack = {s}, [s]
        seen.add(s)
        while stack:
            y = stack.pop()
            for z in adj[y]:
                if z not in seen:
                    seen.add(z)
                    comp.add(z)
                    stack.append(z)
        comps.append(frozenset(comp))
    return comps


def R_generators(rel, n, lin):
    """Indicator vectors of s ш t, S a nonempty proper union of components.

    Only S containing the component of 0 is used (s ш t = t ш s)."""
    comps = components(rel, n)
    k = len(comps)
    gens = []
    first = [c for c in comps if 0 in c][0]
    others = [c for c in comps if c is not first]
    restrict = defaultdict(set)
    for r in range(0, k - 1):
        for extra in itertools.combinations(others, r):
            S = first.union(*extra)
            for w in lin:
                s = tuple(y for y in w if y in S)
                t = tuple(y for y in w if y not in S)
                restrict[(S, s, t)] = True
    for (S, s, t) in restrict:
        gens.append({z: 1 for z in shuffles(s, t)})
    return gens


def first_block_rep(w, comps):
    """True iff the shortest nonempty prefix of w that is a union of
    components contains the component of the letter 0."""
    comp_of = {y: c for c in comps for y in c}
    seen = set()
    for i, y in enumerate(w):
        seen.add(y)
        if all(comp_of[z] <= seen for z in seen):
            return 0 in seen
    return True


def check_posets(nmax, out, connected_only_n=None):
    ok = True
    posets = pj.unlabeled_posets_by_extension(nmax)
    for n in range(2, nmax + 1):
        if connected_only_n is not None and n == connected_only_n:
            continue
        cnt = conn = good_S = good_R = good_conn = good_B = 0
        for rel in posets[n]:
            cnt += 1
            lin = pj.linear_extensions(rel, n)
            eC = len(pj.cyclic_classes(lin))
            r = rank_mod_sh(lin, range(n))
            dimK = len(lin) - r  # >= true dim K
            # Conjecture S: rank = e_C.  rank_p <= rank_Q <= e_C (J-S + Phi),
            # so rank_p == e_C proves it.
            good_S += r == eC
            comps = components(rel, n)
            if len(comps) == 1:
                conn += 1
                good_conn += dimK == 0
                good_R += dimK == 0
            else:
                gens = R_generators(rel, n, lin)
                dimR = rank_words(gens)  # <= true dim R <= true dim K <= dimK
                good_R += dimR == dimK
            B = [w for w in lin if first_block_rep(w, comps)]
            good_B += len(B) == eC and rank_mod_sh(B, range(n)) == len(B)
        line_ok = good_S == cnt and good_R == cnt and good_conn == conn and good_B == cnt
        ok &= line_ok
        out.append(
            f"[S]  n={n}: {cnt} posets ({conn} connected): "
            f"rank(Lin P mod Sh) = e_C: {good_S}/{cnt}; "
            f"K_P = R_P: {good_R}/{cnt}; connected K_P = 0: {good_conn}/{conn}; "
            f"[B] first-block basis: {good_B}/{cnt}: {line_ok}"
        )
    return ok


def check_connected_n(n, out):
    """Connected posets with n elements: K_P = 0 (rank of Lin P mod Sh is |Lin P|)."""
    posets = pj.unlabeled_posets_by_extension(n)[n]
    cnt = good = 0
    for rel in posets:
        if not pj.is_connected(rel, n):
            continue
        cnt += 1
        lin = pj.linear_extensions(rel, n)
        good += rank_mod_sh(lin, range(n)) == len(lin)
    ok = good == cnt
    out.append(f"[S]  n={n}: connected posets: {cnt}; Lin P independent mod Sh: {good}/{cnt}: {ok}")
    return ok


def check_rho_B(nmax, out):
    """Chain level: the splitting cycles rho_w, w in B_P, are independent."""
    ok = True
    posets = pj.unlabeled_posets_by_extension(nmax)
    for n in range(3, nmax + 1):
        cnt = good = 0
        for rel in posets[n]:
            cnt += 1
            lin = pj.linear_extensions(rel, n)
            B = [w for w in lin if first_block_rep(w, components(rel, n))]
            good += rank_words([rho(w) for w in B]) == len(B) == len(pj.cyclic_classes(lin))
        ok &= good == cnt
        out.append(f"[rho] n={n}: {{rho_w : w in B_P}} independent chains, |B_P| = e_C: {good}/{cnt}: {good == cnt}")
    return ok


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--ne", type=int, default=6)
    ap.add_argument("--nrho", type=int, default=5)
    ap.add_argument("--n7-connected", action="store_true",
                    help="also check every connected poset with n = 7")
    args = ap.parse_args(argv)
    out, ok = [], True
    for n in range(2, args.ne + 1):
        ok &= check_E(n, out)
        ok &= check_La_kernel(n, out)
    ok &= check_posets(args.nmax, out)
    ok &= check_rho_B(args.nrho, out)
    if args.n7_connected:
        ok &= check_connected_n(7, out)
    out.append("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    print("\n".join(out))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
