#!/usr/bin/env python3
"""Independent audit computation for notes/qsym_refinement_omega_c.md.

Self-contained: imports nothing from the repository, and was written without
reading the author's script.  Everything is recomputed from definitions:

* posets up to isomorphism (grown by adding a new maximal element over an
  order ideal, deduplicated by a canonical form);
* K_{C,T}(P) in the monomial basis, by LITERAL enumeration of maps f : P -> [k]
  (n <= --litmax), each tested for order preservation and T-anchoring, and by
  a chain-of-ideals dynamic programme (n <= --nmax), the two cross-checked;
* the conversion M -> F by Moebius inversion on subsets of [n-1];
* the candidate sum  sum_kappa F_{Des R_T(kappa)}  from explicitly built
  cyclic classes (rotations at cuts), for every natural labelling (n <= --lmax).

Prints one tagged line per check; exits 0 iff every claim holds and every
CONTROL is refuted somewhere.
"""
import sys, itertools, argparse
from math import comb
from collections import Counter, defaultdict

# ---------------------------------------------------------------- posets
# A poset on {0..n-1}: tuple `down`, down[y] = bitmask of the strict down-set.

def popc(x): return bin(x).count('1')

def up_of(down):
    n = len(down); up = [0] * n
    for y in range(n):
        for x in range(n):
            if down[y] >> x & 1: up[x] |= 1 << y
    return up

def canon(down):
    n = len(down); up = up_of(down)
    inv = [(popc(down[x]), popc(up[x])) for x in range(n)]
    for _ in range(3):
        inv = [(inv[x], tuple(sorted(inv[y] for y in range(n) if down[x] >> y & 1)),
                tuple(sorted(inv[y] for y in range(n) if up[x] >> y & 1))) for x in range(n)]
    keys = sorted(set(inv))
    cells = [[x for x in range(n) if inv[x] == k] for k in keys]
    best = None
    for parts in itertools.product(*[itertools.permutations(c) for c in cells]):
        order = [x for p in parts for x in p]
        code = tuple(down[order[j]] >> order[i] & 1 for i in range(n) for j in range(n))
        if best is None or code < best: best = code
    return (n, best)

def ideals(down):
    n = len(down)
    return [S for S in range(1 << n)
            if all(down[x] & ~S == 0 for x in range(n) if S >> x & 1)]

def all_posets(nmax):
    levels = {1: [(0,)]}
    for n in range(2, nmax + 1):
        seen = {}
        for P in levels[n - 1]:
            for I in ideals(P):
                Q = P + (I,)
                c = canon(Q)
                if c not in seen: seen[c] = Q
        levels[n] = list(seen.values())
    return levels

def components(down):
    n = len(down); up = up_of(down); comp = [-1] * n; cs = []
    for s in range(n):
        if comp[s] >= 0: continue
        stack = [s]; comp[s] = len(cs); mask = 0
        while stack:
            x = stack.pop(); mask |= 1 << x
            for y in range(n):
                if (down[x] >> y & 1 or up[x] >> y & 1) and comp[y] < 0:
                    comp[y] = len(cs); stack.append(y)
        cs.append(mask)
    return cs

def linexts(down):
    n = len(down); res = []
    def rec(w, used):
        if len(w) == n: res.append(tuple(w)); return
        for x in range(n):
            if not used >> x & 1 and down[x] & ~used == 0:
                w.append(x); rec(w, used | 1 << x); w.pop()
    rec([], 0)
    return res

def is_union(mask, comps):
    return all((mask & c) in (0, c) for c in comps)

# ---------------------------------------------------------------- words
def cuts(w, comps):
    res = []; pre = 0
    for p in range(1, len(w)):
        pre |= 1 << w[p - 1]
        if is_union(pre, comps): res.append(p)
    return res

def pieces(w, comps):
    b = [0] + cuts(w, comps) + [len(w)]
    return [w[b[i]:b[i + 1]] for i in range(len(b) - 1)]

def cls(w, comps):
    pc = pieces(w, comps); s = len(pc)
    return frozenset(tuple(x for q in pc[i:] + pc[:i] for x in q) for i in range(s))

def last_piece_has(w, comps, T):
    pc = pieces(w, comps); m = 0
    for x in pc[-1]: m |= 1 << x
    return (m & T) == T

def C_T(w, comps, T):
    """Cuts p with T inside {w_1..w_p}."""
    res = []; pre = 0
    for p in range(1, len(w)):
        pre |= 1 << w[p - 1]
        if is_union(pre, comps) and (pre & T) == T: res.append(p)
    return res

def Des(w, lab):
    return frozenset(i for i in range(1, len(w)) if lab[w[i - 1]] > lab[w[i]])

# ---------------------------------------------------------------- QSym
# A quasisymmetric function of degree n: dict frozenset(J subset [n-1]) -> coeff.

def comp_to_set(alpha):
    s = 0; out = []
    for a in alpha[:-1]:
        s += a; out.append(s)
    return frozenset(out)

def M_to_F(Mc, n):
    """Mc[K] = coefficient of M_K.  F_J = sum_{K >= J} M_K, so
    d_J = sum_{K subset J} (-1)^{|J-K|} c_K."""
    out = {}
    for r in range(n):
        for J in itertools.combinations(range(1, n), r):
            J = frozenset(J); d = 0
            for r2 in range(len(J) + 1):
                for K in itertools.combinations(sorted(J), r2):
                    d += (-1) ** (len(J) - r2) * Mc.get(frozenset(K), 0)
            if d: out[J] = d
    return out

def F_to_M(Fc, n):
    out = Counter()
    for J, d in Fc.items():
        rest = [i for i in range(1, n) if i not in J]
        for r in range(len(rest) + 1):
            for E in itertools.combinations(rest, r):
                out[J | frozenset(E)] += d
    return {k: v for k, v in out.items() if v}

def Fsum(terms):
    c = Counter()
    for J, d in terms: c[J] += d
    return {k: v for k, v in c.items() if v}

def F_spec(Fc, n, m):
    return sum(d * comb(m + n - 1 - len(J), n) for J, d in Fc.items())

# ---------------------------------------------------------------- K_{C,T}, literal
def anchored(f, comps, T, n):
    """f: tuple of values.  Every nonempty upper level set that is a union of
    components contains T."""
    for v in sorted(set(f)):
        U = sum(1 << x for x in range(n) if f[x] >= v)
        if is_union(U, comps) and (U & T) != T: return False
    return True

def op_maps(down, k):
    """All order-preserving f : P -> [1..k] by brute force over [k]^n."""
    n = len(down)
    for f in itertools.product(range(1, k + 1), repeat=n):
        if all(f[x] <= f[y] for y in range(n) for x in range(n) if down[y] >> x & 1):
            yield f

def K_literal(down, comps, Ts):
    """Monomial coefficients by literal enumeration: for each T, Mc[K] counts
    anchored order-preserving surjections onto [k] with composition K."""
    n = len(down); res = {T: Counter() for T in Ts}
    for k in range(1, n + 1):
        for f in op_maps(down, k):
            if len(set(f)) != k: continue
            alpha = tuple(f.count(v) for v in range(1, k + 1))
            K = comp_to_set(alpha)
            for T in Ts:
                if anchored(f, comps, T, n): res[T][K] += 1
    return {T: M_to_F(dict(res[T]), n) for T in Ts}

# ---------------------------------------------------------------- K_{C,T}, chains of ideals
def K_chain(down, comps, T):
    """f <-> chain of ideals 0 = I_0 < I_1 < ... < I_k = P (I_j = f^{-1}[1..j]).
    Upper level set P - I_j is a union of components iff I_j is; T-anchored iff
    no interior I_j is a union of components meeting T."""
    n = len(down); full = (1 << n) - 1
    ids = ideals(down)
    ok = [I for I in ids if I != 0 and I != full and not (is_union(I, comps) and I & T)]
    memo = {}
    def tails(I):  # Counter of compositions (tuples) of the chain from I to full
        if I == full: return Counter({(): 1})
        if I in memo: return memo[I]
        c = Counter()
        for J in ok + [full]:
            if J != I and (I & ~J) == 0:
                d = popc(J) - popc(I)
                for t, v in tails(J).items(): c[(d,) + t] += v
        memo[I] = c; return c
    Mc = Counter()
    for alpha, v in tails(0).items(): Mc[comp_to_set(alpha)] += v
    return M_to_F(dict(Mc), n)

# ---------------------------------------------------------------- labellings
def lab_from_order(order):
    lab = [0] * len(order)
    for i, x in enumerate(order): lab[x] = i
    return lab

def minimal(down, x): return down[x] == 0
def maximal(up, x): return up[x] == 0

def comp_of(comps, x):
    for c in comps:
        if c >> x & 1: return c

def E_star(down, comps, T, lab):
    """(E*_T) as stated in the note, §3.1."""
    n = len(down); up = up_of(down)
    mins = [x for x in range(n) if minimal(down, x)]
    for V in comps:
        if popc(V) < 2: continue
        for a in range(n):
            if not (V >> a & 1 and maximal(up, a)): continue
            for b in mins:
                U = comp_of(comps, b)
                if U in (T, V): continue
                if not lab[a] > lab[b]: return False
    if popc(T) == 1:
        t = T.bit_length() - 1
        for b in mins:
            if not T >> b & 1 and not lab[t] > lab[b]: return False
    return True

def E_star_noiso(down, comps, T, lab):
    """Broken instrument for the control: (E*_T) with the isolated-T clause dropped."""
    n = len(down); up = up_of(down)
    mins = [x for x in range(n) if minimal(down, x)]
    for V in comps:
        if popc(V) < 2: continue
        for a in range(n):
            if not (V >> a & 1 and maximal(up, a)): continue
            for b in mins:
                if comp_of(comps, b) in (T, V): continue
                if not lab[a] > lab[b]: return False
    return True

def separated(down, comps, lab):
    n = len(down); up = up_of(down)
    big = [x for x in range(n) if popc(comp_of(comps, x)) >= 2]
    mn = [x for x in big if minimal(down, x)]; mx = [x for x in big if maximal(up, x)]
    return all(lab[a] < lab[b] for a in mn for b in mx)

def natural(down, lab):
    n = len(down)
    return all(lab[x] < lab[y] for y in range(n) for x in range(n) if down[y] >> x & 1)

def lambda_T(down, comps, T):
    """Built from the note's §3.3 description."""
    n = len(down); up = up_of(down)
    iso = [x for x in range(n) if down[x] == 0 and up[x] == 0]
    g1 = [x for x in range(n) if down[x] == 0 and up[x] != 0]
    mid = [x for x in linexts(down)[0] if down[x] != 0 and up[x] != 0]
    g3 = [x for x in iso if not T >> x & 1]
    g4 = [x for x in range(n) if up[x] == 0 and down[x] != 0 and not T >> x & 1]
    g5 = [x for x in range(n) if up[x] == 0 and T >> x & 1]
    order = g1 + mid + g3 + g4 + g5
    assert sorted(order) == list(range(n))
    return lab_from_order(order)

def stanley_word(f, lab):
    return tuple(sorted(range(len(f)), key=lambda x: (f[x], lab[x])))

def cdes(w, lab):
    return len(Des(w, lab)) + (1 if lab[w[-1]] > lab[w[0]] else 0)

def G_T(w, comps, T, lab):
    D = Des(w, lab); C = C_T(w, comps, T)
    if set(C) & D: return {}
    terms = []
    for r in range(len(C) + 1):
        for S in itertools.combinations(C, r):
            terms.append((D | frozenset(S), (-1) ** r))
    return Fsum(terms)

def single_F(Fc): return len(Fc) == 1 and list(Fc.values())[0] == 1


# ---------------------------------------------------------------- rotation choices
def choice_exists(classes, lab, K):
    """Can one rotation per class be chosen so that sum F_Des = K?  This is a
    bipartite b-matching (classes -> descent sets, capacity K[D]); solved by
    augmenting paths on the expanded slot graph."""
    if any(v < 0 for v in K.values()) or sum(K.values()) != len(classes): return False
    slots = [D for D, v in K.items() for _ in range(v)]
    where = defaultdict(list)
    for j, D in enumerate(slots): where[D].append(j)
    adj = [[j for D in {Des(w, lab) for w in k} for j in where.get(D, [])] for k in classes]
    match = [-1] * len(slots)
    def aug(i, seen):
        for j in adj[i]:
            if j in seen: continue
            seen.add(j)
            if match[j] < 0 or aug(match[j], seen):
                match[j] = i; return True
        return False
    return all(aug(i, set()) for i in range(len(classes)))

def rot_choice(levels, nmax):
    S = Counter()
    for n in range(1, nmax + 1):
        for P in levels[n]:
            comps = components(P)
            if len(comps) == 1: continue
            L = linexts(P); K = {T: K_chain(P, comps, T) for T in comps}
            classes = list({cls(w, comps) for w in L})
            niso = sum(1 for c in comps if popc(c) == 1)
            S['disc'] += 1; S['tdep'] += len({tuple(sorted(K[T].items(), key=str)) for T in comps}) > 1
            S['iso>=2'] += niso >= 2
            anyok = sepok = allE = False
            for order in L:
                lab = lab_from_order(order)
                if all(E_star(P, comps, T, lab) for T in comps): allE = True
                if not anyok or not sepok:
                    if all(choice_exists(classes, lab, K[T]) for T in comps):
                        anyok = True
                        if separated(P, comps, lab): sepok = True
            S['any'] += anyok; S['sep'] += sepok; S['allE'] += allE
            S['allE_iso>=2'] += allE and niso >= 2
            S['any_iso>=2'] += anyok and niso >= 2
    print(f"[rot-choice] disconnected posets n <= {nmax}: {S['disc']} (K depends on T for {S['tdep']}; "
          f">= 2 isolated points: {S['iso>=2']}). Some natural labelling admits, for every T, a choice of one "
          f"rotation per class summing to K_C,T: {S['any']} (separated: {S['sep']}); some labelling satisfies "
          f"(E*_T) for every T: {S['allE']}; among posets with >= 2 isolated points: rotation choice {S['any_iso>=2']}, "
          f"all (E*_T) {S['allE_iso>=2']}")

# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=7)
    ap.add_argument('--lmax', type=int, default=6)
    ap.add_argument('--litmax', type=int, default=6)
    ap.add_argument('--wordmax', type=int, default=5)
    ap.add_argument('--rotchoice', type=int, default=0,
                    help='only run the rotation-choice search (section 2 of the audit note) for n <= k')
    a = ap.parse_args()
    if a.rotchoice:
        rot_choice(all_posets(a.rotchoice), a.rotchoice); return
    bad = []
    def claim(tag, ok, msg):
        print(f'[{tag}] {"OK" if ok else "FAIL"} {msg}')
        if not ok: bad.append(tag)
    def control(tag, nref, ntot, msg):
        print(f'[{tag}] CONTROL {"refuted" if nref else "NOT REFUTED"} on {nref} of {ntot} {msg}')
        if not nref: bad.append(tag)

    levels = all_posets(a.nmax)
    counts = [len(levels[n]) for n in range(1, a.nmax + 1)]
    claim('posets', counts[:7] == [1, 2, 5, 16, 63, 318, 2045][:a.nmax],
          f'counts {counts}, total {sum(counts)}')

    S = Counter()
    for n in range(1, a.nmax + 1):
        for P in levels[n]:
            comps = components(P); Ts = components(P); L = linexts(P)
            S['pairs'] += len(Ts); S['posets'] += 1
            Kc = {T: K_chain(P, comps, T) for T in Ts}
            if n <= a.litmax:
                Kl = K_literal(P, comps, Ts)
                for T in Ts:
                    S['lit'] += 1
                    if Kl[T] != Kc[T]: S['lit_bad'] += 1
            # Gessel sanity: connected P -> K = sum_w F_{Des w} (natural labelling = identity)
            if len(comps) == 1:
                S['gessel'] += 1
                if Kc[Ts[0]] != Fsum((Des(w, list(range(n))), 1) for w in L): S['gessel_bad'] += 1
            # row 0: T-dependence; specialisation T-independent
            vals = list(Kc.values())
            if any(v != vals[0] for v in vals): S[f'Tdep'] += 1; S[f'Tdep{n}'] += 1
            specs = {tuple(F_spec(Kc[T], n, m) for m in range(n + 2)) for T in Ts}
            if len(specs) != 1: S['spec_bad'] += 1
            # classes
            classes = {cls(w, comps) for w in L}
            S['classes'] += len(classes)
            for T in Ts:
                lab = lambda_T(P, comps, T)
                ok_lam = natural(P, lab) and separated(P, comps, lab) and E_star(P, comps, T, lab)
                if not ok_lam: S['lam_bad'] += 1
                reps = []
                for k in classes:
                    R = [w for w in k if last_piece_has(w, comps, T)]
                    if len(R) != 1: S['RT_unique_bad'] += 1
                    reps.append(R[0])
                Q = Fsum((Des(w, lab), 1) for w in reps)
                if Q != Kc[T]: S['thmQ_lam_bad'] += 1
                if any(c < 0 for c in Kc[T].values()): S['Fpos_bad'] += 1
                if sum(Kc[T].values()) != len(classes): S['eC_bad'] += 1
                if n >= 2 and any(len(Des(w, lab)) != cdes(w, lab) - 1 for w in reps):
                    S['size_bad'] += 1
                # Theorem H via the specialisation of Q'
                if n >= 2:
                    hc = tuple(sum(comb(m + n - cdes(w, lab), n) for w in reps) for m in range(n + 2))
                    if hc != tuple(F_spec(Kc[T], n, m) for m in range(n + 2)): S['H_bad'] += 1
                # control: arbitrary representative (lexicographically first member)
                arb = Fsum((Des(min(k), lab), 1) for k in classes)
                if arb != Kc[T]: S['ctl_anyrep'] += 1
                # control: lexicographically-first min-des rep under lambda_0-like labelling
                # (lambda_T for the component of largest label is not used: take
                #  the identity natural labelling of the generated poset)
                lab0 = list(range(n))
                md = Fsum((Des(min(k, key=lambda w: (len(Des(w, lab0)), w)), lab0), 1) for k in classes)
                if md != Kc[T]: S['ctl_mindes_id'] += 1
                # L_T a Lin of a poset?
                LT = [w for w in L if last_piece_has(w, comps, T)]
                common = [(x, y) for x in range(n) for y in range(n) if x != y and
                          all(w.index(x) < w.index(y) for w in LT)]
                cdown = tuple(sum(1 << x for x, y2 in common if y2 == y) for y in range(n))
                S['LT_n'] += 1
                if len(linexts(cdown)) == len(LT): S['LT_is_lin'] += 1

            # ---- every natural labelling, n <= lmax
            if n <= a.lmax:
                seenkeys = set()
                for T in Ts:
                    for order in L:
                        lab = lab_from_order(order)
                        key = (frozenset((lab[x], lab[y]) for y in range(n) for x in range(n)
                                         if P[y] >> x & 1), frozenset(lab[x] for x in range(n) if T >> x & 1))
                        if key in seenkeys: continue
                        seenkeys.add(key)
                        S['lp'] += 1
                        i_ = Fsum((Des(w, lab), 1) for w in L if last_piece_has(w, comps, T)) == Kc[T]
                        notLT = [w for w in L if not last_piece_has(w, comps, T)]
                        x2 = all(set(C_T(w, comps, T)) & Des(w, lab) for w in notLT)
                        x3 = all(C_T(w, comps, T)[0] in Des(w, lab) for w in notLT)
                        e4 = E_star(P, comps, T, lab)
                        e4b = E_star_noiso(P, comps, T, lab)
                        if not (i_ == x2 == x3 == e4): S['iff_bad'] += 1
                        if i_: S['i_holds'] += 1
                        if e4b != i_: S['ctl_Ebroken'] += 1
                        # Prop D_q
                        D = Fsum((J, d) for w in L for J, d in G_T(w, comps, T, lab).items())
                        if D != Kc[T]: S['Dq_bad'] += 1
                        # per-class (Lemma 1 lift) on separated labellings
                        if separated(P, comps, lab):
                            S['sep'] += 1; anybad = False
                            for k in classes:
                                c = Fsum((J, d) for w in k for J, d in G_T(w, comps, T, lab).items())
                                S['sep_classes'] += 1
                                if not single_F(c):
                                    anybad = True; S['perclass_notF'] += 1
                                    if any(v < 0 for v in c.values()): S['perclass_neg'] += 1
                            if anybad: S['sep_bad_pairs'] += 1
                        # per-word G_T = generating function of anchored f with Stanley word w
                        if n <= a.wordmax:
                            per = defaultdict(Counter)
                            for k in range(1, n + 1):
                                for f in op_maps(P, k):
                                    if len(set(f)) != k or not anchored(f, comps, T, n): continue
                                    w = stanley_word(f, lab)
                                    per[w][comp_to_set(tuple(f.count(v) for v in range(1, k + 1)))] += 1
                            S['words'] += 1
                            for w in L:
                                if M_to_F(dict(per.get(w, {})), n) != G_T(w, comps, T, lab):
                                    S['word_bad'] += 1; break
            # ---- bijection B under lambda_T (and the control under identity when E* fails)
            if n <= a.wordmax:
                for T in Ts:
                    for which, lab in (('lam', lambda_T(P, comps, T)), ('id', list(range(n)))):
                        if which == 'id' and E_star(P, comps, T, lab): continue
                        mism = 0
                        for f in op_maps(P, 3):
                            S['bij_maps_' + which] += 1
                            w = stanley_word(f, lab)
                            if anchored(f, comps, T, n) != last_piece_has(w, comps, T): mism += 1
                        S['bij_bad_' + which] += 1 if mism else 0
                        S['bij_pairs_' + which] += 1

    print(f'[pairs] {S["posets"]} posets, {S["pairs"]} pairs (P, T) (every component), {S["classes"]} classes in all')
    claim('literal=chain', S['lit_bad'] == 0,
          f'K_C,T by literal map enumeration = chain-of-ideals DP on {S["lit"]} pairs, n <= {a.litmax}')
    claim('gessel', S['gessel_bad'] == 0, f'connected P: K = sum_w F_Des(w) on {S["gessel"]} posets')
    print(f'[T-dep] K_C,T depends on T for {S["Tdep"]} of {S["posets"]} posets; by n: '
          + str([S[f"Tdep{n}"] for n in range(1, a.nmax + 1)]))
    claim('spec', S['spec_bad'] == 0, f'principal specialisation (m = 0..n+1) independent of T on all {S["posets"]} posets')
    claim('lamT', S['lam_bad'] == 0, f'lambda_T natural, separated, (E*_T) on {S["pairs"]} pairs')
    claim('RT', S['RT_unique_bad'] == 0, 'each class has exactly one rotation with T in the last piece')
    claim('thmQ-lamT', S['thmQ_lam_bad'] == 0, f'K_C,T = sum_kappa F_Des R_T(kappa) under lambda_T on {S["pairs"]} pairs')
    claim('F+', S['Fpos_bad'] == 0 and S['eC_bad'] == 0, f'K_C,T F-positive with coefficient sum #Cyc(P), {S["pairs"]} pairs')
    claim('size', S['size_bad'] == 0, '|Des R_T| = cdes - 1 under lambda_T (n >= 2)')
    claim('H-spec', S['H_bad'] == 0, 'K_C,T(1^m) = sum_kappa C(m+n-cdes, n) under lambda_T (n >= 2)')
    control('ctl-anyrep', S['ctl_anyrep'], S['pairs'], 'pairs: Des of lexicographically first rotation under lambda_T')
    control('ctl-mindes-id', S['ctl_mindes_id'], S['pairs'], 'pairs: lex-first min-des rotation under the generation labelling')
    print(f'[LT-lin] L_T(P) is Lin of a poset (labelling-free) for {S["LT_is_lin"]} of {S["LT_n"]} pairs')
    claim('thmQ-iff', S['iff_bad'] == 0,
          f'(i) <=> (ii) <=> (iii) <=> (E*_T) on {S["lp"]} labelled pairs n <= {a.lmax}; (i) holds on {S["i_holds"]}, fails on {S["lp"] - S["i_holds"]}')
    control('ctl-Ebroken', S['ctl_Ebroken'], S['lp'], 'labelled pairs: (E*_T) without the isolated-T clause disagrees with (i)')
    control('ctl-anylab', S['lp'] - S['i_holds'], S['lp'], 'labelled pairs: (i) for an arbitrary natural labelling')
    claim('propD-qsym', S['Dq_bad'] == 0, f'K_C,T = sum_w G_T(w) on {S["lp"]} labelled pairs')
    claim('G_T-word', S['word_bad'] == 0, f'G_T(w) = anchored maps with Stanley word w, every w, {S["words"]} labelled pairs n <= {a.wordmax}')
    print(f'[perclass-sep] separated labelled pairs {S["sep"]}: some class not a single F on {S["sep_bad_pairs"]}; '
          f'classes {S["sep_classes"]}, not single F {S["perclass_notF"]}, of which with a negative coefficient {S["perclass_neg"]}')
    control('ctl-perclass', S['sep_bad_pairs'], S['sep'], 'separated labelled pairs: per-class contribution a single F')
    claim('bij', S['bij_bad_lam'] == 0,
          f'anchored <=> Stanley word in L_T, under lambda_T, all maps into [3], {S["bij_maps_lam"]} maps, {S["bij_pairs_lam"]} pairs n <= {a.wordmax}')
    control('ctl-bij', S['bij_bad_id'], S['bij_pairs_id'], f'pairs with (E*_T) false for the generation labelling: bijection B ({S["bij_maps_id"]} maps)')
    print('RESULT', 'ALL OK' if not bad else 'FAILURES: ' + ' '.join(bad))
    sys.exit(0 if not bad else 1)

if __name__ == '__main__':
    main()
