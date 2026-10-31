#!/usr/bin/env python3
"""Computations for notes/prior_art_reciprocity_omega_c.md.

Imports nothing from the repository.  Everything is recomputed here:

* posets up to isomorphism (grow by a new maximal element, canonical form);
* Omega_C(P, m) from the COUNTING side of Theorem Omega ([LS] section 2,
  PROVEN + audited): order-preserving f : P -> [m] such that no nonempty
  upper level set is a union of components missing T.  Writing
  I_k = f^{-1}[1, k], f is a multichain  {} = I_0 <= I_1 <= ... <= I_m = P
  of order ideals, and the condition says that no I_k with k < m is a
  proper union of components containing T ("bad" ideal).  So Omega_C(m)
  is a walk count in J(P) minus the bad ideals.  No words, no labellings,
  no Moebius function of OP(P);
* h_C from those values: sum_m Omega_C(m) x^m = sum_j h_j x^{j+1}/(1-x)^{n+1};
* W_P (descent polynomial of linear extensions, natural labelling) by a
  separate dynamic programme over (ideal, last letter).

Line tags in brackets are cited by the note.  Exit status 0 iff every
CHECK passes and every CONTROL is refuted somewhere.
"""
import argparse
import itertools
import sys
from collections import defaultdict
from fractions import Fraction
from math import comb

FAILS = []


def check(ok, label, detail=""):
    print(f"[{label}] {'PASS' if ok else 'FAIL'} {detail}".rstrip())
    if not ok:
        FAILS.append(label)


def control(nrefuted, label, detail=""):
    ok = nrefuted > 0
    print(f"[{label}] CONTROL {'REFUTED' if ok else 'NOT REFUTED'} "
          f"on {nrefuted} {detail}".rstrip())
    if not ok:
        FAILS.append(label)


# ---------------------------------------------------------------- posets
# A poset on {0..n-1} is a tuple `down` of bitmasks: down[x] = {y : y < x}.

def ideals(n, down):
    out = []

    def rec(x, mask):
        if x == n:
            out.append(mask)
            return
        rec(x + 1, mask)
        if down[x] & ~mask == 0:
            rec(x + 1, mask | (1 << x))
    # requires a natural labelling (down[x] subset of {0..x-1})
    rec(0, 0)
    return out


def ideals_any(n, down):
    """Order ideals for an arbitrary labelling (BFS over the lattice)."""
    seen = {0}
    stack = [0]
    while stack:
        I = stack.pop()
        for x in range(n):
            if not I >> x & 1 and down[x] & ~I == 0:
                J = I | (1 << x)
                if J not in seen:
                    seen.add(J)
                    stack.append(J)
    return sorted(seen, key=lambda s: (bin(s).count("1"), s))


def canon(n, down):
    up = [0] * n
    for x in range(n):
        for y in range(n):
            if down[x] >> y & 1:
                up[y] |= 1 << x
    inv = [(bin(down[x]).count("1"), bin(up[x]).count("1")) for x in range(n)]
    cls = defaultdict(list)
    for x in range(n):
        cls[inv[x]].append(x)
    best = None
    for perms in itertools.product(*(itertools.permutations(cls[k])
                                     for k in sorted(cls))):
        order = [x for p in perms for x in p]
        pos = {x: i for i, x in enumerate(order)}
        rel = tuple(sorted((pos[y], pos[x]) for x in range(n)
                           for y in range(n) if down[x] >> y & 1))
        if best is None or rel < best:
            best = rel
    return best


def naturalize(n, down):
    order, placed = [], 0
    while len(order) < n:
        for x in range(n):
            if not placed >> x & 1 and down[x] & ~placed == 0:
                order.append(x)
                placed |= 1 << x
                break
    pos = {x: i for i, x in enumerate(order)}
    new = [0] * n
    for x in range(n):
        for y in range(n):
            if down[x] >> y & 1:
                new[pos[x]] |= 1 << pos[y]
    return tuple(new)


def all_posets(nmax):
    by_n = {0: [()]}
    for n in range(1, nmax + 1):
        seen = {}
        for P in by_n[n - 1]:
            for I in ideals(n - 1, P):
                Q = P + (I,)
                key = canon(n, Q)
                if key not in seen:
                    seen[key] = Q
        by_n[n] = [naturalize(n, Q) for Q in seen.values()]
    return by_n


def components(n, down):
    adj = [0] * n
    for x in range(n):
        for y in range(n):
            if down[x] >> y & 1:
                adj[x] |= 1 << y
                adj[y] |= 1 << x
    comps, seen = [], 0
    for s in range(n):
        if seen >> s & 1:
            continue
        c, frontier = 1 << s, 1 << s
        while frontier:
            new = 0
            for x in range(n):
                if frontier >> x & 1:
                    new |= adj[x]
            frontier = new & ~c
            c |= new
        comps.append(c)
        seen |= c
    return comps


def transitive_closure(n, cover_pairs):
    """cover_pairs: list of (a, b) meaning a < b."""
    below = [0] * n
    for a, b in cover_pairs:
        below[b] |= 1 << a
    changed = True
    while changed:
        changed = False
        for x in range(n):
            acc = below[x]
            for y in range(n):
                if below[x] >> y & 1:
                    acc |= below[y]
            if acc != below[x]:
                below[x] = acc
                changed = True
    for x in range(n):
        if below[x] >> x & 1:
            raise ValueError("cycle")
    return tuple(below)


def disjoint_union(nP, P, nQ, Q):
    return nP + nQ, tuple(P) + tuple(d << nP for d in Q)


def chain(k):
    return k, tuple(((1 << x) - 1) for x in range(k))


def antichain(k):
    return k, tuple(0 for _ in range(k))


# ---------------------------------------------------- Omega_C and h_C

def omega_c_values(n, down, T, mmax, ids=None):
    """Omega_C(P, m) for m = 0..mmax, from the Theorem Omega count."""
    if ids is None:
        ids = ideals_any(n, down)
    full = (1 << n) - 1
    comps = components(n, down)
    unions = set()
    for r in range(len(comps) + 1):
        for sub in itertools.combinations(comps, r):
            u = 0
            for c in sub:
                u |= c
            unions.add(u)
    bad = {u for u in unions if u != full and u & T == T}
    good = [I for I in ids if I not in bad]
    # supersets among good ideals
    sup = {I: [J for J in good if J & I == I] for I in good}
    a = {I: 0 for I in good}
    a[0] = 1
    vals = [0]                       # Omega_C(0) = 0 for n >= 1
    for m in range(1, mmax + 1):
        # Omega_C(m) = sum over good I_{m-1} of a_{m-1}(I) (then I_m = P)
        vals.append(sum(a.values()))
        b = {I: 0 for I in good}
        for I, v in a.items():
            if v:
                for J in sup[I]:
                    b[J] += v
        a = b
    return vals


def h_from_values(n, vals):
    """sum_m Omega(m) x^m * (1-x)^{n+1}; h_j = coefficient of x^{j+1}."""
    N = [0] * (n + 2)
    for k in range(n + 2):
        N[k] = sum((-1) ** i * comb(n + 1, i) * vals[k - i]
                   for i in range(k + 1))
    h = N[1:]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h


def h_c(n, down, T=None):
    comps = components(n, down)
    if T is None:
        T = comps[-1]
    return h_from_values(n, omega_c_values(n, down, T, n + 1))


def W_poly(n, down):
    """Descent polynomial of linear extensions under a natural labelling
    (computed for whatever labelling `down` carries, which must be
    natural: down[x] subset of {0..x-1})."""
    assert all(down[x] >> y & 1 == 0 for x in range(n) for y in range(x, n))
    dp = {(0, -1): [1]}
    for _ in range(n):
        nd = defaultdict(lambda: [0] * (n + 1))
        for (I, last), poly in dp.items():
            for x in range(n):
                if not I >> x & 1 and down[x] & ~I == 0:
                    d = 1 if (last > x) else 0
                    tgt = nd[(I | (1 << x), x)]
                    for k, c in enumerate(poly):
                        if c:
                            tgt[k + d] += c
        dp = {k: v for k, v in nd.items()}
    tot = [0] * (n + 1)
    for poly in dp.values():
        for k, c in enumerate(poly):
            tot[k] += c
    while len(tot) > 1 and tot[-1] == 0:
        tot.pop()
    return tot


# ------------------------------------------------ polynomial predicates

def unimodal(a):
    i = 0
    while i + 1 < len(a) and a[i] <= a[i + 1]:
        i += 1
    while i + 1 < len(a) and a[i] >= a[i + 1]:
        i += 1
    return i == len(a) - 1


def log_concave(a):
    nz = [i for i, x in enumerate(a) if x]
    if nz and nz[-1] - nz[0] + 1 != len(nz):
        return False
    return all(a[i] * a[i] >= a[i - 1] * a[i + 1] for i in range(1, len(a) - 1))


def p_trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def p_rem(a, b):
    a = [Fraction(x) for x in a]
    b = p_trim(b)
    while len(p_trim(a)) >= len(b):
        a = p_trim(a)
        q = a[-1] / b[-1]
        s = len(a) - len(b)
        for i, c in enumerate(b):
            a[i + s] -= q * c
        a = p_trim(a)
        if not a:
            break
    return p_trim(a)


def p_deriv(p):
    return [i * p[i] for i in range(1, len(p))]


def p_gcd(a, b):
    a, b = p_trim([Fraction(x) for x in a]), p_trim([Fraction(x) for x in b])
    while b:
        a, b = b, p_rem(a, b)
    return a


def p_div(a, b):
    a = [Fraction(x) for x in a]
    b = p_trim([Fraction(x) for x in b])
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    a = list(a)
    for s in range(len(a) - len(b), -1, -1):
        c = a[s + len(b) - 1] / b[-1]
        q[s] = c
        for i, bc in enumerate(b):
            a[s + i] -= c * bc
    return p_trim(q)


def sturm_real_roots(p):
    """Number of DISTINCT real roots of p."""
    p = p_trim([Fraction(x) for x in p])
    if len(p) <= 1:
        return 0
    seq = [p, p_deriv(p)]
    while True:
        r = p_rem(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-c for c in r])

    def changes(signs):
        s = [x for x in signs if x != 0]
        return sum(1 for i in range(len(s) - 1) if s[i] * s[i + 1] < 0)
    at_pinf = [1 if q[-1] > 0 else -1 for q in seq]
    at_minf = [(1 if q[-1] > 0 else -1) * (-1) ** (len(q) - 1) for q in seq]
    return changes(at_minf) - changes(at_pinf)


def real_rooted(p):
    p = p_trim(p)
    if len(p) <= 2:
        return True
    g = p_gcd(p, p_deriv(p))
    sqf = p_div(p, g) if len(g) > 1 else p
    return sturm_real_roots(sqf) == len(sqf) - 1


def p_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def p_sub(a, b):
    L = max(len(a), len(b))
    return p_trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
                   for i in range(L)]) or [0]


# --------------------------------------------- Theorem R, brute force

def interp_at(vals, x):
    """Lagrange interpolation through (m, vals[m]), m = 0..len-1."""
    pts = list(range(len(vals)))
    tot = Fraction(0)
    for i in pts:
        term = Fraction(vals[i])
        for j in pts:
            if j != i:
                term *= Fraction(x - j, i - j)
        tot += term
    return tot


def strict_DT_count(n, down, T, m):
    comps = components(n, down)
    others = [c for c in comps if c & T != T]
    clusters = []
    for r in range(1, len(others) + 1):
        for sub in itertools.combinations(others, r):
            u = 0
            for c in sub:
                u |= c
            clusters.append(u)
    rel = [(y, x) for x in range(n) for y in range(n) if down[x] >> y & 1]
    cnt = 0
    for f in itertools.product(range(1, m + 1), repeat=n):
        if any(f[a] >= f[b] for a, b in rel):
            continue
        ok = True
        for U in clusters:
            mn = min(f[x] for x in range(n) if U >> x & 1)
            mx = max(f[x] for x in range(n) if not U >> x & 1)
            if mn >= mx:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


# ------------------------------------------------------ Stembridge's P

def stembridge_candidates():
    """EC1 2nd ed. (version of 15 July 2011), Figure 3.88: two chains
    L1 < ... < L9 (left) and R1 < ... < R8 (right), short cross edges
    R1<L2, R2<L3, R3<L4, R4<L5, R5<L6, R6<L7, R7<L9 (read off the figure),
    plus long edges from the bottom of L to the top of R whose endpoints
    are hard to read.  Enumerate the plausible long-edge sets."""
    L = list(range(9))            # L1..L9 -> 0..8
    R = list(range(9, 17))        # R1..R8 -> 9..16
    base = [(L[i], L[i + 1]) for i in range(8)]
    base += [(R[i], R[i + 1]) for i in range(7)]
    base += [(R[0], L[1]), (R[1], L[2]), (R[2], L[3]), (R[3], L[4]),
             (R[4], L[5]), (R[5], L[6]), (R[6], L[8])]
    longs = [(L[a], R[b]) for a in range(3) for b in range(5, 8)]
    for k in range(1, 5):
        for sub in itertools.combinations(longs, k):
            try:
                down = transitive_closure(17, base + list(sub))
            except ValueError:
                continue
            yield sub, down


STANLEY_AP = [0, 1, 32, 336, 1420, 2534, 1946, 658, 86, 3]  # coeff of x^k


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    ap.add_argument("--bf-nmax", type=int, default=5,
                    help="brute-force Theorem R re-check up to this n")
    ap.add_argument("--chain-max", type=int, default=30,
                    help="C_a + C_b real-rootedness scan, a, b <= this")
    args = ap.parse_args()

    by_n = all_posets(args.nmax)
    expected = [1, 1, 2, 5, 16, 63, 318, 2045, 16999]
    counts = [len(by_n[n]) for n in range(args.nmax + 1)]
    check(counts == expected[:args.nmax + 1], "posets", f"counts {counts}")

    # --- h_C, T-independence, positive controls ---
    H = {}
    tdep = 0
    conn_ok = conn_n = 0
    for n in range(1, args.nmax + 1):
        for P in by_n[n]:
            comps = components(n, P)
            ids = ideals(n, P)
            hs = {tuple(h_from_values(n, omega_c_values(n, P, T, n + 1, ids)))
                  for T in comps}
            if len(hs) != 1:
                tdep += 1
            h = list(next(iter(hs)))
            H[(n, P)] = h
            if len(comps) == 1:
                conn_n += 1
                conn_ok += (h == W_poly(n, P))
    check(tdep == 0, "T-indep", "h_C from Theorem Omega independent of T")
    check(conn_ok == conn_n, "connected=W",
          f"h_C = W_P on all {conn_n} connected posets (Stanley's h-vector)")
    eul_ok = True
    for k in range(1, args.nmax + 1):
        nA, A = antichain(k)
        eul_ok &= (h_c(nA, A) == W_poly(k - 1, antichain(k - 1)[1])
                   if k > 1 else h_c(nA, A) == [1])
    check(eul_ok, "antichain", "h_C(A_k) = Eulerian polynomial of S_{k-1}")
    known = {"C2+C2": [1, 3, 1], "A4": [1, 4, 1], "C3+C1": [1, 2],
             "C3+C3": [1, 8, 9, 1]}
    got = {"C2+C2": h_c(*disjoint_union(*chain(2), *chain(2))),
           "A4": h_c(*antichain(4)),
           "C3+C1": h_c(*disjoint_union(*chain(3), *chain(1))),
           "C3+C3": h_c(*disjoint_union(*chain(3), *chain(3)))}
    check(got == known, "small-values", f"{got}")

    # --- two-component identity h_C(Q+T) = W(Q+T) - t W(Q) W(T) ---
    two = two_ok = 0
    for (n, P), h in H.items():
        comps = components(n, P)
        if len(comps) != 2:
            continue
        two += 1
        parts = []
        for c in comps:
            idx = [x for x in range(n) if c >> x & 1]
            pos = {x: i for i, x in enumerate(idx)}
            sub = tuple(sum(1 << pos[y] for y in idx if P[x] >> y & 1)
                        for x in idx)
            parts.append(W_poly(len(idx), sub))
        pred = p_sub(W_poly(n, P), [0] + p_mul(parts[0], parts[1]))
        two_ok += (pred == h)
    check(two_ok == two, "two-comp",
          f"h_C(Q+T) = W(Q+T) - t*W(Q)*W(T) on all {two} two-component posets")

    # --- unimodality, log-concavity, real-rootedness, n <= nmax ---
    tot = len(H)
    uni = sum(unimodal(h) for h in H.values())
    lc = sum(log_concave(h) for h in H.values())
    rr_fail = [(n, P, h) for (n, P), h in H.items() if not real_rooted(h)]
    check(uni == tot, "unimodal", f"{uni}/{tot} posets n <= {args.nmax}")
    check(lc == tot, "log-concave", f"{lc}/{tot}")
    print(f"[real-rooted] {tot - len(rr_fail)}/{tot} posets n <= {args.nmax} "
          f"have real-rooted h_C")
    for n, P, h in rr_fail[:5]:
        print(f"[real-rooted]   non-real-rooted: n={n} down={P} h_C={h}")
    # positive control for the real-rootedness test: Branden's labelled
    # counterexample W(P_{36,6}) = W(36 + 6) - 1 (Electron. Res. Announc.
    # AMS 10 (2004)), and Stanley's printed A_P for Stembridge's poset.
    br = [comb(36, k) * comb(6, k) for k in range(7)]
    br[0] -= 1
    check(br[1:] == [216, 9450, 142800, 883575, 2261952, 1947792]
          and not real_rooted(br), "rr-control",
          "W(P_{36,6}) = sum C(36,k)C(6,k)t^k - 1 reproduces Branden and "
          "is detected as non-real-rooted")
    check(real_rooted([1, 4, 1]) and real_rooted([1, 26, 66, 26, 1]),
          "rr-control+", "Eulerian polynomials detected as real-rooted")

    # --- Stembridge's 17-element counterexample (EC1 Fig. 3.88) ---
    target = STANLEY_AP[1:]           # W_P = A_P / x
    matches, readings, ncand = {}, 0, 0
    for sub, down in stembridge_candidates():
        ncand += 1
        nat = naturalize(17, down)
        if W_poly(17, nat) == target:
            readings += 1
            # readings that differ only by relations implied by
            # transitivity give the same closure `down`
            matches.setdefault(down, (sub, nat))
    matches = list(matches.values())
    check(len(matches) == 1, "stembridge-W",
          f"{readings} of {ncand} long-edge readings of EC1 Fig. 3.88 "
          f"reproduce Stanley's printed A_P(x); they give {len(matches)} "
          "distinct poset(s) (the rest differ by implied relations)")
    for mi, (sub, S) in enumerate(matches):
        tag = f"stembridge{mi}"
        print(f"[{tag}] long edges (L_a < R_b, 0-based L=0..8, R=9..16): {sub}")
        WS = W_poly(17, S)
        check(not real_rooted(WS) and unimodal(WS) and log_concave(WS),
              f"{tag}-props",
              "W_S not real-rooted (control), but unimodal and log-concave")
        hS = h_c(17, S)
        check(hS == WS, f"{tag}-hC", "connected, so h_C(S) = W_S")
        extras = [("C1", chain(1)), ("C2", chain(2)), ("C3", chain(3)),
                  ("A2", antichain(2)), ("C2+C1",
                                          disjoint_union(*chain(2), *chain(1)))]
        for name, (k, X) in extras:
            n2, P2 = disjoint_union(17, S, k, X)
            comps = components(n2, P2)
            ids = ideals_any(n2, P2)
            hs = {tuple(h_from_values(n2, omega_c_values(n2, P2, T, n2 + 1, ids)))
                  for T in comps}
            h = list(next(iter(hs)))
            print(f"[{tag}+{name}] h_C = {h}  T-indep={len(hs) == 1} "
                  f"unimodal={unimodal(h)} log-concave={log_concave(h)} "
                  f"real-rooted={real_rooted(h)}")
            if not (len(hs) == 1 and unimodal(h) and log_concave(h)):
                FAILS.append(f"{tag}+{name}")
        n2, P2 = disjoint_union(17, S, *chain(2))
        pred = p_sub(W_poly(n2, naturalize(n2, P2)), [0] + p_mul(WS, [1]))
        check(pred == h_c(n2, P2), f"{tag}+C2-identity",
              "h_C(S + C2) = W(S + C2) - t W_S")

    # --- the family C_a + C_b: h_C = sum C(a,k)C(b,k) t^k - t ---
    fam_ok = True
    for a in range(1, 7):
        for b in range(1, 7):
            nn, PP = disjoint_union(*chain(a), *chain(b))
            pred = [comb(a, k) * comb(b, k) for k in range(min(a, b) + 1)]
            pred[1] -= 1
            fam_ok &= (h_c(nn, PP) == p_trim(pred))
    check(fam_ok, "chains-formula",
          "h_C(C_a + C_b) = sum_k C(a,k)C(b,k) t^k - t for a, b <= 6")
    bad = []
    for a in range(1, args.chain_max + 1):
        for b in range(a, args.chain_max + 1):
            p = [comb(a, k) * comb(b, k) for k in range(a + 1)]
            p[1] -= 1
            if not real_rooted(p):
                bad.append((a, b))
    print(f"[chains-rr] C_a + C_b, 1 <= a <= b <= {args.chain_max}: "
          f"{len(bad)} pairs with non-real-rooted h_C; first: {bad[:6]}")

    # --- Theorem R re-checked by brute force, no words ---
    rc = rc_ok = 0
    for n in range(1, args.bf_nmax + 1):
        for P in by_n[n]:
            for T in components(n, P):
                vals = omega_c_values(n, P, T, n + 1)
                for m in range(1, n + 2):
                    rc += 1
                    lhs = (-1) ** n * interp_at(vals, -m)
                    rc_ok += (lhs == strict_DT_count(n, P, T, m))
    check(rc_ok == rc, "recip-bf",
          f"(-1)^n Omega_C(-m) = #strict maps with D_T: {rc_ok}/{rc} "
          f"(P, T, m), n <= {args.bf_nmax}, m <= n+1")
    # control: strict maps with the NON-strict anchoring (> kept)
    naive_bad = 0
    for n in range(2, min(args.bf_nmax, 4) + 1):
        for P in by_n[n]:
            comps = components(n, P)
            if len(comps) < 2:
                continue
            T = comps[0]
            vals = omega_c_values(n, P, T, n + 1)
            for m in range(1, n + 2):
                lhs = (-1) ** n * interp_at(vals, -m)
                others = [c for c in comps if c != T]
                cnt = 0
                rel = [(y, x) for x in range(n) for y in range(n)
                       if P[x] >> y & 1]
                for f in itertools.product(range(1, m + 1), repeat=n):
                    if any(f[a] >= f[b] for a, b in rel):
                        continue
                    ok = True
                    for r in range(1, len(others) + 1):
                        for sub in itertools.combinations(others, r):
                            U = 0
                            for c in sub:
                                U |= c
                            mn = min(f[x] for x in range(n) if U >> x & 1)
                            mx = max(f[x] for x in range(n) if not U >> x & 1)
                            if mn > mx:
                                ok = False
                    cnt += ok
                if cnt != lhs:
                    naive_bad += 1
                    break
    control(naive_bad, "ctl-naive", "posets: strict maps with > anchoring "
            "do not give (-1)^n Omega_C(-m)")

    print(f"[summary] {'ALL PASS' if not FAILS else 'FAILED: ' + ', '.join(FAILS)}")
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
