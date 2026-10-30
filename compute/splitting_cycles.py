#!/usr/bin/env python3
"""Splitting cycles, shuffles and the restricted JKS image (mg-92751).

Companion to notes/literature_novelty_jks_maps.md.  Plain Python 3, no
dependencies; reuses poset helpers from poset_jks_check.py.

Conventions are those of poset_jks_check.py (0-based):
  * a word / permutation w is a tuple, w[i] = letter in position i;
    (p*q)[i] = p[q[i]].  Left multiplication relabels letters, right
    multiplication permutes positions; gamma[i] = i+1 mod n, so w*gamma
    rotates the word left.
  * For a word w, the splitting sphere Pi_w (Wachs, Poset Topology Thm 3.2.8;
    Wachs 1998 Prop. 2.3) consists of the partitions obtained by cutting w
    at a set of positions.  rho_w is its fundamental cycle, oriented so that
    the chain m_w (split off w_1, then w_2, ...) has coefficient +1.  A top
    chain of the proper part of Pi_n is stored as the tuple of its partitions
    listed coarse -> fine.
  * Sh_n = span of proper shuffles u ш v (u, v nonempty, complementary
    letter sets).  By Ree's theorem Sh_n is the orthogonal complement of
    Lie_n in C[S_n] for the form <u, v> = delta_{u,v}.
  * r_tau = [tau_1, [tau_2, [ ..., tau_n]]] (right comb).  {r_tau : tau(n)=n}
    is a basis of Lie_n (Wachs 1998, Sec. 4).  The map
    sigma -> (coefficient of sigma in r_tau)_tau  has kernel exactly Sh_n.

Exact integer arithmetic is used for every "= 0" claim; ranks are computed
modulo a large prime p.  rank_p <= rank_Q always; every rank conclusion
below is drawn in the direction where that inequality makes it rigorous
(see the notes file).

Run:  python3 splitting_cycles.py [--nmax 5] [--nmax-comb 6]
"""

import argparse
import itertools
import sys
from collections import defaultdict
from math import factorial

import poset_jks_check as pj

P = 1_000_000_021  # prime; also check with P2
P2 = 998_244_353


# ---------------------------------------------------------------------------
# Linear algebra mod p


def rank_mod_p(rows, p=P):
    """Rank of a list of sparse rows (dict col -> int) modulo p."""
    pivots = {}  # col -> reduced row (dict), row has leading entry 1 at col
    rank = 0
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
                rank += 1
                break
    return rank


def keyed(rows):
    """Turn rows keyed by arbitrary hashables into rows keyed by ints."""
    index = {}
    out = []
    for r in rows:
        out.append({index.setdefault(k, len(index)): v for k, v in r.items()})
    return out


# ---------------------------------------------------------------------------
# Splitting cycles


def split_partition(w, cuts):
    """Partition of [n] obtained by cutting the word w after the positions in
    `cuts` (a set of integers in 1..n-1)."""
    blocks, start = [], 0
    for c in sorted(cuts) + [len(w)]:
        blocks.append(frozenset(w[start:c]))
        start = c
    return frozenset(blocks)


def rho(w):
    """Fundamental cycle of the splitting sphere of w, as dict chain -> coef.
    Sum over orders tau of the n-1 cut positions of sgn(tau) * chain, where
    the chain is cuts {tau_1}, {tau_1, tau_2}, ... (coarse -> fine)."""
    n = len(w)
    out = {}
    for tau in itertools.permutations(range(1, n)):
        chain = tuple(split_partition(w, set(tau[:k])) for k in range(1, n - 1))
        s = pj.sign(tuple(t - 1 for t in tau))
        out[chain] = out.get(chain, 0) + s
    # orientation: m_w = cuts 1, 2, ..., n-1 in that order has tau = id, sign +1
    return {c: v for c, v in out.items() if v}


def boundary(cyc):
    out = defaultdict(int)
    for chain, a in cyc.items():
        for i in range(len(chain)):
            out[chain[:i] + chain[i + 1:]] += (-1) ** i * a
    return {c: v for c, v in out.items() if v}


def add_scaled(acc, vec, s):
    for k, v in vec.items():
        acc[k] = acc.get(k, 0) + s * v
    return acc


# ---------------------------------------------------------------------------
# Shuffles, right combs


def shuffles(u, v):
    if not u:
        yield v
        return
    if not v:
        yield u
        return
    for s in shuffles(u[1:], v):
        yield (u[0],) + s
    for s in shuffles(u, v[1:]):
        yield (v[0],) + s


def proper_shuffle_elements(n):
    """All u ш v (as dict word -> coef) with u, v nonempty, complementary."""
    out = []
    for k in range(1, n):
        for U in itertools.combinations(range(n), k):
            V = [x for x in range(n) if x not in U]
            for u in itertools.permutations(U):
                for v in itertools.permutations(V):
                    d = defaultdict(int)
                    for s in shuffles(u, v):
                        d[s] += 1
                    out.append(dict(d))
    return out


def bracket(a, b):
    out = defaultdict(int)
    for x, cx in a.items():
        for y, cy in b.items():
            out[x + y] += cx * cy
            out[y + x] -= cx * cy
    return {k: v for k, v in out.items() if v}


def right_comb(tau):
    e = {(tau[-1],): 1}
    for x in reversed(tau[:-1]):
        e = bracket({(x,): 1}, e)
    return e


def comb_coordinates(n):
    """sigma -> {tau-index: coefficient of sigma in r_tau}, tau(n) = n."""
    taus = [t + (n - 1,) for t in itertools.permutations(range(n - 1))]
    coords = defaultdict(dict)
    for j, tau in enumerate(taus):
        for sigma, c in right_comb(tau).items():
            coords[sigma][j] = c
    return coords


# ---------------------------------------------------------------------------
# Group algebra mod p (for e_zeta and Klyachko's idempotent)


def mul(a, b, p):
    out = defaultdict(int)
    for x, cx in a.items():
        for y, cy in b.items():
            z = pj.compose(x, y)
            out[z] = (out[z] + cx * cy) % p
    return {k: v for k, v in out.items() if v}


def scal(a, s, p):
    return {k: v * s % p for k, v in a.items() if v * s % p}


def root_of_unity(n, p):
    assert (p - 1) % n == 0
    for a in range(2, 10_000):
        z = pow(a, (p - 1) // n, p)
        if all(pow(z, n // q, p) != 1 for q in range(2, n + 1) if n % q == 0 and all(q % r for r in range(2, q))):
            return z
    raise ValueError


def prime_1_mod(m, start=10**9):
    q = start - start % m + 1
    while True:
        if q > 2 and all(q % d for d in range(2, int(q ** 0.5) + 1)):
            return q
        q += m


def maj(w):
    return sum(i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def e_zeta(n, z, p):
    gamma = tuple((i + 1) % n for i in range(n))
    inv_n = pow(n, p - 2, p)
    out, g = {}, tuple(range(n))
    zinv = pow(z, p - 2, p)
    for j in range(n):
        out[g] = pow(zinv, j, p) * inv_n % p
        g = pj.compose(g, gamma)
    return out


def klyachko(n, z, p, use_inverse):
    inv_n = pow(n, p - 2, p)
    out = {}
    for s in itertools.permutations(range(n)):
        m = maj(pj.inverse(s)) if use_inverse else maj(s)
        out[s] = pow(z, m, p) * inv_n % p
    return out


def dynkin_left(n):
    """theta_n = [[...[1,2],3],...,n] as a group-algebra element (integers)."""
    e = {(0,): 1}
    for x in range(1, n):
        e = bracket(e, {(x,): 1})
    return e


def proportional(a, b, p):
    keys = sorted(set(a) | set(b))
    for i, k in enumerate(keys):
        for l in keys[i + 1:]:
            if (a.get(k, 0) * b.get(l, 0) - a.get(l, 0) * b.get(k, 0)) % p:
                return False
    return True


# ---------------------------------------------------------------------------
# Poset side


def top_homology_dim(rel, n):
    """dim of top reduced homology of the proper part of OP(P), as
    (#maximal chains) - rank(boundary), mod p.  Returns (dim, chains)."""
    ops = pj.order_preserving_partitions(rel, n)
    by_size = defaultdict(list)
    for x in ops:
        by_size[len(x)].append(x)
    # chains coarse -> fine through block counts 2, 3, ..., n-1
    chains = [(x,) for x in by_size[2]]
    for k in range(3, n):
        chains = [c + (y,) for c in chains for y in by_size[k] if pj.refines(y, c[-1])]
    if n == 3:
        chains = [(x,) for x in by_size[2]]
    rows = keyed([boundary({c: 1}) for c in chains]) if n > 3 else []
    if n == 3:  # reduced H_0: augmentation
        return len(chains) - 1, chains
    return len(chains) - rank_mod_p(rows), chains


def splitting_partitions_order_preserving(w, rel):
    n = len(w)
    for k in range(n):
        for cuts in itertools.combinations(range(1, n), k):
            pi = split_partition(w, set(cuts))
            rgs = [0] * n
            for b, B in enumerate(pi):
                for x in B:
                    rgs[x] = b
            if not pj.is_order_preserving(tuple(rgs), rel):
                return False
    return True


def opposite(rel):
    return frozenset((b, a) for a, b in rel)


# ---------------------------------------------------------------------------


def check_partition_lattice(n, out):
    perms = list(itertools.permutations(range(n)))
    rhos = {w: rho(w) for w in perms}
    assert all(not boundary(r) for r in rhos.values()) if n > 3 else True
    # equivariance g.rho_w = rho_{gw}
    for g in perms[:: max(1, len(perms) // 7)]:
        for w in perms[:: max(1, len(perms) // 11)]:
            moved = {tuple(frozenset(frozenset(g[i] for i in B) for B in x) for x in c): v
                     for c, v in rhos[w].items()}
            assert moved == rhos[pj.compose(g, w)]
    # Phi well defined: every proper shuffle u ш v maps to 0 under
    # sigma -> sgn(sigma) rho_sigma (exact integer check)
    sh = proper_shuffle_elements(n)
    for s in sh:
        acc = {}
        for w, c in s.items():
            add_scaled(acc, rhos[w], c * pj.sign(w))
        assert not {k: v for k, v in acc.items() if v}, s
    rk_rho = rank_mod_p(keyed(list(rhos.values())))
    rk_sh = rank_mod_p(keyed(sh))
    out.append(f"n={n}: {len(sh)} proper shuffles each satisfy sum sgn(w) rho_w = 0 (exact); "
               f"rank rho = {rk_rho} = (n-1)! = {factorial(n-1)}: {rk_rho == factorial(n-1)}; "
               f"rank Sh = {rk_sh} = n!-(n-1)! = {factorial(n)-factorial(n-1)}: "
               f"{rk_sh == factorial(n) - factorial(n-1)}")
    ok = rk_rho == factorial(n - 1) and rk_sh == factorial(n) - factorial(n - 1)
    # comb coordinates: kernel is Sh as well
    coords = comb_coordinates(n)
    for s in sh:
        acc = defaultdict(int)
        for w, c in s.items():
            for j, v in coords.get(w, {}).items():
                acc[j] += c * v
        assert not any(acc.values())
    rk_c = rank_mod_p([dict(coords.get(w, {})) for w in perms])
    ok &= rk_c == factorial(n - 1)
    out.append(f"n={n}: comb coordinates kill every proper shuffle (exact); rank = {rk_c}")
    return ok, rhos


def check_lie_realizations(n, out):
    """e_zeta and Klyachko's idempotent vs the chain / dual-chain pair and Sh."""
    p = prime_1_mod(60)
    z = root_of_unity(n, p)
    ident = tuple(range(n))
    w0 = tuple(reversed(ident))
    ez = e_zeta(n, z, p)
    assert mul(ez, ez, p) == ez
    lines = []
    # chain 0<1<...<n-1 and its dual have the same OP lattice, Lin = {id}, {w0}
    lines.append(f"n={n}: id*e_zeta proportional to w0*e_zeta: {proportional(ez, mul({w0: 1}, ez, p), p)}")
    sh = proper_shuffle_elements(n)
    sh_ez_zero = all(not mul(s, ez, p) for s in sh)
    lines.append(f"n={n}: Sh * e_zeta == 0: {sh_ez_zero}")
    # adjoint Dynkin element theta_n^* = sum c_tau tau^{-1}: right
    # multiplication by it is the adjoint of the Dynkin operator, so its kernel
    # should be Lie_n^perp = Sh_n (exact integer check + rank).
    theta_star = {pj.inverse(t): c for t, c in dynkin_left(n).items()}
    sh_ts_zero = all(not mul(s, theta_star, 1 << 61) for s in sh)
    rk_ts = rank_mod_p(keyed([mul({w: 1}, theta_star, P) for w in itertools.permutations(range(n))]))
    lines.append(f"n={n}: Sh * theta_n^* == 0 (exact): {sh_ts_zero}; "
                 f"rank C[S_n] theta_n^* = {rk_ts} (= (n-1)!: {rk_ts == factorial(n - 1)})")
    theta = {k: v % p for k, v in dynkin_left(n).items()}
    for use_inv in (False, True):
        k = klyachko(n, z, p, use_inv)
        idem = mul(k, k, p) == k
        in_lie = mul(k, theta, p) == scal(k, n, p)
        if idem and in_lie:
            lines.append(f"n={n}: Klyachko kappa (maj of {'inverse' if use_inv else 'word'}) "
                         f"is an idempotent in Lie_n")
            lines.append(f"n={n}: id*kappa proportional to w0*kappa: "
                         f"{proportional(k, mul({w0: 1}, k, p), p)}")
            lines.append(f"n={n}: Sh * kappa == 0: {all(not mul(s, k, p) for s in sh)}")
            out.extend(lines)
            return ez, k, p
    out.extend(lines)
    out.append(f"n={n}: no Klyachko convention passed the idempotent/Lie test")
    return ez, None, p


def check_posets(n, out, rhos=None, realizations=None, opposite_pairs=True):
    posets = pj.unlabeled_posets_by_extension(n)[n]
    coords = comb_coordinates(n)
    bad = []
    stats = defaultdict(int)
    for rel in posets:
        lin = pj.linear_extensions(rel, n)
        ec = len(pj.cyclic_classes(lin))
        conn = pj.is_connected(rel, n)
        assert all(splitting_partitions_order_preserving(w, rel) for w in lin)
        d_comb = rank_mod_p([dict(coords.get(w, {})) for w in lin])
        rec = {"ec": ec, "lin": len(lin), "d_comb": d_comb, "conn": conn}
        if rhos is not None:
            rec["d_rho"] = rank_mod_p(keyed([rhos[w] for w in lin]))
            rec["dimH"], _ = top_homology_dim(rel, n)
        if realizations is not None:
            ez, k, p = realizations
            rec["d_ez"] = rank_mod_p(keyed([mul({w: 1}, ez, p) for w in lin]), p)
            if k is not None:
                rec["d_kappa"] = rank_mod_p(keyed([mul({w: 1}, k, p) for w in lin]), p)
            if opposite_pairs:
                lin_op = pj.linear_extensions(opposite(rel), n)
                a = keyed([mul({w: 1}, ez, p) for w in lin] + [mul({w: 1}, ez, p) for w in lin_op])
                rec["ez_same_as_dual"] = rank_mod_p(a, p) == rec["d_ez"]
        stats["posets"] += 1
        stats["connected"] += conn
        if d_comb != ec:
            bad.append(("d_comb != e_C", sorted(rel), rec))
        if rhos is not None and not (rec["d_rho"] == ec == rec["dimH"]):
            bad.append(("rho/dimH mismatch", sorted(rel), rec))
        if realizations is not None:
            if rec["d_ez"] != ec:
                bad.append(("dim W_P e_zeta != e_C", sorted(rel), rec))
            if "d_kappa" in rec:
                stats["kappa_dim_ok"] += rec["d_kappa"] == ec
            if opposite_pairs:
                stats["W_P e_zeta == W_Pop e_zeta"] += rec["ez_same_as_dual"]
    out.append(f"n={n}: {stats['posets']} unlabeled posets ({stats['connected']} connected); "
               f"dim span{{rho_w : w in Lin(P)}} == e_C(P) for all: {not any(b[0] == 'd_comb != e_C' for b in bad)}"
               + ("" if rhos is None else
                  f"; direct rho rank == e_C == dim H_P (direct homology) for all: "
                  f"{not any(b[0] == 'rho/dimH mismatch' for b in bad)}"))
    if realizations is not None:
        out.append(f"n={n}: dim W_P e_zeta == e_C for all: {not any(b[0].startswith('dim W_P e') for b in bad)}; "
                   f"dim W_P kappa == e_C for {stats['kappa_dim_ok']}/{stats['posets']}; "
                   f"W_P e_zeta == W_(P^op) e_zeta for {stats['W_P e_zeta == W_Pop e_zeta']}/{stats['posets']}")
    for b in bad[:10]:
        out.append(f"  MISMATCH {b}")
    return not bad


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--nmax", type=int, default=5, help="direct chain-level checks up to this n (default 5)")
    ap.add_argument("--nmax-comb", type=int, default=6,
                    help="span check via comb coordinates up to this n (default 6)")
    a = ap.parse_args(argv)
    out = []
    ok = True
    for n in range(3, max(a.nmax, a.nmax_comb) + 1):
        if n <= a.nmax:
            good, rhos = check_partition_lattice(n, out)
            ok &= good
            real = check_lie_realizations(n, out)
            ok &= check_posets(n, out, rhos=rhos, realizations=real)
        else:
            ok &= check_posets(n, out)
        print("\n".join(out), flush=True)
        out.clear()
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
