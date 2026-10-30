#!/usr/bin/env python3
"""Second-read check of the unconditional half of (globalind):

    (+)_{P on [n]} Lie(P)  ~=  Ind_{C_n}^{S_n}(zeta (x) C[B_n])   as S_n-modules,

where Lie(P) = span{ w e_zeta : w in LinExt(P) } inside C[S_n] (seed note,
eq. posetLie) and S_n acts by left multiplication, sending Lie(P) to Lie(tau P).

This deliberately does NOT use the monomial-basis argument being checked
(notes/audit_cyclic_compatible_posets_bn.md, section A). The left side is
computed by plain linear algebra in C[S_n]: for each tau and each tau-fixed P,
row-reduce the spanning set {w e_zeta}, check that the span is tau-stable, and
take the trace of tau on it. The right side is the Frobenius formula
    chi(tau) = (1/n) sum_{g in S_n, g^-1 tau g in C_n} psi(g^-1 tau g),
    psi(gamma^j) = zeta^j * #{P in B_n : gamma^j P = P},
with B_n built straight from its definition (some L_c is a linear extension).

Two positive controls must FAIL: zeta replaced by the trivial character, and
B_n replaced by the set of all labeled posets.

Usage: python3 second_read_globalind.py [NMAX]   (default 5; ~1 min at 5)
Exit status 0 iff the identity holds for 2 <= n <= NMAX and both controls fail
for 3 <= n <= NMAX (at n = 2 every poset is in B_2).
"""
import cmath
import sys
from itertools import permutations

EPS = 1e-9


def posets(n):
    """All labeled posets on {0..n-1}, as frozensets of pairs (a, b) = a < b."""
    if n == 0:
        return [frozenset()]
    out = []
    m = n - 1
    for P in posets(m):
        below = {x: {a for (a, b) in P if b == x} for x in range(m)}
        above = {x: {b for (a, b) in P if a == x} for x in range(m)}
        subsets = [frozenset(x for x in range(m) if mask >> x & 1) for mask in range(1 << m)]
        ideals = [D for D in subsets if all(below[x] <= D for x in D)]
        filters = [U for U in subsets if all(above[x] <= U for x in U)]
        for D in ideals:
            for U in filters:
                if D & U or any((d, u) not in P for d in D for u in U):
                    continue
                out.append(P | {(d, m) for d in D} | {(m, u) for u in U})
    return out


def compose(p, q):  # (p q)(i) = p(q(i)); permutations as tuples i -> p[i]
    return tuple(p[i] for i in q)


def inverse(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def relabel(t, P):
    return frozenset((t[a], t[b]) for (a, b) in P)


def is_ext(w, P):
    """Word w = (w_0..w_{n-1}) is a linear extension of P."""
    pos = inverse(w)
    return all(pos[a] < pos[b] for (a, b) in P)


def rref(vectors, dim):
    """Reduced row echelon basis of span(vectors); returns list of (pivot, row)."""
    rows = []
    for v in vectors:
        v = list(v)
        for p, r in rows:
            c = v[p]
            if abs(c) > EPS:
                v = [x - c * y for x, y in zip(v, r)]
        piv = next((i for i in range(dim) if abs(v[i]) > EPS), None)
        if piv is None:
            continue
        c = v[piv]
        v = [x / c for x in v]
        new_rows = []
        for p, r in rows:
            d = r[piv]
            new_rows.append((p, [x - d * y for x, y in zip(r, v)] if abs(d) > EPS else r))
        rows = new_rows + [(piv, v)]
    return rows


def check(n):
    perms = list(permutations(range(n)))
    idx = {p: i for i, p in enumerate(perms)}
    N = len(perms)
    gamma = tuple((i + 1) % n for i in range(n))  # i -> i+1, the n-cycle (1 2 .. n)
    gpow = [tuple(range(n))]
    for _ in range(n - 1):
        gpow.append(compose(gamma, gpow[-1]))
    zeta = cmath.exp(2j * cmath.pi / n)
    Ps = posets(n)

    def w_ezeta(w):
        v = [0j] * N
        for j in range(n):
            v[idx[compose(w, gpow[j])]] += zeta ** (-j) / n
        return v

    def left(t, v):
        out = [0j] * N
        for i, c in enumerate(v):
            if c != 0:
                out[idx[compose(t, perms[i])]] = c
        return out

    ext = {P: [w for w in perms if is_ext(w, P)] for P in Ps}
    Bn = [P for P in Ps if any(is_ext(gpow[c], P) for c in range(n))]

    # one representative per cycle type
    reps = {}
    for t in perms:
        seen, lam = set(), []
        for i in range(n):
            if i not in seen:
                k, x = 0, i
                while x not in seen:
                    seen.add(x)
                    x = t[x]
                    k += 1
                lam.append(k)
        reps.setdefault(tuple(sorted(lam, reverse=True)), t)

    lhs = {}
    for lam, t in reps.items():
        tr = 0j
        for P in Ps:
            if relabel(t, P) != P:
                continue  # summand is moved to a different summand: no trace
            rows = rref([w_ezeta(w) for w in ext[P]], N)
            for p, r in rows:
                tv = left(t, r)
                # tau-stability: tv must equal its expansion in the RREF basis
                resid = list(tv)
                for q, s in rows:
                    c = tv[q]
                    if abs(c) > EPS:
                        resid = [x - c * y for x, y in zip(resid, s)]
                assert max(abs(x) for x in resid) < 1e-7, "Lie(P) not tau-stable"
                tr += tv[p]
        lhs[lam] = tr

    def induced(fibre, char):
        fix = [sum(1 for P in fibre if relabel(gpow[j], P) == P) for j in range(n)]
        cpos = {g: j for j, g in enumerate(gpow)}
        res = {}
        for lam, t in reps.items():
            s = 0j
            for g in perms:
                c = compose(inverse(g), compose(t, g))
                if c in cpos:
                    j = cpos[c]
                    s += char ** j * fix[j]
            res[lam] = s / n
        return res

    def agree(a, b):
        return all(abs(a[k] - b[k]) < 1e-6 for k in a)

    rhs = induced(Bn, zeta)
    ok = agree(lhs, rhs)
    ctrl_trivial = agree(lhs, induced(Bn, 1))
    ctrl_allposets = agree(lhs, induced(Ps, zeta))
    print(f"n={n}: #posets={len(Ps)} b_n={len(Bn)}")
    for lam in sorted(reps, reverse=True):
        print(f"   {lam}: direct trace {lhs[lam].real:+.6f}{lhs[lam].imag:+.6f}i"
              f"   Ind {rhs[lam].real:+.6f}{rhs[lam].imag:+.6f}i")
    print(f"   identity holds: {ok}; control zeta->1 agrees: {ctrl_trivial};"
          f" control B_n->all posets agrees: {ctrl_allposets}")
    if n < 3:  # B_2 is every poset on [2], so the second control cannot fail
        return ok
    return ok and not ctrl_trivial and not ctrl_allposets


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    good = True
    for n in range(2, nmax + 1):  # n = 1: zeta = 1 and C_1 trivial, controls cannot fail
        good &= check(n)
    print("ALL CHECKS PASSED" if good else "CHECK FAILED")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
