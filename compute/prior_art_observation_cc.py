"""Checks for notes/prior_art_observation_cc.md (standalone, plain Python 3).

For every cycle type of sigma in S_n, n <= NMAX, build the fixed lattice
L = Pi_n^sigma and check:

  [H4]  the meet x_sigma of the coatoms of L equals the orbit partition of
        sigma^r, r = rad(gcd of the cycle lengths)   (Hanlon 1981, Lemma 2 and
        the proof of Lemma 4; this is Lemma CK of observation_cc.md for
        kappa = 0-hat);
  [S71] mu_L(0,1) = 0  iff  x_sigma != 0-hat         (Stanley 1982, Lemma 7.1
        and the Remark after it, combined with H4);
  [LIT] Stanley's literal wording "x_sigma = 0-hat iff all cycles of sigma
        have the same length": reported, with the cycle types where it fails.

Usage:  python3 prior_art_observation_cc.py [--nmax N]
Exit 0 and "ALL CHECKS PASSED" iff H4 and S71 hold on every cycle type and
the positive controls fire.
"""
import argparse
import math
import sys


def set_partitions(n):
    """All set partitions of range(n), as tuples of block labels (RGS)."""
    def rec(i, labels, k):
        if i == n:
            yield tuple(labels)
            return
        for b in range(k + 1):
            labels.append(b)
            yield from rec(i + 1, labels, max(k, b + 1))
            labels.pop()
    yield from rec(0, [], 0)


def normalize(labels):
    seen, out = {}, []
    for x in labels:
        if x not in seen:
            seen[x] = len(seen)
        out.append(seen[x])
    return tuple(out)


def leq(a, b):
    """a refines b."""
    m = {}
    for x, y in zip(a, b):
        if m.setdefault(x, y) != y:
            return False
    return True


def meet(a, b):
    return normalize(list(zip(a, b)))


def perm_from_type(lam):
    sigma, start = [], 0
    for l in lam:
        for i in range(l):
            sigma.append(start + (i + 1) % l)
        start += l
    return sigma


def act(sigma, p):
    """Partition sigma(p): i ~ j in sigma(p) iff sigma^-1 i ~ sigma^-1 j."""
    n = len(p)
    inv = [0] * n
    for i, s in enumerate(sigma):
        inv[s] = i
    return normalize([p[inv[i]] for i in range(n)])


def orbit_partition(sigma, k):
    n = len(sigma)
    lab = [-1] * n
    c = 0
    for i in range(n):
        if lab[i] < 0:
            j = i
            while lab[j] < 0:
                lab[j] = c
                for _ in range(k):
                    j = sigma[j]
            c += 1
    return normalize(lab)


def rad(m):
    r, p = 1, 2
    while m > 1:
        if m % p == 0:
            r *= p
            while m % p == 0:
                m //= p
        p += 1
    return r


def int_partitions(n, mx=None):
    mx = n if mx is None else mx
    if n == 0:
        yield ()
        return
    for k in range(min(n, mx), 0, -1):
        for rest in int_partitions(n - k, k):
            yield (k,) + rest


def analyse(lam):
    n = sum(lam)
    sigma = perm_from_type(lam)
    L = [p for p in set_partitions(n) if act(sigma, p) == p]
    bot, top = tuple(range(n)), tuple([0] * n)
    # Mobius mu(bot, x) by recursion over a linear extension (fewer blocks later).
    L.sort(key=lambda p: -len(set(p)))
    mu = {}
    for x in L:
        mu[x] = 1 if x == bot else -sum(mu[y] for y in mu if y != x and leq(y, x))
    coatoms = [x for x in L if x != top and
               not any(z != x and z != top and leq(x, z) for z in L)]
    xs = top
    for c in coatoms:
        xs = meet(xs, c)
    r = rad(math.gcd(*lam))
    return {"mu": mu[top], "x": xs, "bot": bot,
            "orb": orbit_partition(sigma, r), "size": len(L)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=7)
    a = ap.parse_args()
    ok = True

    # Positive controls: the instruments must fire on known cases.
    c1 = analyse((4,))            # Pi_4^{(1234)}: 3-element chain, mu = 0
    c2 = analyse((1, 1, 1, 1))    # Pi_4: mu = -6
    ctl = (c1["size"] == 3 and c1["mu"] == 0 and c1["x"] != c1["bot"]
           and c2["mu"] == -6 and c2["x"] == c2["bot"])
    print("[CTL] Pi_4^(1234): |L|=%d mu=%d x!=0:%s ; Pi_4: mu=%d x==0:%s -> %s"
          % (c1["size"], c1["mu"], c1["x"] != c1["bot"], c2["mu"],
             c2["x"] == c2["bot"], "ok" if ctl else "FAIL"))
    ok &= ctl

    # Injected fault: with r replaced by 1 (orbit partition = cycle partition),
    # H4 must fail somewhere, or the H4 comparison cannot fire.
    fault = 0
    for n in range(1, a.nmax + 1):
        for lam in int_partitions(n):
            d = analyse(lam)
            if d["x"] != orbit_partition(perm_from_type(lam), 1):
                fault += 1
    print("[CTL] H4 with r := 1 fails on %d cycle types (must be > 0) -> %s"
          % (fault, "ok" if fault else "FAIL"))
    ok &= fault > 0

    lit_fail = []
    print("n  types  H4-fail  S71-fail  literal-Remark-fail")
    for n in range(1, a.nmax + 1):
        types = list(int_partitions(n))
        h4 = s71 = lit = 0
        for lam in types:
            d = analyse(lam)
            xzero = d["x"] == d["bot"]
            if d["x"] != d["orb"]:
                h4 += 1
            if (d["mu"] == 0) != (not xzero):
                s71 += 1
            if xzero != (len(set(lam)) == 1):
                lit += 1
                lit_fail.append(lam)
        print("%d  %5d  %7d  %8d  %d" % (n, len(types), h4, s71, lit))
        ok &= h4 == 0 and s71 == 0
    print("[LIT] cycle types where 'x = 0-hat iff all cycles have one length' "
          "fails:", lit_fail)
    # Every literal failure should be an equal-length type with a
    # non-squarefree length (Hanlon's j is the squarefree part).
    lit_ok = all(len(set(l)) == 1 and rad(l[0]) != l[0] for l in lit_fail) \
        and (4,) in lit_fail
    print("[LIT] all failures are equal lengths, non-squarefree:",
          "ok" if lit_ok else "FAIL")
    ok &= lit_ok
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
