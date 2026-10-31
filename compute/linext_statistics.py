#!/usr/bin/env python3
"""Which identities on linear-extension statistics does the machinery give?

Companion to ../notes/linext_statistics.md.  Each line prints PASS/FAIL with
a bracketed tag used in the note.  Lines marked CONTROL are deliberately
wrong variants that must FAIL somewhere; the script exits 0 iff every claim
holds and every control fails.

Sections:
  faces    face numbers of C_P = surjective P-partitions; order polynomial
           and descent expansion (Stanley; machinery: Lemma F bijection).
  omegaC   Theorem Omega: sum_pi |mu(pi,1)| C(m,|pi|) counts P-partitions
           whose upper component-union level sets all contain a fixed
           component T; its descent expansion (all natural labellings for
           small n).
  chi      the bottom-up characteristic polynomial of OP(P) at t = -1 is NOT
           e(P); the lineality-restricted sum is (Prop. Z).
  maj      maj mod n: rotation lemma; equidistribution on disconnected P with
           gcd of component sizes 1; Kraskiewicz-Weyman-type hypotheses.
  sign     sign-imbalance: disjoint-union factorisation at q = -1, and the
           hypotheses |I(P)| = e_C(P), |I(P)| = |I(B_P)|.

Run from compute/:

    python3 linext_statistics.py --nmax 7 --lmax 5 > output/linext_statistics.txt

Plain Python 3, no dependencies.  Budget: one core.
"""

import argparse
import itertools
import sys
from collections import Counter
from math import comb as _comb, gcd

import n7_sweep
import linear_extensions as LE
import mu_op_elementary as ME

FAILS = []


def comb(a, b):
    """Counting binomial: 0 when a < 0 or b < 0."""
    return _comb(a, b) if a >= 0 and b >= 0 else 0


def check(ok, label):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        FAILS.append(label)


def control(failures, label):
    """A control is a claim that must be refuted somewhere."""
    ok = failures > 0
    print(("PASS " if ok else "FAIL ") + "CONTROL " + label
          + f" (refuted on {failures} cases)")
    if not ok:
        FAILS.append("CONTROL " + label)


def des(w):
    return sum(1 for i in range(len(w) - 1) if w[i] > w[i + 1])


def desset(w):
    return {i + 1 for i in range(len(w) - 1) if w[i] > w[i + 1]}


def maj(w):
    return sum(desset(w))


def cdes(w):
    return des(w) + (1 if w[-1] > w[0] else 0)


def sgn(w):
    s = 1
    for i in range(len(w)):
        for j in range(i + 1, len(w)):
            if w[i] > w[j]:
                s = -s
    return s


def natural_labellings(rel0, n):
    seen = set()
    for perm in itertools.permutations(range(n)):
        rel = frozenset((perm[a], perm[b]) for a, b in rel0)
        if all(a < b for a, b in rel) and rel not in seen:
            seen.add(rel)
            yield rel


def cut_positions(w, lab, comps):
    """P-cuts p in 1..n-1 (prefix of length p is a union of components)."""
    return [p for p in LE.cuts(w, lab, comps) if p > 0]


def last_block(w, lab, comps):
    c = LE.cuts(w, lab, comps)
    return set(w[c[-1]:])


def first_block(w, lab, comps):
    c = LE.cuts(w, lab, comps) + [len(w)]
    return set(w[:c[1]])


def omega(lin, n, m):
    """Order polynomial via Stanley's descent expansion (natural labelling)."""
    return sum(comb(m + n - 1 - des(w), n) for w in lin)


def omegaC_des(lin, n, m, T, lab, comps):
    """Corollary Omega-des: descent expansion of Omega_C."""
    tot = 0
    for w in lin:
        pos = {x: i for i, x in enumerate(w)}
        last = max(pos[x] for x in T) + 1          # 1-based last position of T
        C = [p for p in cut_positions(w, lab, comps) if p >= last]
        D = desset(w)
        if any(p in D for p in C):
            continue
        c = len(C)
        tot += comb(m + n - 1 - des(w) - c, n - c)
    return tot


def condition_T(f, n, comps, T, m):
    """Every nonempty upper level set f^{-1}[v, m] that is a union of
    components contains T."""
    for v in range(m):
        U = {x for x in range(n) if f[x] >= v}
        if not U:
            continue
        if all(set(c) <= U or not (set(c) & U) for c in comps) and not T <= U:
            return False
    return True


def op_data(rel, n):
    L = ME.op_lattice(n, rel)
    mu_top = ME.mu_col(L, tuple([0] * n))        # mu(pi, 1hat)
    return L, mu_top


# ---------------------------------------------------------------------------

def section_faces(posets, nmax):
    bad = ctl = tot = 0
    for n in range(1, nmax + 1):
        for rel in posets[n]:
            rel = frozenset(rel)
            lin = LE.linexts(rel, n)
            L = ME.op_lattice(n, rel)
            e_q = {p: len(LE.linexts(ME.quotient_poset(rel, p)[1], ME.nblocks(p))) for p in L}
            wk = Counter(ME.compositions(n, rel))
            tot += 1
            # face numbers by blocks: w_k = sum_{|pi| = k} e(Q_pi)  (Lemma F bijection)
            byk = Counter()
            for p in L:
                byk[ME.nblocks(p)] += e_q[p]
            ok = byk == wk
            for m in range(0, n + 3):
                a = sum(wk[k] * comb(m, k) for k in wk)
                ok &= a == omega(lin, n, m)
                ok &= a == sum(1 for f in itertools.product(range(m), repeat=n)
                               if all(f[x] <= f[y] for x, y in rel)) if (m <= 3 and n <= 6) else True
            bad += not ok
            if any(sum(comb(m + n - 2 - des(w), n) for w in lin) != omega(lin, n, m) for m in range(n + 3)):
                ctl += 1
    check(bad == 0, f"[faces] w_k = sum_(|pi|=k) e(Q_pi); Omega(P,m) = sum_k w_k C(m,k) = sum_w C(m+n-1-des w, n); {tot} posets n<={nmax}")
    control(ctl, "[faces-ctl] des+1 in place of des")


def section_omegaC(posets, nmax, lmax, fmax):
    # (1) machinery identity |mu(pi,1)| = e_C(Q_pi) for every pi (Theorem A + Lemma U)
    # (2) f-level statement (brute force, m <= 3, n <= fmax), every component T
    # (3) descent expansion, canonical labelling n <= nmax, all natural labellings n <= lmax
    bad1 = bad2 = bad3 = bad4 = 0
    ctl_noT = ctl_max = ctl_BP = ctl_firstblock = 0
    tot = totf = totl = 0
    hneg = 0
    for n in range(1, nmax + 1):
        for rel in posets[n]:
            rel = frozenset(rel)
            L, mu_top = op_data(rel, n)
            comps, lab = LE.components(rel, n)
            tot += 1
            if n <= 6:
                for p in L:
                    k, q = ME.quotient_poset(rel, p)
                    if abs(mu_top[p]) != LE.e_C(q, k) or mu_top[p] * (-1) ** (k - 1) < 0:
                        bad1 += 1
                        break
            OC = [sum(abs(mu_top[p]) * comb(m, ME.nblocks(p)) for p in L) for m in range(n + 3)]
            # h-vector nonnegativity
            h = []
            for j in range(n):
                m = j + 1
                s = OC[m] - sum(h[i] * comb(m + n - 1 - i, n) for i in range(len(h)))
                h.append(s // comb(m + n - 1 - j, n))
            hneg += any(x < 0 for x in h)
            lin = LE.linexts(rel, n)
            if len(comps) == 1:
                bad4 += any(OC[m] != omega(lin, n, m) for m in range(n + 3))
            if n <= fmax:
                for T in comps:
                    T = set(T)
                    for m in range(0, 4):
                        fs = [f for f in itertools.product(range(m), repeat=n)
                              if all(f[x] <= f[y] for x, y in rel)]
                        cnt = sum(1 for f in fs if condition_T(f, n, comps, T, m))
                        totf += 1
                        bad2 += cnt != OC[m]
                        ctl_noT += len(fs) != OC[m]
                        ctl_max += sum(1 for f in fs if fs and max(f[x] for x in T) == max(f)) != OC[m]
            labs = natural_labellings(rel, n) if n <= lmax else [rel]
            for r2 in labs:
                lin2 = LE.linexts(r2, n)
                c2, l2 = LE.components(r2, n)
                for T in c2:
                    T = set(T)
                    totl += 1
                    bad3 += any(omegaC_des(lin2, n, m, T, l2, c2) != OC[m] for m in range(n + 3))
                    BP = [w for w in lin2 if T <= last_block(w, l2, c2)]
                    ctl_BP += any(omega(BP, n, m) != OC[m] for m in range(n + 3))
                    BPf = [w for w in lin2 if T <= first_block(w, l2, c2)]
                    ctl_firstblock += any(omega(BPf, n, m) != OC[m] for m in range(n + 3))
    check(bad1 == 0, f"[omegaC-mu] mu(pi,1) = (-1)^(|pi|-1) e_C(Q_pi) for every pi in OP(P), all posets n<={min(nmax, 6)}")
    check(bad4 == 0, f"[omegaC-conn] P connected: Omega_C(P,m) = Omega(P,m)")
    check(bad2 == 0, f"[omegaC-f] Omega_C(P,m) = #{{f: upper component-union level sets contain T}}, every T, m<=3, n<={fmax} ({totf} cases)")
    check(bad3 == 0, f"[omegaC-des] descent expansion of Omega_C, every component T: all natural labellings n<={lmax}, canonical labelling n<={nmax} ({totl} cases)")
    check(hneg == 0, f"[omegaC-h] h-vector of Omega_C nonnegative on all {tot} posets n<={nmax}")
    control(ctl_noT, "[omegaC-ctl-noT] drop the condition (gives Omega, not Omega_C)")
    control(ctl_max, "[omegaC-ctl-max] condition 'max f attained on T'")
    control(ctl_BP, "[omegaC-ctl-BP] naive sum over w with last block containing T of C(m+n-1-des w, n)")
    control(ctl_firstblock, "[omegaC-ctl-first] naive sum over w with first block containing T")


def section_chi(posets, nmax):
    eq = tot = bad = 0
    for n in range(2, nmax + 1):
        for rel in posets[n]:
            rel = frozenset(rel)
            L = ME.op_lattice(n, rel)
            mu0 = ME.mu_row(L, tuple(range(n)))       # mu(0hat, pi)
            comps, lab = LE.components(rel, n)
            e = len(LE.linexts(rel, n))
            full = (-1) ** n * sum((-1) ** ME.nblocks(p) * v for p, v in mu0.items())
            kap = tuple(lab)
            restr = (-1) ** n * sum((-1) ** ME.nblocks(p) * v for p, v in mu0.items() if ME.leq(kap, p))
            tot += 1
            eq += full == e
            bad += restr != e
    check(bad == 0, f"[chi-restr] Prop. Z: (-1)^n e(P) = sum_(sigma >= kappa) (-1)^|sigma| mu(0,sigma), {tot} posets")
    control(tot - eq, f"[chi-full] unrestricted (-1)^(n-1) chi_P(-1) = e(P) (holds on only {eq} of {tot})")


def section_maj(posets, nmax):
    # rotation lemma on all of S_n
    bad = 0
    for n in range(2, nmax + 1):
        for w in itertools.permutations(range(n)):
            if (maj(w[1:] + w[:1]) - maj(w) + cdes(w)) % n:
                bad += 1
    check(bad == 0, f"[maj-rot] maj(w_2..w_n w_1) = maj(w) - cdes(w) mod n, all w in S_n, n<={nmax}")
    bad_eq = n_eq = 0
    ctl_conn = 0
    ctl_N1 = 0
    prime_bad = 0
    nonprime_fail = 0
    kw_hold = Counter()
    for n in range(2, nmax + 1):
        isprime = all(n % d for d in range(2, n))
        for rel in posets[n]:
            rel = frozenset(rel)
            lin = LE.linexts(rel, n)
            e = len(lin)
            comps, lab = LE.components(rel, n)
            eC = LE.e_C(rel, n)
            N = Counter(maj(w) % n for w in lin)
            g = 0
            for c in comps:
                g = gcd(g, len(c))
            if len(comps) > 1 and g == 1:
                n_eq += 1
                bad_eq += any(N[r] * n != e for r in range(n))
            if len(comps) == 1 and any(N[r] * n != e for r in range(n)):
                ctl_conn += 1
            ctl_N1 += N[1] != eC
            rotset = {LE.rot(w, j) for w in lin for j in range(n)}
            M = Counter(maj(w) % n for w in rotset)
            okM = all(M[r] == eC for r in range(n))
            if isprime:
                prime_bad += not okM
            else:
                nonprime_fail += not okM
            kw_hold[n] += okM
    check(bad_eq == 0, f"[maj-equi] disconnected P, gcd(component sizes)=1: maj equidistributed mod n on Lin P ({n_eq} posets)")
    control(ctl_conn, "[maj-equi-ctl] same claim for connected P")
    control(ctl_N1, "[maj-KW-dim] #{w in Lin P: maj = 1 mod n} = e_C(P)")
    check(prime_bad == 0, "[maj-rot-closure] n prime: maj equidistributed mod n on Lin(P)C_n (each residue e_C(P) times)")
    control(nonprime_fail, "[maj-rot-closure-ctl] same claim for composite n")
    print("     rotation-closure equidistribution holds, by n:", dict(kw_hold))


def section_sign(posets, nmax):
    bad = tot = 0
    ctl_eC = ctl_mu = 0
    for n in range(2, nmax + 1):
        for rel in posets[n]:
            rel = frozenset(rel)
            lin = LE.linexts(rel, n)
            I = sum(sgn(w) for w in lin)
            comps, lab = LE.components(rel, n)
            eC = LE.e_C(rel, n)
            ctl_eC += abs(I) != eC
            if len(comps) > 1:
                tot += 1
                prod = 1
                for c in comps:
                    r, _ = LE.restrict(rel, c)
                    prod *= sum(sgn(w) for w in LE.linexts(r, len(c)))
                qm = LE.poly_eval(LE.q_multinomial([len(c) for c in comps]), -1)
                bad += abs(I) != abs(round(qm.real)) * abs(prod)
    check(bad == 0, f"[sign-union] |I(P)| = |[n; m]_(q=-1)| * prod |I(T_i)| on {tot} disconnected posets n<={nmax}")
    control(ctl_eC, "[sign-ctl-eC] |I(P)| = e_C(P) = |mu(OP(P))|")


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--lmax", type=int, default=5, help="all natural labellings up to this n")
    ap.add_argument("--fmax", type=int, default=6, help="brute-force P-partitions up to this n")
    ap.add_argument("--sections", default="faces,omegaC,chi,maj,sign")
    a = ap.parse_args(argv)
    posets = n7_sweep.unlabeled_posets(a.nmax)
    print("posets by n:", {n: len(posets[n]) for n in range(1, a.nmax + 1)})
    secs = a.sections.split(",")
    if "faces" in secs:
        section_faces(posets, a.nmax)
    if "omegaC" in secs:
        section_omegaC(posets, a.nmax, a.lmax, a.fmax)
    if "chi" in secs:
        section_chi(posets, a.nmax)
    if "maj" in secs:
        section_maj(posets, a.nmax)
    if "sign" in secs:
        section_sign(posets, a.nmax)
    print("FAILURES:", FAILS if FAILS else "none")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
