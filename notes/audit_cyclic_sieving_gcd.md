# Audit of `notes/cyclic_sieving_gcd.md`

**Verdict.**

| # | Claim (all labelled PROVEN in [GCD]) | Verdict |
|---|---|---|
| 1 | Theorem G: X_P(e^{2πi/e}) ≠ 0 for e ≥ 6, e > max k_i, sole exception A_3 at e = 6 | **HOLDS** |
| 2 | Corollary H: clause (a) of Theorem C is necessary for every gcd(k_i); Theorem C becomes an iff | **HOLDS** |
| 3 | Lemma 2 (closed form), with the multi-type (F_d) (re-proved [CSC] Prop. 2) | **HOLDS** |
| 4 | Lemma 3 (phase identity: terms on four rays) and the projection (C) | **HOLDS** |
| 5 | Lemma 4 (A_d/A_1 ≤ (φ(d)/d)K·mult_d(K)/mult_d(n) ≤ φ(d)K/d; y ≥ 1 used once) | **HOLDS** |
| 6 | Lemma 5 (tail bounds (i)–(iii′) plus the 490-triple finite check) | **HOLDS**, re-verified by a different rigorous method; no gap between the tail and the finite range |
| 7 | Lemma 6 (the four exceptional triples) | **HOLDS** |
| 8 | Use of Proposition E at a(e) = 0 in its F1-corrected form | **HOLDS** (it is just the definition evaluated at ζ) |
| 9 | Side correction: the root of 1048410y³ + 50y − 12 is y ≈ 0.02183, not 0.0225 | **HOLDS** |

No fixes are required. Two remarks that do not change any verdict are in §7.

The audited note is [GCD]. Other notes are [CSC] = `notes/cyclic_sieving_cyc.md`,
[AUD] = `notes/audit_cyclic_sieving_cyc.md`, [PACSC2] =
`notes/prior_art_cyclic_sieving_cyc_2.md`, [AUD2] =
`notes/audit_prior_art_cyclic_sieving_cyc_2.md`, and [LE] =
`notes/linear_extensions.md`.

Every step below was re-derived by hand. The computations are in
`compute/audit_cyclic_sieving_gcd.py` ("[Aud]"), written for this audit. It is
plain Python 3 with exact arithmetic only (`Fraction`, integer polynomials, and
reduction modulo Φ_e). It imports nothing from `compute/`. Where [GCD] uses a
method, [Aud] uses a different one:
- **e_C(chains).** [Aud] uses its own DP for e_C of a disjoint union of chains,
  based on e_C(Q) = Σ_{L ∈ Lin Q} 1/(1 + p(L)). Here p(L) is the number of
  proper nonempty prefixes of L that are unions of components.
- **Molien polynomial.** [Aud] computes it by brute force over cycle-type
  representatives, acting on canonical rotation words.
- **The finite step of Lemma 5.** This is the main independence point. [GCD]
  brackets π and uses Taylor series for sin. [Aud] uses neither π nor a
  Taylor series. The numbers cos(jπ/e), j = 1, …, e − 1, are exactly the roots
  of the Chebyshev polynomial U_{e−1}, and all of them are simple. [Aud] finds
  e − 1 disjoint rational brackets, each with a strict sign change of U_{e−1},
  which it evaluates exactly. So each bracket holds exactly one root, and the
  brackets in decreasing order hold cos(π/e), cos(2π/e), …. Each bracket is
  then bisected to width < 10^{−40}. Then s_d² = 4(1 − cos²(πd/e)), and s_d
  is bounded by integer square roots at scale 2^{−200}.

Output is archived in `compute/output/audit_cyclic_sieving_gcd.txt`. Tags such
as `[ineq]` are its section labels. Each computed section has a positive
control that must fail, and it does (§6).

## 1. S1: (F_d), Lemma 1 and Lemma 2 — HOLDS

**Hand check.** Let w ∈ W have all copy-cycles of length d, with d | every k_i.
By Lemma 1 these are the only w with F(w) ≠ 0. Suppose w fixes a class C. Then
wL = Lγ^r for every L ∈ C, with the same r for all L, because
w(Lγ^t) = (Lγ^t)γ^r. Here γ^r has order n/gcd(n, r). That order must be d,
because w and γ^r are conjugate permutations of [n], and every w-orbit on [n]
has length d (the cycle products are trivial). So r = s·n/d with
gcd(s, d) = 1, which gives φ(d) values of s.

The block argument works for any number of types, because it uses only
comparabilities inside a component, and w maps each component onto a
component. So every block is a union of components, and it holds one copy from
each copy-cycle; that is, it is a copy of P_d. The count d^{K/d}/d per class of
P_d is the [CSC] Prop. 2 count with "cycles of w" in place of "cycles of the
k-cycle". [CSC] §2 gives the same formula as a consequence of the fixed-class
formula F(g) = φ(o(g))·S(g) of [LE] §4, and that route is independent of the
lifting count.

The count for Lemma 2 also checks out by hand. The class of cycle type d^{k_i/d}
in S_{k_i} has k_i!/(d^{k_i/d}(k_i/d)!) elements. So
(1/|W|)·#{w}·F(w_d) = d^{−K/d} ∏(k_i/d)!^{−1} · φ(d) d^{K/d−1} c_d = A_d, and
det(1 − qw) = (1 − q^d)^{K/d}.

**COMPUTED** (`[brute]`). [Aud] checked 13 posets by brute force: A_3 through A_6,
C_2^{⊔2}, C_2^{⊔4}, C_3^{⊔2}, V^{⊔2}, V^{⊔2} ⊔ A_2, Λ^{⊔2} ⊔ C_2^{⊔2},
A_2 ⊔ C_2^{⊔2}, A_4 ⊔ C_2^{⊔2} and A_3 ⊔ C_2^{⊔3}. Five of them have two types,
and two have y = 2. The results:
- Lemma 1: F = 0 off the support, on every class.
- (F_d): 30/30 supported classes.
- Proposition F, c_d = ∏ e(T_i)^{k_i/d}·E_d: every (P, d).
- Lemma 2: the closed form equals the brute-force Molien polynomial in 13/13 cases.
- X(1) = e_C(P) in every case, and X_{A_3} = 1 + q³.

**Control.** Dropping φ(d) from the closed form changes X_{A_5}. The DP also
rejects e_C(C_2 ⊔ C_2) = 6; the value is 5.

## 2. Prop. E at a(e) = 0; S2 phases; S3 projection — HOLDS

**Item 1 of the brief (Prop. E, F1 form).** When e > max k_i, every eigenvalue
λ of w ∈ W has order dividing a cycle length ≤ max k_i < e. So λ ≠ ζ^{−1}, and
det(1 − ζw) ≠ 0. Then X_P(ζ) = ∏_i (ζ; ζ)_{k_i}·(1/|W|) Σ_w F(w)/det(1 − ζw)
is simply the defining formula ([CSC] §3) evaluated at a point where it has no
pole. This is exactly what [AUD2] F1 says. [GCD] keeps the prefactor, and the
prefactor is nonzero because j ≤ k_i < e. Nothing deeper from Prop. E is used,
so nothing can go wrong here.

**Item 2 (four rays).** I re-derived the identity
1 − e^{iθ} = −2i sin(θ/2)e^{iθ/2}, which gives
1/(1 − ζ^p) = e^{i(π/2 − πp/e)}/(2 sin(πp/e)) with a positive denominator for
0 < p < e. Every d | g satisfies d ≤ g ≤ max k_i < e. Raising to the power K/d
gives R_d·i^{K/d}·e^{−iπK/e}. Lemma 1 enters here: on the support of F,
det(1 − ζw) is a pure power of a single (1 − ζ^d). So after the common factor
is removed, each term is a positive real times a fourth root of unity. A float
sanity check against the exact closed form agreed in 685/685 cases (`[phase]`).
The rigorous checks in §5 do not depend on it.

**S3.** Re(i^{−K}·i^{K/d}) = cos(π(K/d − K)/2). This is −1 iff
K − K/d ≡ 2 (mod 4), and 0 or 1 otherwise. The coefficients satisfy
A_d, R_d > 0, because c_d ≥ 1 (a class of P_d exists). So
Re(i^{−K}Σ) ≥ A_1R_1 − Σ_{D^−} A_dR_d. Strict inequality in (C) gives
Re(i^{−K}Σ) > 0, hence Σ ≠ 0. For g = 1, D^− = ∅.

## 3. S4: Lemma 4 and where y ≥ 1 enters — HOLDS

**Item 3 of the brief.** I re-derived all six inequalities.
- **Item 1.** The rotation of L = AB to BA is a linear extension iff there is no
  pair x < y with x ∈ A and y ∈ B. The reverse case, y ∈ A and x ∈ B, is already
  excluded because L is a linear extension. Components are connected in the
  comparability graph, so this holds iff A is a union of components. Such
  prefixes are nested and have distinct sizes, so there are at most K − 1
  proper ones. A class therefore meets Lin P in at most K words, which gives
  e(P) ≤ K·c_1.
- **Item 5.** (a)_r(b)_s ≤ (a+b)_r(a+b−r)_s = (a+b)_{r+s} for r ≤ a. Induction
  with r_i = k_i − k_i/d then gives Σr_i = K − K/d.
- **Item 6.** mult_d(dj+d)/mult_d(dj) = ∏_{t=1}^{d}(dj+t)/(j+1)^d ≥ 1.
- **Combining.** A_d/A_1 = (φ(d)/d)(c_d/c_1)∏k_i!/(k_i/d)!. Then
  c_d/c_1 ≤ K e(P_d)/e(P) = K/(mult_d(n)e(P_d)^{d−1}), and
  e(P_d)^{d−1} ≥ ((K/d)!)^{d−1}·y^{g−g/d}.

  **y ≥ 1 enters exactly once:** dropping y^{g−g/d} ≥ 1. The rest is arithmetic:
  K!/(K/d)! · 1/((K/d)!)^{d−1} = mult_d(K).

**COMPUTED** (`[ratio]`). [Aud] checked 699 (vector, y, d) cases with
y ∈ {1, 2, 3}, all inside both bounds. For the antichains A_4, A_6, A_8 and A_9,
A_d/A_1 = φ(d) exactly, which is the sharpness claim.

**Control.** For k = (4, 4), m = (1, 2) and y = 1/50, A_4/A_1 = 4.29, which
exceeds the bound 0.0273.

**Control** (`[yroot]`). For the same (k, m) at e = 6, [Aud] computes X(ζ_6)/y
exactly in Q(ζ_6) as a polynomial in y. It is real, proportional to
1048410y³ + 50y − 12, and has a root at y = 0.0218312… in (0, 1). This
confirms [GCD]'s correction of [AUD] §3(ii): the root is 0.02183, not 0.0225.
(An observation, not a diagnosis: 0.02252 is the root of 1048410y³ + 50y² − 12,
the cubic with the y and y² coefficients swapped. [Aud] first made exactly this
slip, and fixed it.)

## 4. S5: Lemma 5 — coverage of all (e, K, g) — HOLDS

**Item 4 of the brief.** The domain is e ≥ 6, 2 ≤ g ≤ e − 1, g | K. It splits
into four regions:
- e ≥ 18, all K: tail (ii).
- 7 ≤ e ≤ 17, K ≥ K_e: tail (iii).
- e = 6, K ≥ 36: tail (iii′).
- 6 ≤ e ≤ 17, K < K_e (K_6 := 36): finite range (iv).

These regions are disjoint and cover the domain. The cut is K < K_e versus
K ≥ K_e, so no boundary value is missed, and g runs over 2, …, e − 1 in both the
tail and the finite range.

Tail checks, re-derived by hand:
- **(i), e ≥ 7.** s_d ≥ s holds for 1 ≤ d ≤ e − 1. Since s < 1,
  ρ_d ≤ s^{K−K/d} ≤ s^{⌈K/2⌉}. Also K/d ≤ K/2 and Σ_{d|g,d≥2}φ(d) = g − 1 ≤ K − 1.
  The ratio h(K+2)/h(K) = (K+1)(K+2)s/((K−1)K) decreases in K. So h(K_e) < 1,
  h(K_e+1) < 1 and ratio(K_e) ≤ 1 give h < 1 for all K ≥ K_e, by induction in
  steps of 2.
- **(ii).** [Aud] gets 2 sin(π/18) ≤ 0.347296 < 0.3474 from the Chebyshev
  enclosure. The maximum of h(K) over K = 2, …, 9 is 0.7241, at K = 4, and
  (90/56)·0.3474 < 1.
- **(iii).** [Aud] recomputes K_e from its own rigorous upper bound for s:
  127, 55, 33, 23, 17, 13, 11, 9, 7, 4, 4 for e = 7, …, 17, identical to [GCD].
- **(iii′).** d = 5 is never in D^− at e = 6, because k = (5, …, 5) and
  K − K/5 = 4t. Also 3r² > 1 for r = 0.57736. h_6(36, …, 39) = 0.642, 0.659,
  0.677, 0.695, and (K+4)r/K ≤ 1 there.

**Finite range** (`[ineq]`). [Aud] enumerates the finite range itself and gets
**490 triples**, the same count as [GCD]. For each triple it computes rigorous
lower and upper bounds for Σ_{D^−}φ(d)(K/d)ρ_d.
- The upper bound is < 1 in every triple except (6,3,3), (6,8,4), (7,12,6) and
  (8,7,7). The largest upper bound outside these four is 0.7500.
- In (6, 8, 4), (7, 12, 6) and (8, 7, 7) the lower bound is ≥ 1, so these are
  genuine exceptions of the crude bound, not rounding artefacts.
- In (6, 3, 3) the enclosure straddles 1. The exact value is
  φ(3)·1·s³/s_3 = 2·1/2 = 1, so the bound is attained.

**Redundancy.** [Aud] also checked 1701 further triples directly by enclosure:
40 more values of K past every threshold, for e = 6, …, 25. All are < 1. This
confirms the tails numerically, independently of the induction.

## 5. S6: Lemma 6, e < 6, and Corollary H — HOLDS

**Item 5 of the brief.**
- **Forced k-vectors.** [Aud] enumerated every k-vector with Σk_i = K, all
  k_i ≤ e − 1 and gcd = g. The four triples force (3), (4, 4), (6, 6) and (7)
  respectively, as claimed.
- **Mid-term bounds at the minimal n** (`[exc]`). The minimal n are 6, 12, 18
  and 14, which use the fact that there is one connected poset each of sizes 1
  and 2. The bounds are 0.0667, 0.00909, 0.00148 and 8.92·10^{−6}, all as
  stated. They are monotone in n by item 6 of Lemma 4.
- **A_3 at e = 6.** Φ_6 | 1 + q³, which is the genuine zero, with
  A_1R_1 = A_3R_3 = 1/3.
- **A_7 at e = 8.** Exact reduction mod Φ_8 is nonzero. By hand,
  (2 − √2)³ = 20 − 14√2 ≠ 1/6.
- **Which exceptional e can be bad.** Of the four exceptional e, only e = 6 in
  (6, 8, 4) divides an element order of W. That case is covered by the
  mid-term bound.

**e < 6.** Theorem G claims nothing for e < 6, and Corollary H never needs it.
A bad e divides o(g) and exceeds max k_i. If e were a prime power ℓ^b, some
cycle length would be divisible by ℓ^b, so ℓ^b ≤ max k_i, which is impossible.
Every e ≤ 5 is a prime power, so a bad e is at least 6. [Aud] re-checks this
on all element orders with max k_i ≤ 9.

Also, 6 ∤ o(w) for every w ∈ S_3, so the A_3 exception never occurs as a bad e.

One observation: the hypothesis e ≥ 6 cannot be dropped from Theorem G in its
"formal y ≥ 1" form. The data k = (3), m = (1) with formal y = 2 gives Φ_4 | X
(`[exact]`). That data is not realizable, because m = 1 forces y = 1. The real
A_3 has X(i) = 1 − i ≠ 0, and [Aud] found no realizable zero with e < 6.

**Corollary H, step 2.** F(g^{N/e}) = 0 holds because a fixed class would force
all copy-cycles to have one length, equal to the order e > max k_i (Lemma 1).
Step 3 holds because ω^{N/e} = e^{2πi/e}. Vanishing at one primitive e-th root
is equivalent to vanishing at all of them, since X ∈ Q[q].

**Brute-force CSP** (`[corH]`). [Aud] tested the full CSP exactly, comparing
X(ω^j) with F(g^j) mod Φ_{N/gcd(N,j)} for every j, on these cases:
- A_5 with copy-cycles (2, 3);
- A_7 with (2, 5) and (3, 4);
- A_3 ⊔ C_2^{⊔3} with (3), (2, 1);
- A_4 ⊔ C_2^{⊔2} with (3, 1), (2).

In each the CSP fails, F(g^{N/e}) = 0 at the bad e, and X(ζ_e) ≠ 0. A control
that satisfies (a), V^{⊔2} ⊔ A_2 with (2), (2), passes the CSP.

**Independent check of Theorem G** (`[exact]`). [Aud] reduced X_P mod Φ_e
exactly over this range:
- 190 type vectors: up to 3 types, K ≤ 12, m_i ≤ 3, gcd ≥ 2, with types of
  equal size required to be distinct posets;
- single types with k = 13, …, 20 and m = 1, 2;
- y ∈ {1, 2, 7};
- every e with 6 ≤ e < max(40, 2K + 4) and e > max k_i.

That is 17319 triples. The only zero is A_3 at e = 6.

**Positive control.** Every Theorem B(ii) case in range has e ≤ max k_i and
e ∤ some k_i. The checker reports Φ_e | X in 2125/2125 of them.

The counts differ from [GCD]'s 2259 and 2235 because the ranges and
realizability conventions differ. Neither set of counts was used to fix the
other.

## 6. Positive controls (each must fail, and does)

| Instrument | Control | Result |
|---|---|---|
| closed form vs brute | drop φ(d) (A_5) | disagrees |
| chain DP | e_C(C_2⊔C_2) = 6 | rejected (5) |
| Lemma 4 | y = 1/50 | bound violated, 4.29 > 0.027 |
| conclusion vs y | X(ζ_6) at y ∈ (0, 1) | real root 0.0218312 |
| Lemma 5 enclosure | drop the D^− restriction | ≥ 1 in 17 finite triples; A_5 at e = 6 gives exactly 4 |
| Lemma 5 enclosure | the exceptional triples | 3 certified ≥ 1; (6, 3, 3) straddles the exact value 1 |
| mod-Φ_e zero test | B(ii) zeros, and A_3 at e = 6 | 2125/2125 detected; A_3 detected |
| CSP tester | a class satisfying (a) | CSP holds |

## 7. Remarks (no verdict change)

1. **Prop. E is not needed.** [GCD] §0 cites Proposition E at a(e) = 0. The
   argument needs only the absence of poles at ζ, which takes one line. The
   citation is correct but heavier than necessary.
2. **The (F_d) lifting count in S1 is terse.** It is correct, by the [CSC]
   argument verbatim and by the [LE] fixed-class route, and it holds in 30/30
   brute-force classes. It is not re-proved here in more detail than [CSC]
   gives.

## Reproduce

```
cd compute
python3 audit_cyclic_sieving_gcd.py > output/audit_cyclic_sieving_gcd.txt   # ~18 s, one core; exit 0 iff all checks hold and all controls fail
python3 -m unittest test_audit_cyclic_sieving_gcd
```
