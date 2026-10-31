# Clause (a) of Theorem C is necessary for every gcd(k_i)

This note takes up open problem 2 of `notes/cyclic_sieving_cyc.md` ([CSC] §9):
is clause (a), e ≤ max k_i, of Theorem C necessary when gcd(k_i) > 1?
Every claim is tagged **PROVEN**, **COMPUTED**, **CITED** or **OPEN**. The code is
`compute/cyclic_sieving_gcd.py`, and its output is archived in
`compute/output/cyclic_sieving_gcd.txt`. Bracketed tags such as `[ineq]` are
line labels in that output.

## Verdict

**YES. Clause (a) is necessary for every gcd(k_i). Theorem C is therefore an
iff: X_P sieves ⟨g⟩ if and only if (a) and (b) hold (PROVEN, Corollary H).**

The proof rests on one new statement.

**Theorem G (PROVEN).** Let e ≥ 6 with e > max k_i, and let ζ = e^{2πi/e}.
Then X_P(ζ) ≠ 0, with exactly one exception: P = A_3 and e = 6, where
X_P = 1 + q³.

When (a) fails, some divisor e of N = o(g) has e > max k_i. Such an e is
never a prime power ([CSC] §3), so e ≥ 6. The exception does not arise,
because 6 is not the order of any element of S_3. Then X_P(ω^{N/e}) =
X_P(ζ) ≠ 0, while F(g^{N/e}) = 0 by Lemma 1, so the CSP fails.

| Question | Answer |
|---|---|
| Is (a) necessary when gcd(k_i) > 1? | **YES, PROVEN** (Corollary H). This settles [CSC] §9 problem 2. |
| Tool used | Proposition E of [PACSC2] §1 at a(e) = 0, in the corrected form of [AUD2] F1, together with Lemma 1 of [CSC]. |
| Main idea | At ζ = e^{2πi/e}, each surviving term of the Molien sum is a positive real number times e^{−iπK/e} · i^{K/d} (Lemma 3). So the terms lie on four rays. Only the terms on the ray opposite to the w = 1 term can cancel it, and Lemma 4 bounds those terms. |
| Where y ≥ 1 enters | Lemma 4. The ratio A_d/A_1 carries the factor y^{−(g − g/d)}, and the bound needs it to be ≤ 1. For y < 1 the conclusion is false: with k = (4, 4), m = (1, 2) and e = 6, X_P(ζ_6) = 0 at y ≈ 0.02183 (`[yroot]`). |
| Computer-assisted step | One finite step: Lemma 5(iv) checks 490 triples (e, K, g) with exact rational arithmetic and interval bounds for sin (`[ineq]`). Everything else is by hand. |
| Independent evidence | **COMPUTED.** Φ_e does not divide X_P for any of 2259 (type vector, y, e) triples and 548 single-type triples (`[exact]`). The B(ii) zeros serve as positive control: 2235/2235 detected. Brute-force CSP failure was confirmed on 6 classes of real posets (`[brute]`). |

**Audit and prior art.** The independent audit
`notes/audit_cyclic_sieving_gcd.md` finds every claim of this note HOLDS,
with no fixes required; it re-verified Lemma 5(iv) by a different rigorous
method (Chebyshev root brackets, no π and no Taylor series). The prior-art
check `notes/prior_art_cyclic_sieving_gcd.md` did not find Theorem G or the
necessity of (a) for gcd(k_i) > 1 in the sources read (a search result,
not a proof of novelty); the iff form of Theorem C stays PARTLY KNOWN.

**Status changes in [CSC]** (now applied there, after the audit):
- §3, Theorem C: "If (a) fails and gcd(k_i) > 1, necessity is OPEN" becomes
  "If (a) fails, the CSP fails (PROVEN: Proposition 3 for gcd(k_i) = 1, and
  [GCD] Corollary H in general)."
- Verdict table, row 2: "necessity of (a) is PROVEN when gcd(k_i) = 1 and
  OPEN otherwise" becomes "necessity of (a) is PROVEN ([GCD])".
- §9, problem 2: OPEN becomes PROVEN ([GCD]); the audit HOLDS.
- [PACSC2] §1, last paragraph: "for gcd(k_i) > 1 it is [CSC] §9 problem 2
  (OPEN)" becomes "for gcd(k_i) > 1 it is [GCD] Theorem G".
- Small numerical correction to `notes/audit_cyclic_sieving_cyc.md` §3(ii).
  The real root of 1048410y³ + 50y − 12 is y ≈ 0.02183, not "≈ 0.0225"
  (f(0.0225) ≈ 1.07). The qualitative point, a root in (0, 1), stands
  (`[yroot]`).

## 0. Setting and notation

The notation is that of [CSC] §1 and §3. P has connected component types
T_1, …, T_s, with T_i of size m_i occurring k_i times. Write
K = Σ k_i for the number of components, n = |P| = Σ m_i k_i, and
g = gcd(k_i). W = ∏ S_{k_i} permutes the copies, and F(w) = |Cyc(P)^w|. The
fake-degree polynomial is

  X_P(q) = ∏_i (q; q)_{k_i} · (1/|W|) Σ_{w ∈ W} F(w)/det(1 − q·w | V).

For d | g, put P_d = ⊔_i T_i^{⊔ k_i/d}: one copy per d-cycle, a poset with
K/d components and n/d elements. Put c_d = e_C(P_d), so that c_1 = e_C(P).
Put y = ∏_i e(T_i)^{k_i/g}. Write mult_d(x) = x!/((x/d)!)^d for d | x. Fix
e > max k_i and ζ = e^{2πi/e}, and write s_d = 2 sin(πd/e) and s = s_1.

Facts used from earlier notes:
- **Lemma 1 of [CSC] (PROVEN there).** If F(w) ≠ 0 for w ∈ W, then every
  cycle of w on the copies has the same length d, and d divides every k_i.
- **Proposition F of [LE] (PROVEN there).** e_C(P) = ∏ e(T_j) · e_C(⊔ C_{|T_j|}),
  the product over all components. Applied to P_d it gives
  c_d = y^{g/d} E_d, where E_d = e_C(⊔_i C_{m_i}^{⊔ k_i/d}) is the
  chain-pattern count.
- **Proposition E of [PACSC2] at a(e) = 0 (PROVEN there, HOLDS in [AUD2],
  corrected form F1).** When e > max k_i, a(e) = Σ⌊k_i/e⌋ = 0, so
  M = W and

    X_P(ζ) = ∏_i (ζ; ζ)_{k_i} · (1/|W|) Σ_{w ∈ W} F(w)/det(1 − ζw).

  The prefactor ∏_i ∏_{j ≤ k_i}(1 − ζ^j) is nonzero, since j ≤ k_i < e.
  Every denominator is nonzero too: an eigenvalue of w is a root of unity
  of order at most max k_i < e, so it is never ζ^{−1}. This is the starting
  point. Everything below is an analysis of the sum.

## 1. The closed form at ζ

**Lemma 2 (PROVEN; COMPUTED 10/10 against brute-force Molien, `[brute]`).**

  X_P(q) = ∏_i (q; q)_{k_i} · Σ_{d | g} A_d (1 − q^d)^{−K/d},
  A_d = (φ(d)/d) · c_d / ∏_i (k_i/d)!.

*Proof.* By Lemma 1, only w with all cycles of a common length d | g
contribute. For such w, det(1 − qw) = (1 − q^d)^{K/d}, and the number of such w
is ∏_i k_i!/(d^{k_i/d}(k_i/d)!). The multi-type form of [CSC] Proposition 2
is

  (F_d)  F(w_d) = φ(d) · d^{K/d − 1} · c_d.

Then (1/|W|) · #{w of type d} · F(w_d) = A_d. ∎

*Proof of (F_d)* (shared step S1: the [CSC] proof of Proposition 2, with
"the cycles of w" in place of "the cycles of the k-cycle"). Suppose w fixes a
class C. For L ∈ C we have wL = Lγ^r, and r does not depend on L. Since
γ^r is conjugate to w as a permutation of [n], and every w-orbit on [n]
has length d, r = s·n/d with gcd(s, d) = 1. This accounts for the factor
φ(d). Cut L into d blocks of length n/d. Then w maps block j to block j + s.
If x < y in one component and b(x) < b(y), choose t with b(y) + ts ≡ 0 mod d.
Applying w^t then breaks the inequality. So each component lies in one block.
Hence each block is a union of components that contains exactly one copy
from each cycle of w, and so it is a copy of P_d. Conversely, let u be a
linear extension of such a union, and s′ = s^{−1} mod d. Then
u · w^{s′}(u) ⋯ w^{(d−1)s′}(u) is a linear extension whose class is fixed by
w. For fixed s, a class of P_d lifts in d^{K/d} ways, one copy chosen per
cycle. Rotation by a block permutes the lifts in orbits of size d. So
F(w_d) = φ(d) d^{K/d − 1} c_d. ∎ [CSC] §2 records that [AUD] checked this
multi-type form on all 206 classes conjugate into W. Here `[brute]`
reproduces the whole polynomial X_P from it on 10 posets, among them
V^{⊔2} ⊔ A_2 and Λ^{⊔2} ⊔ C_2^{⊔2}, where y = 2.

**Lemma 3 (phase identity; PROVEN; COMPUTED 112/112, `[phase]`).**

  X_P(ζ) = ∏_i (ζ; ζ)_{k_i} · e^{−iπK/e} · Σ_{d | g} A_d R_d i^{K/d},
  R_d = s_d^{−K/d} > 0.

*Proof* (shared step S2). For 0 < p < e,
1 − e^{iθ} = −2i sin(θ/2) e^{iθ/2}, with θ = 2πp/e, so

  1/(1 − ζ^p) = e^{i(π/2 − πp/e)} / (2 sin(πp/e)),  with 2 sin(πp/e) > 0.

Every d | g satisfies d ≤ g ≤ max k_i < e. Raising to the power K/d gives
(1 − ζ^d)^{−K/d} = R_d · e^{iπK/(2d)} · e^{−iπK/e}, and e^{iπK/(2d)} = i^{K/d}.
Substitute into Lemma 2. ∎

The phase of the d-term, after removing the common factor e^{−iπK/e}, is
a fourth root of unity. This is what Lemma 1 buys: on its support, det(1 − ζw)
is a single power of (1 − ζ^d). Dropping the factor i^{K/d} changes the value
in 80/112 cases (`[phase]`, control).

**Projection (PROVEN; shared step S3).** Put Σ = Σ_d A_d R_d i^{K/d} and
D^−(K, g) = {d | g : d ≥ 2, K − K/d ≡ 2 (mod 4)}. Then

  Re(i^{−K} Σ) = Σ_d A_d R_d cos(π(K/d − K)/2) ≥ A_1 R_1 − Σ_{d ∈ D^−} A_d R_d,

since cos(π(K/d − K)/2) is −1 exactly when K/d − K ≡ 2 (mod 4), and is 0 or 1
otherwise. Hence

  (C)  Σ_{d ∈ D^−} (A_d/A_1)(R_d/R_1) < 1  ⟹  X_P(ζ) ≠ 0.

If g = 1, then D^− = ∅, and this recovers [CSC] Proposition 3.

## 2. The ratio bound: where y ≥ 1 is used

**Lemma 4 (PROVEN; COMPUTED 237/237, `[ratio]`).** For d | g with d ≥ 2,

  A_d/A_1 ≤ (φ(d)/d) · K · mult_d(K)/mult_d(n) ≤ φ(d) · K/d.

*Proof* (shared step S4). A_d/A_1 = (φ(d)/d) · (c_d/c_1) · ∏_i k_i!/(k_i/d)!.
Four elementary inequalities follow.

1. *c_1 ≥ e(P)/K.* A class is a coset wC_n. The rotation of L = AB to BA
   is a linear extension iff no element of A lies below an element of B,
   that is, iff the prefix A is a union of components. The proper nonempty
   prefixes that are unions of components are nested and strictly
   increasing, so there are at most K − 1 of them, and a class meets Lin P
   in at most K words ([LE] §4, after Proposition F, records the same bound). Summing over
   classes gives e(P) ≤ K c_1.
2. *c_d ≤ e(P_d).* Each class contains at least one linear extension.
3. *e(P) = mult_d(n) · e(P_d)^d.* P ≅ P_d^{⊔d}, and a linear extension of a
   disjoint union is a shuffle of linear extensions of the parts.
4. *e(P_d) ≥ (K/d)! · y^{g/d}.* Order the K/d components of P_d, and
   concatenate a linear extension of each in that order. Distinct
   (order, extensions) give distinct words. There are
   (K/d)! ∏_i e(T_i)^{k_i/d} = (K/d)! y^{g/d} of them.

So c_d/c_1 ≤ K/(mult_d(n) e(P_d)^{d−1}) ≤ K/(mult_d(n) ((K/d)!)^{d−1} y^{g − g/d}).
**Here y ≥ 1 is used: y^{g − g/d} ≥ 1.** Next,

5. *∏_i k_i!/(k_i/d)! ≤ K!/(K/d)!.* Write (x)_r = x(x − 1)⋯(x − r + 1). For
   r ≤ a, (a)_r (b)_s ≤ (a + b)_r (a + b − r)_s = (a + b)_{r+s}, because
   a ≤ a + b and b ≤ a + b − r. Induct over i with a = k_i and r = k_i − k_i/d.
6. *mult_d(K) ≤ mult_d(n)* for K ≤ n, both multiples of d.
   mult_d(dj + d)/mult_d(dj) = ∏_{t=1}^{d}(dj + t)/(j + 1)^d ≥ 1.

Combining: A_d/A_1 ≤ (φ(d)/d) · K · [K!/(K/d)!] / [mult_d(n) ((K/d)!)^{d−1}]
= (φ(d)/d) · K · mult_d(K)/mult_d(n) ≤ φ(d)K/d. ∎

**How y ≥ 1 is used, exactly.** By Proposition F, A_d/A_1 = y^{−(g − g/d)} · α_d,
where α_d depends only on (k_i, m_i). Lemma 4 bounds α_d. The step from α_d to
A_d/A_1 is the inequality y^{−(g−g/d)} ≤ 1, which is where y ≥ 1 enters. It is
the same as e(T_i) ≥ 1, the fact that a poset has a linear extension, used
in item 4. The A_d with large d carry the low powers y^{g/d}. For small y
they outweigh A_1 (which carries y^g), and nothing then prevents
cancellation. Two controls must fail, and they do:
- With k = (4, 4), m = (1, 2) and y = 1/50, A_4/A_1 = 4.29 exceeds the
  bound 0.027 (`[ratio]`).
- For the same (k, m) and e = 6, X_P(ζ_6) actually vanishes at
  y ≈ 0.021831. This is the root of [AUD]'s cubic 1048410y³ + 50y − 12
  (`[yroot]`).

Lemma 4 is sharp in the worst case. For the antichain A_k, A_d/A_1 = φ(d)
exactly (`[ratio]`). The second inequality loses only the factor K/d, and
that factor is 1 when d = K.

## 3. The inequality (C)

Lemma 4 bounds the left side of (C) by

  Σ_{d ∈ D^−(K,g)} φ(d) (K/d) ρ_d,  ρ_d = R_d/R_1 = s^K / s_d^{K/d}.

This depends only on (e, K, g).

**Lemma 5 (PROVEN; part (iv) is a rigorous finite computation, `[ineq]`).**
Let e ≥ 6, 2 ≤ g ≤ e − 1 and g | K. Then Σ_{d ∈ D^−} φ(d)(K/d)ρ_d < 1,
except for (e, K, g) ∈ {(6, 3, 3), (6, 8, 4), (7, 12, 6), (8, 7, 7)}.

*Proof* (shared step S5). Every d ∈ D^− satisfies 2 ≤ d ≤ g ≤ e − 1, so
s_d = 2 sin(πd/e) ≥ 2 sin(π/e) = s.

- **(i) e ≥ 7, a tail bound.** Here s < 1, so ρ_d ≤ s^{K − K/d}. Since
  K − K/d is an integer ≥ K/2, ρ_d ≤ s^{⌈K/2⌉}. Also K/d ≤ K/2, and
  Σ_{d | g, d ≥ 2} φ(d) = g − 1 ≤ K − 1. So the sum is at most
  h(K) = ((K − 1)K/2) · s^{⌈K/2⌉}, and h(K + 2)/h(K) = (K + 1)(K + 2)s/((K − 1)K),
  which decreases in K.
- **(ii) e ≥ 18.** s ≤ 2 sin(π/18) < 0.3474. With s = 0.3474,
  h(K) < 1 for K = 2, …, 9 (the maximum is 0.7241, at K = 4), and
  h(K + 2)/h(K) ≤ 90 · 0.3474/56 < 1 for K ≥ 8. So h(K) < 1 for every
  K ≥ 2, with no exceptions.
- **(iii) 7 ≤ e ≤ 17, K ≥ K_e.** K_e is the least K with h(K) < 1,
  h(K + 1) < 1 and h(K + 2)/h(K) ≤ 1. By induction in steps of 2, h < 1 for
  all K ≥ K_e. Computed with an upper bound for s: K_e = 127, 55, 33, 23, 17,
  13, 11, 9, 7, 4, 4 for e = 7, …, 17.
- **(iii′) e = 6, K ≥ 36.** Here s = 1, and s_d = √3, 2, √3, 1 for
  d = 2, 3, 4, 5. d = 5 ∉ D^−: d = 5 forces g = 5, so all k_i = 5 and
  K = 5t, and then K − K/5 = 4t ≡ 0 (mod 4). So D^− ⊆ {2, 3, 4}, and
  ρ_d ≤ r^{K/d} with r = 0.57736 > 1/√3. Since K/d ≥ ⌊K/4⌋, K/d ≤ K/2 and
  φ(2) + φ(3) + φ(4) = 5, the sum is at most h_6(K) = (5K/2) r^{⌊K/4⌋}.
  Then h_6 < 1 for K = 36, …, 39, and h_6(K + 4)/h_6(K) = (K + 4)r/K ≤ 1
  there. Induction in steps of 4.
- **(iv) The finite range.** The remaining triples are 6 ≤ e ≤ 17, g ≤ e − 1,
  g | K, K < K_e. There are 490 of them. For each, the script bounds the sum
  above by an exact rational. It uses π ∈ [3.14159265358979323846, …847],
  the alternating Taylor series of sin truncated at two consecutive orders
  (which bracket sin on [0, π/2]), and outward rounding to 2^{−96}. The
  bound is < 1 in all but the four listed triples. The largest such bound
  is 0.75. ∎

**Lemma 6 (the four exceptional triples; PROVEN; `[exc]`).** For these,
Lemma 4 is used with its middle term (φ(d)/d) K mult_d(K)/mult_d(n), not the
crude φ(d)K/d.
- **(6, 3, 3).** g = K = 3 forces one type with k = 3, so D^− = {3}.
  - If m ≥ 2, then n ≥ 6, and the sum is at most
    (2/3) · 3 · mult_3(3)/mult_3(6) · (1/2) = 0.0667 < 1.
  - If m = 1, then P = A_3, X_P = 1 + q³ and X_P(ζ_6) = 0. This is a genuine
    zero: A_1R_1 = A_3R_3 = 1/3, with opposite phases. But no element of
    S_3 has order divisible by 6, so this e never violates (a).
- **(6, 8, 4).** k_i ∈ {4} and K = 8 force k = (4, 4): two distinct types.
  Only one connected poset has size 1, and only one has size 2, so
  m_1 + m_2 ≥ 3 and n ≥ 12. D^− = {4}, and the sum is at most
  (2/4) · 8 · mult_4(8)/mult_4(12) · (1/3) = 0.0091 < 1. This is the case
  where [AUD] found a root 0 < y < 1. With y ≥ 1, the d = 4 term is 100 times
  too small to cancel.
- **(7, 12, 6).** This forces k = (6, 6) with two distinct types, so
  n ≥ 18. D^− = {2, 6}, and the sum is at most 0.0015.
- **(8, 7, 7).** This forces k = (7).
  - If m ≥ 2, the sum is at most 8.9·10^{−6}.
  - If m = 1 (A_7), only d = 1 and d = 7 occur. Their phases are i^7 and
    i^1, which are opposite. So Σ = i(A_7R_7 − A_1R_1), with A_1 = 1/7,
    A_7 = 6/7 and s_7 = s. This vanishes iff s^6 = 1/6. But
    s² = 2 − √2, so s^6 = 20 − 14√2, which is irrational. Hence X_P(ζ_8) ≠ 0.

The last two triples have prime-power e, so they never violate (a). They are
handled only to state Theorem G for every e ≥ 6. Of the four triples, only
(6, 8, 4) has an e that divides the order of an element of W (`[ineq]`).

## 4. The theorem and the corollary

**Theorem G (PROVEN).** Let e ≥ 6 with e > max k_i. Then
X_P(e^{2πi/e}) ≠ 0, unless P = A_3 and e = 6.

*Proof.* If g = 1, D^− = ∅ and (C) holds. If g ≥ 2, then g ≤ max k_i ≤ e − 1.
Lemma 4 reduces (C) to the inequality of Lemma 5, which holds outside the
four triples, and Lemma 6 handles those. In every case the projection
(S3) gives Re(i^{−K}Σ) > 0, except for A_3 at e = 6. The prefactor
∏(ζ; ζ)_{k_i} e^{−iπK/e} of Lemma 3 is nonzero. ∎

**Corollary H (PROVEN). Clause (a) of Theorem C is necessary.** Let g ∈ Aut(P)
be conjugate into W, with N = o(g). Suppose some divisor e > 1 of N has
e > max k_i. Then (Cyc(P), ⟨g⟩, X_P) is not a CSP.

*Proof* (shared step S6).
1. *e is not a prime power.* An element of W whose order is divisible by ℓ^b
   has a cycle of length divisible by ℓ^b, so ℓ^b ≤ max k_i ([CSC] §3).
   Hence e ≥ 6. Also, P ≠ A_3 or e ≠ 6, since 6 divides no element order
   in S_3.
2. *F(g^{N/e}) = 0.* g^{N/e} has order e > max k_i. Its cycles on the copies
   have length ≤ max k_i < e, so they are not all of length e. By Lemma 1,
   F(g^{N/e}) = 0. F is a class function, so it does not matter that g is
   only conjugate into W.
3. *X_P(ω^{N/e}) ≠ 0.* ω^{N/e} = e^{2πi/e}, so Theorem G applies. ∎

Combined with [CSC] Theorem C (sufficiency, and necessity of (b)):

**Theorem C, complete form (PROVEN).** For g ∈ Aut(P) conjugate into W,
X_P sieves ⟨g⟩ iff, for every divisor e > 1 of o(g), (a) e ≤ max k_i
holds, and (b) holds.

**Consistency with the computed data (COMPUTED).**
- *The (a)-only classes of [CSC].* Of the 6 classes where (a) is the only
  failing clause, the 4 with gcd > 1 are A_5 with copy-cycle type (2, 3),
  A_7 with (2, 5) and (3, 4), and A_8 with (3, 5). `[brute]` recomputes them
  by brute force: the CSP fails, F(g^{N/e}) = 0, and |X_P(ζ_e)| = 6, 49.8,
  131.6 and 1079 respectively.
- *Two more classes.* A_3 ⊔ C_2^{⊔3} with (3), (2, 1) at e = 6 (gcd 3), and
  A_4 ⊔ C_2^{⊔2} with (3, 1), (2) at e = 6 (gcd 2). (b) also fails in
  these, so they test Theorem G rather than (a) alone.
- *[exact].* This check is independent of the proof. It reduces X_P mod Φ_e
  exactly and finds no zero. Its range is every type vector with at most
  3 types, K ≤ 12, m_i ≤ 3 and gcd ≥ 2 (199 vectors), with y ∈ {1, 2, 7}
  and every bad e: 2259 triples in all. It adds single types with
  k = 3, …, 20 and m = 1, 2 (548 triples). Positive control: in every
  Theorem B(ii) case (e ≤ max k_i, e ∤ some k_i), Φ_e divides X_P, and the
  check detects it in 2235/2235.

## 5. What the controls show

Each computed claim has a control that must fail:
- `[eC]`: e_C(C_2 ⊔ C_2) = 5, and 6 is rejected.
- `[brute]`: the closed form without φ(d) disagrees with the Molien
  polynomial of A_5.
- `[phase]`: dropping the phases changes 80/112 values.
- `[ratio]` and `[yroot]`: the bound, and the conclusion itself, fail for
  y < 1.
- `[ineq]`: the no-phase sum over all d ≥ 2 is ≥ 1 in 11 triples. For A_5 at
  e = 6 it is 4, because d = 5 has the same phase as d = 1. So magnitude
  dominance alone does not prove Theorem G, and the phase restriction to D^−
  is needed.
- `[exact]`: the B(ii) zeros are detected.

The A_3 exception is the bound of Lemma 5 being attained, not a numerical
artefact. A floating-point exploration missed it, because 2 sin(π/6)
evaluates to 0.9999999999999999. The exact-rational check of part (iv)
found it.

## 6. Shared steps for the audit

The independent audit should check these, in this order:
- **S1.** (F_d), the multi-type Proposition 2 (§1).
- **S2.** The phase identity 1/(1 − ζ^p) = e^{i(π/2 − πp/e)}/(2 sin(πp/e)), and
  that every d | g is < e (§1, Lemma 3).
- **S3.** The projection inequality and the definition of D^− (§1).
- **S4.** The six inequalities of Lemma 4, especially the class-size bound
  (item 1) and the falling-factorial inequality (item 5). The only use of
  y ≥ 1 is in item 4.
- **S5.** Lemma 5. Check the analytic tails (i)–(iii′), and that part (iv)
  is rigorous: interval arithmetic, outward rounding, and exact Fractions
  (`sin_interval`, `C_upper`).
- **S6.** Lemma 6, and the realizability claims used in Corollary H: that a
  bad e is never a prime power, and that 6 is not an element order of S_3.

Not done here: no literature search was made for Theorem G or for the
phase argument. The argument is elementary, and no claim of novelty is made.

## References

[CSC] = `notes/cyclic_sieving_cyc.md`; [AUD] =
`notes/audit_cyclic_sieving_cyc.md`; [PACSC2] =
`notes/prior_art_cyclic_sieving_cyc_2.md` (Proposition E, §1); [AUD2] =
`notes/audit_prior_art_cyclic_sieving_cyc_2.md` (Proposition E HOLDS; fix F1);
[LE] = `notes/linear_extensions.md` (Proposition F); [GCD] = this note.

## Reproduce

From `compute/` (plain Python 3, no dependencies; about 9 s on one core):

    python3 cyclic_sieving_gcd.py > output/cyclic_sieving_gcd.txt
    python3 -m unittest test_cyclic_sieving_gcd

The script exits with status 0 iff every check holds and every positive
control fails as it must.
