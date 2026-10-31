# Audit: Theorem Ω and the statistic claims of linext_statistics.md

This is an independent adversarial audit of `notes/linext_statistics.md`
("[LS]"). Every proof below was re-derived by hand. Every number was
recomputed by `compute/audit_linext_statistics.py`, which was written for
this audit and imports nothing from the repository. In particular it does
not import `compute/linext_statistics.py`. It computes μ(π, 1̂) inside OP(P)
by the defining recursion, so it does not rely on Lemma U. It computes e_C
from rotations of words, so it does not rely on Theorem A. Output:
`compute/output/audit_linext_statistics.txt` and
`compute/output/audit_linext_statistics_des6.txt`.

Tags as in [LS]: [ME] = `notes/mu_op_elementary.md`, [GT] =
`notes/general_theory.md`, [Thm] = `notes/poset_jks_theorem.tex`, EC1 =
Stanley, *Enumerative Combinatorics* vol. 1.

## Verdict

| Claim of [LS] | Verdict |
|---|---|
| **Theorem Ω** (§2.1): Σ_{π∈OP(P)} \|μ(π,1̂)\| C(m,\|π\|) = #{f : P → [m] order-preserving : every nonempty upper level set that is a union of components contains T} | **HOLDS.** The proof is complete. All six steps re-derived (§1). COMPUTED for all 405 posets with n ≤ 6, every component T, m = 0, …, max(n, 4). That is enough points to make it an identity of polynomials. 3720/3720 agree. |
| Sign: (−1)^{\|π\|−1} μ(π, 1̂) = e_C(Q_π) > 0 | **HOLDS.** It follows from Lemma U and Theorem A on Q_π. COMPUTED for every π ∈ OP(P), n ≤ 6, with e_C(Q_π) counted from words. |
| The count does not depend on T | **HOLDS.** The Möbius side does not mention T. COMPUTED: the direct count is the same for every component, for all 405 posets. |
| Degree n, leading coefficient e_C(P)/n!; Ω_C = Ω for connected P | **HOLDS.** COMPUTED for the leading coefficient. |
| Antichain case: Ω_C = Σ_{j≤m} j^{n−1} | **HOLDS.** COMPUTED. |
| **Corollary Ω-des** (§2.2), with the merging at cuts and C(m+n−1−des−c, n−c) | **HOLDS** (§2). COMPUTED for every natural labelling with n ≤ 6 (4824 labelled posets at n = 6), every T, m = 0, …, n: 57,075/57,075. [LS] checked only the canonical labelling at n = 6. |
| §1.3: (−1)^{n−1} χ_P(−1) = e(P) is false except on antichains | **The refutation HOLDS.** C_3 gives 4 ≠ 1 by hand. COMPUTED: the identity holds on exactly the 5 antichains among the 404 posets with 2 ≤ n ≤ 6. I did not recompute n = 7. |
| §3: #{w ∈ Lin P : maj w ≡ 1 (mod n)} = e_C(P) is false | **The refutation HOLDS.** C_2 ⊔ C_1 is a counterexample by hand. COMPUTED: it holds on 6 of 2449 posets (2 ≤ n ≤ 7), as [LS] says. |
| §4: \|I(P)\| = e_C(P) is false | **The refutation HOLDS.** COMPUTED: 6 of 2449, as [LS] says. Already C_2 ⊔ C_1 has I = 0 and e_C = 2. |
| Prop. 3(a), the maj rotation lemma | **HOLDS.** Re-derived. COMPUTED on S_n for n ≤ 7. Control: with des in place of cdes it fails on 2956 of 5912 words. |
| Prop. 3(b), maj on Lin(P)C_n for prime n; 3(c), the composite failure | **HOLDS.** COMPUTED: (b) on 2115/2115 posets with n ∈ {2, 3, 5, 7}; (c) fails on 211 of 334 posets with n ∈ {4, 6}, as [LS] says. |
| Prop. 3′, maj equidistribution mod n when gcd(component sizes) = 1 | **HOLDS.** Re-derived through the q-multinomial. COMPUTED 485/485, as [LS] says. Control: it fails on 1871 of 1946 connected posets. |
| Prop. 4, the sign-imbalance factorisation | **HOLDS.** Re-derived. COMPUTED 503/503. |

**No claim FAILS.** I found one point to make explicit, and none that needs
a fix:
- (a) Step 4 of the proof of Theorem Ω cites [GT] Lemma 1.3 for the fact
  that rotating at a cut gives a word with the same pieces, cyclically
  rotated. [GT] Lemma 1.3 states this fact. The two-line argument is in §1
  below, and it would be worth one sentence in [LS].

The three refutations are counterexamples, not failed proofs. So no true
identity is discarded in the form [LS] states it. For each refuted claim I
also checked the nearest corrected form that [LS] mentions (§3).

## 1. Theorem Ω

Notation as in [LS] §0 and [ME] §0. A *cut* of a word u ∈ Lin Q is an
index 0 < j < |u| such that the prefix u_1⋯u_j is a union of components of
Q. The *pieces* of u are the segments between consecutive cuts.

**Step 1 (coefficients).** By Lemma U, [π, 1̂] ≅ OP(Q_π). By Theorem A on
Q_π, which has |π| ≥ 1 points, μ(π, 1̂) = (−1)^{|π|−1} e_C(Q_π). So the
summand is |μ(π, 1̂)| = e_C(Q_π) ≥ 1. In particular the "|μ|" of the ticket
and the "(−1)^{|π|−1} μ" of [LS] are the same number, and it is never zero.
Lemma U and Theorem A have both been audited ([AudME]); I recomputed both
consequences here without using them (`[omega-sign]`).

**Step 2 (triples).** Let f : P → [m] be order-preserving and let σ be its
partition into nonempty fibres. If x <_P y lie in different fibres, then
f(x) < f(y). So every edge of P/σ goes up in value, P/σ is acyclic, σ ∈ OP(P),
and listing the fibres by value gives u ∈ Lin Q_σ. Conversely, (σ, u, S)
with |S| = |σ| determines f. This is a bijection.

**Step 3 (cuts of u are cuts of P).** For a set X of blocks of σ, write ∪X
for the union of those blocks. Then X has no Q_σ-relation to its complement
iff ∪X has no P-relation to its complement. A Q_σ-relation is a directed
path in P/σ, and such a path between X and its complement contains an edge
of P/σ that crosses, which comes from a crossing P-relation. Conversely a
crossing P-relation gives a crossing edge of P/σ. The same argument shows
that the blocks meeting a component T of P lie in a single component T_σ of
Q_σ. Correct.

**Step 4 (one rotation per class).** By [Thm] Lemma `lem:rot`, the members
of the class of u that lie in Lin Q_σ are the rotations of u at its cuts.
Let u = p_1 ⋯ p_r be the decomposition into pieces, and let u′ = p_{i+1} ⋯
p_r p_1 ⋯ p_i. The boundaries between the p's are cuts of u′, because each
is a difference of two nested unions of components. There is no other cut:
- Suppose a prefix X of u′ ends inside p_j with j > i. Then X ∪ (p_1 ⋯ p_i)
  is a prefix of u that is a union of components and ends inside p_j.
- Suppose X ends inside p_j with j ≤ i. Then the complement of X is a final
  segment of p_1 ⋯ p_i, and removing it from p_1 ⋯ p_i leaves a prefix of u
  that is a union of components and ends inside p_j.

Either way u would have a cut inside a piece, which is impossible. So the
class is the r cyclic rotations of the piece sequence. They are distinct
words, because the letters are distinct. Every piece is a union of
Q_σ-components, so T_σ lies in a single piece. Exactly one rotation has
that piece last. This is what [GT] Lemma 1.3 states, and the step is
correct.

**Step 5 (translation).** The nonempty upper level sets of f are the
suffixes F_{j+1} ∪ ⋯ ∪ F_k for 0 ≤ j < k. By Step 3, such a suffix is a
union of components of P iff j = 0 or j is a cut of u. A union of
components either contains T or misses it. So the condition "every such
suffix contains T" says that T meets the last piece, i.e. that the last
piece contains T_σ. Correct.

**Step 6 (sum).** Summing over σ with C(m, |σ|) choices of S gives the
count. The coefficient of C(m, n) comes only from σ = 0̂, where Q_σ ≅ P, and
it is e_C(P). Since C(m, n) = m^n/n! + lower terms, the degree is n and the
leading coefficient is e_C(P)/n!. For connected P the only union of
components that is an upper level set is P itself, so Ω_C = Ω. At m = 0
both sides are 0 for n ≥ 1.

**T-independence.** The Möbius side does not involve T, so neither does
the count. A bijective explanation is not needed for the claim, and [LS]
does not give one.

**Computation** (`[omega]`, `[omega-poly]`). The Möbius side, with μ
computed inside OP(P), against the direct count over order-preserving maps.
This was done for all 405 posets with 1 ≤ n ≤ 6 (1, 2, 5, 16, 63, 318 by n,
which is OEIS A000112), every component T, and m = 0, …, max(n, 4). There
are 3720/3720 agreements. Both sides are polynomials in m of degree ≤ n, so
agreement at m = 0, …, n is an identity of polynomials.

**Controls** (each must fail somewhere, and each does; counts are over the
2775 triples (P, T, m) with m ≤ 4):

| Control | Fails on |
|---|---|
| drop the T condition, i.e. count Ω(P, m) | 774 |
| \|μ(0̂, π)\| in place of \|μ(π, 1̂)\| | 2181 |
| "max f is attained on T" | 483 |
| require T in *every* nonempty upper level set | 1602 |

The last control shows that the restriction to level sets that are unions
of components does real work.

I also checked the antichain case Σ_k S(n,k)(k−1)! C(m,k) = Σ_{j≤m} j^{n−1}
(`[omega-antichain]`), the h_C table of [LS] §2.2 (all five rows agree), and
h_C ≥ 0 on all 405 posets with n ≤ 6 (this is consistent with [LS]
`[omegaC-h]`, which is still OPEN as a theorem). The transparent example of
[LS] §2.2 also checks: P = {0<2} ⊔ {1<4} ⊔ {3}, T = {1, 4}, fibres
{0,1,4} < {2,3}, satisfies the condition.

## 2. Corollary Ω-des

Stanley's lemma (EC1 Lemma 3.15.3) gives a bijection between order-preserving
f and pairs (w, f). Here w ∈ Lin P is the word sorted by f, with ties broken
by increasing label, and f is weakly increasing along w and strictly
increasing at Des(w). Re-derivation:
- The nonempty upper level sets of f are P together with the suffixes
  w_{p+1} ⋯ w_n at the positions p where f(w_p) < f(w_{p+1}).
- Such a suffix is a union of components iff p is a cut of w. It misses T
  iff T ⊆ {w_1, …, w_p}, i.e. iff p ∈ C_T(w).
- So the condition of Theorem Ω says f(w_p) = f(w_{p+1}) for every
  p ∈ C_T(w). That is incompatible with a descent at p, so w contributes 0
  when C_T(w) ∩ Des(w) ≠ ∅.
- Otherwise, identify positions p and p+1 for each p ∈ C_T(w). This leaves
  L = n − c positions, weakly increasing, strict at the des(w) descents,
  which are disjoint from the merged positions. Subtracting i from the
  value at the position after the i-th strict step turns these into weakly
  increasing sequences of length L in [m − des]. There are
  C(m − des + L − 1, L) = C(m + n − 1 − des − c, n − c) of them.

Correct, including the merging. COMPUTED (`[omega-des]`) for every natural
labelling with n ≤ 6, every T, m = 0, …, n: 4015/4015 cases with n ≤ 5 and
57,075/57,075 with n ≤ 6. This is stronger than [LS], which checked all
labellings only up to n = 5. Controls: dropping the −c merging fails on
10,454 cases, and keeping the words with C_T ∩ Des ≠ ∅ fails on 23,567.

## 3. The three refutations

**§1.3, χ_P(−1).** For C_3, OP(C_3) consists of the four interval
partitions. It is B_2, and χ = t² − 2t + 1, so (−1)^{n−1}χ(−1) = 4 ≠ 1 =
e(C_3). COMPUTED: among the 404 posets with 2 ≤ n ≤ 6 the identity holds on
exactly the 5 antichains (`[chi-refute]`). [LS] reports 6 of 2449 with
n ≤ 7, which is consistent; I did not recompute n = 7. The corrected form
that [LS] cites, Σ_{σ≥κ} (−1)^{|σ|} μ(0̂, σ) = (−1)^n e(P), holds on all 404
(`[chi-restr]`). So the refutation removes only the unrestricted version.

**§3, KW at the dimension level on Lin P.** C_2 ⊔ C_1 with relation 0 < 1:
Lin P = {012, 021, 201}, with maj values 0, 2, 1. One word has
maj ≡ 1 (mod 3), but e_C = 2 (`[ex]`). COMPUTED: 6 of 2449 (`[kw-refute]`).
The nearest corrected form is Prop. 3(b), which is on Lin(P)C_n and holds
for prime n. I also checked whether the residue r = 1 alone (the actual KW
residue) survives on Lin(P)C_n at composite n. It does not: it fails on 185
of the 334 posets with n ∈ {4, 6}. So [LS] discards nothing true here.

**§4, |I(P)| = e_C(P).** COMPUTED: 6 of 2449 (`[sgn-refute]`). For example
C_2 ⊔ C_1 is sign-balanced by Prop. 4 (two odd components), while e_C = 2.

## 4. Propositions 3, 3′, 4

**Prop. 3(a).** Write w = a v. Then
- maj(a v) = [a > v_1] + maj(v) + des(v);
- maj(v a) = maj(v) + (n−1)[v_{n−1} > a].

So maj(va) − maj(av) ≡ −([a > v_1] + des(v) + [v_{n−1} > a]) = −cdes(w)
(mod n). The cyclic descent set rotates with w, so cdes is invariant.
Correct.

**Prop. 3(b).** Lin(P)C_n is the union of the e_C(P) rotation classes
meeting Lin P. Each class has size n, since the letters are distinct. A
cyclic arrangement of distinct letters has at least one cyclic descent and
at least one cyclic ascent, so 1 ≤ cdes ≤ n − 1. When n is prime, cdes is
then a unit mod n, and each orbit meets each residue exactly once. Correct.
For n = 1 the statement is trivial.

**Prop. 3′.** The P-partition generating function is multiplicative over
components, so W_P(q) = [n; m_1, …, m_k]_q ∏ W_{T_i}(q). At a primitive d-th
root of unity with d | n and d > 1, the q-multinomial vanishes to order
n/d − Σ ⌊m_i/d⌋. That order is positive unless d divides every m_i, which
gcd = 1 rules out. So W_P(ζ) = 0 for every n-th root of unity ζ ≠ 1, and
this is equidistribution mod n. The W_{T_i} are polynomials, so there is no
cancelling pole. Correct. The labelling-independence of W_P for natural
labellings, which this uses, is EC1 §3.15 (CITED in [LS], not re-checked).

**Prop. 4.** Some natural labelling puts the components on consecutive
intervals of labels: label each component naturally inside its own
interval. For that labelling, a pair from different components is an
inversion of w iff its pattern letters are inverted. So
I(P) = [n; m]_{q=−1} ∏ I(T_i). Relabelling multiplies every sign by one
fixed sign, so |I(P)| is the same for every natural labelling. The
q-multinomial at q = −1 is 0 when two m_i are odd: the order of vanishing
at d = 2 is ⌊n/2⌋ − Σ⌊m_i/2⌋ = (number of odd m_i − [n odd])/2 > 0. Correct.
COMPUTED 503/503 (`[p4]`), with |I(T_i)| computed separately for each
component.

## 5. Scope

Not re-checked: the prior-art statements (NOT FOUND, KNOWN IN SUBSTANCE),
§5 of [LS] (the descent algebra), §6, and the B_P control counts 708 and
811 of [LS] §2.2. The claim that the n = 7 χ count is 6 of 2449 was not
recomputed. The n ≤ 7 counts for the KW and sign refutations and for
Props. 3–4 were recomputed and agree with [LS].

[AudME] = `notes/audit_mu_op_elementary.md`.

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core):

    python3 audit_linext_statistics.py > output/audit_linext_statistics.txt   # about 30 s
    python3 -c "import audit_linext_statistics as A; A.sec_omega_des(6); print(A.FAILS, A.CONTROLS_UNREFUTED)" > output/audit_linext_statistics_des6.txt   # about 5 min

The first command exits with status 0 iff every CLAIM line holds and every
CONTROL line is refuted somewhere. Options: `--nmax` (default 6) sets the
largest n for the Möbius and χ sections, `--mmax` (default 4) the largest
m for the direct count, `--lmax` (default 5) the largest n for
all-labellings Ω-des, and `--n7` (default 7) the largest n for the Lin P
sections.
