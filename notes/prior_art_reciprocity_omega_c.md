# Prior art for reciprocity of the cyclic order polynomial (Theorems R, R′, ★, E, S, S′, U)

This note checks the claims of `notes/reciprocity_omega_c.md` ([R]) against
the literature. The claims are:
- **R**: (−1)^n Ω_C(P, −m) = Ω̄_C(P, m), the number of strictly
  order-preserving f : P → [m] such that no T-free cluster U has
  min f(U) ≥ max f(P ∖ U) (the condition D_T). This includes Lemmas R1 and R2.
- **R′**: the cdes form of R.
- **★**: Ω_C(P*, m) = Ω_C(P, m).
- **E**: Ehrhart–Macdonald reciprocity for the non-convex anchored region R_T.
- **S**: if every component has height ≤ 2, then Ω̄_C(P, m) = Ω_C(P, m − 1)
  and h_C is palindromic.
- **S′**: h_C is palindromic iff P is connected and graded, or every
  component has height ≤ 2.
- **U**: h_C is unimodal.

[R]'s own prior-art pass (its §7) was two web queries. This is the full pass.

Verdicts are search results:
- **KNOWN**: stated in a source read here, with the exact reference.
- **KNOWN IN SUBSTANCE**: a special case, or the same mechanism, is in a
  source read here.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.

Computations are in `compute/prior_art_reciprocity_omega_c.py`, which
imports nothing from the repository. It computes Ω_C from the counting side
of Theorem Ω ([LS] §2, PROVEN + audited). It counts multichains of order
ideals that avoid the "bad" ideals, so it uses no words, no labellings and
no Möbius function of OP(P). It computes W_P by a separate dynamic
programme over linear extensions. Bracketed tags such as `[two-comp]` are
line labels in `compute/output/prior_art_reciprocity_omega_c.txt`.

## Verdict

| Claim of [R] | Verdict | Closest prior art (read) |
|---|---|---|
| **R**, connected P | **KNOWN.** This is Stanley's reciprocity for order polynomials | EC1 Cor. 3.15.12; Stanley 1974, Prop. 2.1; Beck–Sanyal Thm 1.3.2 |
| **R**, antichain | **KNOWN** (classical). R becomes S_k(−N) = (−1)^{k+1} S_k(N − 1) for power sums | [R] §2. Ω_C(A_n) is [Pet] Prop. 1.1 ([PA]) |
| **R**, polynomial identity given B⁺ | **KNOWN IN SUBSTANCE.** Stanley's reciprocity holds word by word: EC1 Lemma 3.15.9 for one w, then Lemma 3.15.11. So it holds for any set of words, B_T included. In QSym language, ps¹(f)(−m) = ps¹(S f)(m) and S(F_w) = (−1)^n F_{w^opp}. Applied to K_C = Σ_{w∈B_T} F_{Des w} (row F+ of [Q]), this gives the polynomial side of R with no further work | EC1 Lemmas 3.15.9, 3.15.11; [GR] Prop. 5.2.19, Cor. 5.2.20, Prop. 7.1.7(iii) |
| **R**, combinatorial reading: Ω̄_C counts strict maps with D_T, for disconnected P | **NOT FOUND.** No source read has a strict anchoring condition, or any reciprocity for a cyclic or anchored order polynomial. This content is Lemma R2: under λ_T the strict words in B_T are exactly the strict maps with D_T. [Pet], [DMR] and [AGRR] contain no reciprocity statement at all (§1). Re-checked here by brute-force enumeration of strict maps, independently of [R]'s code: 714/714 triples (P, T, m), n ≤ 5 `[recip-bf]`; naive control refuted `[ctl-naive]` | — |
| **R1** | **KNOWN IN SUBSTANCE.** This is row F+ of [Q], already audited as KNOWN IN SUBSTANCE (Gessel–Stanley fundamental lemma with the anchor labelled last; Petersen's Prop. 1.1 move) | [AudQ] Verdicts, row F+ |
| **R2** | **NOT FOUND** | — |
| **R′** | **NOT FOUND** for general P. It is R combined with Theorem H, which [PA] already found NOT FOUND. Antichain case: classical (Ω̄_C(A_n, m) = Σ_{j<m} j^{n−1}) | [PA] |
| **★** Ω_C(P*) = Ω_C(P) | **KNOWN IN SUBSTANCE.** The connected case is the classical Ω(P*, m) = Ω(P, m), via f ↦ m + 1 − f. No source states it for Ω_C, because no source defines Ω_C ([PA]). [R]'s proof (quotient acyclicity is invariant under reversing arrows) is one line | EC1 §3.15; Beck–Sanyal §1.3 |
| **E** | **Mechanism KNOWN IN SUBSTANCE; the statement for R_T is NOT FOUND.** R_T is a union of half-open unimodular simplices, one per w ∈ B_T. Per-simplex reciprocity with complementary half-openness is Beck–Sanyal Prop. 5.3.6 / Thm 5.3.7, and the order-polytope instance is their (6.3.6) and Thm 6.3.11. Macdonald's reciprocity for rational cell complexes whose support is a manifold with boundary is Stanley 1974 Prop. 6.1 (after Macdonald). It would give E only if R_T were a manifold, which is open ([R] §5). The new content is Prop. E itself: the union of the opposite half-open cells is the interior of R_T | Stanley 1974 §6; Beck–Sanyal §§5.3, 5.6, 6.3, Notes to Ch. 5 |
| **S**, connected P | **KNOWN.** A connected poset of height ≤ 2 with n ≥ 2 is graded of rank 1, so S is Stanley's rank-shift bijection σ ↦ σ + δ | EC1 Lemma 3.15.17(b), Cor. 3.15.18(b); Stanley 1974 §2, eq. (4) |
| **S**, antichain | **KNOWN.** h_C(A_n) is the Eulerian polynomial of S_{n−1} ([Pet] Prop. 1.1), and Eulerian polynomials are palindromic | Beck–Sanyal Ex. 6.28; `[antichain]` |
| **S**, general disconnected P of height ≤ 2 | **NOT FOUND.** The mechanism is Stanley's rank shift plus [R]'s unit shift at the anchor | — |
| **S′**, connected P | **KNOWN.** For connected P, h_C = W_P (checked on all 1947 connected posets with n ≤ 7 `[connected=W]`). W_P is palindromic iff P is graded: Beck–Sanyal Ex. 6.27 states this verbatim. Stanley's source is EC1 Cor. 3.15.18(b) (graded ⇔ Ω_P(−ℓ − m) = (−1)^p Ω_P(m) for all m), which goes back to Stanley's 1972 Memoir, Prop. 19.3, as cited in Stanley 1974 §2. **Correction to [R] §6:** do not cite EC1 Thm 3.15.16 for this. That theorem concerns the *maj* generating function and the δ-chain condition | EC1 Cor. 3.15.18; Beck–Sanyal Ex. 6.27 |
| **S′**, disconnected P, "if" | Same as S (NOT FOUND for general P) | — |
| **S′**, disconnected P, "only if" | **NOT FOUND.** It remains OPEN, as in [R] | — |
| **U**, connected P | **KNOWN OPEN.** For connected P, h_C = W_P, so U contains the unimodality of W_P for every naturally labelled poset. That is the surviving weak form of the Neggers–Stanley conjecture, and it is open. It is proved for graded P (Reiner–Welker 2005; Brändén 2004, sign-graded) and for width two (W_P is ultra-log-concave, Alexandersson–Jal) | [AJ] §1.1; [Br-sg] Abstract; EC1 Ex. 3.165 and Ex. 3.173 solutions |
| **U**, general P | **OPEN, and at least as hard as the connected case.** A proof of U for all P would settle the open question above. COMPUTED here: h_C is unimodal **and log-concave** on all 2450 posets with n ≤ 7 `[unimodal]` `[log-concave]` | — |
| h_C real-rooted (not claimed in [R]) | **FALSE.** Stembridge's 17-element naturally labelled poset S is connected, so h_C(S) = W_S, which has non-real zeros. Yet h_C is real-rooted on all 2450 posets with n ≤ 7 `[real-rooted]` | EC1 Ex. 3.165 solution, Fig. 3.88; Stembridge, Trans. AMS 359 (2007) (not read, see §0) |

**Is U at risk from the Neggers–Stanley counterexamples? No, not from any
known one** (§5):
- They are counterexamples to *real-rootedness*, not to unimodality.
- Brändén's are not naturally labelled ([Br] Remark 1). Their shape
  W(m ⊔ n) − 1 does reappear in h_C, as h_C(C_m ⊔ C_n) = W(m ⊔ n) − t.
  That polynomial is real-rooted for all 1 ≤ m ≤ n ≤ 30 `[chains-rr]`.
- Stembridge's S (EC1 Fig. 3.88, reconstructed here and matched against
  Stanley's printed A_S(x) `[stembridge-W]`) gives a unimodal and log-concave
  h_C(S). For S ⊔ C_1, S ⊔ C_2, S ⊔ C_3, S ⊔ A_2 and S ⊔ C_2 ⊔ C_1, h_C is
  unimodal, log-concave and even real-rooted `[stembridge0+…]`.

**New in this pass (elementary, PROVEN in §5 and COMPUTED).** For two components,

  h_C(Q ⊔ T)(t) = W_{Q⊔T}(t) − t · W_Q(t) · W_T(t).

This holds on all 391 two-component posets with n ≤ 7 `[two-comp]` and on
S ⊔ C_2 (n = 19) `[stembridge0+C2-identity]`. It writes h_C as a difference
of W-polynomials, which is the same shape as Brändén's counterexamples.

**Bottom line.**
- The *polynomial* half of Theorem R is Stanley's word-by-word reciprocity
  (EC1 Lemma 3.15.9), equivalently the QSym antipode, applied to the word
  set B_T. What is new is its *combinatorial* half: the strict anchoring
  D_T and Lemma R2. No source states it.
- The connected cases of R, S and S′ are Stanley's. Cite EC1 Cor. 3.15.12
  and Cor. 3.15.18, and Beck–Sanyal Ex. 6.27.
- [R] lists U as OPEN as if it were a new question. That undersells it: its
  connected case is an open problem in the Neggers–Stanley literature. [R]
  should say so, and should not call U a target for a general proof.

## 0. Sources read

- **[Pet]** T. K. Petersen, *Cyclic descents and P-partitions*,
  arXiv:math/0405479v2. Read in full, §§1–5. There is **no reciprocity
  section** and no negative-argument evaluation of any order polynomial.
  Its only order polynomials are Ω_π(k) for chains (type A, B and
  augmented), used for Theorems 1.1–1.5 (descent algebras). §5 (Future
  work) mentions peak algebras only.
- **[DMR]** M. Develin, M. Macauley, V. Reiner, *Toric partial orders*,
  arXiv:1211.4247v1. Searched in full for "reciprocity", "order polynomial"
  and "Ehrhart". The only hit is a bibliography entry (Edelman–Klingsberg). It
  has no order polynomial and no reciprocity theorem. ([PA] had already
  read it in full and shown that Ω_C is not a toric order polynomial.)
- **[AGRR]** R. M. Adin, I. M. Gessel, V. Reiner, Y. Roichman, *Cyclic
  quasi-symmetric functions*, arXiv:1811.05440v5. Searched in full for
  "reciprocity", "antipode", "order polynomial" and "principal
  specialization". Read §3.4 (the involution ω, Lemma 3.27: ω preserves
  cQSym) and §7 (the open problem on principal specialization). It has no
  reciprocity statement.
- **[BS]** M. Beck, R. Sanyal, *Combinatorial Reciprocity Theorems*
  (AMS 2018; beta version of 4 Oct 2018, matthbeck.github.io/papers/crt.pdf).
  Read: §1.3 (Thm 1.3.2), §2.2 (Thm 2.2.2: μ_{J(P)}), §§5.3–5.4 (half-open
  decompositions, Thm 5.3.7, Stanley reciprocity), §5.6 (self-reciprocal
  and Eulerian complexes, Thms 5.6.2, 5.6.4) with the Notes to Ch. 5,
  §6.3 (Thm 6.3.11, (6.3.6)), §6.4 and Exercises 6.27, 6.28. There is no
  reciprocity for a non-convex region other than complexes (Thm 5.6.4:
  Eulerian complexes are self-reciprocal; Notes: Thm 5.2.1 holds for
  complexes homeomorphic to a ball). There is nothing on cyclic or
  anchored order polynomials.
- **[St74]** R. P. Stanley, *Combinatorial reciprocity theorems*, Adv.
  Math. 14 (1974) 194–253 (math.mit.edu/~rstan/pubs/pubfiles/22.pdf).
  Read §2 in full: Prop. 2.1, both proofs (the Möbius function on J(P) and
  the word proof, Lemma 2.2), and eq. (4) with its graded converse cited
  to the 1972 Memoir, Prop. 19.3. Read §6 (Prop. 6.1, Macdonald
  reciprocity for rational cell complexes that are manifolds with
  boundary).
- **[EC1]** R. P. Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed.
  (version of 15 July 2011). Read §3.15.3 (Lemma 3.15.9, Thm 3.15.10,
  Lemma 3.15.11, Cor. 3.15.12), §3.15.4 (Thm 3.15.16, Lemma 3.15.17,
  Cor. 3.15.18), and the solutions to Exercises 3.165 and 3.173 together
  with Fig. 3.88.
- **[GR]** D. Grinberg, V. Reiner, *Hopf algebras in combinatorics*,
  arXiv:1409.8356v7. Read Prop. 5.2.15 ((5.2.7) S(L_α) = (−1)^{|α|} L_{ω(α)}),
  Prop. 5.2.19, Cor. 5.2.20 and Remark 5.2.21 (Malvenuto–Reutenauer), and
  Prop. 7.1.7 (ps¹ and the antipode: ps¹(f)(−m) = ps¹(S f)(m)).
- **[Br]** P. Brändén, *Counterexamples to the Neggers–Stanley conjecture*,
  arXiv:math/0408312v2 (ERA-AMS 10 (2004)). Read in full.
- **[Br-sg]** P. Brändén, *Sign-graded posets, unimodality of
  W-polynomials and the Charney–Davis conjecture*, arXiv:math/0406019v3.
  Read the abstract, §1 and the statements of §§2 and 4.
- **[AJ]** P. Alexandersson, A. Jal, *Rook matroids and log-concavity of
  P-Eulerian polynomials*, arXiv:2410.00127v3. Read the abstract, §1 and
  §5.1 (the history of the Neggers–Stanley conjecture).
- **Not read** (no free copy fetched; cited only through the sources
  above): Stembridge, Trans. AMS 359 (2007) 1115–1128; Reiner–Welker, JCTA
  109 (2005); Brenti, Mem. AMS 413 (1989); Stanley's 1972 Memoir. Their
  content is quoted here only as reported by EC1 (Ex. 3.165, 3.173
  solutions), [Br], [Br-sg] and [AJ].
- **Searched** (arXiv API, 2026-10-31): "Neggers", "Neggers-Stanley",
  "P-Eulerian", "sign-graded posets", and Stembridge × poset. The hits
  used are listed above. None mentions cyclic, toric or anchored order
  polynomials together with reciprocity.

Repository notes used: [R] = `notes/reciprocity_omega_c.md`;
[LS] = `notes/linext_statistics.md`; [PA] = `notes/prior_art_linext_statistics.md`;
[Q] = `notes/qsym_refinement_omega_c.md`; [AudQ] = `notes/audit_qsym_refinement_omega_c.md`.

## 1. Theorem R and Lemmas R1, R2

**The polynomial identity is word by word.** EC1 Lemma 3.15.9 states that
for a single permutation w, x_1⋯x_p F_w(x) = (−1)^p F_{w̄}(1/x), where w̄ has
the complementary descent set. Lemma 3.15.11 turns this into
f(−m) ↔ −H(1/x) for any polynomial. Thm 3.15.10 and Cor. 3.15.12 then sum
over the Jordan–Hölder set, but nothing in the argument uses that the set
is all of L(P, ω). So for any set B of words,

  Σ_{w∈B} C(−m + n − 1 − des w, n) = (−1)^n Σ_{w∈B} C(m + des w, n).

This is [R]'s displayed term-by-term step. [GR] packages the same fact as
ps¹(f)(−m) = ps¹(S f)(m) (Prop. 7.1.7(iii)), with S(F_w) = (−1)^n F_{w^opp}
(Prop. 5.2.19). Applied to f = K_{C,T}(P) = Σ_{w∈B_T} F_{Des w}, which is
[Q]'s F+ under λ_T, this gives

  (−1)^n Ω_C(P, −m) = ps¹(Σ_{w∈B_T} F_{w^opp})(m).

So the *polynomial* side of R is KNOWN IN SUBSTANCE once B⁺ / F+ is in
hand.

**What is not in the literature** is the right-hand side read as maps: the
strict maps whose strict Stanley word lies in B_T are exactly the strict
maps satisfying D_T (Lemma R2). [R]'s control `[ctl-lemma-any]` shows this
depends on λ_T. No source read defines an anchoring condition, strict or
weak.

**Searched for and absent.**
- [Pet] has no reciprocity section (checked in full).
- [DMR] and [AGRR] have none either. [AGRR] has the involution ω on
  cQSym (Lemma 3.27), which is the QSym shadow of complementing descent
  sets, but it never specialises it to order polynomials.
- [BS] treats reciprocity for posets only for Ω_P and Ω°_P (Thm 1.3.2,
  §6.4).

**Independent re-check.** `[recip-bf]` evaluates Ω_C at −m by Lagrange
interpolation of the Theorem Ω counts. It compares the result with a
literal enumeration of strict maps P → [m] satisfying D_T (every U tested).
It agrees on 714 of 714 triples (P, T, m) with n ≤ 5 and m ≤ n + 1. The
naive transplant (strict maps, anchoring with >) fails `[ctl-naive]`.

*Remark (a second route, not carried out).* Stanley's *first* proof of
Prop. 2.1 in [St74] works in J(P): Ω(P, m) = ζ^m(∅, P) and
(−1)^p Ω̄(P, m) = μ^m(∅, P). Theorem Ω says Ω_C(P, m) = ζ^m(∅, P) in the
induced subposet J_T = J(P) ∖ {proper unions of components containing T}.
This is exactly how `[T-indep]` computes it here. So
(−1)^n Ω_C(P, −m) = (−1)^n μ_{J_T}^m(∅, P), and Theorem R amounts to a
formula for μ_{J_T}. That would give a word-free proof of R if μ_{J_T} can
be computed. [BS] Thm 2.2.2 computes μ only for J(P) itself; μ_{J_T} was
not computed here.

## 2. Duality ★

Ω(P*, m) = Ω(P, m) via σ ↦ m + 1 − σ is standard. EC1 and [BS] use it
implicitly: [BS] §6.4 passes between order-preserving and order-reversing
maps, Thms 6.4.8–6.4.9. Ω_C is not defined in any source read ([PA]), so
★ for disconnected P cannot be stated there. Verdict: **KNOWN IN SUBSTANCE**
(the connected case), with a one-line proof in [R].

[R]'s observation that h_C(P*) is *not* the reverse of h_C(P) has no
counterpart in the literature. It is consistent with the classical fact
W_{P*} = W_P for natural labellings.

## 3. The Ehrhart reading E

- **Reciprocity for complexes.** [St74] Prop. 6.1 (Macdonald) gives
  j(n) = (−1)^d i(−n) for a rational cell complex whose support is a
  d-manifold with boundary. [BS] proves the Eulerian-complex case
  (Thm 5.6.4). The Notes to Ch. 5 say that Thm 5.2.1 extends to complexes
  homeomorphic to a ball, but by topology. R_T is a pure n-dimensional
  union of unimodular simplices. If |R_T| is a manifold with boundary,
  [St74] Prop. 6.1 gives E directly. [R] leaves that open.
- **The half-open mechanism.** The cell of w in [R] §5 is the half-open
  unimodular simplex H_φ Δ_w of [BS] (6.3.6), strict at descents. Its
  reciprocal is the simplex with the complementary half-openness, strict
  at ascents ([BS] Prop. 5.3.6, Lemma 5.5.4). Summing over w ∈ B_T gives
  L_{R_T}(−t) = (−1)^n Σ_{w∈B_T} L_{H̄Δ_w}(t) for *any* B_T. This is KNOWN
  IN SUBSTANCE ([BS] Thm 5.3.7 is the convex version).
- **What is new** is that ⊔_{w∈B_T} H̄Δ_w is the interior of R_T
  (Prop. E). That is the geometric form of Lemma R2. It is **NOT FOUND**.

## 4. Palindromicity S, S′

**The exact source for the connected case.** For connected P, h_C = W_P
(`[connected=W]`, 1947 of 1947 connected posets with n ≤ 7). Then:
- EC1 Cor. 3.15.18(b): P is graded ⇔ Ω_P(−ℓ − m) = (−1)^p Ω_P(m) for all
  m ∈ Z. With Cor. 3.15.12 this says Ω̄_P(m) = Ω_P(m − ℓ), and by
  Lemma 3.15.11 that is palindromicity of the h-numerator.
- EC1's solution to Ex. 3.173 says explicitly: "Symmetry of the
  coefficients also follows from Corollary 3.15.18 and Corollary 4.2.4(iii)."
- [BS] Exercise 6.27 states the iff directly: the numerator of
  Σ Ω_P(n) z^{n−1} is palindromic if and only if P is graded.
- The original source is Stanley's 1972 Memoir, Prop. 19.3, as cited in
  [St74] §2 after eq. (4).

EC1 Thm 3.15.16 (the δ-chain condition) is about W_P(x) = Σ x^{maj}, a
different polynomial. [R] §6 cites "EC1 §3.15" without a number; the
number to cite is **Cor. 3.15.18**.

**S.**
- *Connected P:* a connected poset of height ≤ 2 with n ≥ 2 is graded of
  rank 1. [R]'s bijection is then EC1 Lemma 3.15.17's θ: σ ↦ σ + δ.
  KNOWN.
- *Antichain:* the Eulerian polynomial ([BS] Ex. 6.28). KNOWN.
- *General disconnected P of height ≤ 2:* NOT FOUND. The mechanism is
  Stanley's shift plus a unit shift at the anchor.

**S′ "only if" (disconnected).** NOT FOUND. It stays OPEN.

## 5. Unimodality U and the Neggers–Stanley conjecture

**Status in the literature.**
- Neggers (1978) conjectured that W_P is real-rooted for naturally
  labelled P. Stanley (1986) extended this to all labellings. Brenti
  (1989) gave the first published statement (EC1, solution to Ex. 3.165).
- Brändén disproved Stanley's labelled version: W(P_{m,n}) = W(m ⊔ n) − 1
  with a non-natural labelling ([Br] Thm 1, Remark 1).
- Stembridge disproved Neggers' natural version with a 17-element poset
  (EC1 Ex. 3.165 solution and Fig. 3.88).
- Unimodality and log-concavity of W_P for naturally labelled P "has
  remained open" ([AJ] §1.1). It is proved for graded P (Reiner–Welker,
  JCTA 109 (2005); [Br-sg], sign-graded) and for width two ([AJ]: W_P is
  ultra-log-concave).

**Consequence for U.** For connected P, h_C(P) = W_P. So U restricted to
connected posets *is* the open unimodality question for naturally
labelled W_P. [R]'s "U: OPEN" is correct, but it should cite this: U for
all P implies an open problem, so it is not a realistic general target.
A tractable form would be relative: "if W_K is unimodal for each
component K, then h_C(P) is unimodal".

**Are the known counterexamples a risk to U? COMPUTED: no.**
- *Stembridge's poset S.* It was reconstructed from EC1 Fig. 3.88: two
  chains L_1 < ⋯ < L_9 and R_1 < ⋯ < R_8, with R_i < L_{i+1} for i ≤ 6,
  R_7 < L_9, and L_1 < R_6, L_2 < R_7, L_3 < R_8. The three long edges are
  hard to read, so all 255 readings of up to four edges L_a < R_b
  (a ≤ 3, b ≥ 6) were tried. Exactly 4 reproduce Stanley's printed
  A_S(x) = x + 32x² + 336x³ + 1420x⁴ + 2534x⁵ + 1946x⁶ + 658x⁷ + 86x⁸ + 3x⁹,
  and all 4 are the same poset (they differ only by relations implied by
  transitivity) `[stembridge-W]`. Then:
  - W_S is detected as not real-rooted. This is the positive control for
    the Sturm test.
  - W_S is unimodal and log-concave `[stembridge0-props]`.
  - h_C(S) = W_S `[stembridge0-hC]`. So **"h_C is real-rooted" is false at
    n = 17**, although it holds on all 2450 posets with n ≤ 7.
  - For S ⊔ X with X ∈ {C_1, C_2, C_3, A_2, C_2 ⊔ C_1} (n = 18 to 20),
    h_C is independent of T, unimodal, log-concave, and real-rooted
    `[stembridge0+C1]` … `[stembridge0+C2+C1]`.
- *Brändén's family.* It is not naturally labelled, so it does not enter
  h_C directly. But the two-component identity below gives
  h_C(C_m ⊔ C_n) = W(m ⊔ n) − t = Σ_k C(m,k)C(n,k) t^k − t. This is
  checked against the Theorem Ω count for m, n ≤ 6 `[chains-formula]`.
  Brändén's W(m ⊔ n) − 1 loses real-rootedness for large m, n ([Br]
  Thm 1). His argument does not transfer: under his scaling t ↦ t/mn,
  W(m ⊔ n) − 1 tends to F(z) − 1 = Σ_{k≥1} z^k/(k!)², which has no zeros
  on the negative axis (|F| < 1 there), so the many real zeros of F
  become non-real. W(m ⊔ n) − t tends to F(z) itself, whose zeros are
  negative and simple.
  That is a heuristic, not a proof. Sturm sequences give the computed
  fact: W(m ⊔ n) − t is real-rooted for every 1 ≤ m ≤ n ≤ 30
  `[chains-rr]`. The control W(P_{36,6}) reproduces [Br]'s
  printed coefficients and is detected as not real-rooted `[rr-control]`.
- *Small posets.* h_C is unimodal and log-concave on all 2450 posets with
  n ≤ 7 `[unimodal]` `[log-concave]`. [R] did not check log-concavity.

**The two-component identity (PROVEN here; COMPUTED).** Let P = Q ⊔ T with Q
and T connected. Then

  h_C(P)(t) = W_P(t) − t · W_Q(t) · W_T(t).

*Proof.* By Theorem Ω with anchor T, the order-preserving maps that are
*not* T-anchored are exactly those with min f(Q) > max f(T). With only two
components, the only T-free cluster is Q. These maps are the
(T ⊕ Q, ω)-partitions of the ordinal sum T ⊕ Q (T below Q), where ω is
natural on T and on Q and labels every element of T above every element
of Q. Their linear extensions are the concatenations uv with u ∈ Lin T and
v ∈ Lin Q. The junction is a descent, so des(uv) = des u + des v + 1. By
EC1 Thm 3.15.8 their count is Σ_{u,v} C(m + n − 1 − (des u + des v + 1), n),
and its h-numerator is t W_T W_Q. Subtract this from Ω_P(m), whose
h-numerator is W_P. ∎

This holds on all 391 two-component posets with n ≤ 7 `[two-comp]` and on
S ⊔ C_2 `[stembridge0+C2-identity]`. With three or more components the
non-anchored maps need inclusion–exclusion over T-free clusters. That was
not done here. The identity was not found in the sources read. It is the
same shape as Brändén's W(m ⊔ n) = 1 + W(P_{m,n}).

## 6. What [R] should change

1. §7 Prior art:
   - Replace the two-query search with the verdicts above. The polynomial
     side of R is KNOWN IN SUBSTANCE (EC1 Lemma 3.15.9; [GR]
     Prop. 7.1.7(iii) with Prop. 5.2.19). The D_T reading (Lemma R2) is
     NOT FOUND.
   - [Pet] has been read in full and has no reciprocity section.
2. §6 S′: cite EC1 **Cor. 3.15.18(b)** and [BS] **Ex. 6.27** for the
   connected case, not "EC1 §3.15".
3. Table row U and §8: U for connected P is the open unimodality question
   for W_P of naturally labelled posets ([AJ] §1.1). Add that log-concavity
   holds for n ≤ 7, and that real-rootedness fails at n = 17 (Stembridge).
4. §5: [St74] Prop. 6.1 (Macdonald, manifolds with boundary) is the
   result that would give E directly if R_T is a manifold. "PL ball" is
   more than needed.

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 5 s):

    python3 prior_art_reciprocity_omega_c.py --nmax 7 --bf-nmax 5 --chain-max 30 > output/prior_art_reciprocity_omega_c.txt
    python3 -m unittest test_prior_art_reciprocity_omega_c

The script exits 0 iff every check passes and the control is refuted.
Options:
- `--nmax`: the poset sweep.
- `--bf-nmax`: the brute-force strict-map re-check of Theorem R. Its
  cost grows like (n + 1)^n per (P, T); only n ≤ 5 was run.
- `--chain-max`: the C_m ⊔ C_n real-rootedness scan.

The sources in §0 were fetched on 2026-10-31 from arXiv, Stanley's
publication page (EC1, [St74]) and Beck's page ([BS]). They are not
committed.
