# Audit of `literature_novelty_jks_maps.md` (refutation of eq. restrictionlemma, Prop. Φ, Conjecture S)

Work item: mg-350d5. Subject: `notes/literature_novelty_jks_maps.md` (merged
in bc37251, mg-92751; called "the audited note" below). Equation names refer
to `notes/poset_jks_research_note.tex` ("the seed note").

Method. Every claim was re-derived by hand, or recomputed with new code that
shares nothing with `compute/splitting_cycles.py` or `compute/poset_jks_check.py`:

    cd compute
    python3 audit_jks_maps.py > output/audit_jks_maps.txt   # ~40 s, exit 0, ends "ALL CHECKS PASSED"
    python3 -m unittest test_audit_jks_maps

Every result below is tagged PROVEN (proof given here), COMPUTED (by the
command above, output in `compute/output/audit_jks_maps.txt`), CITED (exact
location given) or CONJECTURED. Each row of the claim table is graded
CONFIRMED, BROKEN, OVERSTATED or UNCHECKED.

Conventions are the audited note's. A word w is the permutation i ↦ w_i. Left
multiplication relabels letters, and right multiplication permutes positions.
ρ_w is the splitting cycle of w, normalised so that the chain m_w has
coefficient +1 (this is Wachs's normalisation; see §5). Sh_n is the span of
the proper shuffles.

## Verdict

**Prop. C (the refutation of eq. restrictionlemma): CONFIRMED. It refutes
the seed note's statement as the note makes it. A P-dependent J does not
escape it either.**

- The seed note fixes J first ("Let J be a classical JKS isomorphism"), then
  asserts J(H_P ⊗ sgn) = W_P e_ζ for every P. Lemma B (O(P) = O(P^op)) is
  correct, so H_P = H_{P^op} as subspaces. For the chain C and its dual, the
  two required lines C·e_ζ and C·(n⋯1)e_ζ differ. So no linear map J, fixed
  in advance, works for both. This refutes the statement the seed note made,
  not a stronger one.
- **Strengthening (PROVEN here, §1.2).** Let J be any S_n-equivariant linear
  map H̃_{n−3}(Π̄_n) ⊗ sgn → C[S_n]e_ζ, and let it be chosen after P. Then
  J(H_P ⊗ sgn) = W_P e_ζ already fails for P = a single chain, with any
  labeling, for every n ≥ 3. Choosing J per poset does not help. The same
  holds without the sign twist. It also holds for κ_n in place of e_ζ, for
  n ≤ 5 (COMPUTED).
- **What escapes.** Two weaker statements are not refuted:
  - a J_P that is only Aut(P)-equivariant. That version is *equivalent* to
    eq. (mainconj) (§1.3), so it reduces nothing;
  - an embedding of H_P other than the inclusion (eq. homembed).

  **eq. (mainconj) itself is untouched**, as the audited note says.

**S2 (Conjecture S ⇒ eq. mainconj for connected P): CONFIRMED.**

- Aut(P) acts freely on Lin(P). This holds for every P, connected or not.
- For connected P, Lie(P) is the permutation module C[Lin P] (J–S Cor. 4.4).
  Conjecture S makes H_P the same permutation module. Free modules are
  unchanged by the sign twist.
- The map ρ_w ⊗ 1 ↦ sgn(w)·w e_ζ is an explicit equivariant isomorphism.
- S2′ (connected P: eq. mainconj ⇔ μ(O(P)^g) = 0 for all g ≠ 1) is also
  correct.

Independent confirmation of the consequence (COMPUTED):
- Conjecture S holds at chain level for all 318 unlabeled posets at n = 6.
- μ(O(P)^g) = 0 for all 773 non-identity automorphisms of connected
  6-element posets.

So eq. (mainconj) holds for every connected P with n ≤ 6, by two separate
routes.

No row is BROKEN. Two rows are mildly OVERSTATED (rows 23, 30), one
computational dependency is closed here (row 14), and several side claims are
UNCHECKED.

## Claim table

| # | Claim (audited note §) | Grade | Reason |
|---|---|---|---|
| 1 | Lemma B: O(P) = O(P^op), so H_P = H_{P^op} as subspaces (§3.3) | CONFIRMED | PROVEN: π is order-preserving iff the quotient digraph P/π is acyclic, and reversing every edge preserves acyclicity. COMPUTED on all naturally labelled P with n ≤ 5. This suffices because relabeling commutes with ^op. |
| 2 | Prop. C: no linear J satisfies eq. (restrictionlemma) for both the chain and its dual, n ≥ 3 (§3.3) | CONFIRMED | H_C = C·ρ_{12⋯n}, since O(chain) is Boolean. The rotation orbits of 12⋯n (≤ 1 descent each) and of n⋯1 (n−1 ≥ 2 descents) are disjoint, so the two lines differ. The quantifiers match the seed note: one J, all P. |
| 3 | "eq. (restrictionlemma) is false as stated" (Summary 4) | CONFIRMED | Same as row 2. It is in fact false even with a P-dependent S_n-equivariant J (§1.2). |
| 4 | "The second formulation W_P κ_n fails for the same reason" (COMPUTED n = 3, 4, 5) | CONFIRMED | Recomputed for n = 3, 4, 5. It is also PROVEN here for all n ≥ 3 (§1.4): κ_n and w_0κ_n are never proportional. |
| 5 | "eq. (mainconj) is untouched" | CONFIRMED | Prop. C concerns images of a fixed map. eq. (mainconj) is an abstract isomorphism. |
| 6 | Uniform J into C[S_n]a forces J = c·(·a)∘Φ, so it needs Sh_n a = 0 (§3.3) | CONFIRMED | The derivation is correct. §1.2 below generalises it to a J chosen for one chain. |
| 7 | Sh_n e_ζ ≠ 0 for all n ≥ 3 (§3.3) | CONFIRMED | Hand witness (PROVEN, §1.2): the coefficient of the identity in (1 ш 2⋯n)·e_ζ is (1+ζ)/n ≠ 0. COMPUTED n ≤ 5. |
| 8 | Sh_n κ_n ≠ 0, n = 3, 4, 5 | CONFIRMED | COMPUTED (floating point, tolerance 1e-9). κ_n was checked to be idempotent and Lie in the same run. General n: UNCHECKED. |
| 9 | Sh_n θ_n^* = 0, and ker(·θ_n^*) = Sh_n (§3.3) | CONFIRMED | PROVEN by the adjoint argument. Right multiplication by a* = Σ a_τ τ^{−1} is adjoint to right multiplication by a for ⟨σ,τ⟩ = δ (checked by hand). The image of ·θ_n is the span of left-normed brackets, which is Lie_n. The kernel is therefore Lie_n^⊥ = Sh_n. The audited note's numerical check of this was not recomputed. |
| 10 | Prop. Φ: ρ_σ ↦ sgn(σ)σ mod Sh_n is a well-defined S_n-isomorphism (§3.2) | CONFIRMED | For n ≤ 6 it is PROVEN outright by COMPUTED data, with no use of Wachs (§2): every signed shuffle relation holds exactly at chain level, and rank{ρ_σ} + rank Sh_n = n!. For general n it rests on Wachs's Lemma 3.1 and Thms 4.2–4.3. Those statements were checked against the preprint (§5); the dualisation step (§2.2) re-derives. |
| 11 | Sign twist and left/right conventions in Φ | CONFIRMED | Sh_n is a left ideal (relabeling commutes with shuffling), and g·ρ_σ = ρ_{gσ} (COMPUTED n ≤ 6). Positive control: the *unsigned* relation fails for every shuffle (6/6, 36/36, 240/240, 1800/1800). The equivariance computation in §3.2 is correct. |
| 12 | Φ verified at chain level, n ≤ 5 (12/72/480 shuffles) | CONFIRMED | Recomputed independently and extended to n = 6. This audit counts unordered pairs {u, v} (6/36/240/1800), which is half the ordered count. |
| 13 | Lemma D: ρ_w ∈ H_P for w ∈ Lin P (§3.4) | CONFIRMED | PROVEN: cutting a linear extension gives the kernel of an isotone surjection, whose quotient is acyclic. COMPUTED on all unlabeled posets with n ≤ 6. Positive control: ρ_213 is not supported in O(1<2<3). |
| 14 | Conjecture S COMPUTED for all posets with n ≤ 6 (§3.4) | CONFIRMED (with a gap now closed) | Recomputed at chain level for all 5/16/63/318 unlabeled posets. rank_p{ρ_w} = dim_p ker ∂ = e_C(P) everywhere. This also re-proves dim H_P = e_C(P) (J–S Thm 4.5) for n ≤ 6 without citing it. The audited note's n = 6 check went through comb coordinates, so it depended on Prop. Φ at n = 6, which that note verified only for n ≤ 5 (general n by citation). The chain-level n = 6 run here removes that dependence. Conjecture S remains CONJECTURED for n ≥ 7. |
| 15 | Mod-p rank argument: rank_p ≤ rank_Q ≤ dim H_P = e_C(P), so rank_p = e_C ⇒ equality (§3.4) | CONFIRMED | The direction is right: a nonzero minor mod p is a nonzero integer. This audit uses the stronger sandwich rank_p{ρ_w} ≤ rank_Q{ρ_w} ≤ dim_Q H_P ≤ dim_p ker ∂, which needs no citation. |
| 16 | S1: Φ(H_P ⊗ sgn) = (W_P + Sh_n)/Sh_n, and J(H_P ⊗ sgn) = W_P θ_n^*, given Conjecture S | CONFIRMED | Immediate from Prop. Φ and row 9. |
| 17 | S2: Aut(P) acts freely on Lin(P) | CONFIRMED | gw = w as words means g(w_i) = w_i for all i, so g = 1. This holds for every P, not only connected P. |
| 18 | S2: for connected P, {we_ζ} is a basis of Lie(P) permuted freely | CONFIRMED | Connected ⇒ distinct linear extensions lie in distinct rotation orbits (J–S Cor. 4.4, CITED by the audited note, not rechecked). we_ζ is supported on wC_n with nonzero coefficients, so these vectors are independent. g(we_ζ) = (gw)e_ζ, with no scalar. |
| 19 | S2: Conjecture S ⇒ eq. (mainconj) for connected P | CONFIRMED | PROVEN: both sides are ≅ C[Lin P] ≅ C[G]^r, and sgn ⊗ C[G] ≅ C[G]. An explicit equivariant map: ρ_w ⊗ 1 ↦ sgn(w)·w e_ζ. Check: g sends the left side to sgn(g)ρ_{gw} ⊗ 1, which maps to sgn(g)sgn(gw)·gw e_ζ = sgn(w)·g w e_ζ. |
| 20 | S2: eq. (mainconj) holds for every connected P with n ≤ 6 | CONFIRMED | Route 1: Conjecture S at n ≤ 6 (row 14) plus row 19. Route 2, independent: S2′ criterion COMPUTED directly. μ(O(P)^g) = 0 for all 2/16/112/773 non-identity automorphisms of connected posets, n = 3..6. Positive control: the antichain on 3 points with g = (123) gives μ = −1. |
| 21 | S2′: connected P: eq. (mainconj) ⇔ μ(O(P)^g) = 0 for all g ≠ 1 | CONFIRMED | Lie(P) is free (row 18), so eq. (mainconj) ⇔ H_P is free ⇔ χ_{H_P}(g) = 0 for g ≠ 1. Lefschetz/Hopf trace (eq. homchar) needs homology concentrated in one degree (J–S Thm 4.5) and Δ(Q)^g = Δ(Q^g). The latter holds because an order-preserving g fixing a chain setwise fixes it pointwise. |
| 22 | S3: eq. (mainconj) ⇔ W_P/(W_P∩Sh_n) ≅ W_P/(W_P∩K_ζ), given Conjecture S; W_P∩K_ζ spanned by wγ^j − ζ^j w; W_P∩Sh_n contains shuffles of extensions of complementary unions of components | CONFIRMED | ker(·e_ζ) = C[S_n](1−e_ζ). Orbits are independent, so within one orbit the kernel is the codimension-1 space Σ x_w ζ^{j(w)} = 0, spanned by those differences. A shuffle of linear extensions of complementary unions of components is a linear extension. |
| 23 | Lemma A: if g ∈ Aut(P) fixes a cyclic class and a point, then g = 1; hence χ_{Lie(P)}(g) = 0 for g ≠ 1 in any point stabiliser (§2.3) | CONFIRMED | PROVEN: gw = wγ^r and g(w_i) = w_i force w_{i+r} = w_i, so r = 0 and g = 1. The claim that the equivariance group of the J–S recursion contributes 0 on the Lie side is correct. **Mildly OVERSTATED framing:** "says only H_P is G_a-free" undersells the content. G_a-freeness of H_P is the nontrivial statement μ(O(P)^g) = 0 for g ∈ G_a∖1, which eq. (mainconj) predicts and the recursion could in principle prove. The conclusion stands that the recursion cannot reach the fixed-point-free elements that carry the phases. |
| 24 | The restriction map H_P → ⊕_b H̃(Ô(P/π_{a,b})) is an isomorphism (§2.3) | UNCHECKED | The audited note correctly labels it CONJECTURED. |
| 25 | Partial result: the ρ_w with w_1 = a (a minimal) are independent (§3.5) | CONFIRMED | COMPUTED: all (n−1)! ρ_w with w_1 = 1 are independent, n ≤ 6, which contains the claim. The argument (words beginning with the least letter are a basis of C[S_n]/Sh_n, then Φ) is standard. The cited theorem numbers were not checked. |
| 26 | Topics Ex. 10.9 (top-cone version) is false as printed: counterexample [2,[1,3]] on cone {x_1 ≤ x_2, x_1 ≤ x_3} (§4.2) | CONFIRMED | The text, as quoted, is on p. 267 of the preliminary version. A "top-cone" there is any intersection of arrangement half-spaces of full dimension (§2.1.1, §2.1.3), so the cone qualifies. COMPUTED: [2,[1,3]] = 213 − 231 − 132 + 312, with sum −1 on {123, 132}. |
| 27 | Chamber sum outside Sh_n for 2/4, 9/15, 43/62 non-chain posets (§4.2) | CONFIRMED | COMPUTED with a different membership test (orthogonality to a basis of left-normed brackets). The counts agree. They are labeling-independent because Sh_n is a left ideal. |
| 28 | W_P e_ζ = W_{P^op} e_ζ for 4/5, 7/16, 11/63 posets "for a fixed labeling" (§3.3) | UNCHECKED | The count depends on the labeling, and the labeling is not specified, so the figure cannot be reproduced as stated. It is not needed for Prop. C. |
| 29 | dim W_P κ_n = e_C(P), n ≤ 5 (§3.3) | UNCHECKED | Not recomputed. Not used anywhere. |
| 30 | Summary 6: "Do not try to prove containment in W_P e_ζ or W_P κ_n: it is false" | CONFIRMED / mildly OVERSTATED | It is false for any S_n-equivariant J. For e_ζ that holds at every n (§1.2), and for κ_n it is COMPUTED only for n ≤ 5. For κ_n and n ≥ 6 the fixed-J version is PROVEN here (§1.4), but the P-dependent version is unchecked. |
| 31 | Citations: Wachs 1998 Prop. 2.2, 2.3, Lemma 3.1, Thms 2.5, 3.2, 3.3, 4.1, 4.2, 4.3, 5.3, 5.4 (preprint numbering) | CONFIRMED (preprint) / UNCHECKABLE (journal) | §5. |
| 32 | Citations: Topics Lemma 10.5, 10.7, 10.8, Ex. 10.9, Prop. 14.25, 14.27, Thm 14.32 | CONFIRMED (preliminary version) / UNCHECKABLE (print) | §5. |
| 33 | Wachs, Poset Topology Thms 1.6.2, 3.2.8, 3.2.9, 3.2.15; J–S numbering; Reutenauer Thm 3.1 | UNCHECKED | Not in this audit's spot-check list. |
| 34 | Novelty search, bibliography corrections (§1, §5 of the audited note) | UNCHECKED | Out of scope. |

## 1. Prop. C and what it refutes

### 1.1 The statement in the seed note

The seed note, section "Embedding into the classical JKS module", reads: "Let
J … be a classical JKS isomorphism … The conjecture follows from the single
restricted-image statement J(H_P ⊗ sgn) = span{we_ζ : w ∈ Lin(P)}." The
lemma in "Potential proof via splitting spheres" says: "Under a suitable
explicit JKS isomorphism, the span of top cycles supported on
order-preserving partitions of P maps onto W_P e_ζ."

In both, J is a JKS isomorphism, which is S_n-equivariant by definition, and
it is chosen independently of P. Prop. C refutes exactly this statement. The
audited note does not inflate it.

### 1.2 A P-dependent S_n-equivariant J does not escape (PROVEN)

**Proposition C′.** Let n ≥ 3, w ∈ S_n, and let P_w be the chain
w_1 < w_2 < ⋯ < w_n. Then no S_n-equivariant linear map
J : H̃_{n−3}(Π̄_n) ⊗ sgn → C[S_n]e_ζ satisfies J(H_{P_w} ⊗ sgn) = C·we_ζ.

*Proof.*
1. H_{P_w} = C·ρ_w, so the hypothesis forces J(ρ_w ⊗ 1) = c·we_ζ with c ≠ 0.
2. Put y = Σ_{u ∈ 1 ш 2⋯n} u w^{−1} ∈ C[S_n].
3. Then y·(ρ_w ⊗ 1) = Σ_u sgn(uw^{−1}) ρ_u ⊗ 1 = ±Σ_u sgn(u) ρ_u ⊗ 1. This
   is 0 by the signed shuffle relation (Prop. Φ, kernel half).
4. Equivariance gives 0 = J(y·(ρ_w ⊗ 1)) = c·y·we_ζ = c·(1 ш 2⋯n)·e_ζ.
5. In the product (1 ш 2⋯n)·e_ζ = (1/n) Σ_u Σ_j ζ^{−j} uγ^j, the identity
   word arises from exactly two words u of 1 ш 2⋯n: u = 12⋯n, from j = 0,
   and u = 23⋯n1 = γ, from j = n−1. A rotation of the identity lies in
   1 ш 2⋯n only if 2, …, n stay in order, and that happens only for these
   two.
6. So the identity coefficient is (1 + ζ^{−(n−1)})/n = (1 + ζ)/n, which is
   ≠ 0 since ζ ≠ −1 for n ≥ 3. Contradiction. ∎

Notes on the proof:
- The only input beyond algebra is the signed relation for the single
  shuffle 1 ш 2⋯n. It is COMPUTED exactly for n ≤ 6 and follows from Prop. Φ
  (Wachs) for all n.
- The coefficient (1 + ζ)/n is COMPUTED for n = 3, 4, 5.
- *Without the sign twist* (J : H̃ → C[S_n]e_ζ), use y = Σ_u sgn(u) uw^{−1}
  instead. The identity coefficient becomes (1 + (−1)^{n−1}ζ)/n ≠ 0, so that
  version fails too.
- *κ_n in place of e_ζ*: the same argument needs some s ∈ Sh_n with
  sκ_n ≠ 0. That is COMPUTED for n = 3, 4, 5 (row 8).

So eq. (restrictionlemma) fails on the simplest posets, the chains, for
which eq. (mainconj) is trivial. Choosing J per poset cannot help. The
obstruction is structural: the annihilator of ρ_w in C[S_n] is Sh_n·w^{−1},
while that of we_ζ is C[S_n](1−e_ζ)w^{−1}, and these differ because
Sh_n e_ζ ≠ 0.

### 1.3 What is not refuted

- **Aut(P)-equivariant J_P.** Suppose only Aut(P)-equivariance is required.
  Then "∃ J_P with J_P(H_P ⊗ sgn) = W_P e_ζ" is equivalent to eq. (mainconj).
  - ⇒: restrict J_P to H_P.
  - ⇐: Res_{Aut P} of H̃ ⊗ sgn and of Lie_n are isomorphic, since they are
    S_n-isomorphic. Suppose H_P ⊗ sgn ≅ Lie(P). By semisimplicity
    (Krull–Schmidt) the complements are isomorphic, so the isomorphism
    extends.

  This is PROVEN but contentless: it is a restatement of eq. (mainconj), not
  a lemma that reduces it.
- **Other embeddings.** Prop. C uses the inclusion H_P ⊂ H̃(Π̄_n) of
  eq. (homembed). That inclusion depends only on O(P), and Lemma B makes it
  blind to P ↦ P^op. Any construction that depends only on O(P) and this
  inclusion has the same blindness. An embedding that sees the orientation of
  P is not excluded, but none is proposed in either note.
- **eq. (mainconj)** as an abstract isomorphism.

### 1.4 κ_n and w_0κ_n are never proportional (PROVEN)

Take κ_n = (1/n) Σ_σ ζ^{maj σ}σ. With the product (uv)_i = u_{v_i} this is
idempotent and Lie for n ≤ 5 (COMPUTED). Left multiplication by
w_0 = n⋯1 complements letters, which swaps descents and ascents. So
maj(w_0σ) = n(n−1)/2 − maj σ, and (w_0κ_n)_σ = ζ^{n(n−1)/2} ζ^{−maj σ}/n.

Proportionality to κ_n would need ζ^{2 maj σ} to be constant in σ. But maj
takes the values 0 and 1, and ζ^2 ≠ 1 for n ≥ 3. So the fixed-J refutation
of the "second formulation" holds for every n ≥ 3. The audited note claimed
it only for n ≤ 5.

## 2. Prop. Φ

### 2.1 Chain-level verification, n = 3..6 (COMPUTED)

The splitting cycle ρ_w is built directly from its definition:
- Maximal chains of Π_w are the orders τ ∈ S_{n−1} in which the n−1 cuts are
  removed.
- ρ_w = ε Σ_τ sgn(τ) c_τ, with ε chosen so that m_w has coefficient +1.
- m_w removes the cuts n−1, n−2, …, 1 in that order. It is Wachs's chain
  whose k-block partition is w_1|⋯|w_{k−1}|rest.

Checks:
- Each ρ_w is a cycle.
- g·ρ_w = ρ_{gw}.
- For every proper shuffle u ш v, the sum Σ_{x ∈ u ш v} sgn(x) ρ_x is
  identically 0 as an integer chain (6, 36, 240 and 1800 shuffles).
- rank_p{ρ_σ} = (n−1)! and rank_p Sh_n = n! − (n−1)!.

*Why this proves Φ for n ≤ 6.* The map C[S_n] → chains, σ ↦ sgn(σ)ρ_σ,
kills Sh_n, so dim ker ≥ rank_Q Sh_n ≥ rank_p Sh_n. Also
dim ker = n! − rank_Q{ρ} ≤ n! − rank_p{ρ}. The two rank_p values add up to
n!, so ker = Sh_n exactly. The image is spanned by the ρ_σ, all of which are
cycles, and has dimension (n−1)!. That equals dim H̃_{n−3}(Π̄_n) (the
classical |μ(Π_n)| = (n−1)!), so the image is all of homology.

Ree's side, also COMPUTED: the (n−1)! left-normed brackets [⋯[1, w_2], ⋯, w_n]
are orthogonal to every proper shuffle and have rank (n−1)!. Hence
Sh_n = Lie_n^⊥ for n ≤ 6.

### 2.2 General n (re-derived; it rests on Wachs)

The dualisation in §3.2 of the audited note was re-done:
- ⟨ρ_σ, ψ(r_τ)⟩ = sgn(τ)·sgn′(α)·[α minmax], with α = σ^{−1}τ.
- Wachs's identity sgn(α) = (−1)^{des α} sgn′(α) for minmax α (proof of
  Thm 4.3), together with sgn(τ)sgn(α) = sgn(σ), turns this into
  sgn(σ)·(−1)^{des α}·[α minmax].
- By Thm 4.2 / eq. (4-3) that is sgn(σ)·⟨r_τ, σ⟩.

The algebra is right. The signs inside Wachs's Lemma 3.1 and Thm 4.2 were
checked as *statements* against the preprint, not re-proved. The n ≤ 6
computation agrees with the resulting formula.

## 3. Conjecture S, n ≤ 6 (COMPUTED)

For each unlabeled poset (the enumeration reproduces the counts 1, 2, 5, 16,
63, 318, with naturally labelled counts 1, 2, 7, 40, 357 checked in the test
suite), the run computes:
- O(P), as the set partitions with acyclic quotient;
- the top chains of Ô(P), and the rank mod p = 2^31 − 1 of the boundary map
  on them;
- the rank mod p of {ρ_w : w ∈ Lin P}.

In every case rank_p{ρ_w} = (#top chains − rank_p ∂) = e_C(P). Since
rank_p{ρ_w} ≤ rank_Q{ρ_w} ≤ dim_Q H_P ≤ dim_p ker ∂, all of these are equal.
This gives Conjecture S and dim H_P = e_C(P) over Q for every poset with
n ≤ 6, without citing Jenča–Sarkoci or Prop. Φ.

Positive control: for V = {1<2, 1<3}, a single ρ_w falls short of
e_C(V) = 2.

A proof of Conjecture S for all n has since been posted on main
(`notes/conjecture_s_splitting_cycles_span.md`). It is not audited here. The
n ≤ 6 data above is an independent check of its conclusion.

n = 7 was not attempted. The pure-Python canonical-form step over 96428
naturally labelled posets × 5040 permutations is too slow.

## 4. §2.3: the J–S recursion and the Lie side

Lemma A is correct (row 23), and so is its corollary: every g ≠ 1 that fixes
a point has χ_{Lie(P)}(g) = 0. The elements carrying nontrivial phases
ζ^{r_g(C)} are therefore fixed-point-free on [n], and lie in no
point-stabiliser G_a. A G_a-equivariant recursion can give at most
Res_{G_a} H_P ≅ Res_{G_a}(sgn ⊗ Lie(P)) = free. That is a real but partial
statement, and it says nothing about the phases.

The S2′ data above (μ(O(P)^g) = 0 for connected P) is consistent with
G_a-freeness for connected P.

## 5. Citation spot-checks

Sources fetched for this audit:
- the Wachs preprint `homlie.ps`, dated "Dec. 31, 1994 (revised Jan. 1996)",
  linked from https://www.math.miami.edu/~wachs/abstracts/homlie.html;
- Aguiar–Mahajan, *Topics in Hyperplane Arrangements*, authors' preliminary
  version, https://pi.math.cornell.edu/~maguiar/surv-226.pdf.

| Citation | Verdict | Notes |
|---|---|---|
| Wachs, Prop. 2.3 (splitting basis {ρ_σ : σ(n) = n}, dual basis {m̄_σ}) and the normalisation of ρ_σ (m_σ has coefficient 1; k-block partition of m_σ = σ(1)\|⋯\|σ(k−1)\|rest) | CONFIRMED (preprint) | Matches the audited note and this audit's code. |
| Wachs, Prop. 2.2 (Björner basis), Thm 2.5 (caterpillar), Thm 3.2, Thm 3.3 | CONFIRMED (preprint) | Numbers and topics as stated. |
| Wachs, Lemma 3.1 (⟨ρ_σ, m̄_τ⟩ = sgn′(σ^{−1}τ) if minmax, else 0; sgn′(α) = (−1)^{inv(α(1)⋯α(n−1))}; minmax = avoids 213 and 231) | CONFIRMED (preprint) | |
| Wachs, Thm 4.1 (Barcelo correspondence, Lyndon basis ↦ dual Björner basis, Lie_n → H^{n−3}(Π̄_n) ⊗ sgn) | CONFIRMED (preprint) | It is a cohomology statement, as the audited note says. |
| Wachs, Thm 4.2 (comb representation matrix (−1)^{des}·[minmax]) and Thm 4.3 (comb correspondence r_w ↦ sgn(w) m̄_w, joint with Sundaram) | CONFIRMED (preprint) | The identity sgn(α) = (−1)^{des α} sgn′(α) for minmax α is in the proof of Thm 4.3. |
| Wachs, Thm 5.3 (generating set c(T,w); Hanlon–Wachs Thm 3.11) and Thm 5.4 (general correspondence ψ) | CONFIRMED (preprint) | |
| Wachs 1998 journal numbering (Discrete Math. 193, 287–319) | UNCHECKABLE | The journal text was not accessible. The audited note's warning to check it stands. |
| Topics Lemma 10.5 (Friedrichs criterion) | CONFIRMED (prelim.) | |
| Topics Lemma 10.7 (z ∈ Lie iff coefficient sums vanish on all non-singleton combinatorial top-lunes) and Lemma 10.8 (vertex-based top-lunes suffice) | CONFIRMED (prelim., p. 267) | "Ree criterion" is the authors' own name for them. |
| Topics Exercise 10.9 ("…in any non-singleton top-cone of A is zero") | CONFIRMED as quoted (prelim., p. 267) | False as printed (row 26). The print edition: UNCHECKABLE. |
| Topics Prop. 14.25, Prop. 14.27, Thm 14.32 (the maps (14.22) H^{r−2}(Π[A]) ⊗ E^o[A] → Lie[A] and (14.23) are natural isomorphisms) | CONFIRMED (prelim.; Thm 14.32 on p. 392) | The print edition: UNCHECKABLE. |

## 6. Reproduction

    cd compute
    python3 audit_jks_maps.py > output/audit_jks_maps.txt   # ~40 s; exit status 0 iff every check passes
    python3 -m unittest test_audit_jks_maps                 # < 1 s

Options: `--nphi N` (Prop. Φ and Ree up to N, default 6), `--ns N`
(Conjecture S and S2′ up to N, default 6), `--direct N` (direct dim H_P up to
N, default 6). The Prop. C, κ_n and Ex. 10.9 checks are fixed at n ≤ 5.
