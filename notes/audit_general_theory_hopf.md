# Audit of the general-theory note, framework (b): Q′, Theorems 6–8 and "(b) = (a)"

**Verdict.** Lemma 2.1: **HOLDS**. Theorem 7: **HOLDS WITH FIXES** (wording
only). Theorem 8: **HOLDS**. Theorem 6: **HOLDS WITH FIXES** (one
clarification). "(b) = (a) on the braid arrangement": **HOLDS WITH FIXES**
(status tag and an overstatement).

Scope: `notes/general_theory.md` §2 ("[GT]") as merged in df0b9c1, together
with the summary item 5 and the status-table rows that restate it. Other
abbreviations follow [GT]: [Thm] = `notes/poset_jks_theorem.tex`, [Glob] =
`notes/global_module_operations_plethlog.md`, [Cone] =
`notes/cone_lune_lie_theory.md`, [CC] = `notes/citation_check.md`.

Method: every PROVEN claim is re-derived step by step below. The computations
are in `compute/audit_general_theory_hopf.py`, written for this audit. It does
not import `compute/general_theory.py` or any other module of the repository.
Every check has a positive control, i.e. a deliberately wrong variant that
must fail and does.

Tags used for this audit's own claims:
- **PROVEN**: re-derived here.
- **COMPUTED**: by the audit script.

No mathematical error was found. All the defects are in wording, in status
tags, or in citation pointers.

## Summary of defects (for the maintainer of [GT]; not applied here)

1. **Thm 7, summary item 5.** "The bracket Lie(P) ⊗ Lie(Q) → Lie(P + Q) is
   the truncation of the free Lie bracket" uses Lie(P) as [Thm] defines it,
   namely Lie(P) = W_P e_ζ. But the bracket is defined on
   𝔭_P = R_P^⊥ ⊆ W_P. On W_P e_ζ it exists only by transport through the
   isomorphism 𝔭_P ≅ W_P/R_P →(ψ_P^{-1}) W_P e_ζ. It is **not** induced by
   concatenation on the e_ζ model, which is exactly [Glob, §3.4]'s negative
   result (reproduced in §2.3 below).

   Suggested wording: "the bracket 𝔭_P ⊗ 𝔭_Q → 𝔭_{P+Q} (𝔭_P ≅ Lie(P)) is
   the truncation of the free Lie bracket. On Klyachko's model it exists
   only by transport, and is not induced by concatenation ([Glob, §3.4])."
2. **Thm 7(a) citation pointer.** "Aguiar–Mahajan, Ch. 11" can be made
   precise as AM, *Monoidal Functors*, §11.9.2 (p. 394): "P(h) is a Lie
   submonoid of h" for the commutator of Prop. 1.26. A five-line direct
   proof is in §2.1 below, so the citation is optional.
3. **Thm 7(b): Ree.** Ree's theorem is used only for the description
   𝔭_P = pr_P(Lie_I). I could not access Ree 1958 or Reutenauer, *Free Lie
   algebras*, Thm 3.1 (NOT ACCESSIBLE, as also recorded in [CC]). The
   description is COMPUTED here for n ≤ 6 without Ree. The identification
   𝔭_P = R_P^⊥ and parts (a), (c), (d) do not use Ree.
4. **Thm 8 citation pointer.** "CMM–PBW for species (CITED as in [Glob])"
   should point to AM, *Monoidal Functors*, §11.9.3, eq. (11.40) (CMM) and
   the paragraph after Cor. 11.46 (PBW), pp. 395–396. This is the pointer
   [CC] row H already gives. I re-read the text, and the hypotheses match
   (§3).
5. **Thm 6, second isomorphism.** In ⊕_σ ⊗_{B∈σ} (sgn ⊗ H_{P|_B}), an
   element g ∈ Aut(P) may map a block B to a different block gB. Then
   "sgn of g on B" is undefined. The factor must be read as the orientation
   line det(k^B), which is functorial under bijections. With that reading,
   the transport argument in the proof is correct. Add one sentence.
6. **(b) = (a), status tag.** "Indecomposables M_P ≅ H_P ⊗ sgn ([Thm, Thm
   S(d)])" inherits Thm S(d)'s dependence on Prop. Φ, which is CITED for
   n ≥ 7. The same abstract isomorphism follows without Φ from
   ψ_P (Cor. psi) and Thm main. Either cite that route, or tag the claim
   "given Prop. Φ for n ≥ 7". Also add n ≥ 3 (or the [Thm] conventions for
   n ≤ 2).
7. **(b) = (a), overstatement.** What is proven is a single subspace
   identity:

   (W_+ · W_+)_P = R_P = span{top-lunes ⊆ C_P}.

   The summary's "(b) and (a) are the same structure on the braid
   arrangement" claims more. The coproduct of W, the bracket and the PBW
   decomposition have no stated counterpart in (a). The sentences "This is
   how Lemma L … reads algebraically" and "It also explains why …" are
   interpretation and should be marked as a remark, not as PROVEN.
8. **Lemma 2.1, minor.** The proof shows that Q′ is a connected
   cocommutative *bimonoid*. That it is *Hopf* follows from connectedness
   (AM, *Monoidal Functors*, Prop. 8.10, Takeuchi's formula (8.24)), and
   this should be said. The proof also uses, without saying so, that
   uu′ ∈ Lin(P + P′) and ℓ|_S ∈ Lin(P|_S).

## 1. Lemma 2.1: Q′ is a connected cocommutative Hopf monoid

**Re-derivation (PROVEN).** Q′[I] has basis the pairs (P, ℓ), with
ℓ ∈ Lin P. Write "S ⊑ P" for "S is a union of components of P", i.e. no
comparability of P joins S to I ∖ S. The empty set and I are both unions of
components.

- **Well defined.** A concatenation uu′ of u ∈ Lin P and u′ ∈ Lin P′ lies in
  Lin(P + P′). A restriction ℓ|_S lies in Lin(P|_S) for every S. Relabelling
  commutes with μ and Δ, so both are morphisms of species.
- **Unit and counit.** Q′[∅] = k·(∅, ()), so Q′ is connected. Since ∅ ⊑ P,
  Δ_{∅,I}(P, ℓ) = 1 ⊗ (P, ℓ), and similarly Δ_{I,∅}.
- **Associativity** is that of disjoint union and concatenation.
- **Coassociativity.** Take I = S_1 ⊔ S_2 ⊔ S_3.
  - (id ⊗ Δ_{S_2,S_3})Δ_{S_1,S_2⊔S_3} is nonzero iff S_1 ⊑ P and
    S_2 ⊑ P|_{S_2⊔S_3}.
  - When S_1 ⊑ P, the set S_2 ⊔ S_3 = I ∖ S_1 is also ⊑ P. Its components
    in P|_{S_2⊔S_3} are the components of P that it contains. So the second
    condition is S_2 ⊑ P.
  - The other bracketing gives the same condition, S_1, S_2, S_3 ⊑ P. Both
    sides then equal ⊗_i (P|_{S_i}, ℓ|_{S_i}).
- **Cocommutativity.** S ⊑ P iff I ∖ S ⊑ P.
- **Compatibility.** Let (P, u) live on S and (P′, u′) on T, and let
  I = S ⊔ T = S′ ⊔ T′, with A, B, C, D as in [GT].
  - The components of P + P′ are those of P together with those of P′. So
    S′ ⊑ P + P′ iff A ⊑ P and C ⊑ P′.
  - In that case (P + P′)|_{S′} = P|_A + P′|_C and (uu′)|_{S′} = u|_A u′|_C,
    because restricting a concatenation restricts each factor. The same
    holds for T′.
  - The right-hand side (μ_{A,C} ⊗ μ_{B,D})(Δ_{A,B} ⊗ Δ_{C,D}) is nonzero
    under exactly the same condition, and then the two sides agree.
- **Antipode.** A connected bimonoid in species is Hopf: AM, *Monoidal
  Functors*, Prop. 8.10(ii), read in the source. [GT]'s proof omits this
  step (defect 8).
- **Grading.** μ(Q′_P ⊗ Q′_{P′}) ⊆ Q′_{P+P′}. If S ⊑ P, then
  Δ_{S,T}(Q′_P) ⊆ Q′_{P|_S} ⊗ Q′_{P|_T} and P = P|_S + P|_T.

No missing hypothesis. Verdict: **HOLDS**.

**COMPUTED** (`[axioms]`). Every axiom (associativity, unit, counit,
coassociativity, cocommutativity, compatibility, closure of the basis,
naturality under relabelling) was checked on every basis element of Q′[I],
for all labelled posets with |I| ≤ 4 and every decomposition of I.
- **Sanity check.** [Glob]'s 𝐐 (restriction to every S) passes all axioms
  for n ≤ 3.
- **Control 1.** With the coproduct restricted to down-sets instead of
  unions of components, the instrument reports a failure of cocommutativity
  only.
- **Control 2.** With the ordinal sum P ⊕ P′ as the product, it reports a
  failure of compatibility only.

## 2. Theorem 7: the P-graded Lie structure

### 2.1 Part (a): grading and bracket (PROVEN)

- **Grading.** Fix S, T nonempty and let x = Σ_P x_P be primitive.
  - Δ_{S,T}x_P = 0 unless S ⊑ P.
  - For S ⊑ P, Δ_{S,T}x_P lies in Q′_{P|_S} ⊗ Q′_{P|_T}, and the pair
    (P|_S, P|_T) determines P = P|_S + P|_T.
  - So the nonzero Δ_{S,T}x_P lie in independent summands, and
    Δ_{S,T}x = 0 forces each of them to vanish.

  The argument is exactly [GT]'s and is correct.
- **Bracket.** Here is a direct proof, so the citation is not needed. Let
  x ∈ 𝔭[S] and y ∈ 𝔭[T], and take S′ ⊔ T′ = S ⊔ T with S′, T′ nonempty.
  - By compatibility, Δ_{S′,T′}(xy) = Σ μ ⊗ μ (Δ_{A,B}x ⊗ Δ_{C,D}y).
  - Primitivity kills every term except those with A, B ∈ {∅, S} and
    C, D ∈ {∅, T}. With S′, T′ ≠ ∅, only (S′, T′) = (S, T), giving x ⊗ y,
    and (S′, T′) = (T, S), giving y ⊗ x, survive.
  - The same holds for yx = μ_{T,S}(y ⊗ x). So Δ_{S′,T′}(xy − yx) = 0.

  The cited source says the same: AM, *Monoidal Functors*, §11.9.2, p. 394,
  "P(h) is a Lie submonoid of h" (read in the source).

### 2.2 Parts (b)–(e) (PROVEN; one cited input NOT ACCESSIBLE)

**(b), 𝔭_P = R_P^⊥.** Let x = Σ c_ℓ ℓ ∈ W_P, let S ⊑ P be proper and
nonempty, s ∈ Lin(P|_S) and t ∈ Lin(P|_T).
- The words ℓ ∈ Lin P with ℓ|_S = s and ℓ|_T = t are exactly the shuffles
  of s and t. Every shuffle is in Lin P, because S ⊑ P, and distinct
  shuffles are distinct words.
- So ⟨Δ_{S,T}x, s ⊗ t⟩ = ⟨x, s ш t⟩.
- For S not ⊑ P, Δ_{S,T} vanishes on Q′_P. Hence 𝔭_P = R_P^⊥ ∩ W_P. ✓

**(b), 𝔭_P = pr_P(Lie_I).**
- The linear algebra pr_W(U^⊥) = (U ∩ W)^⊥ ∩ W is correct for the standard
  bilinear form and a coordinate subspace W. The kernel of pr_W is W^⊥, and
  U^⊥ ∩ W^⊥ = (U + W)^⊥.
- With U = Sh_I, it needs Sh_I^⊥ = Lie_I, which is Ree's theorem in its
  multilinear form. Pairing with multilinear elements only sees shuffles of
  complementary multilinear words, so the multilinear form follows from the
  general one.
- It also needs Sh_I ∩ W_P = R_P, which is [Thm, Thm S(b)] (PROVEN,
  audited, elementary).
- **Ree: NOT ACCESSIBLE** (Ree 1958 and Reutenauer Thm 3.1 were not
  available to me).
- **COMPUTED** (`[ree]`), without Ree, for n ≤ 6:
  - the (n − 1)! right combs [σ_1, [σ_2, …, [σ_{n−1}, n]]] pair to zero,
    exactly over ℤ, with every proper shuffle;
  - they have rank (n − 1)!;
  - for n ≤ 5, the proper shuffles have rank n! − (n − 1)!.

  So Sh_n^⊥ = Lie_n holds for n ≤ 5, by a rank count. For n = 6 only
  Lie_6 ⊆ Sh_6^⊥ and dim Lie_6 = 5! are checked; the truncation statement
  below is nonetheless checked directly at n = 6.
- **COMPUTED** (`[trunc]`): pr_P(Lie_n) = R_P^⊥ directly, for all 405
  posets with n ≤ 6:
  - the truncated combs are orthogonal to the generators of R_P, exactly
    over ℤ;
  - they have rank e_C(P);
  - rank R_P = |Lin P| − e_C(P).
- **Controls.**
  - Klyachko's elements w e_ζ are not orthogonal to Sh_3, so the instrument
    tells Lie elements apart from the e_ζ model.
  - pr_P(Lie) fails to be orthogonal to the *down-set* shuffles, the
    primitives of the other coproduct, for 399 of the 405 posets.

**(c), dimension and module structure.**
- dim 𝔭_P = |Lin P| − dim R_P = e_C(P), by Thm S(b). ✓
- The pairing is Aut(P)-invariant, because Aut(P) permutes Lin P.
- R_P is defined over ℚ, so W_P = R_P ⊕ R_P^⊥ and 𝔭_P ≅ W_P/R_P = M_P
  directly. This is a shortcut; [GT]'s route through M_P^* and real
  characters is also correct.
- M_P ≅ Lie(P) by ψ_P ([Thm, Cor. psi], audited, unconditional).
- Lie(P) ≅ sgn ⊗ H_P by [Thm, Thm main], which needs n ≥ 3 and [Thm]'s
  cited inputs.
- **COMPUTED** (`[char]`), independently of ψ_P: for all 2,460 pairs
  (P, g ∈ Aut P) with n ≤ 6, 𝔭_P is g-stable, and the trace of g on 𝔭_P
  equals Σ_{gC=C} ζ^{r_g(C)}, the character of Lie(P), with no sign twist.
  Control: the untwisted count Σ_{gC=C} 1 differs on 220 pairs.

**(d), the bracket is the truncated free bracket.** A word uv (u on S, v on
T) lies in Lin(P + P′) iff u ∈ Lin P and v ∈ Lin P′. So
pr_{P+P′}(xy) = pr_P(x)·pr_{P′}(y), where · is concatenation, i.e. μ of Q′.
The same holds for yx. ✓

**(e)** For an antichain, Lin is every word, pr is the identity, and Q′
restricted to antichains is 𝐋 with concatenation and restriction. So
𝔭 = Lie. ✓

**COMPUTED** (`[prim]`, `[brkt]`).
- Prim(Q′)[n] was computed over the whole of Q′[n], not poset by poset, for
  n ≤ 4. It has dimension 1, 3, 32, 786 = Σ_P e_C(P), and it is
  P-homogeneous: dim Prim = Σ_P dim(Prim ∩ Q′_P).
- **Control.** The same instrument on [Glob]'s 𝐐 gives Σ_P dim(Prim ∩ 𝐐_P)
  equal to 1, 2, 6, against 3, 32, 786 for n = 2, 3, 4. This reproduces
  [Glob, §4.3]'s non-homogeneity.
- For 286 pairs (P, P′) with |P| + |P′| ≤ 6, three random comb pairs each:
  [pr x, pr y] lies in W_{P+P′}, is orthogonal to R_{P+P′} (so it is
  primitive), and equals pr_{P+P′}[x, y], exactly over ℤ.
- **Control.** [12, 3], with 12 a single non-primitive word, is not
  primitive.

Verdict on the body of Theorem 7: correct.

### 2.3 Consistency with the negative result of [Glob, §3.4]

[Glob, §3.4] asks whether u ⊗ v ↦ uv − vu, a map W_P ⊗ W_Q → W_{P+Q},
**descends** to the quotients W_P e_ζ ⊗ W_Q e_ζ → W_{P+Q} e_ζ. That is, it
asks whether the map sends ker(W_P → W_P e_ζ) ⊗ W_Q into
ker(W_{P+Q} → W_{P+Q} e_ζ). The answer is no.

Theorem 7 uses the same map W_P ⊗ W_Q → W_{P+Q}, but **restricts** it to
the subspaces R_P^⊥ ⊗ R_Q^⊥ → R_{P+Q}^⊥. A map can preserve a family of
subspaces without descending to a family of quotients, and here the two
families are different. R_P^⊥ is a complement of R_P, while the kernel of
W_P → W_P e_ζ is

  K_P = span{wγ^k − ζ^k w : k a cut},

which differs from R_P. So the two results do not conflict.

**What Theorem 7 changes.** It changes the **model**, not the abstract
claim.
- The P-graded Lie structure lives on 𝔭_P = pr_P(Lie_I) ⊆ C[Lin P]. These
  are truncated Lie polynomials, not Klyachko's W_P e_ζ.
- The isomorphism 𝔭_P ≅ Lie(P) is of Aut(P)-modules. It is canonical
  (𝔭_P → M_P is the quotient map, then ψ_P^{-1}), but it does not carry
  concatenation to anything on W_P e_ζ.
- So the open item "a P-graded bracket" of [Glob, §5] is answered in the 𝔭
  model. The e_ζ model still carries no concatenation-induced bracket.
- Even classically (P an antichain), the bracket is on Lie_n ⊂ C[S_n], not
  on C[S_n] e_ζ.

[GT]'s body is consistent with this, but its summary item 5 writes the
bracket on "Lie(P)", which is ambiguous (defect 1).

**COMPUTED** (`[brkt]` control).
- Re-derived from scratch: of the 71 pairs with p + q ≤ 5, 20 have
  K_P ≠ 0, and all 20 fail to descend. This matches [Glob, §3.4]'s 20 of 71
  exactly.
- Extended to p + q ≤ 6: 77 of 77 such pairs fail.
- On the same pairs, the bracket closes on 𝔭 (above).

Verdict: **HOLDS WITH FIXES** (defects 1–3).

## 3. Theorem 8: the filtration

**Re-derivation (PROVEN).**
- **r is a filtration.**
  - r(P + P′) = r(P) + r(P′).
  - r(P|_S) + r(P|_T) = r(P) − #{relations between S and T}. So the sum is
    at most r(P), with equality iff S ⊑ P.
  - Hence F_r is a Hopf filtration of the species 𝐐: it is exhaustive,
    F_{−1} = 0, and it is preserved by relabelling.
- **The associated graded is Q′.**
  - μ is strictly additive in r, so gr μ = μ.
  - The term Δ_{S,T}(P, ℓ) lies in F_{a′} ⊗ F_{b′}, with a′ + b′ < r(P)
    unless S ⊑ P. Such a term lies in (F ⊗ F)_{r−1}, so it vanishes in
    gr_r(F ⊗ F) ≅ ⊕_{a+b=r} gr_a ⊗ gr_b.
  - So gr Δ = Δ_{Q′}, and gr 𝐐 ≅ Q′ once the r-grading is forgotten.
- **Leading terms.**
  - If x ∈ Prim ∩ F_r, then gr Δ_{S,T}(x̄) is the class of Δ_{S,T}x = 0.
    So x̄ ∈ Prim(Q′).
  - In finite dimension, dim gr V = dim V for a filtered subspace V.
  - So dim Prim(𝐐)[I] ≤ dim Prim(Q′)[I].
- **Equality.** CMM (U(P(h)) = h) and PBW (U(g) ≅ S(g) as comonoids) give
  h ≅ S(P h) = E ∘ P(h) as species, for every connected cocommutative Hopf
  monoid h. Then exp(egf P(h)) = egf h, so dim P(h)[n] depends only on the
  dimensions of h. 𝐐 and Q′ have the same underlying species, so the two
  dimensions are equal and the inclusion is an equality.
  - The figure "(n − 1)! b_n" in [GT] is not needed for this argument.

**Cited input, read in the source.** The input is AM, *Monoidal Functors,
Species and Hopf Algebras*, §11.9.3, pp. 395–396 (authors' PDF,
`pi.math.cornell.edu/~maguiar/a.pdf`).
- Eq. (11.40): "for any Lie monoid g and any connected cocommutative Hopf
  monoid h, we have P(U(g)) = g and U(P(h)) = h". AM attribute this to
  Stover, Prop. 7.10 and Thm 8.4.
- The paragraph after Cor. 11.46: "an analogue of the Poincaré–Birkhoff–Witt
  theorem for species … U(g) = S(g) as comonoids for any Lie monoid g"
  (Joyal, §4.2 Thm 2; Stover, Thm 11.3).
- "Connected" is Def. 8.41: a bimonoid in (Sp°, ·), i.e. h[∅] ≅ k. 𝐐 and Q′
  are connected and cocommutative, and they are Hopf by Prop. 8.10.

So the hypotheses are met, and what is used is what is stated. [CC] row H
gave the same pointer, and I confirm it. The primaries (Stover, Joyal) were
not read.

**COMPUTED** (`[filt]`).
- The equality criterion "r(P|_S) + r(P|_T) = r(P) iff S ⊑ P" holds for all
  139,062 pairs (labelled P, S) with n ≤ 5.
- For 𝐐[n] with n ≤ 4, the filtered dimensions were computed directly
  (dim gr_r Prim(𝐐) = dim(Prim ∩ F_r) − dim(Prim ∩ F_{r−1})), and in every
  r-degree they equal Σ_{r(P)=r} e_C(P):

  | n | dim gr_r Prim(𝐐), r = 0, 1, … |
  |---|---|
  | 2 | [1, 2] |
  | 3 | [2, 12, 12, 6] |
  | 4 | [6, 72, 204, 240, 168, 72, 24] |

  This is finer than the total-dimension equality that CMM gives, and it
  uses no CMM for these n.
- Every leading term was checked to be Q′-primitive.
- **Control.** The same leading terms are *not* primitive for 𝐐's own
  (ungraded) coproduct, for n = 2, 3, 4.

Verdict: **HOLDS**. Fix the citation pointer (defect 4).

## 4. Theorem 6: local PBW

**Re-derivation (PROVEN).**

- **Choice of V_Q.** Transporting an Aut-stable complement is well defined:
  two isomorphisms Q_0 → Q differ by an element of Aut(Q_0), which
  stabilizes V_{Q_0}. R_Q and W_Q are natural under relabelling.

  A simpler canonical choice is V_Q = R_Q^⊥ = 𝔭_Q. It is natural with no
  choices, because the standard form is relabelling-invariant. With this
  choice the domain of m_P is the degree-P part of S(𝔭).
- **m_P is well defined and equivariant.** Let σ ∈ Π(K), and let each block
  be a union of components. Shuffles of linear extensions of the P|_B then
  lie in Lin P, because there are no relations between blocks. Shuffle is
  commutative and associative, so the unordered tensor product is fine.
  g ∈ Aut(P) sends σ to gσ and V_{P|_B} to V_{P|_{gB}}.
- **Surjectivity.** The induction on |K| is correct.
  - If P is connected, then R_P = 0, so V_P = W_P.
  - Otherwise W_P = V_P + R_P. The generators s ш t of R_P have
    s ∈ W_{P|_S} and t ∈ W_{P|_T}, which are in the image by induction (each
    of P|_S and P|_T has fewer components).
  - Associativity of shuffle concatenates the two partitions into one
    partition of K.
- **Dimension.** dim V_Q = e_C(Q) by Thm S(b), and
  |Lin P| = Σ_σ Π_B e_C(P|_B) by Lemma 1.3. I re-read [GT]'s bijective
  proof of Lemma 1.3 (Foata on irreducible pieces) and found it correct.
- **Consequences.**
  - V_Q → M_Q → Lie(Q) is natural under all relabellings: the first map
    because V_Q is, the second by ψ_Q and Thm Θ. So the first isomorphism
    C[Lin P] ≅ ⊕_σ ⊗_B Lie(P|_B) holds as Aut(P)-modules.
  - The second isomorphism needs a family Lie(Q) ≅ sgn ⊗ H_Q that is
    natural under *all* poset isomorphisms, including those between
    different ground sets. Transport from one Q_0 per class works, because
    the Aut(Q_0)-isomorphism commutes with Aut(Q_0). But the factor "sgn" of
    a block must then be the line det(k^B) (defect 5). With that reading,
    the trace of g on an orbit of k blocks is χ(g^k|_B), as used in
    `[pbw-eq]`.
  - Freeness: Aut(P) acts freely on Lin P, so the left side is free. ✓

**COMPUTED** (`[pbw]`), for all 405 posets with n ≤ 6.
- The shuffle products over all σ ∈ Π(K) give exactly |Lin P| vectors of
  rank |Lin P|. This holds for V_Q = 𝔭_Q and for V_Q = span B_Q.
- Lemma 1.3 holds.
- The equivariant form
  |Lin P|·[g = 1] = Σ_{gσ=σ} Π_{orbits} χ_{𝔭(P|_B)}(g^k|_B) holds on all
  2,460 pairs (P, g). Here χ_𝔭 is a trace on 𝔭, computed independently of
  the e_ζ formula.
- **Controls.**
  - Dropping the partitions with ≥ 3 blocks loses rank on 29 posets.
  - Replacing χ_𝔭 by dim breaks the character identity on 2,055 pairs.

Verdict: **HOLDS WITH FIXES** (defect 5; the dependencies Thm S(b),
Lemma 1.3, ψ_P/Thm Θ and Thm main are correctly listed in [GT]'s status
table).

## 5. "(b) = (a) on the braid arrangement"

**Re-derivation (PROVEN).** Let W = Q′^*, using finite-dimensional
components and the dual basis.

- **Product.** ⟨(P_1, s)^* · (P_2, t)^*, (P, ℓ)⟩ is nonzero iff S ⊑ P,
  P|_S = P_1, P|_T = P_2, ℓ|_S = s and ℓ|_T = t. Equivalently, P = P_1 + P_2
  and ℓ is a shuffle of s and t. So the product is disjoint union with
  shuffle. ✓
- **Coproduct.** ⟨Δ(P, ℓ)^*, a ⊗ c⟩ is nonzero iff μ(a ⊗ c) = (P, ℓ), i.e.
  S ⊑ P and S is the letter set of a prefix of ℓ. That is deconcatenation
  at cuts. ✓
- **Decomposables.** (W_+ · W_+)_P = span{s ш t : S ⊑ P proper} = R_P, by
  definition of R_P. ✓
- **Lunes.** R_P = span{top-lunes ⊆ C_P} is [Cone, Cor. 3.1], which is
  audited and which I re-read.
- **Indecomposables.** W_P/R_P = M_P ≅ H_P ⊗ sgn for n ≥ 3. [GT] cites Thm
  S(d) for this, which is conditional on Prop. Φ for n ≥ 7. The abstract
  isomorphism also follows from ψ_P and Thm main, without Φ (defect 6).

**What is not proven.** Only the subspace identity of decomposables with
lune spans is proven. "The same structure" and the two explanatory
sentences go beyond it (defect 7).

**COMPUTED** (`[dual]`).
- The dual product and coproduct were computed from the pairing for n ≤ 4.
  They equal disjoint union with shuffle, and deconcatenation at cuts.
- **Control.** The dual of 𝐐's coproduct is *not* disjoint union with
  shuffle.
- Braid top-lunes were computed from sign vectors and the Tits product,
  with no use of the shuffle description: L(H, D) = {C : HC = D} for every
  face H ≠ O and every chamber. For all 86 posets with 2 ≤ n ≤ 5, the lunes
  contained in C_P span exactly R_P.
- **Control.** The truncations of the lunes that merely *meet* C_P span a
  different space on 82 of them.

Verdict: **HOLDS WITH FIXES** (defects 6, 7).

## Cited inputs: what was read

| Input | Used in | Status |
|---|---|---|
| AM, *Monoidal Functors*, §11.9.3, eq. (11.40) and PBW paragraph (pp. 395–396) | Thm 8 | Read; matches, hypotheses met |
| AM, *Monoidal Functors*, §11.9.2 (p. 394), P(h) a Lie submonoid | Thm 7(a) | Read; matches (also re-proved directly) |
| AM, *Monoidal Functors*, Prop. 8.10 (antipode of connected bimonoids), Def. 8.41 | Lemma 2.1 | Read; matches |
| Ree 1958 / Reutenauer Thm 3.1 (Lie_n = Sh_n^⊥) | Thm 7(b) only | NOT ACCESSIBLE; COMPUTED n ≤ 6 (Sh_n^⊥ = Lie_n proven for n ≤ 5 by rank count) |
| [Thm] Thm S(b), Cor. psi, Thm Θ, Thm main; [Cone] Cor. 3.1 | Thms 6–7, §2.3 | Internal, previously audited; not re-audited here beyond the computations above |

## Reproduce

From `compute/` (plain Python 3, no third-party packages):

    python3 audit_general_theory_hopf.py > output/audit_general_theory_hopf.txt   # ~40 s, ALL CHECKS PASSED, exit 0
    python3 -m unittest test_audit_general_theory_hopf                           # < 1 s

The archived output is `compute/output/audit_general_theory_hopf.txt`.
Ranks are computed modulo the prime 1999999861. A full rank mod p certifies
full rank over ℚ. Every orthogonality and bracket identity is checked
exactly over ℤ.
