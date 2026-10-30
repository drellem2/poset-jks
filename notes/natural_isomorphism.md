# Is there a natural isomorphism H_P ⊗ sgn ≅ Lie(P)?

Work item: mg-2d2b3.

Builds on:
- `notes/conjecture_s_splitting_cycles_span.md` (the "Conjecture S note"; audited in
  `notes/audit_conjecture_s.md`);
- `notes/literature_novelty_jks_maps.md` (the "literature note", Prop. C, Prop. Φ) and its audit
  `notes/audit_literature_novelty_jks_maps.md` (Prop. C′);
- `notes/global_module_operations_plethlog.md` (the "global note").

Every claim is tagged PROVEN, COMPUTED, CITED or CONJECTURED. "PROVEN given (Φ), (D), (JS)"
means: proven, using the same three inputs as Theorem C of the Conjecture S note.

**Audit (mg-583e6).** This note has been independently audited in
`notes/audit_natural_isomorphism.md`. Verdict: Theorem Ψ, Cor. Ψ.1, Theorems 1 and 2 HOLD.
Cor. Ψ.1 is elementary: it needs none of (Φ), (D), (JS). One defect was found, in the computational
evidence only: the `[wgt]` check and the λ ≡ 1 counts "5/6, 16/19, 63/80" were computed on a wrong
object. They are corrected in §3.2 below (the true counts are 6/6, 19/19, 80/80, and the drop is
PROVEN for every disconnected P). The script was fixed in commit 7c10288 (mg-dab53): `[wgt]` now
prints the true counts and asserts them (§3.2). A minor notation slip in Prop. 3 is also corrected (§4).

## Summary

Part 1 sorts the possible meanings of "natural". Part 2 answers each one.

| Meaning of "natural" | Verdict |
|---|---|
| (G) natural on the groupoid of labeled posets and isomorphisms | trivial (§1.1) |
| (E) natural along order extensions, target the e_ζ model | **holds exactly on connected posets.** It fails at *every* disconnected P with n ≥ 3, already against P's own linear extensions (Theorem 1) |
| (c) a canonical iso given by one explicit formula | **yes, for every P** (Theorem 2): the "ζ-twisted class sum" Θ_P |
| (b) compatible with ordinal sum | possible, but it pins nothing down, and it is incompatible with every family that is the identity on connected posets, Θ included (Prop. 3) |
| (a) compatible with disjoint sum | the e_ζ model carries no natural restriction, deconcatenation or cobracket map (Prop. 4); the M-model carries the cobracket. As stated, the question only makes sense on the M side |
| (d) a more functorial Lie-side model | **yes:** M_P = image of W_P in Lie_n^* = C[S_n]/Sh_n. It is natural in every sense listed (Prop. 5) |

The headline results:

1. **Theorem 2 (PROVEN given (Φ), (D), (JS)).** For every finite poset P with n ≥ 3, the map

       Θ_P^{−1} : Lie(P) = W_P e_ζ → H_P ⊗ sgn,
       w e_ζ ↦ (sgn(w)/n) · Σ_{k a cut of w} (−1)^{(n−1)k} ζ^{−k} · ρ_{wγ^k} ⊗ 1

   is a well-defined Aut(P)-isomorphism. Here the sum runs over the k with w_1⋯w_k a union of
   connected components, i.e. over the members wγ^k of the cyclic class of w. It is given by one
   formula with no choices, and it commutes with all relabelings.
   - On connected P it is w e_ζ ↦ (sgn(w)/n) ρ_w ⊗ 1, the extension-natural isomorphism of
     Theorem 1.
   - This gives a **second, constructive proof of eq. (mainconj)**, which does not use the
     character identity of the global note.
2. **Theorem Ψ (PROVEN, elementary).** This is the algebraic core of Theorem 2. Let P be a poset
   on A, and λ : A → C^× weights with λ(A) = 1 and λ(U) ≠ 1 for every nonempty proper union U of
   components. Then the twisted class sums s_λ(C) = Σ_{k cut} λ(w_1⋯w_k)^{−1} wγ^k, one for each
   cyclic class C, are linearly independent modulo proper shuffles.
   - The proof is the contraction induction of Theorem A in the Conjecture S note, carried out
     with weights.
   - For the antichain it gives C[S_n]e_ζ ∩ Sh_n = 0. That is a short proof of Klyachko's
     Lie_n ≅ Ind_{C_n}^{S_n} ζ (Cor. Ψ.2; probably known in some form).
3. **Theorem 1 (PROVEN).** Fix a family η_P : H_P ⊗ sgn → W_P e_ζ compatible with the inclusions
   H_{C_w} ⊆ H_P for the chains C_w, w ∈ Lin P. If P is disconnected and n ≥ 3, then η_P is not
   injective. If P is connected, the identity-induced map ρ_w ⊗ 1 ↦ c·sgn(w) w e_ζ is an
   isomorphism. It is natural for relabelings and for all extensions among connected posets, and
   it is unique up to the scalar c once relabelings are required.
   - This sharpens Prop. C, which uses only the antichain. Here every disconnected poset
     obstructs, and no relabeling naturality is needed.

So the precise answer is the following.
- The natural object is W_P modulo shuffles, M_P ⊂ Lie_n^*.
- The e_ζ model is natural along extensions exactly for connected posets.
- Nevertheless there is a canonical, explicit, relabeling-natural isomorphism for every P. It is
  given by truncating the support of y ∈ W_P e_ζ to Lin P and reading the result modulo shuffles.
- That isomorphism cannot be natural along extensions or ordinal sums once disconnected posets
  are present, and Theorem 1 and Prop. 3 show that nothing can.

Everything is COMPUTED for all unlabeled posets with n ≤ 6 (some checks at n = 7), §6.

## 0. Notation and conventions

- Words with distinct letters are permutations. The product is composition,
  (uv)(i) = u(v(i)), so σ·w relabels letters and wγ^j = w_{j+1}⋯w_n w_1⋯w_j is the left rotation
  by j. Here γ = (1 2 ⋯ n).
- e_ζ = (1/n) Σ_j ζ^{−j} γ^j, with ζ a primitive n-th root of unity, so γ^j e_ζ = ζ^j e_ζ. This
  is the convention of `compute/poset_jks_check.py`.
- The form is ⟨σ, τ⟩ = δ_{στ} (bilinear), and x^* is the linear extension of σ ↦ σ^{−1}. Then
  ⟨xy, z⟩ = ⟨x, z y^*⟩ and e_ζ^* = e_{ζ^{−1}}.
- W_P = C{Lin P}. Sh_n is the span of the proper shuffles. R_P = W_P ∩ Sh_n is spanned by the
  s ш t with s, t linear extensions of complementary unions of components (Theorem B of the
  Conjecture S note).
- **Cut.** A cut of w ∈ Lin P is a k ∈ {0, …, n−1} such that w_1⋯w_k is a union of components.
  The cyclic class of w is {wγ^k : k a cut} (Lemma 4 of the Conjecture S note). There are e_C(P)
  classes.
- **Models:**
  - M_P := W_P / R_P = (W_P + Sh_n)/Sh_n ⊆ Lie_n^*, of dimension e_C(P);
  - L_P := Lie(P) = W_P e_ζ, with basis {w_C e_ζ}, one w_C per class, of dimension e_C(P).
    Distinct classes lie in distinct rotation orbits, so these supports are disjoint.
- Φ_P : H_P ⊗ sgn → M_P, ρ_w ⊗ 1 ↦ sgn(w) w̄. This is an Aut(P)-isomorphism (Cor. 5.5 of the
  Conjecture S note: PROVEN given (Φ), (D), (JS)). It is the restriction of the single
  S_n-isomorphism Φ : H̃_{n−3}(Π̄_n) ⊗ sgn → Lie_n^* of Prop. Φ.

## 1. Part 1: which naturality questions are non-trivial

### 1.1 (G) The groupoid: trivial (PROVEN)

Let 𝒢 be the groupoid whose objects are posets on [n] and whose morphisms P → σP are relabelings
σ ∈ S_n. Both P ↦ H_P ⊗ sgn and P ↦ L_P are functors on 𝒢 via σ·.

A natural isomorphism on a groupoid is the same thing as one Aut(P)-isomorphism for each
isomorphism class, transported along the morphisms. The abstract Aut(P)-isomorphism exists
(`notes/audit_character_identity_proof.md`), so (G) holds with no further content. It does not
single out any isomorphism. **Dismissed.**

What follows asks for more than (G):
- naturality for a bigger class of morphisms: extensions (E), ordinal sums (b), disjoint sums (a);
- or canonicity, meaning no choices (c);
- or a change of target (d).

### 1.2 (E) Extensions

Let ℰ be the category of posets on [n] with a morphism P → P′ whenever σ(P) ⊆ P′ for some
σ ∈ S_n, i.e. P′ extends a relabeling of P. Both functors are contravariant on ℰ:
- O(P′) ⊆ O(σP), which gives H_{P′} ⊆ H_{σP};
- Lin P′ ⊆ Lin σP, which gives W_{P′}e_ζ ⊆ W_{σP}e_ζ.

The literature note's Prop. C refutes naturality on all of ℰ: the antichain A_n extends to both
1<⋯<n and n<⋯<1. The audit's Prop. C′ refutes any S_n-equivariant ambient J. Neither says which
subcategories escape. Theorem 1 answers that.

### 1.3 Candidates (a)–(d)

- **(c)** is non-trivial if "canonical" means: one rule, no choices, defined for every P,
  commuting with relabelings. "Explicit formula" alone does not make it non-trivial. It cannot be
  a uniform S_n-map on an ambient space (Prop. C′).
- **(b), (a)** need structure maps on both sides. On the M side these are natural (§4, §5). On
  the e_ζ side one has to ask first whether any natural structure map exists. If none does,
  "monoidal" can only mean "transport the M-side structure", which is tautological.
- **(d)** is non-trivial as a question about which model is functorial, not about whether an
  isomorphism exists.

## 2. Theorem 1: extension-naturality holds exactly on connected posets

**Theorem 1 (PROVEN given (Φ) and (D)).** Let P be a poset on [n].

- (i) Suppose P has at least two components and n ≥ 3. Let η_P : H_P ⊗ sgn → W_P e_ζ be any
  linear map with η_P(H_{C_w} ⊗ sgn) ⊆ W_{C_w} e_ζ = C·we_ζ for every w ∈ Lin P, where C_w is the
  chain w_1 < ⋯ < w_n. Then η_P is **not injective**. Hence no family of isomorphisms is natural
  along the morphisms P → C_w of ℰ.
- (ii) If P is connected, η_P(ρ_w ⊗ 1) := sgn(w) w e_ζ (w ∈ Lin P) defines an Aut(P)-isomorphism.
  On the full subcategory of ℰ of connected posets, this family is a natural isomorphism. Every
  natural isomorphism on that subcategory is c_n·η, with one scalar c_n per n.
- (iii) For n ≤ 2 every poset behaves as in (ii). For n = 2 the antichain has
  R_P = C(01+10) and (01+10)e_ζ = 0, since ζ = −1.

*Proof.*
- (i), first step. H_{C_w} = Cρ_w. So the hypothesis says η_P(ρ_w ⊗ 1) = c_w·we_ζ for some
  scalar c_w.
- Choose a nonempty proper union S of components. Name it so that T = [n]∖S has |T| ≥ 2, which is
  possible since n ≥ 3.
- Let s ∈ Lin(P|_S) and t ∈ Lin(P|_T). Every word of s ш t lies in Lin P, and Σ_{z∈sшt} z ∈ Sh_n.
  By (Φ) this means Σ_{z∈sшt} sgn(z) ρ_z = 0. Applying η_P gives

      Σ_{z∈sшt} sgn(z) c_z · z e_ζ = 0.

- Let u = t_1 s t_2⋯t_b. Then u ∈ s ш t. The element z e_ζ is supported on the rotations of z,
  so only words z ∈ s ш t that are rotations of u contribute to the coefficient of u.
- **No proper rotation of u lies in s ш t.**
  - A rotation starting at a letter of s, or at t_k with k ≥ 2, puts t_2 (resp. t_k) before t_1.
  - This uses b ≥ 2.
- So the coefficient of u is sgn(u)c_u/n. Hence c_u = 0.
- But ρ_u ≠ 0: a single word is never in Sh_n, since it pairs to 1 with its own left-normed comb.
  So η_P(ρ_u ⊗ 1) = 0 with ρ_u ⊗ 1 ≠ 0.
- (ii) For connected P, R_P = 0 (Corollary A′ of the Conjecture S note), so M_P = C[Lin P]. Every
  cyclic class is a single word, so W_P ∩ K_ζ = 0 and L_P has basis {we_ζ : w ∈ Lin P}. So
  ρ_w ⊗ 1 ↦ sgn(w)w̄ ↦ sgn(w)we_ζ is the composite of two isomorphisms. It is visibly compatible
  with Lin P′ ⊆ Lin P and with relabelings, using g(ρ_v ⊗ 1) = sgn(g)ρ_{gv} ⊗ 1.
- Uniqueness. Compatibility with P → C_w forces η_P(ρ_w ⊗ 1) = c_w we_ζ. Relabeling
  naturality on chains forces c_{σw} = sgn(σ)c_w, i.e. c_w = c_n sgn(w). ∎

**Remarks.**
- (i) uses only the arrows from P to its own linear extensions. No arrow between two non-chains is
  needed, and the antichain is not needed.
- (i) also refutes the diagonal variant w̄ ↦ c_w we_ζ with arbitrary c_w ≠ 0.
- Prop. C is the special case P = A_n. Prop. C′ is the statement that even one chain obstructs a
  *uniform* J. Theorem 1(ii) shows that a non-uniform family has no obstruction on connected
  posets.

COMPUTED (`[ext]`, `[wit]`, §6): R_P e_ζ = 0 ⇔ (P connected or n ≤ 2), for all
1+2+5+16+63+318 unlabeled posets with n ≤ 6 and all 2045 with n = 7. The coefficient of u is
exactly 1/n in all 5467 cases (P, S, s, t) with n = 6.

## 3. Theorems Ψ and 2: a canonical explicit isomorphism for every P

### 3.1 The weighted class sums

Let P be a poset on a finite set A, with |A| = n. Call λ : A → C^× **admissible** if:
- λ(A) = 1, where λ(U) := Π_{x∈U} λ(x);
- λ(U) ≠ 1 for every nonempty proper union U of components.

For w ∈ Lin P put

    s_λ(w) := Σ_{k a cut of w} λ(w_1⋯w_k)^{−1} · wγ^k   ∈ C[S_A].

**Lemma Ψ.0 (PROVEN).** If wγ^m is a rotation of w at a cut, then s_λ(wγ^m) = λ(w_1⋯w_m)·s_λ(w).
So each class C determines a line C·s_λ(C).

*Proof.*
- Let w′ = wγ^m and V = {w_1, …, w_m}. Both s_λ(w) and s_λ(w′) range over the same class.
- Let z = wγ^k with prefix set U.
  - If k ≥ m, z is reached from w′ by moving U∖V to the end.
  - If k < m, z is reached by moving (A∖V) ∪ U.
- So the phase of z in s_λ(w′) is λ(U∖V)^{−1} = λ(V)λ(U)^{−1} in the first case, and
  λ(A∖V)^{−1}λ(U)^{−1} = λ(V)λ(U)^{−1} in the second. The second uses λ(A) = 1. ∎

**Theorem Ψ (PROVEN).** For admissible λ, the elements s_λ(C), one for each cyclic class C of P,
are linearly independent modulo Sh_A.

*Proof.* Induction on n.
- n = 1 is clear, since Sh = 0.
- n = 2: if P is a chain there is one class {xa}, and a single word is not in Sh. If P is an
  antichain there is one class, s = xa + λ(x)^{−1}ax, and Sh_2 = C(xa + ax). Since {x} is a
  proper union, λ(x) ≠ 1, so s ∉ Sh_2.

Let n ≥ 3 and X = Σ_C c_C s_λ(C) ∈ Sh_A. For v ∈ Lin P in class C, define c̃(v) by
c̃(v)s_λ(v) = c_C s_λ(C). This is well defined by Lemma Ψ.0. Put c̃ = 0 off Lin P. Lemma Ψ.0
gives

    c̃(v) = λ(v_1⋯v_m) · c̃(vγ^m)   for every cut m.      (Ψ.1)

*Step 1: contraction.*
- Let a ≠ x be letters adjacent in some word of Lin P. Let Q = P/{a, x} on A∖x (Lemma 2 of the
  Conjecture S note), with weights λ′(a) = λ(a)λ(x) and λ′ = λ elsewhere.
- Unions of Q-components pull back exactly to the unions of P-components that contain both or
  neither of a, x (Lemma 2(c)). So λ′ is admissible for Q.
- **Claim:** if x immediately precedes a in v ∈ Lin P, then E_{a,x}(s_λ(v)) = s_{λ′}(v∖x). If a
  immediately precedes x, then E_{a,x}(s_λ(v)) = −s_{λ′}(v∖x). E_{a,x} is the contraction
  operator of the Conjecture S note §2.
- Proof of the claim:
  - The Q-cuts of v∖x are exactly the images of the P-cuts of v that do not separate a from x
    (as in the proof of Lemma 5 there).
  - A rotation at such a cut keeps x immediately before a. The image under E is the
    corresponding rotation of v∖x. Its phase is λ(U)^{−1} = λ′(U∖x)^{−1}, because U contains
    both a and x or neither.
  - The one remaining cut, if it exists, lies exactly between x and a. Its rotation begins with a
    and ends with x. Since n ≥ 3 they are not adjacent there, so E gives 0.
- Group X by Q-classes:
  - The P-classes whose E-image lies in the Q-class C′ of v′ ∈ Lin Q are those of v′[a→xa] and
    v′[a→ax]. Either may be absent from Lin P.
  - The two are distinct, because n ≥ 3 makes the cyclic words differ.
  - A class in which a, x are not cyclically adjacent, or which is the single word a⋯x, has E = 0.
  - So

        E_{a,x}(X) = Σ_{C′} ( c̃(v′[a→xa]) − c̃(v′[a→ax]) ) s_{λ′}(v′_{C′}).

- E_{a,x}(X) ∈ Sh_{A∖x} by Lemma 1 of the Conjecture S note (PROVEN there). By the induction
  hypothesis for (Q, λ′), every bracket vanishes:

      c̃(v′[a→xa]) = c̃(v′[a→ax])   for all v′ ∈ Lin Q.          (Ψ.2)

*Step 2: constancy.*
- Take w ∈ Lin P with letters y, z in positions i, i+1. Apply (Ψ.2) with x = y, a = z,
  v′ = w∖y.
- If y ∥ z: c̃(w) = c̃(w with y, z swapped).
- If y <_P z: the swapped word is not in Lin P, so c̃(w) = 0.
- By Lemma 3 of the Conjecture S note, c̃ is a constant c on Lin P.
- If P is disconnected, take a cut m with 0 < m < n. Then (Ψ.1) gives c = λ(U)c with U a
  nonempty proper union, so c = 0.
- If P is connected with n ≥ 2, P has a cover p ⋖ q realized adjacently in some extension (as in
  Theorem A). So c = 0.
- Hence every c_C = 0. ∎

**Corollary Ψ.1.** Take λ ≡ ζ, a primitive n-th root of unity. It is admissible, since
ζ^{|U|} ≠ 1 for 0 < |U| < n. And s_ζ(w) = n·pr_P(we_ζ), where pr_P : C[S_n] → W_P is the
coordinate truncation to Lin P. Hence:

**the map ψ_P : L_P → M_P, y ↦ pr_P(y) mod Sh_n, is an Aut(P)-isomorphism, for every P.**

*Proof.*
- Well defined and linear: clear.
- Aut(P)-equivariant: Aut(P) preserves Lin P, so pr_P commutes with it.
- Injective: ψ_P(w_C e_ζ) = s_ζ(C)/n, and Theorem Ψ applies.
- Bijective: both spaces have dimension e_C(P), by Lemma 4 and Theorem B of the Conjecture S
  note. ∎

**Corollary Ψ.2 (antichain; Klyachko).** C[S_n]e_ζ ∩ Sh_n = 0 for every primitive ζ. Hence:
- y ↦ y mod Sh is an S_n-isomorphism C[S_n]e_ζ ≅ Lie_n^*;
- Lie_n ∩ C[S_n](1−e_ζ) = 0, i.e. x ↦ xe_ζ is injective on Lie_n.

For the second point:
- xe_ζ = 0 ⇔ ⟨x, σe_{ζ^{−1}}⟩ = 0 for all σ.
- So the kernel is Lie_n ∩ (C[S_n]e_{ζ^{−1}})^⊥.
- By dimension count, this kernel is 0 ⇔ Sh_n ∩ C[S_n]e_{ζ^{−1}} = 0, using Lie_n^⊥ = Sh_n (Ree,
  CITED in the Conjecture S note).

Together with Lie_n^* ≅ Lie_n, Cor. Ψ.2 reproves Klyachko's theorem
Lie_n ≅ Ind_{C_n}^{S_n} ζ.
- **Novelty: unclear.** This is a proof via Ree's theorem and contraction. It is likely known in
  some form, e.g. through necklace/Lyndon arguments, but no source was checked for this exact
  argument.
- COMPUTED (`[lie]`): rank Lie_n e_ζ = (n−1)! for n ≤ 6.

### 3.2 Theorem 2: the canonical isomorphism

**Theorem 2 (PROVEN given (Φ), (D), (JS)).** For every poset P with n ≥ 3,

    Θ_P := ψ_P^{−1} ∘ Φ_P : H_P ⊗ sgn → Lie(P) = W_P e_ζ

is an Aut(P)-isomorphism, and it commutes with every relabeling σ : P → σP. Its inverse is the
explicit formula

    Θ_P^{−1}(we_ζ) = (1/n) Σ_{k cut of w} ζ^{−k} sgn(wγ^k) ρ_{wγ^k} ⊗ 1
                   = (sgn(w)/n) Σ_{k cut of w} (−1)^{(n−1)k} ζ^{−k} ρ_{wγ^k} ⊗ 1.

In words: **the class C of P goes to the ζ-twisted signed sum of the splitting cycles of the
members of C.**

*Proof.*
- Compose Cor. Ψ.1 with Cor. 5.5 of the Conjecture S note.
- The formula: Φ_P^{−1}(v̄) = sgn(v)ρ_v ⊗ 1 and ψ_P(we_ζ) = (1/n) Σ_k ζ^{−k} \overline{wγ^k}.
- sgn(γ) = (−1)^{n−1}.
- Relabeling: both Φ and pr_∗ are given by formulas that commute with σ·. ∎

**Remarks.**
- **No choices are made.** There is no base component, no class representative (Lemma Ψ.0) and
  no basis.
- The formula is uniform: "truncate to Lin P, then apply the inverse of the single S_n-map Φ".
  The only P-dependence is the support Lin P. Some P-dependence is forced, because a uniform
  S_n-map fails already on one chain (Prop. C′).
- On connected P, Θ_P^{−1}(we_ζ) = (sgn(w)/n)ρ_w ⊗ 1. That is Theorem 1(ii) with c_n = n.
- **Consequence.** Theorem 2 proves eq. (mainconj), H_P ≅ sgn ⊗ Lie(P) as Aut(P)-modules, for
  every P, with no use of the character identity.
  - Its inputs are those of Conjecture S: Prop. Φ (Wachs + Ree), Lemma D, and Jenča–Sarkoci
    Thm 4.5. The last is only used for dim H_P = e_C(P).
  - It is independent of `notes/global_module_operations_plethlog.md` §2. It has been
    independently audited (`notes/audit_natural_isomorphism.md`, rows 5–6: HOLDS).
- Θ_P is **not** natural along extensions when P is disconnected and n ≥ 3. Nothing is
  (Theorem 1(i)).
  - Concretely: for y ∈ L_{P′} ⊆ L_P, the truncations pr_{P′}(y) and pr_P(y) differ on
    Lin P ∖ Lin P′.

COMPUTED (`[psi]`): ψ_P is an isomorphism for all 2+5+16+63+318 unlabeled posets with
2 ≤ n ≤ 6, and for all 2045 with n = 7 (395 of them disconnected). The check is a rank
computation modulo Sh_n via L_0, so it is independent of the proof.

`[wgt]` was **defective** (audit §5): it took as class representative the least rotation of a
word, which need not lie in Lin P, so on such posets it did not compute s_λ(C). **Fixed** in commit
7c10288 (mg-dab53): it now takes the least word of C ∩ Lin P (`lin_class_reps`).
- COMPUTED (`[wgt]`, after the fix): s_λ(C) independent mod Sh for 2 random admissible λ per poset,
  4/4, 10/10, 32/32, 126/126, 636/636 draws for n = 2..6.
- The statement is also COMPUTED by the audit's own `[psi]` (3 random admissible λ per poset, all
  posets n ≤ 6).

Positive control: λ ≡ 1 is inadmissible, and the rank drops for **every** disconnected P.
- PROVEN (audit §5): Σ_C s_1(C) = Σ_{w∈Lin P} w. Write P = P_1 + P′ with P_1 a component. Then
  Lin P is the disjoint union of the shuffle sets s ш t (s ∈ Lin P_1, t ∈ Lin P′), so this sum
  lies in Sh_n.
- COMPUTED: the drop occurs for 1/1, 2/2, 6/6, 19/19, 80/80 disconnected posets, n = 2..6
  (`audit_natural_isomorphism.psi_rank` with λ ≡ 1; see the audit's Reproduce section). The fixed
  `[wgt]` prints the same counts and fails unless every disconnected P drops.
- The figures "5/6, 16/19, 63/80" printed by this note's `[wgt]` (and quoted in an earlier version
  of this paragraph) are **wrong**; they come from the defect above. So λ ≡ 1 always fails, and the
  earlier remark that "admissibility is only sufficient" does not apply to it.

### 3.3 A second canonical isomorphism (COMPUTED; CONJECTURED in general)

For each component P_i, let B_i be the words whose first block contains P_i. This is a basis of
M_P (Theorem A/B of the Conjecture S note). Define φ_i : M_P → L_P by b ↦ be_ζ for b ∈ B_i.
- φ_i is an isomorphism, but only Stab(P_i)-equivariant.
- gφ_ig^{−1} = φ_{g(i)}, so φ_Σ := Σ_i φ_i is Aut(P)-equivariant and canonical (PROVEN).

COMPUTED (`[sum]`):
- φ_Σ is invertible for all 1 + 2 + 6 + 19 + 80 disconnected posets with n ≤ 6.
- So is the size-weighted Σ|P_i|φ_i.
- Aut-equivariance was checked for n ≤ 5. Control: φ_0 alone is not equivariant whenever Aut(P)
  moves P_0 (5 posets, n ≤ 5).

**Proposition (PROVEN for antichains).** For P = A_n, φ_Σ(x̄) = xθ_n^* e_ζ, where
θ_n = [⋯[[1,2],3],…,n] is the Dynkin element.

*Proof.*
- The dual basis of B_i = {iy} modulo Sh is given by the left combs [⋯[i, y_1], …, y_{n−1}].
  (The comb has coefficient δ_{yy′} at iy′, and kills Sh.)
- So the L-coordinate of φ_Σ(x) at the class of r is Σ_j ζ^j ⟨x, rγ^jθ_n⟩.
- Since rγ^j e_ζ = ζ^j re_ζ, this gives φ_Σ(x) = Σ_τ ⟨x, τθ_n⟩ τe_ζ = xθ_n^* e_ζ. ∎

COMPUTED (`[dyn]`, n ≤ 5, scalar exactly 1).

φ_Σ ∘ ψ_P is not a scalar (COMPUTED, n ≤ 5). So Theorem Ψ does not directly give the invertibility
of φ_Σ.

**Conjecture 3.3 (CONJECTURED).** φ_Σ is invertible for every P.

## 4. (b) Ordinal sums

Write P ⊕ Q (all of P below all of Q). It is connected, and Lin(P⊕Q) = Lin P · Lin Q.

Structure maps (PROVEN well defined):
- q^M : M_{P⊕Q} = W_P W_Q → M_P ⊗ M_Q, uv ↦ ū ⊗ v̄. This is the deconcatenation at the unique
  cut set P, and R_{P⊕Q} = 0.
- q^L : L_{P⊕Q} → L_P ⊗ L_Q, uve_ζ ↦ ue_{ζ_P} ⊗ ve_{ζ_Q}. L_{P⊕Q} has basis {uve_ζ}. Here
  ζ_P, ζ_Q are primitive |P|-th and |Q|-th roots of unity, as L_P, L_Q require (corrected per
  the audit, row 13; an earlier version wrote e_ζ with ζ the n-th root).

Call a family η "ordinal-compatible" if (η_P ⊗ η_Q) q^M = q^L η_{P⊕Q} for all P, Q.

**Proposition 3 (PROVEN).**
- (i) **Ordinal-compatible families of Aut-isomorphisms exist.**
  - Every poset is uniquely R = R_1 ⊕ ⋯ ⊕ R_k with the R_i ordinally indecomposable, and
    Aut(R) = Π Aut(R_i).
  - For each indecomposable R_i choose an Aut(R_i)-automorphism T_i of C[Lin R_i] with
    T_i(R_{R_i}) = W_{R_i} ∩ K_ζ. It exists by Krull–Schmidt, since R_{R_i} ≅ W ∩ K_ζ as
    Aut-modules (both are complements of isomorphic quotients). Take T_i = id for connected R_i.
  - Put η_R = T_1 ⊗ ⋯ ⊗ T_k for k ≥ 2, and η_{R_i} = the map induced by T_i.
  - Each cut of R is between two consecutive R_i, so each compatibility square commutes.
  - The choices of T_i are arbitrary. So (b) **does not single out an isomorphism.**
- (ii) **Ordinal compatibility excludes every family that is the identity on connected posets.**
  - Suppose η_R = c·(w ↦ we_ζ) for every connected R. This is what Theorem 1(ii) forces for
    extension-naturality among connected posets, and Θ also has this form.
  - Take any disconnected P with |P| ≥ 3 and R = P ⊕ 1. Compatibility gives η_P(ū) = c′·ue_ζ.
    That is well defined only if R_P e_ζ = 0, which is false (Theorem 1).
  - So the canonical Θ is not ordinal-compatible, and extension-naturality on connected posets
    is incompatible with ordinal-compatibility.

## 5. (a) Disjoint sums, and (d) the functorial model

Let P be on S and Q on T, with S ⊔ T = [n] and n = |S| + |T| ≥ 2.

**Proposition 4 (PROVEN).** Consider maps f : C[Lin(P+Q)] → L_P ⊗ L_Q, given on w ∈ Lin(P+Q) by
one of:
- *restriction* w ↦ w|_S ⊗ w|_T;
- *deconcatenation* w ↦ [w = st, s on S] s ⊗ t;
- *cobracket* w ↦ [w = st] s⊗t − [w = ts] s⊗t.

The restriction and deconcatenation maps never descend to L_{P+Q}. The cobracket descends iff P
and Q are both connected and |S| = |T|.

*Proof.*
- The kernel of C[Lin(P+Q)] → L_{P+Q} is spanned by wγ^m − ζ^m w, for m a cut.
- Take w = st, so ts = wγ^{|S|}.
  - Restriction: f(ts) − ζ^{|S|}f(st) = (1 − ζ^{|S|}) s⊗t ≠ 0.
  - Deconcatenation: 0 − ζ^{|S|} s⊗t ≠ 0.
  - Cobracket: (−1 − ζ^{|S|}) s⊗t. This is ≠ 0 unless |S| = n/2.
- If |S| = n/2 and, say, P is disconnected, write s = s_1s_2 at a proper cut. Then
  s_2ts_1 ∈ Lin(P+Q) and f(s_2ts_1) = 0, so the relation fails.
- If P and Q are connected and |S| = |T|, the only cuts are 0, |S|, |T|. Every relation is of the
  first kind with ζ^{n/2} = −1, so it holds.
- s⊗t ≠ 0 in L_P ⊗ L_Q, since se_ζ ≠ 0. ∎

COMPUTED (`[cop]`): all 71 pairs with n ≤ 5. The global note §3.4 found that the commutator
bracket also fails to descend (COMPUTED there; not re-run here).

On the M side the cobracket does descend (PROVEN):
- Deconcatenation Δ̄ is multiplicative for ш.
- Hence Δ̄(u ш v) ≡ u⊗v + v⊗u modulo Sh ⊗ T + T ⊗ Sh, and δ = (1−τ)Δ̄ kills Sh.
- Its (S,T)-component maps W_{P+Q} into W_P ⊗ W_Q, and Sh ∩ W = R (Theorem B).

COMPUTED control: it descends on M for all 71 pairs.

So **(a) is posed on the wrong side.** The disjoint-sum structure lives on M. On the e_ζ model it
exists only after transport by an isomorphism such as Θ, and then compatibility holds by
definition.

**Proposition 5 ((d), PROVEN given (Φ)).** The M-model is natural in every sense considered here:
1. Φ_P is the restriction of the single S_n-isomorphism Φ (ambient-uniform).
2. Along extensions P′ of P, W_{P′} ⊆ W_P induces an *injection* M_{P′} ↪ M_P, since
   R_{P′} = W_{P′} ∩ Sh. This matches H_{P′} ⊆ H_P under Φ.
3. Ordinal sums: q^M as above.
4. Disjoint sums: the cobracket M_{P+Q} → M_P ⊗ M_Q.
5. Dually, the Lie bracket on D_P := Lie_n|_{Lin P} ≅ M_P^* (Cor. 5.4 of the Conjecture S note).
   [F, G] restricted to Lin(P+Q) depends only on F|_{Lin P} and G|_{Lin Q}.

An equivalent model sits inside the free Lie algebra itself:
- Λ_P := π(W_P) ⊂ Lie_n, where π is the orthogonal projection onto Lie_n. Its kernel is
  Lie_n^⊥ = Sh_n.
- Λ_P ≅ M_P canonically and S_n-uniformly.
- By Prop. C′, no S_n-uniform map takes Λ_P or M_P onto W_P e_ζ, even for a single chain.

**Conclusion of Part 2.**
- *The natural object is W_P modulo shuffles.*
- *The e_ζ model is natural along extensions exactly for connected posets (Theorem 1).*
- *For every poset it is canonically, but not functorially, identified with the natural object,
  by the ζ-twisted class-sum map Θ_P (Theorem 2).*

## 6. Reproduce

Code: `compute/natural_isomorphism.py`. It is plain Python 3 and imports `poset_jks_check.py`,
`splitting_cycles.py` and `conjecture_s.py`. Run from `compute/`:

    python3 natural_isomorphism.py --nmax 6 > output/natural_isomorphism.txt   # ~6 s
    python3 natural_isomorphism.py --nmax 7 --only ext,psi > output/natural_isomorphism_n7.txt  # ~100 s
    python3 -m unittest test_natural_isomorphism

Each command exits with status 0 iff every check passes. The last line printed is
`ALL CHECKS PASSED`. Archived outputs: `compute/output/natural_isomorphism.txt` and
`compute/output/natural_isomorphism_n7.txt`.

| Tag | What | Range |
|---|---|---|
| `[ext]` | R_P e_ζ = 0 ⇔ (P connected or n ≤ 2) | all posets, n ≤ 6 (and n = 7 with `--only`) |
| `[wit]` | coefficient of u = t_1st_2⋯t_b in (s ш t)e_ζ is 1/n | every (P, S, s, t), 3 ≤ n ≤ 6 |
| `[lie]` | rank Lie_n e_ζ = (n−1)! | n ≤ 6 |
| `[sum]` | φ_Σ and Σ\|P_i\|φ_i invertible; φ_Σ equivariant (n ≤ 5); control φ_0 not equivariant | disconnected P, n ≤ 6 |
| `[psi]` | ψ_P is an isomorphism (Theorem 2) | all posets, n ≤ 6 (and n = 7) |
| `[wgt]` | Theorem Ψ, random admissible weights; control λ ≡ 1 drops for every disconnected P. Was defective (audit §5, wrong class representatives); **fixed** in 7c10288 | all posets, n ≤ 6 |
| `[dyn]` | φ_Σ(x) = xθ_n^*e_ζ for the antichain | n ≤ 5 |
| `[cop]` | Prop. 4 for the three maps; control: cobracket descends on M | all pairs, n ≤ 5 |

Rigour:
- Arithmetic is modulo primes p ≡ 1 (mod 420), with ζ an n-th root of unity mod p.
- **Full rank mod p proves full rank over Q(ζ).** Reduction modulo a prime of Z[ζ] above p is a
  ring map, so a nonzero minor mod p is nonzero in Z[ζ].
- So `[psi]`, `[sum]` (invertibility), `[lie]` and (since the fix in 7c10288) `[wgt]` are proofs
  for the listed n, the last for the sampled λ.
- A *vanishing* mod p is only evidence. The vanishings in `[ext]` (connected or n ≤ 2) are checked
  at two primes, and are PROVEN anyway (Theorem 1(ii), (iii)).
- Non-vanishings ("R_P e_ζ ≠ 0", "does not descend") are certified by one nonzero coordinate mod
  p, which is nonzero over Z[ζ] as well.

Positive controls (`test_natural_isomorphism.py` and in-script):
- λ ≡ 1 makes the antichain rank drop;
- `[wgt]` rerun with the old least-rotation representatives fails (5/6 at n = 4);
- φ_0 alone is not equivariant;
- the cobracket does descend for C_2 + C_2 and for 1 + 1;
- the witness coefficient for two 2-chains is exactly 1/4;
- (01+10)e_ζ = 0 at n = 2.

## 7. Open

- Conjecture 3.3: φ_Σ invertible for all P.
- ~~An independent audit of Theorem Ψ / Theorem 2.~~ Done: `notes/audit_natural_isomorphism.md`
  (HOLDS).
- ~~Fix `[wgt]` in `compute/natural_isomorphism.py` to use a class member lying in Lin P (audit §5).~~
  Done in commit 7c10288 (mg-dab53).
- Whether Theorem Ψ (weighted contraction) or Cor. Ψ.2 appears in the literature on Klyachko's
  theorem. Not searched.
- A natural e_ζ-side coproduct of a twisted form. A phase-twisted restriction w ↦ χ(w) w|_S⊗w|_T
  is consistent on each class, since its monodromy around a full rotation is
  ζ_n^n ζ_p^{−p} ζ_q^{−q} = 1. But every candidate χ found needs a base letter or base point,
  which is a choice. No canonical χ was found, and this was not pursued.
