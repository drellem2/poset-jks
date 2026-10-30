# Audit: Proposition W′ and its sharpness; Theorem G\* for g outside W

This is an independent adversarial audit of two claims that had not been
audited:
1. **Proposition W′** of `notes/audit_fixed_point_formula.md` §C.3
   ("[AudFP]"). It says the Weisner identity of Prop. W of
   `notes/fixed_point_formula.md` ("[FP]") holds whenever Fix(g) lies in a
   hyperplane of A. [AudFP] says this condition is sharp, but only on
   computed data.
2. **Theorem G\* for g ∉ Stab_W(V).** [FP] §1 identifies χ_V(g) with the
   character of (Lie[A]|_V)^\* (equivalently, (−1)^d μ(Λ(V)^g) with the
   character of det ⊗ (Lie[A]|_V)^\*) for every finite-order linear symmetry
   g of (A, V). Its only support is a remark after the Definition, which
   [FP] marks as "not re-audited" ([FP] §1, §7; [AudFP] §D, §F).

Other sources:
- [GT] = `notes/general_theory.md`;
- [AudA] = `notes/audit_general_theory_cones.md`, where Theorem C (= G\*) is
  proved in §C;
- [AudC] = `notes/audit_theorem_c.md`;
- [Thm] = `notes/poset_jks_theorem.tex`.

Notation is that of [FP] §1:
- A is a finite central essential real arrangement in R^d, with d ≥ 1;
- V is a top-cone, and L = lin V;
- g is a linear map of finite order with gA = A and gV = V;
- U = Fix(g);
- M = Λ(V)^g, the lattice of g-stable flats in Λ(V), with 0̂ = 0 and 1̂ = R^d;
- 𝓛^g is the set of g-stable flats inside L.

The Weisner sum is

  S(g) := Σ_{X ∈ M, X ∩ U = 0} μ_M(X, 1̂).

Tags: **PROVEN** (proof given here, inputs named), **COMPUTED** (by
`compute/audit_prop_w_prime.py`, written for this audit; it imports nothing
from the repository).

## Verdict

**Prop. W′ HOLDS. Its hypothesis is sharp, and that is now PROVEN rather
than only computed: S(g) has an exact closed value (Theorem W″). G\* for g
outside the reflection group HOLDS. It is already proved by Theorem C(iv) of
[AudA], which is stated for any finite group of linear symmetries, with the
sign audited in [AudC] §B. The remark in [FP] §1 is a pointer to that proof,
not a proof. It understates the status.**

| # | Claim | Verdict |
|---|---|---|
| 1 | Prop. W′: g ≠ 1 and Fix(g) in a hyperplane of A ⇒ S(g) = 0 | **HOLDS.** [AudFP]'s proof re-derived step by step (§1.1). A second proof by a conical contraction is in §1.2. COMPUTED on 1,879 pairs: 1,466 with Fix(g) a flat, and 413 with Fix(g) in a hyperplane but not a flat. |
| 2 | Sharpness: Fix(g) in no hyperplane ⇒ S(g) ≠ 0 ([AudFP]: COMPUTED only, "OPEN") | **HOLDS; now PROVEN.** Theorem W″ (§2): if Fix(g) lies in no hyperplane, S(g) = (−1)^{dim Fix g} m(V^{Fix g}), with m ≥ 1. In χ-form, Σ_{X ∈ 𝓛^g, X ∩ Fix g = 0} χ_{V_X}(ḡ) = m(V^{Fix g}). This needs [GT] Theorem 1, but not Brown. COMPUTED: exact on all 285 such pairs. |
| 3 | [AudFP] §C.3 side remark: (−1)^d det(g)·S is "a positive integer, between 1 and 3" | **Explained, and the bound is not general.** The value is m(V^{Fix g}). It reaches 15 on D_4 (§4). |
| 4 | [FP] §4: "the flat hypothesis is needed" | **Overstated**, as [AudFP] already says. The exact condition is now proven: for g ≠ 1, S(g) = 0 **iff** Fix(g) lies in a hyperplane of A. |
| 5 | G\* for g ∉ Stab_W(V): (Lie[A]\|_V)^\* ≅ (Γ_V + Lune)/Lune ≅ det ⊗ H̃_{d−2}(Λ̄(V)) as ⟨g⟩-modules, so χ_V(g) is its character | **HOLDS.** It is PROVEN by [AudA] Thm C(iv) as stated there. That theorem covers every finite group of linear maps preserving A, and [AudC] §B (iv) audits its sign for every linear g. The [FP] remark adds nothing that must be proved. It cites the outline in [GT] §1.5, which states G\* only for "Stab_W(V)". §3 lists the steps that make up the proof and where each is proved. COMPUTED: the trace identity holds on all 2,363 pairs (V, g), 1,548 of them with g outside the reflection group of A. The chain-level sign holds for all 255,432 pairs (g, chamber). This includes a non-orthogonal g of order 6 and the triality elements of W(F_4) acting on D_4. |

No proof in [FP] or [AudFP] is wrong. The corrections are to status tags and
to one bound (§5).

---

## 1. Proposition W′: re-derivation

**Statement ([AudFP] §C.3).** Let g ≠ 1, and let a := cl(U) be the smallest
flat containing U. Suppose a ≠ R^d, that is, U lies in a hyperplane of A.
Then S(g) = 0.

### 1.1 The published proof, checked step by step

1. *a is a g-stable flat containing U.* g permutes the hyperplanes of A that
   contain U, because gU = U. So g·a = a. ✓
2. *X ∩ a ∈ M for every X ∈ M.* This is Lemma B(a) of [FP], with the
   hypothesis as fixed in [AudFP] §C.1: "a is a g-stable flat containing
   Fix(g)".
   - X ∩ |V| is a convex cone of dimension dim X, and g maps it to itself.
   - Averaging a point of its relative interior over ⟨g⟩ gives a point p̄.
     It is g-fixed, so p̄ ∈ U ⊆ a, and it is still in the relative interior,
     because that set is convex and g-stable.
   - So a neighbourhood of p̄ in X ∩ a lies in |V|. Hence
     dim(X ∩ a ∩ |V|) = dim(X ∩ a), and X ∩ a ∈ Λ(V) by [GT] Lemma 0.1(a).
   - X ∩ a is a flat, and it is g-stable.

   The original wording of Lemma B(a) also required a ∈ Λ(V). That made the
   use in [FP] circular. The fixed wording does not need it, and the proof
   above never uses it. ✓
3. *X ∩ a is the meet X ∧ a in M.* It lies in M, and it is the largest
   subspace below both. ✓
4. *The condition X ∩ U = 0 depends only on b = X ∧ a.* Since U ⊆ a, we have
   X ∩ U = (X ∩ a) ∩ U. ✓
5. *Grouping.* S(g) = Σ_{b ∈ M, b ≤ a, b ∩ U = 0} Σ_{X ∈ M, X ∧ a = b} μ_M(X, 1̂).
   ✓
6. *Each inner sum vanishes.*
   - X ∧ a = b forces X ≥ b. So the inner sum runs over the interval [b, 1̂]
     of M. Meets in [b, 1̂] are meets in M.
   - [b, 1̂] is a finite lattice with bottom b. It contains a, since b ≤ a,
     and a ≠ 1̂.
   - The dual Weisner theorem in a finite lattice says: Σ_{x : x ∧ a = 0̂} μ(x, 1̂) = 0
     for every a ≠ 1̂ ([Thm, Lemma weisner] applied to the opposite
     lattice, as in [FP] §4). Applied to [b, 1̂], it kills the inner sum.
   - μ_{[b,1̂]}(X, 1̂) = μ_M(X, 1̂), because intervals agree. ✓
7. *The χ-form.* By Lemma B(b), X ∩ U = 0 forces X ⊆ L, so X ∈ 𝓛^g.
   - det(g|_X) = (−1)^{dim X − dim X^g} ([AudFP] §A.1(i)), so det(g|_X) = (−1)^{dim X}
     when X^g = 0.
   - Lemma A gives μ_M(X, 1̂) = μ(Λ(V_X)^ḡ).
   - So each term equals (−1)^d det(g) χ_{V_X}(ḡ). ✓

The proof is complete and correct. The hypothesis g ≠ 1 is used only in the
form a ≠ R^d, which already implies g ≠ 1.

### 1.2 A second proof (PROVEN)

This proof is the one that generalizes in §2.
- Put Q′ = {X ∈ M : X ≠ R^d, X ∩ U ≠ 0}. Then Q = Q′ ∪ {1̂} is an up-set of
  M, and M ∖ Q is exactly the index set of S(g).
- M has 0̂ ≠ 1̂, so Σ_{X ∈ M} μ_M(X, 1̂) = 0. Hence
  S(g) = −Σ_{X ∈ Q} μ_M(X, 1̂).
- Intervals [X, 1̂] of M lie in Q. So this equals μ(0̂, 1̂) in the poset
  Q̂ = Q′ ∪ {0̂, 1̂}.
- By P. Hall's theorem, that is χ̃(Δ(Q′)).
- If U = 0, then Q′ = ∅ and S(g) = Σ_M μ = 0 directly.
- Otherwise a ∈ Q′. For X ∈ Q′ we have X ∩ a ∈ Q′, because (X ∩ a) ∩ U = X ∩ U ≠ 0.
  Also X ≥ X ∩ a ≤ a.
- So id ≥ r ≤ const_a on Q′, with r(X) = X ∩ a. By the order-homotopy
  lemma (f ≤ g ⇒ Δ(f) ≃ Δ(g); proved at chain level in [AudC] §B.2),
  Δ(Q′) is contractible. Then χ̃ = 0 and S(g) = 0. ∎

## 2. Sharpness: Theorem W″ (exact value of S(g))

**Theorem W″ (PROVEN; inputs: [GT] Lemma 0.1, [GT] Theorem 1, P. Hall's
theorem, Quillen's order-homotopy lemma).** Let (A, V, g) be as above, with
any g, including g = 1. Let U = Fix(g).
- (a) If U lies in a hyperplane of A, then S(g) = 0. This is Prop. W′.
- (b) If U lies in no hyperplane of A, let k = dim U ≥ 1, and define:
  - A^U = {H ∩ U : H ∈ A}, the restriction, an essential arrangement in U;
  - V^U, the top-cone of A^U with |V^U| = |V| ∩ U.

  Then

    S(g) = μ_{Λ(V^U)}(0, U) = (−1)^k m(V^U),   and m(V^U) ≥ 1.

  So S(g) ≠ 0.
- (c) In χ-form,

    Σ_{X ∈ 𝓛^g, X ∩ Fix(g) = 0} χ_{V_X}(ḡ) = m(V^{Fix g}) if Fix(g) lies in no hyperplane of A, and 0 otherwise.

In particular, for g ≠ 1, the identity of Prop. W holds **iff** Fix(g) lies
in a hyperplane of A. At g = 1, (b) is the definition of m(V).

*Proof of (b).* U ≠ 0, because U lies in no hyperplane. As in §1.2,
S(g) = χ̃(Δ(Q′)). We compare Q′ with the proper part P_U = Λ̄(V^U).

*V^U is a top-cone of A^U.*
- |V| ∩ U = {u ∈ U : s_e α_e(u) ≥ 0, e ∈ S_max(V)}.
- No α_e vanishes on U, so this cone is cut out by hyperplanes of A^U.
- It is full-dimensional in U: average an interior point of |V|. The average
  is g-fixed and still interior, so a neighbourhood of it in U lies in |V|.
- A full-dimensional cone cut out by hyperplanes of A^U is the union of the
  closed chambers of A^U that lie in it.
- A^U is essential, because ∩A = 0.

So Λ(V^U) = {flats Z of A^U : dim(Z ∩ |V|) = dim Z}, by [GT] Lemma 0.1(a)
in U.

*π : Q′ → P_U, X ↦ X ∩ U.*
- X ∩ U = ∩_{H ⊇ X} (H ∩ U) is a flat of A^U.
- It is nonzero, since X ∈ Q′.
- It is not U. Otherwise U ⊆ X, and X ≠ R^d is a flat, so U would lie in a
  hyperplane.
- dim(X ∩ U ∩ |V|) = dim(X ∩ U): the averaged point p̄ of §1.1 step 2 is an
  interior point of X ∩ |V| in X, and it lies in X ∩ U.
- π is order-preserving.

*σ : P_U → Q′, Z ↦ cl(Z) = ∩{H ∈ A : H ⊇ Z}.*
- cl(Z) ∩ U = Z. If Z = U ∩ ∩_{e ∈ T} H_e, then cl(Z) ⊆ ∩_{e ∈ T} H_e, so
  cl(Z) ∩ U ⊆ Z. The reverse inclusion is clear.
- cl(Z) is g-stable, because g fixes Z pointwise and so permutes the
  hyperplanes through Z.
- cl(Z) ∈ Λ(V):
  - Take p in the relative interior of Z ∩ |V| in Z, off every hyperplane
    that does not contain Z. Such a p exists: the relative interior is a
    nonempty open subset of Z, and each such hyperplane meets Z in a
    proper subspace.
  - The face F of A containing p has zero set {H : H ⊇ Z}, so span F = cl(Z).
  - F ⊆ |V|, because |V| is an intersection of closed half-spaces of A and
    so is a union of faces.
  - By [GT] Lemma 0.1(a), cl(Z) ∈ Λ(V).
- cl(Z) ≠ R^d and cl(Z) ∩ U = Z ≠ 0, so σ(Z) ∈ Q′.
- σ is order-preserving.

*Galois connection.* For X ∈ Q′ and Z ∈ P_U, Z ⊆ X ∩ U iff cl(Z) ⊆ X.
- If Z ⊆ X ∩ U, then cl(Z) ⊆ X, because X is a flat containing Z.
- Conversely, Z = cl(Z) ∩ U ⊆ X ∩ U.

So π∘σ = id and σ∘π ≤ id. By Quillen's order-homotopy lemma (f ≤ g ⇒
Δ(f) ≃ Δ(g); proved at chain level by the prism operator in [AudC] §B.2),
Δ(π) is a homotopy equivalence Δ(Q′) ≃ Δ(P_U). Hence

  S(g) = χ̃(Δ(Q′)) = χ̃(Δ(Λ̄(V^U))) = μ_{Λ(V^U)}(0, U) = (−1)^k m(V^U),

using Hall's theorem again.

*m(V^U) ≥ 1.* Write W′ for V^U.
- If k = 1, then A^U = {0} in the line U, Λ(W′) = {0, U}, and m = 1.
- Let k ≥ 2. By [GT] Theorem 1 (proven; given the cell facts, the fiber
  theorem can be replaced by [AudA] Prop. A), Δ(Λ̄(W′)) is a wedge of
  m(W′) spheres of dimension k − 2. So m(W′) = rank H̃_{k−2}.
- Take a chamber C of W′.
  - Its chamber cycle ρ_C ([AudA] §C; explicit formula [AudC] §B.1) is a
    (k − 2)-cycle in Δ(Λ̄(C)) ⊆ Δ(Λ̄(W′)).
  - ρ_C has coefficient ±1 on each chain (span F_1 < ⋯ < span F_{k−1}) of a
    complete flag of proper faces of C. Distinct flags give distinct chains,
    because F ↦ span F is injective on the faces of C.
  - So ρ_C ≠ 0 as a chain.
  - Δ(Λ̄(W′)) has no (k − 1)-simplices, so H̃_{k−2} is the space of
    (k − 2)-cycles, and [ρ_C] ≠ 0.
- Hence m(W′) ≥ 1. ∎

*Proof of (c).* By §1.1 step 7, the χ-sum is (−1)^d det(g) S(g). Also
(−1)^d det(g) = (−1)^d (−1)^{d − dim U} = (−1)^{dim U}, by [AudFP] §A.1(i)
with X = R^d. ∎

**Remarks.**
- The argument for m ≥ 1 applies to every top-cone. **m(V) ≥ 1 for every
  top-cone V.** [GT] Theorem 1 states only m(V) ≥ 0. (COMPUTED: `[m>=1(V)]`,
  199 cones.)
- [AudFP] §C.3 sketched a route to necessity: "Q ∖ {1̂} should be a
  sphere-like poset". This is now made precise. Q ∖ {1̂} is homotopy
  equivalent to Λ̄(V^{Fix g}), which is a wedge of m ≥ 1 spheres of
  dimension dim Fix(g) − 2.
- When Fix(g) lies in no hyperplane, the generic points of Fix(g) are
  interior to chambers. By [FP] Lemma F, the g-fixed chambers of V
  correspond to the chambers of V^{Fix g}. So m(V^{Fix g}) ≤ #V^g, with
  equality when V^{Fix g} is pointed. The negative control `neg:Wex-count`
  shows the two numbers differ in general (§4).

## 3. Theorem G\* for g ∉ Stab_W(V)

### 3.1 Is the [FP] remark a proof?

[FP] §1 says: "G\* is stated there for Stab_W(V). The proof outline in [GT,
§1.5] uses only g·ρ_C = det(g) ρ_{gC} for linear g, so we read it as holding
for any linear symmetry; that reading has not been re-audited."

**This is not a proof.** It points to one step of an outline and asserts
that nothing else uses W. **The proof does exist, though.** [AudA] §C,
Theorem C(iv), is stated "for every finite group W of linear maps preserving
A, and every g ∈ Stab_W(V)". So "W" there is not the reflection group.
[AudC] §B (iv) audits that step and records that "for a general g, read
sign det g" and that finiteness is needed only so that the module is a
representation of a finite group. Taking W = ⟨g⟩ gives G\* for every
finite-order g with gA = A and gV = V. The phrase "stated there for
Stab_W(V)" in [FP] refers to [GT] §1.5. That section writes "symmetry group
W", which [FP] §1 reads as the reflection group. The source of the
statement, [AudA] Theorem C(iv), is already general.

### 3.2 The proof, step by step, with g any finite-order linear symmetry

Re-derived here. Each step names where it is proved and confirms that it
uses no reflection-group property.

1. *g acts on everything in sight.* g permutes the faces of A and preserves
   the face order, the Tits product and spans: span(gF) = g span F.
   - From gV = V: g acts on Q′ (non-chamber faces ≠ O of V), on Λ̄(V), on
     L̄(A) and on Γ_V.
   - f : F ↦ span F commutes with g.
   - Only linearity and gA = A, gV = V are used.
2. *Chain-level sign* ([AudC] §B.1, (iv)).
   - [C] = Σ ε(F_1 < ⋯ < F_d = C)(F_1, …, F_d), with
     ε = sign det(b_1, …, b_d) for any b_i ∈ F_i. The sign does not depend
     on the choice, because each F_i is convex and the determinant never
     vanishes.
   - g b_i ∈ gF_i, so ε(gF_•) = sign det(g) · ε(F_•).
   - So g_#[C] = sign det(g) [gC] and g·ρ_C = sign det(g) ρ_{gC}. For finite
     order, sign det(g) = det(g) = ±1.
   - No orthogonality and no reflection is used.
3. *ker φ = Lune* ([AudA] Prop. B, audited in [AudC] §B.2). φ : C ↦ ρ_C is
   defined without any group. Lune is the span of the non-singleton top-lunes,
   and g permutes those, since gL(H, D) = L(gH, gD).
4. *Restriction to V* ([AudA] Thm C(i)–(ii)).
   - The ρ_C with C ∈ V span H̃_{d−2}(Λ̄(V)).
   - H̃_{d−2}(Λ̄(V)) → H̃_{d−2}(L̄(A)) is injective, since both complexes
     have dimension ≤ d − 2.
   - So φ|_{Γ_V} induces Γ_V/(Γ_V ∩ Lune) ≅ H̃_{d−2}(Λ̄(V)).
   - By step 2 this map intertwines g with det(g)·g. Hence
     H̃_{d−2}(Λ̄(V)) ≅ det ⊗ Γ_V/(Γ_V ∩ Lune) as ⟨g⟩-modules.
   - The kernel Γ_V ∩ Lune is g-stable automatically, as the kernel of an
     equivariant map.
5. *Dual form.*
   - The pairing ⟨C, D⟩ = δ_{CD} on Γ is invariant under every permutation
     of chambers.
   - Lie[A] = Lune^⊥ (the Ree criterion, CITED as in [GT] §0).
   - So Lie[A]|_V is the annihilator of Γ_V ∩ Lune in Γ_V^\*, and
     (Lie[A]|_V)^\* ≅ Γ_V/(Γ_V ∩ Lune) ≅ (Γ_V + Lune)/Lune, g-equivariantly.
   - These modules are defined over Q, so their characters are real, and
     dualizing does not change the character.
6. *Character* ([FP] §1, "Why χ_V is the character we want").
   - g acts on Δ(Λ̄(V)) simplicially. A g-stable chain of flats is fixed
     pointwise, since g preserves the order. So the trace on chains is the
     count of g-fixed chains, with sign +1.
   - Hopf's trace formula and Hall's theorem give
     Σ_i (−1)^i tr(g | H̃_i) = μ(Λ(V)^g).
   - By [GT] Theorem 1, only i = d − 2 survives, so
     tr(g | H̃_{d−2}(Λ̄(V))) = (−1)^d μ(Λ(V)^g).
   - No group property is used.

Combining steps 4–6:

  χ_V(g) = (−1)^d det(g) μ(Λ(V)^g) = det(g)·tr(g | H̃_{d−2}) = tr(g | Γ_V/(Γ_V ∩ Lune)) = tr(g | (Lie[A]|_V)^\*).

Equivalently, (−1)^d μ(Λ(V)^g) is the character of det ⊗ (Lie[A]|_V)^\*.
**HOLDS** for every finite-order linear symmetry g of (A, V). Steps 1–5 are
[AudA] Thm C(iv) as stated, with the sign audited in [AudC]. Step 6 is
[FP]'s homchar argument, which [AudFP] §F already notes is group-free.

**What was missing** is a citation, not an argument. [FP] §1 should cite
[AudA] Thm C(iv) and [AudC] §B (iv) in place of "we read it as holding …
not re-audited".

## 4. Computations (COMPUTED)

`compute/audit_prop_w_prime.py`, plain Python 3. Faces and flats use exact
rationals. The Lune quotient traces use exact elimination modulo
p = 2^31 − 1 on the chamber space, with dimensions cross-checked against
m(V) (`[q=m]`). The script imports nothing from the repository.
- Faces come from oriented-matroid covector closure of the cocircuits.
- Flats are closed sets of hyperplanes.
- Symmetries act through their induced signed permutation of hyperplanes,
  which is checked to exist for every element of G.
- Every top-cone of each arrangement is enumerated by intersecting
  half-spaces. One cone is taken per G-orbit, and every element of its
  stabilizer is tested.
- A^U is built in coordinates on U = Fix(g), and m(V^U) is computed from
  its own faces. It is not derived from M.

**Arrangements.**

| arrangement | d | hyperplanes | chambers | top-cones | G | G-orbits of cones | g outside the reflection group of A |
|---|---|---|---|---|---|---|---|
| A_3 (as D_3) | 3 | 6 | 24 | 219 | W(B_3), 48 | 12 | odd sign changes, incl. −1 |
| B_3 | 3 | 9 | 48 | 941 | W(B_3), 48 | 35 | none (control) |
| tetra7: x_i = 0, (1, ±1, ±1)^⊥ | 3 | 7 | 32 | 397 | signed permutations, 48 | 21 | all; A is not a reflection arrangement |
| hex7: z = 0 and the ⟨h⟩-orbit of x + z | 3 | 7 | 38 | 507 | ⟨h, −1⟩, 12 | 48 | all; h = [[0,−1,0],[1,1,0],[0,0,1]] has order 6, is **not orthogonal**, and Fix(h) lies in no hyperplane |
| A_4 (coordinates y_i = x_i − x_5) | 4 | 10 | 120 | 4,231 | ±S_5, 240 | 39 | −w |
| D_4 | 4 | 12 | 192 | 12,313 | W(F_4), 1,152 | 44 | W(F_4) ∖ W(D_4), incl. **triality** |

**Results** (archived in `compute/output/audit_prop_w_prime.txt`; every
asserted check passes):

| check | statement | checks | failures |
|---|---|---|---|
| `[Wp]` | Fix(g) in a hyperplane, g ≠ 1 ⇒ S(g) = 0 (Prop. W′) | 1,879 | 0 |
| `[Wex]` | Fix(g) in no hyperplane ⇒ S(g) = (−1)^{dim U} m(V^U) (Thm W″) | 285 | 0 |
| `[m>=1]` | m(V^U) ≥ 1 | 285 | 0 |
| `[m>=1(V)]` | m(V) ≥ 1 for every cone (§2 remark) | 199 | 0 |
| `[sgn]` | (−1)^d det(g) = (−1)^{dim Fix g} | 2,164 | 0 |
| `[G*]` | tr(g \| (Γ_V + Lune)/Lune) = (−1)^d det(g) μ(Λ(V)^g) | 2,363 | 0 |
| `[q=m]` | dim (Γ_V + Lune)/Lune = m(V) | 199 | 0 |
| `[rho]` | g·ρ_C = sign det(g) ρ_{gC} at chain level | 255,432 | 0 |

The `[G*]` pairs by class of g:

| arrangement | g = 1 | g ∈ W∖1 | g outside W |
|---|---|---|---|
| A_3 | 12 | 36 | 37 |
| B_3 | 35 | 99 | — |
| tetra7 | 21 | — | 97 |
| hex7 | 48 | — | 28 |
| A_4 | 39 | 200 | 153 |
| D_4 | 44 | 281 | 1,233 |

The Weisner sum for g ≠ 1, by where Fix(g) sits:

| arrangement | Fix(g) a flat: S = 0 | in a hyperplane, not a flat: S = 0 | in no hyperplane: S ≠ 0 |
|---|---|---|---|
| A_3 | 53 | 9 | 11 |
| B_3 | 99 | — | — |
| tetra7 | 52 | — | 45 |
| hex7 | 9 | — | 19 |
| A_4 | 245 | 72 | 36 |
| D_4 | 1,008 | 332 | 174 |

The A_3 and A_4 columns "in a hyperplane, not a flat" and "in no hyperplane"
reproduce [FP]'s "11 of 20" and "36 of 108" failures, and [AudFP]'s 9/11 and
72/36 splits, by independent code. [FP]'s D_4 figure (250 of 642) counts
W(B_4)-orbits of cones. Here the orbits are W(F_4)-orbits, so the counts
are not comparable.

The values of m(V^{Fix g}) found are:
- 1–3 on A_3, A_4 and tetra7;
- 1 on hex7, where Fix(g) is a line;
- 1–5 on D_4 with dim Fix(g) = 2;
- 1–15 on D_4 with dim Fix(g) = 3.

So the "between 1 and 3" of [AudFP] §C.3 was a property of its sample.

**Positive controls** (all fire):
- the chamber counts 24, 48, 120 and 192;
- the top-cone counts 219, 941, 4,231 and 12,313 (the first three as in
  [GT], the last as in [FP] §5);
- |W(F_4)| = 1,152;
- dim Lune = #chambers − |μ(L(A))| on all six arrangements (18, 33, 23, 26,
  96, 147). This is [AudA] Prop. B;
- Prop. W itself (Fix(g) a flat), S = 0 on 1,466 pairs;
- the A_3/A_4 splits above.

**Negative controls** (each must fail somewhere, and each does):
- `[Wex]` with #V^U in place of m(V^U): 128 of 285 fail;
- `[Wex]` without the sign (−1)^{dim U}: 131 of 285 fail;
- `[G*]` without det(g): 582 of 2,363 fail;
- `[G*]` with the permutation character #V^g in place of the Lune quotient:
  1,267 of 2,363 fail;
- `[rho]` with sign +1 in place of sign det(g): 127,716 of 255,432 fail.

## 5. Corrections to existing notes (not applied)

Per the standing constraints, no existing note was edited.
- **[AudFP] verdict table, Prop. W row, and §C.3 "Is the weak hypothesis
  necessary? (OPEN)":** necessity is now PROVEN (Theorem W″). For g ≠ 1 the
  identity holds iff Fix(g) lies in a hyperplane of A. When it does not,
  the sum is (−1)^{dim Fix g} m(V^{Fix g}) ≠ 0.
- **[AudFP] §C.3, side experiment:** "(−1)^d det(g) times the sum was always a
  positive integer, between 1 and 3". The value is m(V^{Fix g}), and the
  range 1–3 is not general (up to 15 on D_4).
- **[AudFP] §D, last row, and §F, first bullet:** G\* for g ∉ Stab_W(V) is
  covered by [AudA] Thm C(iv) as stated, audited in [AudC] §B (iv) (§3
  above).
- **[FP] §1, the remark after the Definition, and [FP] §7, last bullet:**
  replace "we read it as holding for any linear symmetry; that reading has
  not been re-audited" by a citation to [AudA] Thm C(iv) and [AudC] §B (iv).
- **[FP] §4, "The flat hypothesis is needed":** read "the hypothesis can be
  weakened to: Fix(g) lies in a hyperplane of A, and that is exact
  (Thm W″ of `notes/audit_prop_w_prime.md`)".
- **[GT] §1.5, statement of Theorem G\*:** "with symmetry group W …
  Stab_W(V)-modules" should say "for every finite group G of linear maps
  with GA = A … Stab_G(V)-modules", matching [AudA] Thm C(iv).
- **[GT] Theorem 1:** m(V) ≥ 0 can be sharpened to m(V) ≥ 1 (§2 remark).

## Reproduce

From `compute/` (plain Python 3; no third-party packages):

    python3 audit_prop_w_prime.py > output/audit_prop_w_prime.txt   # ~30 s; ends "ALL CHECKS PASSED", exit 0
    python3 audit_prop_w_prime.py --quick                             # < 1 s: A3, B3, tetra7, hex7
    python3 -m unittest test_audit_prop_w_prime                       # < 1 s, positive and negative controls

The archived log is `compute/output/audit_prop_w_prime.txt`.
