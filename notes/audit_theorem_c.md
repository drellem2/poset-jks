# Audit: Theorem C (chamber cycles span; Conjecture G\*) and Props. A, B

Work item: mg-96f1a. This is an independent adversarial audit of §C of
`notes/audit_general_theory_cones.md` ("[AudGT]"): Proposition A,
Proposition B and Theorem C. Those results appeared beyond the brief of
the audit that produced them, so no one had yet read them adversarially.
Other sources are abbreviated as follows:
- [GT] = `notes/general_theory.md`;
- [Thm] = `notes/poset_jks_theorem.tex`.

Every step of Props. A and B and of Theorem C was re-derived by hand. Each
cited input was read in a source where one was accessible. The
computations are `compute/audit_theorem_c.py`, written for this audit. It
imports nothing from the repository, and it builds the faces by a
different method from the earlier scripts (see §E). No existing file was
changed.

Tags for this audit's own claims: **PROVEN** (proof given here) and
**COMPUTED** (script and command in Reproduce).

## Verdict

| Claim | Verdict |
|---|---|
| Proposition A (BWW is removable from Theorem 1) | **HOLDS.** |
| Proposition B (Φ_A exists: ker(C ↦ ρ_C) = Lune) | **HOLDS.** It needs one proof fix in positive characteristic, inherited from Prop. 3(b) (§B.3). Its sign convention matches Prop. Φ of [Thm] up to one global sign c_n = ±1 that depends only on n (§C). |
| Theorem C (chamber cycles span every top-cone; Conjecture G\* holds) | **HOLDS WITH FIXES.** The fixes are to proofs and statements; no conclusion changes. (1) Prop. 3(a) must say "non-singleton lunes" (already in [AudGT]). (2) In characteristic p, Prop. 3(b) must count multiplicities by rank, not by trace (§B.3). (3) The cell facts and two homotopy lemmas should be cited or proved; full proofs are in §A and §B. |
| Braid case of the det-twisted identity vs [Thm] | **Reproduces the main theorem's sgn twist exactly** (§C). As a by-product, Prop. Φ of [Thm] is PROVEN for every n given Brown, without Wachs or Ree (§C.3). |

Hypotheses that Theorem C actually needs:
- A finite, real, central arrangement. Essentiality can be assumed without
  loss of generality.
- d ≥ 2.
- V a nonempty top-cone. V may be pointed or not, and may be all chambers
  or a single chamber.

No further hypothesis is missing (§D).

COMPUTED (§E): Theorem C(i) on 1,210 sampled cones of three arrangements the
earlier audit did not use:
- a non-simplicial (hence non-Coxeter) arrangement R4 in R^4;
- a non-simplicial arrangement R5 in R^5;
- non-pointed cones of B_4 and A_5.

110 of the cones were also checked by exact rank over Q. Also checked:
- Prop. B at chain level on R4, R5 and B_4;
- q(V) = m(V);
- the det twist at chain level on B_4 and on the braid arrangement A_4;
- the braid sign constant c_n for n = 3,…,6.

Every check has a positive control that fires. No failures.

---

## A. Proposition A — HOLDS

**Statement ([AudGT, §C]).** Let Q′ be the faces F ≠ O of V that are not
chambers, and let f : Q′ → Λ̄(V), F ↦ span F. Then there is a map
g : Δ(Λ̄(V)) → Δ(Q′) with Δ(f) ∘ g ≃ id. Hence f_* is split surjective on
H̃_i for every i, and onto on π_1.

**Re-derivation.**

1. **The carrier is well defined.** Take a simplex σ of sd Δ(Λ̄(V)), that
   is, a flag of chains c_0 ⊂ ⋯ ⊂ c_k. Put Y(σ) = max c_k and
   Φ(σ) = Δ(f^{-1}(Λ̄_{≤Y})).
   - f^{-1}(Λ̄_{≤Y}) is the set of faces F ≠ O with F ⊆ |V| ∩ Y. No such F
     is a chamber, because Y ≠ R^d.
   - The set is nonempty, because Y ∈ Λ(V) is the span of some face of V.
   - Its order complex is |V| ∩ Y ∩ S, by the cell facts (§A.1).
   - By Lemma 0.1(a) of [GT], dim(|V| ∩ Y) = dim Y. Lemma 0.2 of [GT] then
     says that this is S^{dim Y − 1} if Y ⊆ lin V and contractible
     otherwise.
   - Lemma 0.2 was re-derived. It is correct for non-pointed cones C ≠ Y:
     the proof uses only C ∩ −int C = ∅, and that holds whenever C ≠ Y,
     pointed or not.
   - If τ ⊆ σ, then the top chain of τ is a subset of c_k, so
     Y(τ) ≤ Y(σ) and Φ(τ) ⊆ Φ(σ).
2. **Dimension count.** c_k is a chain of proper flats inside [0, Y], so it
   has at most dim Y elements, with dimensions in 1, …, dim Y. Since
   c_0 ≠ ∅ and the c_i strictly increase, k ≤ |c_k| − 1 ≤ dim Y − 1.
   - The boundary ∂σ ≅ S^{k−1} needs to extend over σ inside Φ(σ). So
     Φ(σ) must be (k − 1)-connected, and k − 1 ≤ dim Y − 2.
   - S^{dim Y − 1} is (dim Y − 2)-connected, and a contractible space is
     ∞-connected. For dim Y = 1 the requirement is "nonempty", and k = 0.
   - So g exists, built skeleton by skeleton. **Checked.**
3. **The homotopy.** Both h_0 = Δ(f) ∘ g and h_1 = the canonical
   homeomorphism |sd Δ| → |Δ| send σ into
   T(σ) := Δ(Λ̄_{≤Y(σ)}).
   - For h_1: σ lies in the simplex c_k.
   - For h_0: Δ(f)(Φ(σ)) ⊆ T(σ).
   - T(σ) is a cone with apex Y(σ), so it is contractible, and T is
     monotone in σ.

   **Carrier lemma (PROVEN here, so that no citation is needed).** Let K
   be a finite simplicial complex. Let h_0, h_1 : |K| → X be maps with
   h_j(σ) ⊆ T(σ), where T is monotone and every T(σ) is contractible.
   Then h_0 ≃ h_1.

   *Proof.* Define H on |K| × {0, 1} by the h_j. Then extend over σ × I
   by induction on dim σ. The boundary ∂(σ × I) = ∂σ × I ∪ σ × {0, 1} is
   a sphere. By monotonicity and induction, H already maps it into T(σ),
   which is contractible, so H extends over σ × I with image in T(σ). ∎

4. **Consequences.**
   - f_* g_* = id on H̃_*(−; Z), so f_* is split surjective.
   - On π_1 the composite is an isomorphism, up to change of basepoint, so
     f_* is onto.

**Consequence (A1): Theorem 1 of [GT] without BWW. Checked.**
- H̃_i(Δ(Λ̄(V))) is a direct summand of H̃_i(X).
- By Step 4 of [GT] (re-read), H̃_i(X) = 0 for i < d − 2 and H̃_{d−2}(X)
  is free. X has dimension d − 2, so H̃_i(X) = 0 for i > d − 2.
- For d ≥ 4, π_1(X) = π_1(Z) = 1, because (Z, X) is (d − 2)-connected. So
  π_1(Δ(Λ̄(V))) = 1.
- For d = 3, H̃_0 = 0 gives connectedness. For d = 2 nothing more is
  needed.
- Hurewicz–Whitehead, as in Step 5 of [GT], then gives a wedge of
  (d − 2)-spheres.
- The rank is (−1)^d μ(0, R^d) = m(V), by P. Hall's theorem. Read: Wachs,
  *Poset topology*, arXiv:math/0602226, Prop. 1.2.6.

**Consequence (A2): Theorem C(i). Checked.**
- H̃_{d−2}(Z) = 0. For d ≥ 3, Z is a sphere S^{d−1} or contractible. For
  d = 2, Z is S^1 or an arc.
- So the connecting map H_{d−1}(Z, X) → H̃_{d−2}(X) is onto.
- H_{d−1}(Z, X) is free on the relative fundamental classes [C] of the
  closed cells (excision; each C̄ ∩ S is a (d − 1)-ball with boundary in
  X).
- The connecting map sends [C] to ∂[C], and Δ(f)_# sends ∂[C] to ρ_C.

### A.1 The cell facts, read in a source

Theorem C uses two facts, which [GT, §0] cites to Björner–Las Vergnas–
Sturmfels–White–Ziegler and to Björner 1984.

1. **(Regular cells.)** The faces F ≠ O of an essential A meet S in the
   open cells of a regular CW decomposition of S^{d−1}.
2. **(Order complex.)** The order complex of the face poset of a finite
   regular CW complex is homeomorphic to the complex.

- **BLSWZ and Björner 1984: NOT ACCESSIBLE** here (no open copy found).
- **Björner, *Topological methods* (Handbook of Combinatorics): NOT
  ACCESSIBLE.** Guessed URLs on the author's KTH pages returned 404.
- **Fact 2 is read in an open source.** Matoušek, *Using the Borsuk–Ulam
  theorem* (Springer 2003; author-hosted PDF), §4.5, "Notes", p. 85:
  > in a regular (finite) cell complex [...] if we define the partial
  > order on the set of closed cells by inclusion, then the order complex
  > of this poset is homeomorphic to the original cell complex (and it is
  > natural to call the resulting simplicial complex the first barycentric
  > subdivision of the regular cell complex).

  This is stated without proof. Wachs's notes cite it as [23] (Björner
  1984) but do not state it in this form. Wachs's Theorem 3.1.12, also by
  Björner, is a related recognition theorem and is not what is used.
- **Fact 1 is elementary (PROVEN).**
  - For essential A, each closed face F̄ is a pointed polyhedral cone. Its
    faces are the faces of A below F.
  - Pick u in the interior of the dual cone of F̄. Then
    F̄ ∩ {⟨u, x⟩ = 1} is a polytope of dimension dim F − 1, and radial
    projection maps it homeomorphically onto F̄ ∩ S.
  - Its relative interior goes to F ∩ S, and its boundary goes to the
    union of the proper faces.

**A version that needs neither fact.** Everything in the proofs is about
the order complex Δ(faces ≠ O). The topological input used is only this:
- (i) Δ(faces ≠ O, ≤ C) is a (d − 1)-ball whose boundary is
  Δ(faces ≠ O, < C);
- (ii) Δ(faces ≠ O of |V| ∩ Y) has the homotopy type of |V| ∩ Y ∩ S.

Both follow from a concrete geometric realization.
- Choose b(F) ∈ F, for example the sum of the rays of F̄.
- Map each chain F_1 < ⋯ < F_k to the cone spanned by b(F_1), …, b(F_k).
- These cones form a simplicial fan refining the fan of A. This is the
  derived subdivision of each polytope F̄ ∩ {⟨u, x⟩ = 1}, and it is
  compatible across faces because b(F) is chosen once per face.
- So Δ(faces ≠ O) is homeomorphic to S^{d−1}, with Δ(faces ≤ F) going to
  F̄ ∩ S.

The script checks the combinatorial shadow of this. With
ε(F_1 < ⋯ < F_d) = sign det(b(F_1), …, b(F_d)), the chain Σ_C [C] is a
cycle for R4, R5 and B_3, and it is not a cycle with all signs +1
(COMPUTED, §E).

## B. Proposition B and Theorem C — HOLD (Theorem C with fixes)

### B.1 An explicit formula for ρ_C (PROVEN; sharpens [AudGT])

[AudGT] orients [C] "by a fixed orientation of R^d". Concretely:

  [C] = Σ ε(F_1 < ⋯ < F_{d−1} < C) · (F_1, …, F_{d−1}, C),
  ε(F_1, …, F_d) = sign det(b_1, …, b_d), with b_i ∈ F_i,

where the sum is over complete flags of faces of C̄ with dim F_i = i.

**ε is well defined.** Each b_i ∈ F_i ⊆ span F_i, and b_i ∉ span F_{i−1}:
F_i is a face not contained in the flat span F_{i−1}, so it is disjoint
from some hyperplane through that flat. So the determinant never
vanishes. Each F_i is convex, so the sign does not depend on the choice
of b_i.

**∂[C] avoids C.** In ∂[C], the terms that delete some F_i with i < d
cancel in pairs.
- The interval (F_{i−1}, F_{i+1}) of the face lattice of the pointed cone
  F̄_{i+1} has exactly two elements, F_i and F_i′ (diamond property).
- Modulo span F_{i−1}, the points b_i and b_i′ span the two boundary rays
  of a 2-dimensional pointed cone, and b_{i+1} lies strictly between them.
- So the two determinants have opposite signs.

Hence

  ρ_C = (−1)^{d−1} Σ ε(F_1 < ⋯ < F_{d−1} < C) · (span F_1 < ⋯ < span F_{d−1}),

a chain in Δ(Λ̄(C)) ⊆ Δ(Λ̄(V)) with coefficients ±1.

**Adjacent chambers induce opposite orientations.** Let C and C′ be
adjacent across a wall W ⊆ h_e. Then b(C) and b(C′) lie on opposite sides
of h_e = span(b_1, …, b_{d−1}), so ε changes sign. This is what Prop. B
step 2 uses.

### B.2 Proposition B, step by step

**Step 1 (onto) is (A2) with V = all chambers. Checked.**

**Step 2 (Lune ⊆ ker φ). Checked.**

- *The lune.* For H ≠ O, the lune L(H, D) = {C : HC = D} is
  {C : C_e = D_e for e ∈ z(H)}, since HC = D forces C_e = D_e exactly on
  z(H). It is a top-cone with |ℒ| = {D_e α_e ≥ 0, e ∈ z(H)}, whose
  lineality is ∩_{z(H)} h_e = span H =: K.
- *The case H a chamber.* Then ℒ is all chambers, and Σ_C [C] is a cycle
  by B.1, so z := Σ_C ∂[C] = 0.
- *The cycle z.* Otherwise 0 ≠ K ≠ R^d. z = ∂(Σ_{C∈ℒ} [C]) is a cycle.
  - By B.1, the terms whose top wall W lies between two chambers of ℒ
    cancel.
  - A wall W between C ∈ ℒ and C′ ∉ ℒ lies in the unique h_e on which C
    and C′ differ, and C′ ∉ ℒ forces e ∈ z(H).
  - So z lives on Q″ = {F ∈ Q′ : F ⊆ h_e for some e ∈ z(H)}, which is a
    down-set.
- *Pushing into a cone.* On Q″, put g(F) = span F ∨ K, the join in L(A).
  - g is monotone.
  - g(F) ⊆ h_e, because h_e is a flat containing F and K. So
    g(F) ≠ R^d.
  - g(F) ≥ K ≠ 0.
  - f ≤ g pointwise.
- *The homotopy.* The prism operator
  P(x_0 < ⋯ < x_k) = Σ_i (−1)^i (f x_0, …, f x_i, g x_i, …, g x_k),
  with degenerate terms dropped, is a chain homotopy f_# ≃ g_#. Each term
  is a chain, since f x_j ≤ f x_i ≤ g x_i ≤ g x_l for j ≤ i ≤ l. This is
  Quillen's order-homotopy property at the chain level; Quillen 1978,
  Prop. 1.3, was NOT ACCESSIBLE, so it is proved here.
- *Conclusion.* g_#(z) lies in the cone Δ(L̄_{≥K}), so it is a boundary.
  Hence f_#(z) = Σ_{C∈ℒ} ρ_C is a boundary in a complex of dimension
  d − 2, so it is 0 as a chain.
- *d = 2.* z is a reduced 0-cycle (augmentation 0, being a boundary), and
  the argument is the same.

**Step 3 (dim Γ/Lune ≤ |μ|). Checked; HOLDS WITH FIXES in characteristic
p (§B.3).**
- For V = all chambers, L = R^d, and every non-singleton lune lies in V.
- Prop. 3(a), with the non-singleton fix, gives
  Lune = Lie_{R^d}(Γ)^⊥, so dim Γ/Lune = dim Lie_{R^d}(Γ).
- Lie_{R^d}(Γ) is a submodule on which x ≠ O acts by 0 and O acts by 1.
  So all its composition factors are S_0, and its dimension is at most
  [Γ : S_0] = Σ_X μ(0, X) c_X = m(all) = |μ(L(A))|. The last equality is
  Theorem 2 of [GT], or Rota's sign alternation.

**Step 4. Checked.**
- rank H̃_{d−2}(L̄(A)) = |μ(L(A))|, by (A1) for V = all, which is
  Folkman's theorem.
- φ induces a surjection Γ/Lune ↠ H̃ (Steps 1–2) from a space of
  dimension ≤ |μ| (Step 3) onto a space of dimension |μ|. So it is an
  isomorphism and ker φ = Lune.
- Over any field k, dim_k H̃_{d−2}(L̄(A); k) = |μ|, because the integral
  homology is free and concentrated in degree d − 2 (universal
  coefficients).

**A check on Prop. 3(a) as used.**
- The identity "non-singleton lune ⟺ L(H, D) with H ≠ O" needs
  essentiality.
  - If H ≠ O, then K = span H ≠ 0.
  - Since A is essential, some hyperplane h_e has H_e ≠ 0, so K ⊄ h_e.
  - So |ℒ| contains a line not in h_e, and ℒ has chambers on both sides of
    h_e. Hence ℒ is not a singleton.
- Lemma L ("L(H, D) ⊆ V iff D ∈ V and H ⊆ lin V") was re-derived by the
  same argument. If e ∈ S_max(V) and H_e ≠ 0, then ℒ has chambers on both
  sides of h_e, but V does not.

### B.3 Positive characteristic: Prop. 3(b) needs Brown's rank argument, not a trace

[GT, Prop. 3(b)] and [AudGT] obtain the multiplicities [Γ_V : S_X] from
traces:

  tr(x | Γ_V) = Σ_X [Γ_V : S_X] χ_X(x).

Over a field of characteristic p this is an identity in k. It determines
the integers [Γ_V : S_X] only modulo p. So "k any field" in Theorem C is
**not justified by the argument as written**.

**Fix (PROVEN; read in Brown).** Replace trace by rank, exactly as Brown
does in the proof of his Theorem 4 (arXiv:math/0006145, §7.3).
- x ∈ Σ_L acts on Γ_V as an idempotent. Its image is spanned by the
  chambers of V that are ≥ x, so its rank is the integer c_{span x}.
- In a composition series, x is triangular with diagonal entries
  χ_{X_i}(x) ∈ {0, 1} (Brown, end of §7.2).
- The rank of an idempotent equals the multiplicity of the eigenvalue 1,
  over any field.
- So c_Y = Σ_{X ⊇ Y} [Γ_V : S_X] as integers, and Möbius inversion gives
  [Γ_V : S_0] = m(V) over every field.

Brown's own sentence: "the rank of a projection is the multiplicity of 1
as an eigenvalue, so r = Σ_{Y≥X} m′_Y" (p. 22).

With this fix, Prop. B, and hence Theorem C (ii)–(iv), hold over every
field. Theorem C(i) is integral and never needed it.

The fix matters only in characteristic p. [Thm] and every use downstream
work over C, where the trace argument is already correct.

COMPUTED corroboration: the lune matrices of R4, R5 and B_4 have the same
rank over Q, GF(2) and GF(3) (§E). So Z^Γ/Lune_Z has no 2- or 3-torsion
there, as the fixed statement predicts. Over every prime this follows from
the fix: dim_{GF(p)} Γ/Lune = |μ| = dim_Q.

### B.4 Brown's theorem as used, read independently

Read in arXiv:math/0006145 (Brown, *Semigroups, rings, and Markov chains*,
J. Theoret. Probab. 13 (2000)), from the arXiv PDF.

- **§2.1, Definition.** S is an LRB if there are a lattice L and a
  surjection supp : S ↠ L with
  - (2) supp xy = supp x ∨ supp y, and
  - (3) xy = x if supp y ≤ supp x.
- **§7.2.** "We therefore work in the semigroup algebra kS of S over an
  arbitrary field k."
  - **Theorem 3 (Bidigare):** "There is an algebra surjection ψ : kS ↠ k^L
    whose kernel J is nilpotent. The X-component of ψ is the homomorphism
    χ_X : kS → k given by χ_X(y) = 1_{supp y ≤ X}."
  - **Corollary:** "Every irreducible representation of kS is
    1-dimensional. There is one such for each X ∈ L, given by the
    character χ_X."
- **End of §7.2 and proof of Theorem 4 (§7.3):** simultaneous
  triangularization, and the rank argument quoted in §B.3.

**Hypotheses for Σ_L = faces of A inside L = lin V (checked
independently).** Take supp = span and L = Λ_L = [0, L] in L(A). This is
a lattice, being an interval of a lattice.
- *Surjective.* Each flat X ⊆ L has a face of span X, and that face lies
  in X ⊆ L.
- *(2).* Take x₀ ∈ x and y₀ ∈ y. For small ε > 0, x₀ + εy₀ ∈ xy, and
  x₀ ∈ closure(xy). So y₀ ∈ span(xy), and span xy ⊇ span x + span y.
  Conversely, let J be the join flat. Then x₀ + εy₀ ∈ J, and a face
  meeting a flat lies in it, so xy ⊆ J. Hence span xy = J.
- *(3).* If span y ⊆ span x, then y₀ ∈ span x, and x₀ + εy₀ stays in the
  relatively open face x for small ε. So xy = x.
- *Closure.* Σ_L is closed under the product, because L is a flat.
- *S_0 is the bottom simple.* With this order, χ_0(y) = [span y = 0] =
  [y = O]. So S_0 is the module on which every x ≠ O acts by 0, as [GT]
  uses.

**Verdict on Brown as used: HOLDS.** The statement and its field
generality match. The only gap is the trace-versus-rank point of §B.3.
Saliola is not needed anywhere in Theorem C.

### B.5 Theorem C, step by step

- **(i)** is (A2). Checked.
- **(ii)** Checked.
  - Λ̄(V) is an induced subposet of L̄(A), so Δ(Λ̄(V)) is a full
    subcomplex of Δ(L̄(A)).
  - Both have dimension ≤ d − 2, so their H̃_{d−2} are their spaces of
    (d − 2)-cycles. (For d = 2, the reduced 0-cycles.) So the inclusion is
    injective on H̃_{d−2}.
  - The span of {ρ_C : C ∈ V} therefore has the same dimension in both.
  - In H̃(Λ̄(V)) it is m(V), by (i) and (A1).
  - In H̃(L̄(A)) it is dim Γ_V/(Γ_V ∩ ker φ) = dim Γ_V/(Γ_V ∩ Lune) = q(V),
    by Prop. B.
- **(iii)** Checked. q ≤ dim Lie_L(Γ_V) ≤ m (Prop. 3(a)–(b), with the
  §B.3 fix in characteristic p), and q = m. So:
  - dim span{non-singleton lunes in V} = #V − m = dim(Γ_V ∩ Lune);
  - the first space is contained in the second, so they are equal.

  This is (G1), and it does not use Saliola.
- **(iv)** Checked.
  - g is linear and preserves A, so it permutes faces and preserves order,
    and span(gF) = g span F.
  - By B.1, ε(gF_1, …, gF_d) = sign det(g b_1, …, g b_d) = det(g) ·
    ε(F_1, …, F_d), for g of determinant ±1. (For a general g, read
    sign det g; for finite W, det g = ±1.)
  - So g · ρ_C = det(g) ρ_{gC} at chain level.
  - Restricted to Γ_V, for g ∈ Stab(V), φ becomes an equivariant map
    det ⊗ Γ_V → H̃_{d−2}(Λ̄(V)). It is onto by (i), and its kernel is
    Γ_V ∩ Lune by Prop. B and the injectivity in (ii). Lune is
    W-stable.
  - Finiteness of W is not needed for the chain-level identity. It is
    needed only for "k[Stab]-module" to mean a representation of a finite
    group.

## C. Prop. B's sign convention vs Prop. Φ of [Thm]

### C.1 Setup

The braid arrangement of S_n, essentialized in R^n/R·1, has d = n − 1.
- **Chambers.** C_w = {x_{w_1} < ⋯ < x_{w_n}}.
- **Flats.** Set partitions π, with flat {x constant on the blocks of π}.
  So L(A) ≅ Π_n^op.
- **Faces of C̄_w.** The ordered set partitions that are coarsenings of w
  into consecutive segments. So Λ̄(C_w) = Π̄_w (the interval partitions of
  w), and ρ_{C_w} =: ρ^B_w is a fundamental cycle of the sphere Δ(Π̄_w).
- **Wachs's ρ_w (= ρ^W_w)**, as in [Thm, §basis], is the fundamental cycle
  of the same sphere. It is normalized so that the chain
  w_1|⋯|w_{k−1}|rest, listed in refinement order, has coefficient +1.
- **Lunes.** For H with blocks S_1, …, S_k, L(H, D) is the set of
  shuffles of the words D|_{S_1}, …, D|_{S_k}. A k-fold shuffle is a sum
  of 2-fold shuffles, (u ш v) ш w = Σ_{x∈uшv} x ш w, and 2-fold shuffles
  are lunes. So **Lune = Sh_n**.
- **det = sgn.** On R^n a permutation matrix has determinant sgn(g). It
  fixes R·1 pointwise, so det on R^n/R·1 is also sgn(g). (COMPUTED as
  well: every transposition has det −1 in the essential coordinates, for
  n ≤ 6.)

### C.2 The comparison (PROVEN)

ρ^B_w = c_n · sgn(w) · ρ^W_w for all w ∈ S_n, with c_n ∈ {±1} depending
only on n.

*Proof.*
- At the identity word e, both ρ^B_e and ρ^W_e are nonzero cycles with
  ±1 coefficients in the 1-dimensional top cycle space of the sphere
  Δ(Π̄_e). So ρ^B_e = c_n ρ^W_e with c_n = ±1.
- For g ∈ S_n, g C_e = C_g. By Theorem C(iv) at chain level,
  ρ^B_g = sgn(g) g·ρ^B_e.
- Relabeling letters maps Wachs's normalizing chain for w to the one for
  gw, since (gw)_i = g(w_i). So ρ^W_{gw} = g·ρ^W_w.
- Hence ρ^B_g = sgn(g) c_n g·ρ^W_e = c_n sgn(g) ρ^W_g. ∎

COMPUTED values, at chain level for every w ∈ S_n:
- c_3 = −1;
- c_4 = +1;
- c_5 = +1;
- c_6 = −1.

The value of c_n depends on the convention for listing chains
(inclusion order vs refinement order) and on the sign in [C]. It plays
no role below.

**Consequence.** Prop. B for the braid arrangement says:

  Σ b_w ρ^B_w = 0 ⟺ Σ b_w w ∈ Sh_n.

Substituting b_w = c_n sgn(w) a_w turns this into

  Σ a_w ρ^W_w = 0 ⟺ Σ a_w sgn(w) w ∈ Sh_n,

which is exactly Prop. Φ of [Thm]. The two maps "ρ^B_C ↦ C" and
"ρ_σ ⊗ 1 ↦ sgn(σ)σ" differ by the global scalar c_n. The control is that
c(w) alone (without sgn(w)) is not constant (COMPUTED).

### C.3 The det-twisted identity in the braid case reproduces the main theorem's sgn twist exactly

Take V = C_P.
- Stab_{S_n}(C_P) = Aut(P), since C_P determines P.
- Λ̄(C_P) ≅ OP(P)^op (proper parts), with the same order complex and
  compatible S_n-actions. So H̃_{n−3}(Λ̄(C_P)) = H_P as Aut(P)-modules. The
  chain-order reversal is a global sign and does not affect the module
  structure.
- Γ_{C_P} = W_P, and Γ_{C_P} ∩ Lune = W_P ∩ Sh_n.

Theorem C(iv) therefore reads

  H_P ≅ sgn ⊗ W_P/(W_P ∩ Sh_n) = sgn ⊗ M_P   (as Aut(P)-modules),

which is [Thm, Thm S(d)]: H_P ⊗ sgn ≅ C[Lin P]/R_P, using
W_P ∩ Sh_n = R_P (Thm S(b)). With the twist-free isomorphism ψ_P : PLie(P)
→ M_P ([Thm, Cor. psi]), this gives H_P ≅ sgn ⊗ PLie(P), the main theorem
(eq. mainiso).

**The twist is exactly sgn = det, with no extra sign.** The only sign
freedom, c_n, is a scalar and cannot change a module isomorphism class.

**Knock-on (PROVEN given Brown and the cell facts; not previously
recorded).** Prop. Φ of [Thm] holds for every n.
- Prop. B uses only Prop. 3(a)–(b) of [GT] (Brown), Theorem 2 of [GT],
  (A1) (Folkman, reproved) and Lemma 0.2.
- It uses neither Wachs's comb basis nor Ree's theorem.
- [Thm] currently marks Prop. Φ as cited for n ≥ 7. On this audit's
  reading, that status can become "PROVEN given Brown (read)". As a
  consequence, Thm S(c)–(d) are no longer conditional on Wachs.

Per the standing constraints, this audit changes nothing in [Thm]. The PM
should decide whether a second audit is wanted before the status change.

## D. Hypotheses: what is and is not needed

- **Essential.** Used in three places:
  - the cell facts (faces ≠ O are pointed);
  - "H ≠ O ⟺ non-singleton lune";
  - Lemma L.

  For a non-essential A, pass to A/(∩A). Faces, flats, top-cones, lunes,
  Λ(V) and the S-actions all correspond, so nothing is lost. Theorem C as
  stated assumes essentiality, which is correct.
- **Central.** Assumed throughout and needed. For affine arrangements
  there are no "faces ≠ O on a sphere". Theorem C makes no affine claim.
- **Lineality / non-pointed cones.** Handled uniformly by Lemma 0.2,
  which is correct for non-pointed C ≠ Y. For pointed V every fiber of f
  is contractible, so Prop. A is just Quillen's fiber lemma there. There
  is no special case to miss.
- **V = all chambers.** Z = S^{d−1}. Step 4 and (A2) were re-checked; the
  only point is H̃_{d−2}(S^{d−1}) = 0, true for d ≥ 2.
- **V a single chamber.** m = 1, and ρ_C spans H̃ of the sphere Δ(Λ̄(C)).
  This is consistent.
- **d.** d ≥ 2 is required for H̃_{d−2} to mean something non-vacuous. For
  d = 2 everything is in reduced H̃_0, and Steps 2 and 4 hold with
  augmentation.
- **Field.** Any field, after the §B.3 fix. Over C, no fix is needed.
- **Prop. 3(a) "non-singleton" fix.** Confirmed necessary. L(O, D) = {D}
  is a lune, and with singletons the span would be all of Γ_V.

  It is also sufficient. Theorem C(iii) is stated with "non-singleton",
  and Prop. B's Lune is defined (in [GT, §0]) as the span of the
  non-singleton lunes.

## E. Computations (COMPUTED)

`compute/audit_theorem_c.py` is plain Python 3. It imports nothing from
the repository.

**Construction.** The method differs from the earlier scripts, which used
the Tits-product closure of rays.
- Rays come from exact integer cofactor vectors of (d − 1)-subsets of
  normals.
- A sign vector s is a chamber iff the rays compatible with s span R^d.
  Chambers are found by a wall-crossing search from a generic point.
- The faces of each closed chamber are the sign vectors of sums of
  subsets of its rays.
- Faces of V are the faces below a chamber of V.
- Λ(V) is the set of zero sets of the faces of V.
- ρ_C is computed from the explicit formula of §B.1.

**Arrangements not used by [AudGT]:**

| Name | d | Hyperplanes | Chambers | Faces | Non-simplicial chambers |
|---|---|---|---|---|---|
| R4 (9 normals from {−1,0,1}^4, seed 11) | 4 | 9 | 138 | 829 | 86 |
| R5 (8 normals from {−1,0,1}^5, seed 7) | 5 | 8 | 174 | 1,871 | 144 |
| B_4 | 4 | 16 | 384 | 1,697 | 0 |
| A_5 (essentialized) | 5 | 15 | 720 | 4,683 | 0 |

**Why R4 and R5 are not Coxeter.** A chamber with more than d walls is
not simplicial. Every Coxeter (reflection) arrangement is simplicial, and
being simplicial does not depend on the linear coordinates. The normals
are printed in the log.

Every face list passes the Euler characteristic of S^{d−1}. A_5 has 4,683
faces, the Fubini number for n = 6.

**Results (full run).** No failures.

| Check | Arrangement | Cones | Lineality dims | Result |
|---|---|---|---|---|
| C(i) spanning, mod p (rigorous, see below) | R4 | 400 random + 100 non-pointed | 0–3 | rank span ρ = dim H̃ = m(V) for all |
| | R5 | 400 random + 100 non-pointed | 0–4 | all |
| | B_4 | 150 non-pointed, sizes 8–192 | 1–3 | all |
| | A_5 | 60 non-pointed, sizes 6–360 | 1–4 | all |
| C(i) spanning, **exact over Q** | R4 / R5 / B_4 / A_5 | 40 / 40 / 20 / 10 non-pointed | 1–4 | all |
| Prop. B: Σ_{C∈ℒ} ρ_C = 0 exactly, for every non-singleton lune | R4 / R5 / B_4 | 515 / 1,275 / 1,089 lunes | | all zero |
| Prop. B: #chambers − rank Lune = \|μ\| (exact), and rank span ρ = \|μ\| | R4 / R5 / B_4 | | | 138 − 104 = 34; 174 − 149 = 25; 384 − 279 = 105 |
| Lune rank over GF(2), GF(3) equals rank over Q | R4 / R5 / B_4 | | | equal (104, 149, 279) |
| C(ii)–(iii): q(V) = m(V) = #V − rank{lunes in V} | R4, R5 (**exact**), B_4 (mod p) | 60 / 60 / 40 non-pointed | | all |
| C(iv) chain level: g·ρ_C = det(g) ρ_{gC} | B_4 | 60 signed permutations × 40 chambers | | 0 failures |
| C(iv) chain level, braid, det = sgn | A_4 (n = 5) | all 120 g × 10 chambers | | 0 failures |
| Braid sign: ρ^B_w = c_n sgn(w) ρ^W_w | n = 3, 4, 5, 6 | all w ∈ S_n | | c_n = −1, +1, +1, −1 |

The random samples of R4 and R5 also contain pointed cones (lineality 0)
and may overlap the non-pointed samples.

**Positive controls (each must fire, and does).**
- **Exact vs modular rank.** The exact rank routine gives rank 1 on
  [[p]], and the mod-p routine gives 0. The instruments are distinct.
- **Torsion.** The mod-2 rank detects the torsion of Z/[[2]].
- **Known values.**
  - Face counts: A_3 has 24 chambers and 75 faces; B_3 has 48 and 147.
  - |μ| = dim H̃: 6 for A_3 and 15 for B_3.
- **Orientation.** Σ_C [C] is a cycle with the det signs and is not one
  with all signs +1 (B_3).
- **Spanning can fail.** A random non-convex set U of 6 chambers of B_3
  has chamber cycles of rank 6 in an H̃ of rank 11.
- **Lune relation.** It fails when one chamber's sign is flipped.
- **Det twist.**
  - Without det(g), chain-level equivariance fails: on B_3 (control), and
    on B_4 in 1,000 of the 2,400 sampled pairs.
- **Braid sign.** c(w) without sgn(w) is not constant (n = 4).
- **Simplicial certificate.** The non-simplicial test returns 0 on B_3,
  B_4 and A_5, which are simplicial.

**Rigour of the mod-p spanning checks.** For each cone, ∂ρ_C = 0 is
checked exactly over Z. Then

  rank_p(ρ) ≤ rank_Q(ρ) ≤ dim_Q ker ∂ = N − rank_Q ∂ ≤ N − rank_p ∂.

So rank_p(ρ) = N − rank_p ∂, which is what is checked, forces
rank_Q(ρ) = dim_Q H̃. The exact-rank samples check the same equality with
no modular step. The q(V) checks for B_4 are mod p, and are evidence only,
since q is a difference of ranks. Those for R4 and R5 are exact.

## F. Defects to file (for the maintainers of [GT] / [AudGT] / [Thm])

1. **[GT] Prop. 3(b) / [AudGT] Theorem C, "k any field".** In
   characteristic p, derive the multiplicities from ranks of idempotents
   (Brown, proof of Thm 4), not from traces (§B.3). Alternatively,
   restrict to characteristic 0. No conclusion over C changes.
2. **[AudGT] §C, orientation.** Replace "oriented by a fixed orientation
   of R^d" by the explicit ε = sign det(b_1, …, b_d) of §B.1. That formula
   is what makes Prop. B step 2's cancellation and Theorem C(iv)'s det
   immediate.
3. **[AudGT] §C, citations.**
   - Say that the carrier lemma and the order-homotopy step are standard,
     or use the short proofs in §A and §B.2.
   - Cite the order-complex fact to Matoušek §4.5 (open), in addition to
     Björner 1984.
4. **[Thm], Prop. Φ status (for decision, not a defect).** Prop. B gives
   Prop. Φ for all n, given Brown, with matching sign convention up to the
   global c_n (§C). If adopted, Prop. Φ moves from "cited for n ≥ 7" to
   PROVEN given Brown, and Thm S(c)–(d) lose their dependence on Wachs.
5. **[AudGT], "Possible knock-on, not verified here".** This audit has
   now verified it (§C).

## Reproduce

```
cd compute
python3 audit_theorem_c.py            # full run, about 3 min; prints the log
python3 audit_theorem_c.py --quick    # about 20 s
python3 -m unittest test_audit_theorem_c
```

Log of the full run: `compute/output/audit_theorem_c.txt` (ends
"RESULT: ALL CHECKS PASS").
