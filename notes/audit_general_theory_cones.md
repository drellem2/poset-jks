# Audit: general theory, framework (a) (cone wedge theorem, cone Zaslavsky, J–S reproof, Prop. 3, G\*)

Work item: mg-7ab20. This is an independent adversarial audit of §§0–1 of
`notes/general_theory.md` (the "note", merged in df0b9c1). Every PROVEN
claim in those sections was re-derived by hand. Every cited input that a
proof rests on was read in the source where one was accessible. The audit
code is `compute/audit_general_theory_cones.py`. It imports nothing from the
repository; in particular it does not import or run
`compute/general_theory.py`. Nothing in the note was changed.

Tags for the audit's own claims: **PROVEN** (proof given here) and
**COMPUTED** (script + command, see Reproduce).

## Verdict

**Overall: HOLDS, with small fixes. One status is wrong in the other
direction: Conjecture G\* is a theorem.** Every PROVEN claim in §§0–1 is
correct. The three inputs cited "as recalled" (Björner–Wachs–Welker,
Brown, Saliola) say what the note uses, with hypotheses that hold. The
audit also proves (Theorem C below) that the chamber cycles of every top-cone
span its top homology. With Prop. 3(a)–(b) this gives q(V) = m(V) and the
det-twisted equivariant identity for every top-cone of every finite real
central essential arrangement. The note's open conjecture, and its §5
recommendation to attack it, are therefore settled.

| Claim | Verdict |
|---|---|
| Lemma 0.1 (a)–(c) | **HOLDS.** |
| Lemma 0.2 | **HOLDS.** One implicit step: v ≠ 0 (§B.1). |
| Theorem 1 (cone wedge theorem) | **HOLDS.** BWW Thm 1.1 read; every hypothesis checked (§A.1, §B.2). The BWW input is in fact removable (Prop. A). |
| Corollary 1.1 | **HOLDS.** |
| Theorem 2 (Zaslavsky for cones) | **HOLDS.** |
| Lemma 1.3 (component formula, Foata) | **HOLDS.** |
| Corollary 1.4 (J–S Thm 4.5 reproved) | **HOLDS.** Λ(C_P) ≅ OP(P)^op and m(C_P) = e_C(P) confirmed, by proof and by computation for all 4,231 labeled posets with n ≤ 5. |
| Prop. 3(a) | **HOLDS WITH FIXES.** "Top-lunes contained in V" must mean the **non-singleton** ones (H ≠ O). Read literally, singletons are lunes and the left side is all of Γ_V. |
| Prop. 3(b) (Brown) | **HOLDS.** Brown's Theorem 3 (Bidigare) and its Corollary read; the hypotheses hold for Σ_L (§A.2). |
| Prop. 3(c) (Saliola) | **HOLDS.** Saliola (4.1), Lemma 4.1 and Thm 4.2 read (§A.3). Also implied by Theorem C, without Saliola. |
| G\* known case: pointed V | **HOLDS.** |
| G\* known case: V = all chambers | **HOLDS WITH FIXES.** It rests on Aguiar–Mahajan, which was not re-checked, and the citation is unnecessary: (G1) is a tautology for V = all, so Prop. 3(c) gives q = m directly. |
| G\* known case: braid | **HOLDS.** |
| Conjecture G\* (numerical and equivariant) | **Status wrong: it is a theorem.** PROVEN here, given Brown (read) and the standard cell facts (Theorem C, §C). COMPUTED on 6,910 cones (§D). |

## A. Cited inputs, read in the source

### A.1 Björner–Wachs–Welker, *Poset fiber theorems*

Read in the authors' preprint (M. Wachs's web page,
`math.miami.edu/~wachs/papers/fibers.pdf`, dated July 25, 2002). The
published version (Trans. AMS 357 (2005) 1877–1899) was **NOT ACCESSIBLE**,
so the published theorem number was not confirmed. In the preprint the
statement is Theorem 1.1.

> Theorem 1.1. Let f : P → Q be a poset map such that for all q ∈ Q the
> fiber Δ(f^{-1}(Q_{≤q})) is ℓ(f^{-1}(Q_{<q}))-connected. Then
> Δ(P) ≃ Δ(Q) ∨ ⋁_{q∈Q} (Δ(f^{-1}(Q_{≤q})) ∗ Δ(Q_{>q})), where the wedge is
> formed by identifying each q ∈ Q with some element of f^{-1}(Q_{≤q}).

The note's recollection matches this word for word. These conventions from
the paper matter:
- all posets are finite;
- ℓ(∅) = −1;
- "(−1)-connected" means nonempty, and r-connected for r ≥ 0 includes
  nonempty and connected;
- X ∗ ∅ = X (the simplicial join).

The note's Step 3 uses X ∗ ∅ = X for the flats Y ⊆ L of dimension d − 1,
where Λ̄_{>Y} is empty. This matches the paper's convention.

The paper does **not** state that the homotopy equivalence is compatible
with Δ(f). So the sentence in the note's §1.5 (ii), "f_* is surjective. This
holds because …", is not a consequence of BWW as written. It is true, by
Prop. A below.

### A.2 Brown, *Semigroups, rings, and Markov chains*

Read in arXiv:math/0006145 (J. Theoret. Probab. 13 (2000)), §7.2:
Theorem 3 (attributed to Bidigare) and the Corollary after it.

> Theorem 3. There is an algebra surjection ψ : kS → k^L whose kernel J is
> nilpotent. The X-component of ψ is the homomorphism χ_X : kS → k given by
> χ_X(y) = 1_{supp y ≤ X}.
>
> Corollary. Every irreducible representation of kS is 1-dimensional. There
> is one such for each X ∈ L, given by the character χ_X.

The hypotheses are Brown's definition of a left regular band (LRB) in
§2.1: a finite semigroup S with a lattice L and a surjection supp : S → L
such that
- (2) supp xy = supp x ∨ supp y, and
- (3) xy = x if supp y ≤ supp x.

The field k is arbitrary.

**Check for Σ_L.** Take supp x = span x and L = Λ_L, the flats contained
in L.
- *Surjective.* Every flat X ⊆ L is the span of a face of A, and that face
  lies in X ⊆ L.
- *(2).* The face xy contains x₀ + εy₀ for x₀ ∈ x, y₀ ∈ y and small ε. So
  its span is the least flat containing x and y. That flat lies in L,
  because L is a flat.
- *(3).* If span y ⊆ span x, then x₀ + εy₀ stays in the open face x for
  small ε, so xy = x.

The note's trace argument (composition series, each factor acting by χ_X)
is Brown's own paragraph after the Corollary.

**Related prior art (not used by the note).** Brown's §4.2, Theorem 2,
studies the LRB G of all faces of a convex set of chambers D. That is
exactly the face monoid F(V) of a top-cone. Brown computes its random-walk
eigenvalue multiplicities as |μ(X, V)| for flats X meeting the open cone.
The resulting chamber count Σ_{X∈M₀} |μ(X, V)| is the Zaslavsky L^int count
the note quotes, not Theorem 2. This is worth a pointer in the note's §1.4,
"Correction to [Cone, §6]": the F(V)-module structure of Γ_V was studied
there.

### A.3 Saliola, *The quiver of the semigroup algebra of a left regular band*

Read in arXiv:math/0608698v1 (IJAC 17 (2007); the published version was not
accessed). Section 4 says the following.
- **(4.1)** For each X ∈ L, fix x with supp x = X and set
  e_X = x − Σ_{Y>X} x e_Y.
- **Lemma 4.1.** If supp w ≰ X, then w e_X = 0.
- **Theorem 4.2.** For a finite LRB with identity and any field k, the e_X
  form a complete system of primitive orthogonal idempotents.
- The proof of Thm 4.2 records that e_{0̂} = 1 − Σ_{Y>0̂} e_Y, and that e_Y
  is a combination of elements of support ≥ Y.

In Σ_L, O is the only element of support 0. So Lemma 4.1 at X = 0 says
exactly x e_0 = 0 for x ≠ O. Also e_0 − O is a combination of faces ≠ O.
These are the two properties the note uses.

A simplification: any element e = O + (combination of faces ≠ O) with
x e = 0 for all x ≠ O is automatically idempotent, since
e·e = O·e + (…)·e = e. And χ_X(e) = δ_{X0} follows from
χ_X(x_X) χ_X(e) = χ_X(x_X e) = 0 for X ≠ 0.

### A.4 Other inputs

- **P. Hall's theorem, μ(P̂) = χ̃(Δ(P)).** Read in Wachs, *Poset topology:
  tools and applications* (arXiv:math/0602226), Prop. 1.2.6.
- **Cell facts** (the faces F ≠ O meet S in a regular CW decomposition of
  S^{d−1}; the order complex of a regular CW complex's face poset is
  homeomorphic to it). The cited sources (Björner–Las Vergnas–Sturmfels–
  White–Ziegler; Björner 1984) are **NOT ACCESSIBLE** here.
  - The second fact is the classical barycentric-subdivision statement.
    Wachs's notes cite it to Björner 1984.
  - The first fact is elementary for an essential A. The closure of a face
    F is the pointed polyhedral cone F̄, the union of F and its proper
    faces. F̄ ∩ S is a closed (dim F − 1)-ball, whose boundary sphere is
    the union of the proper faces.
  - Neither fact is in doubt. Both are flagged only because the note marks
    them "not re-checked".
- **Aguiar–Mahajan, *Topics*** (Ree criterion; Thm 14.32; dim Lie[A] = |μ|)
  is **NOT ACCESSIBLE** here.
  - None of §§0–1's proofs needs it once the "all chambers" case is argued
    as in §B.8.
  - The existence of Φ_A is PROVEN in §C, given Brown.
- **[Cone] Lemma L, Prop. 2.2, Thm 5.2 and [Thm] Thm S(b).** These are
  internal and already audited. They were read, and the statements used
  match:
  - Lemma L: L(H, D) ⊆ V iff D ∈ V and H ⊆ lin V.
  - Prop. 2.2: the supports of the faces of C_P are OP(P).
  - Thm 5.2: if V is pointed, Γ_V ∩ Lune = 0.
  - Thm S(b): dim W_P ∩ Sh_n = |Lin P| − e_C(P), so q(C_P) = e_C(P),
    because Lune = Sh_n and Γ_{C_P} = W_P.
- **Jenča–Sarkoci Thm 4.5** is only reproved, not used.

## B. Claim-by-claim re-derivation

### B.1 Lemmas 0.1 and 0.2 — HOLD

**0.1(a).** This was re-derived as written.
- The forward direction holds because a face is open in its span.
- For the converse: faces in Y of span ≠ Y have dimension < dim Y.

**0.1(b)** is immediate.

**0.1(c).** Each step checks out.
- |V| is the closed cone {s_e α_e ≥ 0, e ∈ S_max}. It is the closure of the
  nonempty open cone, hence the union of the closed chambers of V.
- Its lineality space is ∩_{S_max} h_e.
- The flats Y ⊇ X of A are exactly the preimages of the flats of A_X/X.
- Y ∩ |V| is the preimage of (Y/X) ∩ K′, so dimensions shift by dim X.

**0.2.** The proof is correct. The only implicit step is v ≠ 0. That
holds because 0 ∈ int C would mean C = Y, and it is in fact covered by the
displayed argument C ∩ −int C = ∅, since 0 ∈ C.

### B.2 Theorem 1 — HOLDS

**Steps 1–3.** Δ(f) is a poset map into Λ̄(V).
- The fiber over Y is the face poset of |V| ∩ Y ∩ S.
- By Lemma 0.1(a) and Lemma 0.2, that fiber is S^{dim Y−1} if Y ⊆ L and
  contractible otherwise.
- The longest chain of f^{-1}(Λ̄_{<Y}) has length dim Y − 2. A full flag of
  faces of a face of span Y exists, so the length is exactly that.
- So the BWW hypothesis holds, with equality in the sphere case.

**Step 4** is correct.
- The note says "H̃_{d−2}(Z) = 0, which holds for d ≥ 3". With reduced
  homology it holds for d = 2 as well. This is cosmetic.
- The fundamental class of S^{d−1} is Σ ±C, which is primitive. So the
  quotient Z^N/⟨Σ ±C⟩ is free.

**Step 5** is correct.
- Retract argument: a wedge summand is a retract.
- Dimension count: chains of proper flats have length ≤ d − 2.
- Hurewicz–Whitehead finish for d ≥ 4.
- Hall's theorem.

The tag can be upgraded from "statement as recalled" to "read: BWW
preprint Thm 1.1".

### B.3 Corollary 1.1 — HOLDS

These steps were re-derived:
- H̃_{d−2}(S^a ∗ T) = H̃_{d−3−a}(T);
- the degree bookkeeping;
- the dim Y = d − 1 terms (S^{d−2} ∗ ∅, rank 1 = m of a rank-1 cone);
- the X = 0 term (Δ(Λ̄(V)) itself, rank m(V));
- the X = R^d term, which occurs iff V is all chambers.

### B.4 Theorem 2 — HOLDS

These steps were re-derived:
- f(Y) = 1 − χ(|V| ∩ Y ∩ S) = (−1)^{dim Y} [Y ⊆ L] on Λ(V);
- the inversion f(Y) = Σ_{X≤Y} (−1)^{dim X} g(X);
- g(R^d) = #V, with only X ⊆ L surviving;
- the use of Lemma 0.1(b), so that every flat in L lies in Λ(V), and
  of 0.1(c).

The specializations are correct. For V = all chambers, Rota's sign
alternation gives (−1)^{codim X} μ(X, R^d) = |μ|.

### B.5 Lemma 1.3 — HOLDS

These steps were re-derived:
- the cut/piece decomposition and the irreducibility of pieces;
- the converse concatenation, using no relations between distinct T_i;
- the claim that cuts of a rotated word are the rotated cuts. If
  w₁…w_k is a union of components, a prefix of wγ^k is a union of
  components iff the matching prefix of w is.

Pieces have disjoint letter sets, so a cyclic sequence of pieces has no
rotational symmetry. Classes therefore correspond bijectively to cyclic
sequences.

Foata's bijection is applied to each fixed collection of pieces, and the
union is taken over collections. Irreducibility relative to P|_T is the
same whether T is viewed inside P or inside P|_B, because the components of
P|_B inside T are the components of P inside T.

### B.6 Corollary 1.4 — HOLDS

These steps were re-derived:
- **S_max(C_P) is the set of comparable pairs.** Incomparable i, j are
  ordered both ways by linear extensions. Hence lin C_P is the constants on
  components.
- **The flats in lin C_P are the partitions σ of K.** The localization is
  Π_{B∈σ} of the braid arrangement on B, and the localized cone is
  Π C_{P|_B}.
- **Λ, μ and the sign (−1)^rank are multiplicative**, and a one-point
  factor has m = 1 = e_C.
- **Λ(C_P) ≅ OP(P)^op.** The span of the face with block partition π is
  {x constant on the blocks of π}, so refinement reverses inclusion. The set
  of supports is OP(P) by [Cone] Prop. 2.2.
- **Base case.** P connected gives L = 0, so V is pointed and
  m = #V = |Lin P|. Also e_C(P) = |Lin P|, by Lemma rot: a connected P has
  no proper cut.
- The induction on the number of components is sound.

**Hypothesis remark.** J–S state their theorem for n ≥ 3. The corollary
says n ≥ 2. For n = 2 it reads ⋁^1 S^{−1} = ∅ under the note's convention,
which is correct but conventional.

### B.7 Proposition 3 — (a) HOLDS WITH FIXES, (b) HOLDS, (c) HOLDS

**(a)**
- The action stays in V because H_e = 0 on S_max.
- The adjoint of C ↦ HC sends D to Σ_{HC=D} C. That sum is L(H, D) if
  D ≥ H and 0 otherwise.
- Every chamber C with HC = D satisfies C_e = D_e on S_max, so it lies in V
  without any appeal to Lemma L.
- Conversely, a non-singleton lune inside V is L(H, D) with H ⊆ L, by Lemma
  L. The audit re-derived this: if e ∈ S_max and H ⊄ h_e, then the lune
  contains chambers on both sides of h_e.
- So span{L(H, D) : H ∈ Σ_L ∖ O} = (∩_H ker T_H)^⊥.

*Fix.* State that the lunes are the non-singleton ones (H ≠ O). L(O, D) = {D}
is a top-lune in [Cone]'s convention, and with singletons the statement is
false whenever Lie_L(Γ_V) ≠ 0.

**(b)**
- Brown is read and the hypotheses are checked (§A.2).
- The trace of x on Γ_V is #{C ∈ V : x ≤ C}. That equals c_{span x} = #V_X,
  because chambers C ≥ x correspond to chambers of A_X with the same signs
  on S_max ⊆ z(x).
- Möbius inversion on Λ_L = [0, L] is sound. The Möbius functions of Λ_L
  and of Λ(V) agree on these intervals.
- The comparison with m(V) via Theorem 2 for V_X is correct.
- So are both inequalities.

**(c)**
- Saliola is read (§A.3).
- e_0 Γ_V = Lie_L(Γ_V), and its dimension is the trace of e_0, which is
  [Γ_V : S_0]. This is correct.

### B.8 "Known cases (PROVEN)" of G\*

- **Pointed V.** [Cone] Thm 5.2 gives Γ_V ∩ Lune = 0, so q(V) = #V.
  Theorem 2 gives #V = m(V). **HOLDS.**
- **V = all chambers. HOLDS WITH FIXES.** The note cites Aguiar–Mahajan for
  q = |μ(L(A))|, not re-checked (Topics is NOT ACCESSIBLE here). The
  citation is unnecessary.
  - For V = all chambers, L = R^d and every non-singleton lune lies in V.
    So (G1), Γ ∩ Lune = span{lunes in V}, is a tautology.
  - Prop. 3(c) then gives q = dim Lie_{R^d}(Γ) = m(V) = |μ(L(A))|.
  - So the case is PROVEN given Saliola, or given Brown alone by
    Theorem C.
- **Braid.** q(C_P) = e_C(P) by [Thm] Thm S(b), as checked in §A.4. And
  m(C_P) = e_C(P) by Cor. 1.4. **HOLDS.** The equivariant braid statement is
  correctly tagged "given Prop. Φ".

### B.9 Wording in §1.5 (ii)

"Equivalently, the map f_* … is surjective. This holds because H_{d−2}(X)
is spanned by the boundaries of the chambers, and f_* sends ∂C to ρ_C."
- Read as a justification of the *equivalence*, it is correct.
- Read as a claim that f_* *is* surjective, it would have proved the
  conjecture, but BWW does not supply it (§A.1).
- It is in fact true (Prop. A). The sentence should be rewritten either
  way.

## C. New: the chamber cycles always span, and Conjecture G\* holds

Throughout, A is a finite real central essential arrangement of rank d ≥ 2,
V is a top-cone, and k is any field.
- Q′ is the poset of faces F ≠ O of V that are not chambers.
- f : Q′ → Λ̄(V) is F ↦ span F, as in Theorem 1.
- X ≅ Δ(Q′) is the (d − 2)-skeleton of |V| ∩ S.
- For a chamber C, [C] is its fundamental chain in the order complex of
  faces ≠ O, oriented by a fixed orientation of R^d.
- ρ_C := Δ(f)_#(∂[C]).

f restricted to the proper faces of C is an isomorphism onto Λ̄(C), because
a face of a chamber is C̄ ∩ (its span). So ρ_C is the fundamental cycle of
the sphere Δ(Λ̄(C)) of [Cone, (G3)], with a definite sign.

**Proposition A (PROVEN; uses only Lemma 0.2 and the cell facts).** There
is a continuous map g : Δ(Λ̄(V)) → Δ(Q′) with Δ(f) ∘ g ≃ id. Hence
f_* : H̃_i(X) → H̃_i(Δ(Λ̄(V))) is split surjective for every i, and
π_1(X) → π_1(Δ(Λ̄(V))) is onto.

*Proof.* Work on the barycentric subdivision sd Δ(Λ̄(V)). Its vertices are
the chains c of Λ̄(V), and its k-simplices are the flags c_0 ⊂ ⋯ ⊂ c_k.

*Carrier.* For a simplex σ with top chain c_k, put Y(σ) = max c_k and
Φ(σ) = Δ(f^{-1}(Λ̄_{≤Y(σ)})). This is the fiber over Y(σ), which is
contractible or the sphere S^{dim Y−1}, hence (dim Y − 2)-connected. If
τ ⊆ σ, then Y(τ) ≤ Y(σ), so Φ(τ) ⊆ Φ(σ).

*Construction of g.* Build g skeleton by skeleton with g(σ) ⊆ Φ(σ).
- On vertices, pick any point of the (nonempty) fiber.
- For a k-simplex σ, the map is already defined on ∂σ, with image in
  Φ(σ).
- A chain of Λ̄_{≤Y} has at most dim Y elements, so
  k ≤ |c_k| − 1 ≤ dim Y − 1.
- Hence ∂σ ≅ S^{k−1} maps into a (k − 1)-connected space and the map
  extends over σ.

*The homotopy.* Both Δ(f) ∘ g and the identity homeomorphism
sd Δ(Λ̄) → Δ(Λ̄) send σ into Δ(Λ̄_{≤Y(σ)}). That is a cone with apex
Y(σ), hence contractible, and it is monotone in σ. By the contractible
carrier lemma the two maps are homotopic.

The homotopy gives f_* g_* = id on homology. On π_1 it gives the same up to
a change-of-basepoint isomorphism. ∎

**Consequences.**
- **(A1) Theorem 1 without BWW.** H̃_i(Δ(Λ̄(V))) is a direct summand of
  H̃_i(X). This is zero for i ≠ d − 2 and free for i = d − 2, by Step 4.
  Also π_1 is a quotient of π_1(X) = 1 for d ≥ 4. Step 5 of the note then
  finishes verbatim. (Corollary 1.1 still uses the BWW decomposition, but
  Theorem 2 reproves it.)
- **(A2) (G3) holds for every top-cone.** H̃_{d−2}(X) is generated by the
  boundaries ∂C of the chambers (Step 4), and f_* sends ∂C to ρ_C. So
  {ρ_C : C ∈ V} spans H̃_{d−2}(Δ(Λ̄(V)); Z).

**Proposition B (Φ_A exists; PROVEN given Brown).** Let
φ : kΓ → H̃_{d−2}(Δ(L̄(A)); k) be C ↦ ρ_C, where L̄(A) is the proper part of
the intersection lattice. Then ker φ = Lune, and φ induces
Γ/Lune ≅ H̃_{d−2}(L̄(A)).

*Proof.*
1. **φ is onto.** This is (A2) with V = all chambers.
2. **Lune ⊆ ker φ.** Let ℒ = L(H, D) with H ≠ O.
   - If H is a chamber, then ℒ is all chambers, and Σ ∂[C] = ∂[S^{d−1}] = 0
     already as a chain.
   - Otherwise ℒ is the top-cone {C : C_e = D_e, e ∈ z(H)}. Its lineality
     is K = span H, with 0 ≠ K ≠ R^d.
   - In z = Σ_{C∈ℒ} ∂[C], each codimension-1 face interior to |ℒ| appears
     twice with opposite signs. So z is a cycle supported on the faces in
     the boundary of |ℒ|. Each such face lies in some h_e with
     e ∈ z(H), hence h_e ⊇ K.
   - On that face poset, g(F) = span F ∨ K is a poset map into L̄(A). Its
     value lies in h_e, so it is ≠ R^d, and it is ≥ K, so it is ≠ 0.
   - f ≤ g pointwise, so Δ(f) ≃ Δ(g) by Quillen's order-homotopy lemma.
     Δ(g) lands in the cone Δ(L̄_{≥K}).
   - So f_#(z) = Σ_{C∈ℒ} ρ_C is a boundary in Δ(L̄(A)). But that complex
     has no (d − 1)-simplices, so this (d − 2)-chain is 0.
3. **dim Γ/Lune ≤ |μ(L(A))|.** Apply Prop. 3(a) with V = all chambers, so
   that L = R^d and Lune is the span of the lunes in V. That gives
   dim Γ/Lune = dim Lie_{R^d}(Γ). Prop. 3(b) (Brown) bounds this by
   m(all) = |μ(L(A))|.
4. **Conclusion.** H̃_{d−2}(L̄(A)) has rank |μ(L(A))| by Theorem 1 (A1),
   which is Folkman. Comparing dimensions in steps 1–3 gives ker φ = Lune.
   ∎

**Theorem C (Conjecture G\*; PROVEN given Brown, Hall and the cell facts).**
For every top-cone V of every finite real central essential arrangement of
rank d ≥ 2:
- (i) {ρ_C : C ∈ V} spans H̃_{d−2}(Δ(Λ̄(V))) (G3);
- (ii) q(V) = m(V);
- (iii) Γ_V ∩ Lune = span{non-singleton lunes in V} (G1), and
  dim Lie_L(Γ_V) = m(V), which is Prop. 3(c) without Saliola;
- (iv) for every finite group W of linear maps preserving A, and every
  g ∈ Stab_W(V), g·ρ_C = det(g) ρ_{gC}. Consequently
  H̃_{d−2}(Λ̄(V); k) ≅ det ⊗ Γ_V/(Γ_V ∩ Lune) ≅ det ⊗ (Γ_V + Lune)/Lune
  as k[Stab_W(V)]-modules.

*Proof.*

(i) is (A2).

(ii) Δ(Λ̄(V)) is a subcomplex of Δ(L̄(A)), and both have dimension ≤ d − 2.
So H̃_{d−2} of each is its group of (d − 2)-cycles, and the inclusion is
injective. Hence:
- the span of {ρ_C : C ∈ V} has the same dimension in both groups;
- in H̃(Λ̄(V)) that dimension is m(V), by (i) and Theorem 1;
- in H̃(L̄(A)) it is dim φ(Γ_V) = dim Γ_V/(Γ_V ∩ Lune) = q(V), by Prop. B.

(iii) Prop. 3 gives q ≤ dim Lie_L ≤ m. With (ii) these are equalities.
Prop. 3(a) then gives dim span{lunes in V} = #V − q = dim(Γ_V ∩ Lune).
Inclusion is clear, so the two spaces are equal.

(iv) g is linear. It maps [C] to det(g)[gC] and commutes with f, since
span(gF) = g span F. So g·ρ_C = det(g) ρ_{gC}. Thus
φ|_{Γ_V} : Γ_V → det ⊗ H̃_{d−2}(Λ̄(V)) is g-equivariant. It is onto by (i),
and its kernel is Γ_V ∩ Lune by Prop. B. Lune is W-stable because g maps
lunes to lunes. ∎

**What this changes in the note.**
- Summary item 4 and §1.5: G\* is PROVEN (given Brown), not conjectured.
  The COMPUTED evidence becomes a check.
- §5's recommendation to attack G\* is moot.
- §1.5 "Equivalent forms" (ii) needs no Φ_A citation, by Prop. B.
- §1.5 "V = all chambers" needs no Aguiar–Mahajan citation.

**Possible knock-on, not verified here.** For the braid arrangement,
Theorem C gives the following, by a route independent of the Conjecture S
proof:
- Γ_{C_P} ∩ Sh_n = span of the shuffles inside C_P;
- H_P ⊗ sgn ≅ C[Lin P]/R_P;
- a construction of Φ that does not cite Aguiar–Mahajan.

These are [Thm] Thm S(b)–(d) and its Prop. Φ input. Whether Prop. B's map
matches [Thm]'s Prop. Φ sign convention (ρ_w ↦ sgn(w) w) was **not
checked**. Nothing in [Thm] should be changed on the strength of this note
without that check and an independent audit of Props. A and B.

## D. Computations (COMPUTED)

`compute/audit_general_theory_cones.py`, written independently in plain
Python 3 with no dependencies.

**Faces.** Rays are exact rational kernels. Faces are the closure of {O}
under the Tits product with rays: a face F equals r_1 r_2 ⋯ r_k for its
rays, since r_1 + εr_2 + ε²r_3 + ⋯ lies in its relative interior. The face
counts match Zaslavsky (A_3: 75, B_3: 147).

**Top-cones.** All top-cones are enumerated as distinct chamber bitmasks of
{C : C_e = s_e, e ∈ S}. Counts:

| Arrangement | Top-cones | Audited |
|---|---|---|
| A_2 | 19 | all |
| B_2 | 33 | all |
| A_3 | 219 | all |
| B_3 | 941 | all |
| generic5 in R^3 | 163 | all |
| rand7 in R^3 (own random arrangement) | 635 | all |
| A_4 | 4,231 | all |
| rand6 in R^4 (own random arrangement) | 609 | all |
| D_4 | 12,313 | random sample of 60 |

A_4 has 4,231 top-cones, which equals the number of labeled posets on 5
points.

| Check | What it verifies | Scope |
|---|---|---|
| [thm1] | H̃_*(Δ(Λ̄(V))) over GF(2) and GF(1000003) is zero outside degree d − 2 and has rank m(V) ≥ 0 there | every audited cone |
| [loc] | Lemma 0.1(c): (−1)^{codim X} μ_{Λ(V)}(X, top) equals m of V_X, with V_X built **independently** from the faces of the localized arrangement A_X | every flat X ⊆ lin V |
| [zas] | Theorem 2 / Cor. 1.1 | every audited cone |
| [rho] | ρ_C is a cycle; the span of {ρ_C : C ∈ V} has rank m(V) (Theorem C(i)) | every audited cone |
| [lune] | Σ_{C∈ℒ} ρ_C = 0 **exactly** (integers) for every non-singleton lune (Prop. B step 2). For arrangements with ≤ 200 faces, the lune list is cross-checked against the literal Tits-product definition | every arrangement |
| [eqv] | g·ρ_C = det(g) ρ_{gC} at chain level (Theorem C(iv)) | every signed permutation g and chamber C of B_2 (64 pairs) and B_3 (2,304 pairs) |
| [prop3] | (a) dimensions add to #V, and exact orthogonality when #V ≤ 48; Lemma L. (b) c_X depends only on span x, equals #V_X, and Σ μ(0,X) c_X = m(V). q ≤ dim Lie_L ≤ m, and q = m | every audited cone |
| [sal] | Saliola's e_0 in kΣ_L: x e_0 = 0 for x ≠ O, e_0² = e_0, coefficient of O = 1 | every cone with \|Σ_L\| ≤ 80 in A_2, B_2, A_3, B_3, generic5, rand7 |
| [braid] | For every labeled poset with n ≤ 5: the cones are exactly the C_P; Lin P = chambers; {partitions of Λ(C_P)} = OP(P) (computed from the acyclic-quotient definition), with refinement reversing inclusion; m(C_P) = e_C(P) (computed from cyclic cosets); Lemma 1.3 | all labeled posets n ≤ 5, plus Lemma 1.3 on 120 random posets with n = 6, 7 |

**Positive controls** (each must FAIL, and each does):
- Theorem 2 summed over all of Λ(V) instead of the flats in lin V fails on
  A_3.
- Theorem 2 fails on the non-convex chamber set {C, −C} of A_2.
- Lemma 1.3 with |Lin(P|_B)| in place of e_C(P|_B) fails (2-antichain:
  3 ≠ 2).
- Prop. 3 with the whole face monoid F(V) in place of Σ_L fails on a
  non-pointed cone of A_3.
- Saliola's recursion without the left factor x fails x e_0 = 0.
- The lune relation with incoherent orientations (each ρ_C normalized to a
  positive leading coefficient) fails.
- **The chamber cycles do not span off top-cones.** For the non-convex pair
  {C_0, C_2} of A_3, they span rank 2 < 3 = rank H̃_1. So [rho] can fail,
  and the span property is specific to convex sets.
- The homology routine reproduces S^1 (a square's face poset) and S^0.

**Caveats.**
- Ranks of rational matrices are taken mod p = 1000003, except where noted
  exact.
- For [rho] this is rigorous: rank_p ≤ rank_Q ≤ m, so rank_p = m forces
  rank_Q = m.
- For q(V), a difference of two ranks, the mod-p value is evidence, not
  proof. Theorem C does not depend on it.
- The D_4 coverage is a 60-cone sample.
- The note's own figures (6,676 cones, the 150-cone D_4 sample, the det-twist
  failure counts 9/33, 115/941, 64/150) were **not re-derived**. They are
  the note's.

## E. Defects to file (for the note's maintainer)

1. **Prop. 3(a).** Say "non-singleton top-lunes" (H ≠ O).
2. **Status of Conjecture G\*.** It is a theorem (Theorem C here, given
   Brown). Update:
   - Summary item 4, §1.5 and §5;
   - the status table;
   - the "Equivalent forms" paragraph, which no longer needs Φ_A from
     Aguiar–Mahajan.
3. **"V = all chambers" known case.** Replace the Aguiar–Mahajan citation
   with Prop. 3(c) (G1 is tautological there), or with Prop. B.
4. **§1.5 (ii) wording.** "f_* … is surjective. This holds because …"
   should either say "is equivalent to" or cite Prop. A. BWW alone does not
   give it.
5. **Citation tags.** Upgrade to read:
   - BWW: preprint Thm 1.1 (published numbering not checked);
   - Brown: arXiv:math/0006145 §7.2, Thm 3 and its Corollary;
   - Saliola: arXiv:math/0608698 §4, (4.1), Lemma 4.1, Thm 4.2.
6. **Cosmetic.**
   - Theorem 1 Step 4: H̃_{d−2}(Z) = 0 also for d = 2.
   - Cor. 1.4's n = 2 case is conventional (J–S assume n ≥ 3).
7. **Prior art.** Brown §4.2 Thm 2 (the LRB of faces of a convex set of
   chambers) belongs next to "Correction to [Cone, §6]".

## Reproduce

```
cd compute
python3 audit_general_theory_cones.py      # full run, about 2.5 min; prints the log
python3 -m unittest test_audit_general_theory_cones
```

Log of the full run: `compute/output/audit_general_theory_cones.txt`
(ends "RESULT: ALL CHECKS PASS").
