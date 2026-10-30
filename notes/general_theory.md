# General theory: the framework in which poset JKS is one instance

Work item: mg-2858d. This note looks for the general statement of which the
poset JKS theorem (`notes/poset_jks_theorem.tex`, "[Thm]") is one case. Three
candidate frameworks named in [Thm, §open] are assessed, together with two
others. For each one we give the conjectured general statement, the evidence
for it, how poset JKS specializes from it, and the prior art we found. The
note ends with a ranked recommendation.

Sources are abbreviated as in [Thm]: [Cone] = `notes/cone_lune_lie_theory.md`,
[AudCone] its audit, [Glob] = `notes/global_module_operations_plethlog.md`,
[S] = `notes/conjecture_s_splitting_cycles_span.md`, [Nat] =
`notes/natural_isomorphism.md`, [Nov2] = `notes/novelty_search_2.md`.

Every claim carries one of these tags:
- **PROVEN**: a full proof is given here. Cited inputs are named.
- **COMPUTED**: checked by `compute/general_theory.py` (see Reproduce).
- **CITED**: a published result. We say whether its statement was re-checked
  against the source.
- **CONJECTURED**.

## Summary

**The framework is (a): top-cones of real hyperplane arrangements.** Within
it, (b) is the braid-arrangement shadow of the same structure, and (c) adds
nothing that (a) does not already contain. The new results are these.

1. **Theorem 1 (cone wedge theorem; PROVEN, given the poset fiber theorem of
   Björner–Wachs–Welker).** Let V be any top-cone of a finite real central
   essential arrangement of rank d. The proper part of its lattice of
   supports Λ(V) is homotopy equivalent to a wedge of m(V) spheres of
   dimension d − 2. The cone does not need to be pointed. For the braid
   arrangement Λ(C_P) ≅ OP(P)^op, so the theorem specializes to the whole of
   Jenča–Sarkoci Thm 4.5 (input (A) of [Thm]), including m(C_P) = e_C(P).
   This gives J–S a new proof and makes it the braid case of a general
   theorem. For V = all chambers it is Folkman's theorem for geometric
   lattices.
2. **Theorem 2 (Zaslavsky's theorem for cones, with lineality; PROVEN,
   elementary).** #V = Σ_X m(V_X), where X runs over the flats contained in
   the lineality space lin V and V_X is the localized cone. This has three
   specializations:
   - V = all chambers gives Zaslavsky's theorem;
   - pointed V gives #V = m(V);
   - the braid case is the component formula |Lin P| = Σ_σ Π_B e_C(P|_B).
3. **Proposition 3 (PROVEN, given Brown).** m(V) is the multiplicity of the
   bottom ("Lie") simple module of the face monoid Σ_L of the lineality space
   L = lin V, acting on the chambers of V. As a consequence
   q(V) ≤ m(V), where q(V) = dim Γ_V/(Γ_V ∩ Lune) is the cone's Lie
   dimension. This corrects [Cone, §6]: the LRB that sees H_P is Σ_L, not
   the face monoid F(V) of the whole cone.
4. **Conjecture G\* (the cone JKS conjecture).** q(V) = m(V) for every
   top-cone, and equivariantly H̃_{d−2}(Λ(V)) ≅ det ⊗ (Γ_V + Lune)/Lune as
   Stab_W(V)-modules.
   - It is PROVEN for pointed cones, for V = all chambers, and for the braid
     arrangement.
   - The numerical form is COMPUTED on every top-cone of A_2, A_3, A_4, B_2,
     B_3 and of three non-reflection arrangements (6,676 cones), and on 150
     sampled cones of D_4.
   - The equivariant form is COMPUTED on all cones of A_2, A_3, A_4, B_2 and
     B_3, and on the D_4 sample. This computation is new. The det twist is
     detected: without it the identity fails on 9/33 cones of B_2, 115/941 of
     B_3 and 64/150 of D_4.

   For the braid arrangement this conjecture is exactly Theorem S(d) of
   [Thm], H_P ⊗ sgn ≅ C[Lin P]/R_P.
5. **Hopf monoids (b): the P-graded Lie structure exists (PROVEN).** Let Q′
   be the Hopf monoid of pairs (P, ℓ), with ℓ a linear extension of P. Its
   product is disjoint union with concatenation. Its coproduct is
   restriction, but only to unions of components. Q′ is cocommutative and
   graded by posets.
   - Its primitives are Prim(Q′)_P = pr_P(Lie) ≅ Lie(P) ≅ sgn ⊗ H_P. The
     bracket Lie(P) ⊗ Lie(Q) → Lie(P + Q) is the truncation of the free Lie
     bracket (Theorem 7).
   - Q′ is the associated graded of [Glob]'s Hopf monoid 𝐐, for the
     filtration by number of relations (Theorem 8). This settles [Glob]'s
     filtration conjecture.
   - The local PBW conjecture of [Glob] also holds (Theorem 6):
     C[Lin P] ≅ ⊕_{σ ∈ Π(components)} ⊗_{B∈σ} Lie(P|_B) as Aut(P)-modules.
   - The lunes inside C_P are exactly the decomposables of the dual
     commutative Hopf monoid. So (b) and (a) are the same structure on the
     braid arrangement.

**Recommendation (§5).** Pursue (a). The first theorem to attack is
Conjecture G\*, in the form "the chamber cycles of V span
H̃_{d−2}(Λ(V))". By Theorem 1 this is a statement about one map in a fiber
decomposition that is already proven. It would be refuted by a single
top-cone with q(V) < m(V).

| Framework | Status after this note | Rank |
|---|---|---|
| (a) cones of real arrangements | General theorems 1–2 and Prop. 3 proven. One conjecture (G\*) carries all of the poset JKS content beyond J–S. | **1** |
| (b) species / Hopf monoids | Settled for posets (Thms 6–8). What remains is the extension to general arrangements (Aguiar–Mahajan bimonoids) and a cooperad. | 2 |
| (c) congruence lattices / closure systems | No general lattice statement survives. The lattices that matter are the Λ(V) of (a). An oriented-matroid version is the only lattice-level generalization proposed. | 3 |

---

## 0. Conventions

A is a finite central essential arrangement in R^d. Its faces are the
relatively open cones given by sign vectors, as in [Cone, §1]. A **top-cone**
V is a nonempty set of chambers of the form {C : C_e = s_e for e ∈ S}. Write:
- |V| for the closed polyhedral cone that is the union of the closed chambers
  of V;
- S_max(V) for the set of all hyperplanes with V on one side;
- L = lin V = |V| ∩ −|V| for its lineality space.

So |V| = {x : s_e α_e(x) ≥ 0, e ∈ S_max} and L = ∩_{e ∈ S_max} h_e. A face
F of A is a face of V if F ⊆ |V|.

**Flats and Λ(V).** A flat is an intersection of hyperplanes of A. We order
flats by inclusion of subspaces, so the bottom is 0 and the top is R^d. Let

  Λ(V) = {span F : F a face of V}.

Its bottom is span O = 0 and its top is R^d. Write Λ̄(V) for its proper part
(both removed). [Cone, §2] orders the same set by zero sets; this is the same
poset.

**Lemma 0.1 (PROVEN).**
- (a) A flat Y lies in Λ(V) iff dim(Y ∩ |V|) = dim Y.
- (b) Every flat X ⊆ L lies in Λ(V).
- (c) Let X ⊆ L be a flat. Let A_X be the localization {h ∈ A : h ⊇ X},
  viewed in R^d/X. Then the image V_X of |V| in R^d/X is a top-cone of the
  essential arrangement A_X/X, and the interval [X, R^d] of Λ(V) is
  isomorphic to Λ(V_X).

*Proof.*
- (a) If F ⊆ |V| is a face with span Y, then F is open in Y. Conversely,
  Y ∩ |V| is a union of faces of A, because Y and |V| are unions of faces.
  Each such face has span ⊆ Y. Those of span ≠ Y are finitely many cones of
  dimension < dim Y. So if Y ∩ |V| has dimension dim Y, it contains a face
  of span Y.
- (b) X ⊆ L ⊆ |V|, so X ∩ |V| = X. Apply (a).
- (c) Every e ∈ S_max has h_e ⊇ L ⊇ X. So α_e factors through R^d/X, and
  |V| = X + |V| is the preimage of the cone K′ = {s_e ᾱ_e ≥ 0, e ∈ S_max}.
  - K′ is defined by hyperplanes of A_X/X and is full-dimensional, so it is
    a union of closed chambers of A_X/X, i.e. a top-cone.
  - A_X/X is essential, because X is the intersection of the hyperplanes
    that contain it.
  - The flats Y ⊇ X of A correspond to the flats Y/X of A_X/X. Since
    Y ∩ |V| is the preimage of (Y/X) ∩ K′, the condition of (a) holds for Y
    iff it holds for Y/X. ∎

**m(V).** Set m(V) = (−1)^d μ_{Λ(V)}(0, R^d). For a rank-0 arrangement,
Λ is a single point and m = 1. By Lemma 0.1(c), for a flat X ⊆ L,

  m(V_X) = (−1)^{codim X} μ_{Λ(V)}(X, R^d).

**Lie side.** Γ_V = span V, and Lune = span of the non-singleton top-lunes
([Cone, §1]). Put q(V) = dim Γ_V/(Γ_V ∩ Lune) = dim (Γ_V + Lune)/Lune. By
Aguiar–Mahajan's Ree criterion (CITED in [Cone]), this is
dim (Lie[A]|_V), the dimension of the Lie elements restricted to V.

**Cell structure.** The following are CITED as standard and were not
re-checked against a source:
- the faces F ≠ O of A, intersected with the unit sphere S, are the open
  cells of a regular CW decomposition of S^{d−1}, with cell dimension
  dim F − 1 (Björner–Las Vergnas–Sturmfels–White–Ziegler, *Oriented
  Matroids*, §4.1 and Ch. 5);
- the order complex of the face poset of a regular CW complex is
  homeomorphic to the complex (Björner, *Posets, regular CW complexes and
  Bruhat order*, Europ. J. Combin. 5 (1984)).

Each |V| ∩ Y ∩ S, for a flat Y, is a subcomplex.

**Lemma 0.2 (PROVEN).** Let Y ≠ 0 be a subspace and C ⊆ Y a closed convex
polyhedral cone with dim C = dim Y.
- If C ≠ Y, then C ∩ S is contractible.
- If C = Y, then C ∩ S is the sphere S^{dim Y − 1}.

*Proof.* The second case is clear. Suppose C ≠ Y.
- First we show that C ∩ −int C = ∅, where int is the interior in Y.
  Suppose u ∈ int C and −u ∈ C. For y ∈ Y and small ε > 0 we have
  u + εy ∈ C. Hence εy = (u + εy) + (−u) ∈ C, because C is closed under
  addition. So C = Y, a contradiction.
- Fix v ∈ int C. The homotopy (x, t) ↦ (1 − t)x + tv stays in C (by
  convexity) and avoids 0. Indeed, (1 − t)x + tv = 0 with x ∈ C would give
  x ∈ −int C if t > 0; and if t = 0 the point is x ≠ 0.
- So C ∖ 0 is contractible. C ∩ S is a deformation retract of C ∖ 0, by
  radial projection. ∎

---

## 1. Framework (a): cones of real arrangements

### 1.1 Theorem 1: every cone's support lattice is a wedge of spheres

**Theorem 1 (PROVEN, given the poset fiber theorem and the cell facts of
§0).** Let V be a top-cone of a finite real central essential arrangement of
rank d ≥ 1. Then

  Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{d−2},  and m(V) ≥ 0.

(For d = 1 read ⋁^1 S^{−1} = ∅.)

**Cited input (CITED; statement as recalled, theorem number not
re-checked).** This is the poset fiber theorem: Björner–Wachs–Welker,
*Poset fiber theorems*, Trans. AMS 357 (2005) 1877–1899, Thm 1.1. Let
f : P → Q be a poset map such that, for every q ∈ Q, the fiber
Δ(f^{-1}(Q_{≤q})) is ℓ(f^{-1}(Q_{<q}))-connected, where ℓ is the length of
the longest chain and ℓ(∅) = −1. Then

  Δ(P) ≃ Δ(Q) ∨ ⋁_{q ∈ Q} Δ(f^{-1}(Q_{≤q})) ∗ Δ(Q_{>q}),

where each wedge is taken at q.

*Proof.*

*d = 1.* The arrangement is {0} in R. Λ(V) = {0, R}, its proper part is
empty, μ = −1 and m(V) = 1. The statement holds.

Let d ≥ 2.

*Step 1: the map.* Let Q′ be the set of faces F of V with F ≠ O and F not a
chamber, ordered by the face order. Define f : Q′ → Λ̄(V) by
f(F) = span F. If F ≤ G then span F ⊆ span G, so f is a poset map. span F is
neither 0 (F ≠ O) nor R^d (F is not a chamber), so f lands in Λ̄(V).

*Step 2: the fibers.* Let Y ∈ Λ̄(V).
- f^{-1}(Λ̄_{≤Y}) is the set of faces F ≠ O of A with F ⊆ |V| ∩ Y. Such an F
  is never a chamber, because Y ≠ R^d. This set is the face poset of the
  regular CW complex |V| ∩ Y ∩ S. So its order complex is homeomorphic to
  |V| ∩ Y ∩ S.
- The cone C = |V| ∩ Y has dimension dim Y, by Lemma 0.1(a).
- C = Y iff Y ⊆ |V| ∩ −|V| = L. By Lemma 0.2, the fiber is a sphere
  S^{dim Y−1} if Y ⊆ L, and contractible otherwise.

*Step 3: connectivity.* f^{-1}(Λ̄_{<Y}) is the set of faces F ≠ O with
span F ⊊ Y. They have dimensions 1, …, dim Y − 1, so its longest chain has
length dim Y − 2. A contractible fiber is k-connected for every k. The sphere
S^{dim Y−1} is (dim Y − 2)-connected. So the hypothesis of the fiber theorem
holds, and

  Δ(Q′) ≃ Δ(Λ̄(V)) ∨ ⋁_{Y ∈ Λ̄(V), Y ⊆ L} S^{dim Y−1} ∗ Δ(Λ̄_{>Y}).   (1.1)

The terms with contractible fibers drop out, since the join with a
contractible space is contractible. By Lemma 0.1(c), Λ̄_{>Y} is the proper
part of Λ(V_Y), where V_Y has rank d − dim Y.

*Step 4: the left side.* Let Z = |V| ∩ S. It is a regular CW complex of
dimension d − 1, and its (d − 1)-cells are the N = #V chambers. Q′ is the
face poset of its (d − 2)-skeleton X, so Δ(Q′) ≅ X.
- By Lemma 0.2 with Y = R^d, Z is contractible if V is not all chambers,
  and Z = S^{d−1} if it is.
- Consider the exact sequence of the pair (Z, X). We have
  H_{d−1}(Z, X) ≅ Z^N (cellular chains), H_i(Z, X) = 0 for i ≤ d − 2, and
  H_{d−1}(X) = 0.
- So H̃_i(X) ≅ H̃_i(Z) = 0 for i < d − 2.
- In degree d − 2,

    H̃_{d−2}(X) ≅ Z^N / image(H_{d−1}(Z)).

  This is Z^N if Z is contractible. If Z = S^{d−1}, it is Z^{N−1}, the
  quotient by the primitive vector given by the fundamental class. Here we
  use H̃_{d−2}(Z) = 0, which holds for d ≥ 3. For d = 2, Z is S^1 or an
  arc, X is N or N + 1 points, and the same counts hold.
- Since (Z, X) is (d − 2)-connected, π_i(X) ≅ π_i(Z) = 0 for i ≤ d − 3.

*Step 5: conclusion.*
- In (1.1), Δ(Λ̄(V)) is a retract of the right-hand wedge: collapse the
  other wedge summands to the base point. So H̃_i(Δ(Λ̄(V)); Z) is a direct
  summand of H̃_i(X; Z). It is therefore free and zero for i ≠ d − 2.
- Similarly π_1(Δ(Λ̄(V))) is a retract of π_1(X) = 1 when d ≥ 4.
- Δ(Λ̄(V)) has dimension ≤ d − 2. A chain of proper flats has dimensions
  among 1, …, d − 1.
- Conclude by dimension:
  - **d = 2:** a finite set of points with H̃_0 free of rank r is
    ⋁^r S^0.
  - **d = 3:** a graph with H̃_0 = 0 is connected, and a connected graph is
    a wedge of circles.
  - **d ≥ 4:** a simply connected CW complex of dimension d − 2 whose only
    homology is free in degree d − 2 is a wedge of (d − 2)-spheres, by
    Hurewicz and Whitehead.
- The number of spheres is the reduced Euler characteristic, up to sign. By
  P. Hall's theorem (CITED, as in [Thm] input (B)),

    μ_{Λ(V)}(0, R^d) = χ̃(Δ(Λ̄(V))) = (−1)^{d−2} rank H̃_{d−2}.

  So the number is m(V) ≥ 0. ∎

**Corollary 1.1 (rank count; PROVEN).** For every top-cone V,

  #V = Σ_{X flat, X ⊆ lin V} m(V_X),

with m = 1 for the rank-0 localization X = R^d, which occurs only when V is
all chambers.

*Proof.* Take ranks of H̃_{d−2} in (1.1), using Step 4. For a sphere
S^a ∗ T we have H̃_{d−2}(S^{a} ∗ T) ≅ H̃_{d−3−a}(T). With a = dim Y − 1,
this is the top degree d − dim Y − 2 of Λ̄(V_Y). Its rank is m(V_Y) by the
theorem applied to V_Y, including the empty case dim Y = d − 1. So

  #V − [V = all] = m(V) + Σ_{0 ≠ Y ⊆ L, Y ≠ R^d} m(V_Y).

Move [V = all] to the right as the term Y = R^d. ∎

Theorem 2 below proves the same identity without the fiber theorem.

**Specializations.**
- *V = all chambers.* Λ(V) is the full intersection lattice, and Theorem 1
  is Folkman's theorem.
- *Pointed V.* Here L = 0. Every fiber is contractible, and Quillen's fiber
  lemma alone gives Δ(Λ̄(V)) ≃ X ≃ ⋁^{#V} S^{d−2}, so m(V) = #V.
- *The braid arrangement* (§1.3). This gives Jenča–Sarkoci.

### 1.2 Theorem 2: Zaslavsky's theorem for cones, via Euler characteristic

**Theorem 2 (PROVEN; uses only the cell facts of §0 and Möbius
inversion).** For every top-cone V of a finite real central essential
arrangement,

  #V = Σ_{X flat, X ⊆ lin V} m(V_X) = Σ_{X ⊆ lin V} (−1)^{codim X} μ_{Λ(V)}(X, R^d).

*Proof.*
- For Y ∈ Λ(V), put g(Y) = #{faces F of V with span F = Y} and
  f(Y) = Σ_{F face of V, F ⊆ Y} (−1)^{dim F}.
- Every face F ⊆ |V| ∩ Y has span in Λ(V) (Lemma 0.1(a)), and this span is
  ≤ Y. So f(Y) = Σ_{X ≤ Y in Λ(V)} (−1)^{dim X} g(X).
- On the other hand, O contributes 1, and the faces F ≠ O are the cells of
  |V| ∩ Y ∩ S, in dimension dim F − 1. So f(Y) = 1 − χ(|V| ∩ Y ∩ S).
- By Lemma 0.2 and Lemma 0.1(a), this is:
  - 0 if Y ⊄ L, since the complex is contractible;
  - 1 − (1 + (−1)^{dim Y − 1}) = (−1)^{dim Y} if 0 ≠ Y ⊆ L;
  - 1 if Y = 0.

  In every case f(Y) = (−1)^{dim Y} [Y ⊆ L].
- Möbius inversion on the finite poset Λ(V) gives
  (−1)^{dim Y} g(Y) = Σ_{X ≤ Y} f(X) μ(X, Y).
- At Y = R^d we have g(R^d) = #V. Using Lemma 0.1(b),
  #V = Σ_{X ⊆ L} (−1)^{d − dim X} μ(X, R^d).
- Lemma 0.1(c) turns each term into m(V_X). ∎

**Specializations (PROVEN).**
- *V = all chambers.* Then L = R^d, Λ(V) = L(A), and
  m(V_X) = |μ_{L(A)}(X, R^d)|, by the alternating signs of a geometric
  lattice. This is Zaslavsky's theorem.
- *Pointed V.* #V = m(V).
- *Braid arrangement.* See Corollary 1.4.

**COMPUTED** (`[zas]`, `[flatL]`; every top-cone of A_2, A_3, A_4, B_2, B_3
and generic5 / random7 in R^3 / random6 in R^4, plus 150 cones of D_4). The
negative control `test_lineality_restriction_matters` checks that summing
over all of Λ(V), instead of over the flats in lin V, fails on some cone of
A_3.

**Prior art.**
- Zaslavsky (1975, Example A, as quoted in Dorpalen-Barry–Kim–Reiner,
  *Whitney numbers for poset cones*, arXiv:1906.00036, eq. (2); CITED from
  the arXiv text) counts the chambers in a cone K by a different poset,
  L^int(K) = {X : X ∩ int K ≠ ∅}. That is an order ideal of L(A), and the
  formula is #C(K) = Σ_{X ∈ L^int(K)} |μ(R^d, X)|. It does not involve the
  lineality space or Λ(V).
- Dorpalen-Barry–Kim–Reiner refine this count for poset cones by Whitney
  numbers. Their poset is not OP(P): a grep of the text finds no
  "order-preserving", "Jen[čc]a" or homology of the closed-cone lattice.
- Theorem 2 with Λ(V) and the lineality sum was **not found**. It is
  elementary, and may be folklore.
- Theorem 1 for non-pointed cones was **not found** either. The pointed case
  is a one-line Quillen fiber lemma argument.
- Margolis–Saliola–Steinberg (*CW left regular bands*, arXiv:1508.05446)
  is the most likely place for a related statement, since the face monoid of
  a cone is a CW LRB. It was **not read** (search result only).

### 1.3 The braid case: Jenča–Sarkoci reproved

Essentialize the braid arrangement in R^n/R·1, so d = n − 1. The top-cones
are the order cones C_P ([Cone, §8], A001035 count). Prop. 2.2 of [Cone]
(PROVEN, audited) identifies the supports of the faces of C_P with OP(P). A
partition π corresponds to the subspace {x constant on the blocks of π}, so
finer partitions give larger subspaces and Λ(C_P) ≅ OP(P)^op. The order
complexes of P and P^op coincide. Also lin C_P = {x constant on components},
whose flats are the partitions σ of the component set K. The localization
at σ is the product of the braid arrangements on the blocks, and
(C_P)_σ = Π_{B ∈ σ} C_{P|_B}. Since Λ and μ are multiplicative on products,
and the signs (−1)^{rank} multiply, m((C_P)_σ) = Π_B m(C_{P|_B}).

**Lemma 1.3 (component formula; PROVEN, elementary).** For every finite
poset P with set of components K,

  |Lin P| = Σ_{σ ∈ Π(K)} Π_{B ∈ σ} e_C(P|_B).

[Glob, §3.3] proves this by generating functions and [Thm] states it as
Cor. eC. Here is a bijective proof.

*Proof.*
- A **cut** of w ∈ Lin(P) is a k ∈ {1, …, n} such that {w_1, …, w_k} is a
  union of components. The **pieces** of w are the segments between
  consecutive cuts, with 0 and n counted as cuts.
- Each piece is a word p on a union of components T. It is a linear
  extension of P|_T, and it is **irreducible**: it has no proper prefix that
  is a union of components of P|_T. Indeed, a difference of two unions of
  components is a union of components, and the components of P|_T are the
  components of P inside T.
- Conversely, let p_1, …, p_k be irreducible words on disjoint unions of
  components T_i covering [n], each p_i ∈ Lin(P|_{T_i}). Then w = p_1⋯p_k
  is in Lin(P), because there are no relations between different T_i. Its
  cuts are exactly the boundaries |p_1| + ⋯ + |p_j|. Boundaries are cuts
  since the prefixes are unions of components. A cut inside p_j would make
  a proper prefix of p_j a union of components of P|_{T_j}.
- So Lin(P) is in bijection with the **sequences** of irreducible pieces
  covering [n].
- In the same way, the cyclic class of w ∈ Lin(P|_B) is
  {wγ^k : k a cut} ([Thm, Lemma rot]). So the classes of P|_B are in
  bijection with the **cyclic sequences** of irreducible pieces covering B.
  Rotating at a cut rotates the sequence of pieces, the pieces of the
  rotated word are the same pieces, and distinct cyclic sequences give
  distinct sets of words.
- Order the pieces by their least letter. Apply Foata's fundamental
  transformation to the sequence of pieces. That is: cut the sequence before
  each left-to-right maximum; each segment, read cyclically, is a cycle. The
  inverse writes each cycle starting at its maximum, sorts the cycles by
  increasing maximum and concatenates.
- This is a bijection between the sequences of a finite set of distinct
  totally ordered objects and the sets of cycles that partition it.
  Pieces with disjoint letter sets are distinct objects.
- So the sequences of irreducible pieces covering [n] correspond to the sets
  of cyclic sequences whose letter sets partition [n]. Such a set is a
  partition σ of K together with one cyclic class of P|_B for each block B.
  ∎

**COMPUTED** (`[foata]`): for all 405 unlabeled posets with n ≤ 6, the Foata
images are distinct and their number is |Lin P| = Σ_σ Π e_C(P|_B). Negative
control: with |Lin(P|_B)| in place of e_C(P|_B), the 2-antichain gives 3 ≠ 2.

**Corollary 1.4 (Jenča–Sarkoci Thm 4.5, reproved; PROVEN, given the fiber
theorem).** For every finite poset P on n ≥ 2 points,
Δ(OP̄(P)) ≃ ⋁^{e_C(P)} S^{n−3}.

*Proof.*
- Theorem 1 gives a wedge of m(C_P) spheres of dimension n − 3.
- By Theorem 2 and the multiplicativity above,
  |Lin P| = Σ_{σ ∈ Π(K)} Π_{B ∈ σ} m(C_{P|_B}).
- The term σ = {K} is m(C_P). Every other term involves posets with fewer
  components.
- Lemma 1.3 is the same recursion with e_C in place of m. The base case is a
  connected P, where m(C_P) = |Lin P| = e_C(P).
- Induction on the number of components gives m(C_P) = e_C(P). ∎

**Consequence for [Thm].** Input (A) of [Thm] (Jenča–Sarkoci) can be
replaced by the poset fiber theorem together with standard facts on regular
CW complexes. This does not remove citations; it trades a specialized one for
standard tools. But it makes the dimension and the homotopy type of H_P the
braid case of a statement about every cone of every real arrangement.

### 1.4 The Lie side: what governs q(V)

Let L = lin V and let Σ_L be the set of faces of A contained in L. It is
closed under the Tits product, since L is a subspace, so it is a sub-LRB of
the Tits monoid. It is the face monoid of the essential arrangement induced
on L.

**Proposition 3.**
- (a) (PROVEN) Σ_L acts on V by C ↦ HC, so Γ_V is a left kΣ_L-module.
  Put Lie_L(Γ_V) = {z ∈ Γ_V : Hz = 0 for all H ∈ Σ_L ∖ O}. Then, under the
  standard inner product,

    span{top-lunes contained in V} = Lie_L(Γ_V)^⊥   (inside Γ_V).

- (b) (PROVEN, given Brown's description of the simple modules of an LRB
  algebra; CITED, as in [Cone, §6], not re-checked) The multiplicity of the
  bottom simple module S_0 in Γ_V is

    [Γ_V : S_0] = Σ_{X ∈ Λ_L} μ(0, X) c_X = m(V).

  Here Λ_L is the set of flats contained in L, and c_X is the number of
  chambers of V above a face of span X. Hence

    q(V) ≤ dim Lie_L(Γ_V) ≤ m(V).

- (c) (PROVEN, given Saliola's idempotents; the property used was not
  re-checked against the source) dim Lie_L(Γ_V) = m(V). So q(V) = m(V) iff
  Γ_V ∩ Lune is spanned by the lunes inside V, which is (G1) of [Cone].

*Proof.*

(a) *The action.* Let H ∈ Σ_L and C ∈ V. HC is a chamber, and it lies in V:
on e ∈ S_max we have H_e = 0, so (HC)_e = C_e = s_e. Associativity of the
Tits product makes Γ_V a module.

(a) *The adjoint.* Let T_H : Γ_V → Γ_V be C ↦ HC. Its adjoint sends a
chamber D ∈ V to Σ_{C ∈ V, HC = D} C.
- This is the full top-lune L(H, D) = {C : HC = D} when D ≥ H, and 0
  otherwise.
- The lune lies in V: by Lemma L of [Cone] (PROVEN, audited), a lune L(H, D)
  with D ∈ V lies in V iff H ⊆ L.
- Conversely, every lune inside V is of this form, again by Lemma L.

So span{lunes in V} = Σ_{H ≠ O} T_H^*(Γ_V) = (∩_{H ≠ O} ker T_H)^⊥.

(b) *Simple modules.*
- For x ∈ Σ_L let χ_X(x) = [span x ⊆ X]. Since span(xy) = span x + span y
  (taken in the flat lattice), χ_X is multiplicative.
- Brown (CITED) shows that the χ_X, for X ∈ Λ_L, are the simple modules of
  kΣ_L. Write S_X for them.
- So for every finite-dimensional module M, tr(x | M) = Σ_X [M : S_X] χ_X(x),
  summing over a composition series.

(b) *Traces.* For M = Γ_V, x acts by an idempotent map on chambers, so
tr(x | Γ_V) is the number of fixed chambers, #{C ∈ V : xC = C}. This number
is c_{span x}: the chambers C ≥ x in V correspond to the chambers of the
localization in V_{span x}. So c_Y = Σ_{X ⊇ Y} [Γ_V : S_X], and Möbius
inversion gives [Γ_V : S_0] = Σ_X μ(0, X) c_X.

(b) *Comparison with m(V).* c_X = #V_X. Theorem 2 applied to V_X reads
#V_X = Σ_{X ⊆ X′ ⊆ L} m(V_{X′}). Here we use that lin V_X = L/X and that
the flats of A_X/X inside L/X are the X′/X; the intervals of Λ_L are
compatible. Möbius inversion on Λ_L gives m(V_X) = Σ_{X′ ⊇ X} μ(X, X′) #V_{X′}.
At X = 0 this is [Γ_V : S_0].

(b) *The inequalities.* Lie_L(Γ_V) is a submodule all of whose composition
factors are S_0: x ≠ O acts by 0 and O acts by 1. So
dim Lie_L(Γ_V) ≤ [Γ_V : S_0]. Also span{lunes in V} ⊆ Γ_V ∩ Lune, so
q(V) = #V − dim(Γ_V ∩ Lune) ≤ #V − dim span{lunes in V} = dim Lie_L(Γ_V)
by (a).

(c) *Cited input.* Saliola (*The quiver of the semigroup algebra of a left
regular band*, IJAC 17 (2007), §4; CITED, statement not re-checked) gives an
idempotent e_0 ∈ kΣ_L that satisfies x e_0 = 0 for x ≠ O and χ_0(e_0) = 1.

(c) *Proof.*
- e_0 Γ_V ⊆ Lie_L(Γ_V), because H e_0 = 0 for H ≠ O.
- Conversely, if z ∈ Lie_L(Γ_V), then every term of e_0 − O, which is a
  combination of faces ≠ O, kills z. So e_0 z = z.
- Hence Lie_L(Γ_V) = e_0 Γ_V. Its dimension is the trace of the idempotent
  e_0, which is Σ_X [Γ_V : S_X] χ_X(e_0) = [Γ_V : S_0]. The values
  χ_X(e_0) = δ_{X0} follow from orthogonality of the idempotent system. ∎

**COMPUTED** (`[brown]`): Σ_{X ⊆ L} μ(0, X) c_X = m(V) on every cone tested.
Together with [Cone]'s `[K]` check, (G1), this gives equality throughout
(c) on all those cones.

**Correction to [Cone, §6].** [Cone] concluded that "LRB theory of F(P)
does not see H_P". The intrinsic Lie part, killed by all of F(V) ∖ O, is
indeed 0 for proper cones. The right LRB is the smaller monoid Σ_L of the
lineality space. Its bottom multiplicity is exactly m(V) = dim H̃(Λ̄(V)).
This uses the opposite involution through Lemma L, as [Cone] said it must:
H ⊆ L iff −H ⊆ L.

### 1.5 The general conjecture

**Conjecture G\* (cone JKS; CONJECTURED).** For every top-cone V of every
finite real central essential arrangement with symmetry group W:
- (numerical) q(V) = m(V);
- (equivariant) H̃_{d−2}(Λ̄(V); C) ≅ det ⊗ (Γ_V + Lune)/Lune as
  Stab_W(V)-modules, where det is the determinant of the action on R^d.

**Equivalent forms of the numerical statement.** The first is PROVEN given
Prop. 3(c). The second is PROVEN given that an ambient isomorphism
Φ_A : H̃_{d−2}(L̄(A)) → Γ/Lune with Φ_A(ρ_C) = ±C exists. For the braid
arrangement this is Prop. Φ of [Thm] (CITED). For general A it is
Aguiar–Mahajan, Topics, Thm 14.32 (CITED from [Cone], statement not
re-checked).
- (i) (G1) Γ_V ∩ Lune = span{lunes in V}.
- (ii) (G3) The chamber cycles ρ_C, C ∈ V, span H̃_{d−2}(Λ̄(V)).
  - Φ_A maps the span of these cycles isomorphically onto
    (Γ_V + Lune)/Lune, which has dimension q(V). The whole group has
    dimension m(V) by Theorem 1. So (ii) holds iff q(V) = m(V).
  - Equivalently, the map f_* : H_{d−2}(X) → H_{d−2}(Λ̄(V)) in the proof of
    Theorem 1 is surjective. This holds because H_{d−2}(X) is spanned by
    the boundaries of the chambers, and f_* sends ∂C to ρ_C.
- (iii) (extension) Every vector of Lie_L(Γ_V) is the restriction to V of a
  global Lie element. This is (i) dualized, since
  (Γ_V ∩ Lune)^⊥ = pr_V(Lie[A]).

**Known cases (PROVEN).**
- *Pointed V:* Γ_V ∩ Lune = 0 ([Cone, Thm 5.2], audited), so q = #V = m(V)
  by Theorem 2.
- *V = all chambers:* q = |μ(L(A))| (Aguiar–Mahajan, CITED), and this
  equals m(V).
- *Braid arrangement:* q(C_P) = e_C(P) by [Thm, Thm S(b)] (pure word
  combinatorics, audited), and m(C_P) = e_C(P) by Cor. 1.4.
- The equivariant form for braid is [Thm, Thm S(d)], H_P ⊗ sgn ≅ M_P,
  since det = sgn there. That is PROVEN given Prop. Φ, as in [Thm].

**COMPUTED.**
- `[q=m]`: all top-cones of A_2 (19), A_3 (219), A_4 (4231), B_2 (33),
  B_3 (941), generic5 (163), random7 in R^3 (491) and random6 in R^4 (579),
  plus 150 sampled cones of D_4.
- `[eq]` (new): the equivariant form for every g in the stabilizer of every
  cone of A_2, A_3, A_4, B_2 and B_3, and of the D_4 sample. Here W is the
  full hyperoctahedral group W(B_4), which preserves D_4.
  - The left side is computed as (−1)^d μ(Λ(V)^g). This is the
    Hopf trace / Hall argument of [Thm, Lemma homchar], valid because of
    Theorem 1.
  - The right side is the trace of g on the image of Γ_V in Γ/Lune,
    computed by exact elimination mod p. Both sides are integers of
    absolute value ≤ #V.
- **Control:** without the det twist the identity fails on 9/33 cones of
  B_2, 115/941 of B_3 and 64/150 of D_4. For A_2, A_3 and A_4 the twist is
  invisible: sgn ⊗ M ≅ M for every cone at n ≤ 5. This is the same
  phenomenon as the n = 6 twist in [Thm, Prop. frob].

**How poset JKS specializes.** For V = C_P:
- Theorem 1 gives Jenča–Sarkoci;
- Conjecture G\*, already a theorem in this case, gives H_P ⊗ sgn ≅
  C[Lin P]/R_P = M_P;
- the truncation isomorphism ψ_P of [Thm, Cor. psi] identifies M_P with
  Klyachko's model Lie(P) = W_P e_ζ.

The last step is type-A specific. It uses the Coxeter element γ = (1 2 ⋯ n)
acting on the chambers by rotation, and the admissibility of ζ (Theorem Ψ).
For other types, H̃_{top}(L(A_W)) is not induced from the cyclic group
generated by a Coxeter element in general: for B_2, |μ| = 3 but
|W|/h = 2. So the natural general object is (Lie[A]|_V)^*, not an e_ζ-model.
The character formula [Thm, eq. closed], proved by Weisner's theorem on the
orbit partition, has no general analogue yet. Finding the fixed-point
formula for μ(Λ(V)^g) in a general reflection arrangement is an open
sub-problem (§5).

**What is new beyond the Lawrence / Khovanskii–Pukhlikov valuation.** [Nov2,
§4.3] shows that the pointed-cone theorem ([Cone, Thm 5.2]) follows from the
exponential valuation, which kills every polyhedron containing a line. That
argument says nothing about non-pointed cones, because it kills all the
lunes of the lineality space at once. The results here concern exactly that
case:
- the homotopy type of Λ̄(V) for every cone (Theorem 1);
- the lineality-sum count (Theorem 2), an Euler-characteristic argument (the
  Euler valuation) that keeps track of the flats in lin V instead of killing
  them;
- the identification of m(V) with an LRB multiplicity of Σ_L (Prop. 3);
- the equivariant computation.

None of these follows from the valuation. Conjecture G\* is a statement about
non-pointed cones by construction, since it holds trivially for pointed
ones.

---

## 2. Framework (b): species and Hopf monoids

[Glob, §4] built the Hopf monoid 𝐐 of pairs (P, ℓ), with ℓ ∈ Lin(P). Its
product is (P, u)(P′, u′) = (P + P′, uu′), and its coproduct is restriction
to every S. It found that Prim(𝐐)[n] ≅ ⊕_P Lie(P) only as S_n-modules, not
P-homogeneously. It conjectured three things:
1. a poset cooperad;
2. a filtration whose associated graded primitives are ⊕_P Lie(P);
3. a local PBW.

(2) and (3) are proved below. The fix is to restrict the coproduct to unions
of components.

### 2.1 The Hopf monoid Q′

Let Q′[I] have basis the pairs (P, ℓ), with P a poset on I and ℓ ∈ Lin(P).
Put

  μ_{S,T}((P, u) ⊗ (P′, u′)) = (P + P′, uu′),
  Δ_{S,T}(P, ℓ) = (P|_S, ℓ|_S) ⊗ (P|_T, ℓ|_T) if S is a union of components
  of P, and 0 otherwise.

Write Q′_P = span{(P, ℓ) : ℓ ∈ Lin P}, so Q′[I] = ⊕_P Q′_P.

**Lemma 2.1 (PROVEN).** Q′ is a connected, cocommutative Hopf monoid in
species. μ maps Q′_P ⊗ Q′_{P′} to Q′_{P+P′}. If Δ_{S,T} is nonzero on Q′_P,
it maps Q′_P to Q′_{P|_S} ⊗ Q′_{P|_T}, and in that case P = P|_S + P|_T.

*Proof.*
- **Associativity, unit and counit** are clear. Q′[∅] = k.
- **Coassociativity.** Both iterated coproducts at S_1 ⊔ S_2 ⊔ S_3 equal
  ⊗_i (P|_{S_i}, ℓ|_{S_i}) when every S_i is a union of components of P,
  and 0 otherwise. This uses that, for S a union of components, the unions
  of components of P|_S are exactly the unions of components of P contained
  in S.
- **Cocommutativity.** The complement of a union of components is one.
- **Compatibility.** Let (P, u) live on S and (P′, u′) on T, and let
  I = S ⊔ T = S′ ⊔ T′. Put A = S ∩ S′, B = S ∩ T′, C = T ∩ S′, D = T ∩ T′.
  - S′ is a union of components of P + P′ iff A is one for P and C is one
    for P′.
  - In that case (P + P′)|_{S′} = P|_A + P′|_C and (uu′)|_{S′} = u|_A u′|_C,
    and similarly for T′.
  - So Δ_{S′,T′} μ_{S,T} = (μ_{A,C} ⊗ μ_{B,D})(Δ_{A,B} ⊗ Δ_{C,D}), including
    when both sides are zero.
- The grading statements are immediate. P is recovered from (P|_S, P|_T)
  when S is a union of components. ∎

**Theorem 7 (P-graded Lie structure; PROVEN).** Let 𝔭 = Prim(Q′).
- (a) 𝔭 = ⊕_P 𝔭_P is graded by posets, with 𝔭_P = 𝔭 ∩ Q′_P. The commutator
  [x, y] = μ_{S,T}(x ⊗ y) − μ_{T,S}(y ⊗ x) maps 𝔭_P ⊗ 𝔭_{P′} to 𝔭_{P+P′}.
- (b) Identify Q′_P with W_P = C[Lin P]. Then 𝔭_P = R_P^⊥, the annihilator of
  R_P under the pairing with orthonormal basis Lin(P). Also
  𝔭_P = pr_P(Lie_I), the truncations of Lie polynomials to the linear
  extensions. Here Lie_I is the multilinear part of the free Lie algebra on
  I, and Ree's theorem is CITED as in [Thm].
- (c) dim 𝔭_P = e_C(P). As Aut(P)-modules,
  𝔭_P ≅ M_P^* ≅ M_P ≅ Lie(P) ≅ sgn ⊗ H_P.
- (d) The bracket is the truncation of the free Lie bracket:
  [pr_P x, pr_{P′} y] = pr_{P+P′}[x, y] for x ∈ Lie_S and y ∈ Lie_T.
- (e) For the antichains, 𝔭 restricts to the classical Lie species with its
  bracket.

*Proof.*

(a) *Grading.* Let x = Σ_P x_P be primitive.
- If S is a union of components of P, then Δ_{S,T} x_P lies in
  Q′_{P|_S} ⊗ Q′_{P|_T}.
- Distinct P with this property have distinct pairs (P|_S, P|_T), since
  P = P|_S + P|_T. So these images lie in independent summands.
- If S is not a union of components of P, then Δ_{S,T} x_P = 0.
- So Δ_{S,T} x = 0 forces Δ_{S,T} x_P = 0 for each P, and each x_P is
  primitive.

The commutator of primitives is primitive in any bimonoid in species
(Aguiar–Mahajan, *Monoidal Functors, Species and Hopf Algebras*, Ch. 11;
CITED, standard). By Lemma 2.1 it lies in degree P + P′.

(b) *Primitives as an annihilator.* Let x = Σ c_ℓ ℓ ∈ W_P, let S be a
proper nonempty union of components, s ∈ Lin(P|_S) and t ∈ Lin(P|_T). Then

  ⟨Δ_{S,T} x, s ⊗ t⟩ = Σ_{ℓ : ℓ|_S = s, ℓ|_T = t} c_ℓ = ⟨x, s ш t⟩.

Every shuffle of s and t lies in Lin P, and each occurs once. So x is
primitive iff x ⊥ R_P.

(b) *Truncations of Lie elements.* For a subspace U of C^N and a coordinate
subspace W, pr_W(U^⊥) = (U ∩ W)^⊥ ∩ W.
- "⊆": if z ⊥ U and u ∈ U ∩ W, then ⟨pr_W z, u⟩ = ⟨z, u⟩ = 0.
- Equal dimensions:
  dim pr_W(U^⊥) = dim U^⊥ − dim(U^⊥ ∩ W^⊥) = dim(U + W) − dim U
  = dim W − dim(U ∩ W).

Take U = Sh_I and W = W_P. Then U^⊥ = Lie_I (Ree), and U ∩ W = R_P by
[Thm, Thm S(b)] (PROVEN, audited, elementary).

(c) *Dimension and module structure.*
- dim = |Lin P| − dim R_P = e_C(P), by Thm S(b).
- The pairing is Aut(P)-invariant, so 𝔭_P = R_P^⊥ ≅ (W_P/R_P)^* = M_P^*.
- M_P is defined over Q, so its character is real and M_P^* ≅ M_P.
- M_P ≅ Lie(P) by ψ_P ([Thm, Cor. psi]; PROVEN, audited, unconditional).
- Lie(P) ≅ sgn ⊗ H_P by [Thm, Thm main].

(d) *The bracket.* A word uv, with u on S and v on T, is in Lin(P + P′) iff
u ∈ Lin P and v ∈ Lin P′. So pr_{P+P′}(xy) = pr_P(x) pr_{P′}(y)
(concatenation), and likewise for yx.

(e) For an antichain, pr is the identity. ∎

**COMPUTED** (`[prim]`): dim 𝔭_P = |Lin P| − rank R_P = e_C(P) for all 405
posets with n ≤ 6.

**Theorem 8 (the filtration; PROVEN).** Let r(P) be the number of strict
relations of P, and let F_r𝐐 = span{(P, ℓ) : r(P) ≤ r}. This is a Hopf
filtration of [Glob]'s 𝐐, and gr 𝐐 ≅ Q′ as Hopf monoids. Moreover, given the
Cartier–Milnor–Moore and PBW theorems for species (CITED as in [Glob]),
gr Prim(𝐐) = Prim(Q′) = ⊕_P 𝔭_P with 𝔭_P ≅ Lie(P). So [Glob]'s conjecture
(2) holds for this filtration.

*Proof.*
- r(P + P′) = r(P) + r(P′). Also r(P|_S) + r(P|_T) ≤ r(P), with equality
  iff no relation joins S to T, i.e. iff S is a union of components.
- So μ(F_a ⊗ F_b) ⊆ F_{a+b} and Δ(F_r) ⊆ Σ_{a+b=r} F_a ⊗ F_b.
- In gr, the coproduct of (P, ℓ) keeps exactly the terms with
  r(P|_S) + r(P|_T) = r(P). Those are the restrictions to unions of
  components, i.e. the coproduct of Q′. The product is unchanged.
- Leading terms of primitives are primitive. A relation Δ_{S,T}x = 0
  vanishes in every bidegree, in particular in the top one. Leading terms of
  a filtered subspace span a subspace of gr of the same dimension. So
  gr Prim(𝐐) ⊆ Prim(gr 𝐐).
- Both sides have dimension (n − 1)! b_n in degree [n]. By CMM–PBW, Prim of
  a connected cocommutative Hopf monoid has cycle index Log of that of the
  monoid, and 𝐐 and Q′ have the same underlying species. So the inclusion is
  an equality. ∎

### 2.2 The local PBW theorem

**Theorem 6 (local PBW; PROVEN, given [Thm, Thm S(b)]).** For every finite
poset Q, choose a complement V_Q to R_Q in W_Q, natural under poset
isomorphisms. That is, choose an Aut-stable complement for one
representative of each isomorphism class (Maschke) and transport it; the
result is well defined because the complement is Aut-stable. Let K be the
set of components of P. Then shuffle multiplication

  m_P : ⊕_{σ ∈ Π(K)} ⊗_{B ∈ σ} V_{P|_B} → W_P = C[Lin P]

is an Aut(P)-equivariant isomorphism. The tensor product is over the
unordered blocks, and shuffle is commutative. Consequently, as
Aut(P)-modules,

  C[Lin P] ≅ ⊕_{σ ∈ Π(K)} ⊗_{B∈σ} Lie(P|_B) ≅ ⊕_{σ} ⊗_{B∈σ} (sgn ⊗ H_{P|_B}),

which is "Sym over components" of the Lie(P|_T), as conjectured in
[Glob, §4.3]. For n = |B| ≤ 2 use the conventions of [Thm]. Since C[Lin P]
is a free Aut(P)-module, so is the right-hand side.

*Proof.*

*Well defined.* For B a union of components, shuffles of linear extensions
of the P|_B lie in Lin(P). The map is equivariant because shuffle commutes
with relabelling and the V_Q are natural.

*Surjective, by induction on the number of components.* If P is connected,
R_P = 0, so V_P = W_P, and only σ = {K} occurs. In general
W_P = V_P + R_P, and V_P is the image of σ = {K}.
- R_P is spanned by s ш t with s ∈ W_{P|_S} and t ∈ W_{P|_T}, where S is a
  proper nonempty union of components ([Thm, §basis]).
- P|_S and P|_T have fewer components. By induction s and t are sums of
  shuffle products over partitions of their component sets.
- Shuffle of words on disjoint alphabets is associative and commutative. So
  s ш t is a sum of products over partitions of K, and lies in the image.

*Equal dimensions.* dim V_Q = e_C(Q) by Thm S(b). So the domain has
dimension Σ_σ Π_B e_C(P|_B) = |Lin P| by Lemma 1.3.

*The consequences.*
- V_Q ≅ M_Q naturally, by the quotient map.
- M_Q ≅ Lie(Q) by ψ_Q, which is natural under relabelling ([Thm, Cor. psi]
  and Thm Θ).
- Lie(Q) ≅ sgn ⊗ H_Q by [Thm, Thm main], applied to one Q in each
  isomorphism class and transported ([Thm, Remark abstract]). ∎

For the antichain, Theorem 6 is the classical PBW decomposition
C[S_n] ≅ ⊕_{σ ∈ Π_n} ⊗_B Lie(B), i.e. T ≅ Sym ∘ Lie, as S_n-modules.

**COMPUTED.**
- `[pbw]`: with V_Q = span(B_Q), the first-block basis, the shuffle products
  over all σ are exactly |Lin P| vectors of rank |Lin P|, for all 405 posets
  with n ≤ 6.
- `[pbw-eq]`: for every g ∈ Aut(P), the character of C[Lin P] (that is,
  |Lin P|·[g = 1]) equals Σ_{gσ=σ} Π_{g-orbits of blocks} χ_{Lie(P|_B)}(g^k|_B).
  Here χ_{Lie} is computed independently, as Σ ζ^r over the fixed cyclic
  classes. This holds for all 405 posets with n ≤ 6.

### 2.3 How (b) meets (a), what remains, and prior art

**(b) = (a) on the braid arrangement (PROVEN).** Let W = Q′^* be the dual.
It is commutative: its product is the shuffle product with disjoint union,
and its coproduct is deconcatenation at cuts. Its decomposables in degree P
are (W_+ · W_+)_P = R_P = span{lunes in C_P} ([Cone, Cor. 3.1]). Its
indecomposables are M_P = W_P/R_P ≅ H_P ⊗ sgn ([Thm, Thm S(d)]).

So the relations that cut Γ_{C_P} down to H_P are exactly the products. This
is how Lemma L of (a), "lunes in V have their flat in lin V", reads
algebraically. It also explains why the "functorial model" of [Thm,
§natural] is the M side: it is the indecomposable quotient of a Hopf monoid.

**Remaining conjectures (CONJECTURED).**
- (b1) *Arrangement version.* For a general real arrangement, the cones V
  should carry the analogous structure in Aguiar–Mahajan's theory of
  bimonoids over the Tits monoid (*Bimonoids for Hyperplane Arrangements*,
  CUP 2020), with "lunes in V" as the decomposables. Conjecture G\* would
  then be a PBW statement for the cone. This is the precise way (b) would
  generalize, and it is the same open problem as (a).
- (b2) *Cooperad.* [Glob]'s deconcatenation at all down-sets (not only at
  cuts) gives maps W_P → ⊕_{S ideal} W_{P|_S} ⊗ W_{P|_T}. This is the
  coproduct of Malvenuto–Reutenauer's double-poset Hopf algebra, restricted
  to special double posets. (CITED from a search summary: Malvenuto–
  Reutenauer, JCTA 118 (2011) 1322–1333, arXiv:0905.3508, with coproduct
  over inferior ideals. The exact product convention was not re-checked.)
  - Its associated graded, by number of relations, is again Q′^*. The proof
    of Theorem 8 applies verbatim: equality of relation counts holds iff S
    is a union of components.
  - Whether the down-set coproduct descends to ⊕_P M_P, giving a "poset Lie
    cooperad", is untested.
  - The general framework for operads from families of partition-type
    posets is Delcroix-Oger–Dupont (arXiv:2505.06094, found in [Nov2]).
    OP(P) is not among their examples.

**Prior art.**
- The tools are standard: Hopf monoids in species, CMM–PBW, Foata's
  transformation, and Ree.
- Pairs (P, ℓ) with ℓ a linear extension are Malvenuto–Reutenauer's special
  double posets. Their Hopf algebra uses the down-set coproduct, not the
  union-of-components one.
- Theorems 6–8 for general P, i.e. a P-graded Lie structure with components
  Lie(P), were **not found**. Only one search was made, and it was not
  exhaustive.

---

## 3. Framework (c): congruence lattices and closure systems

**The structure.** OP(P) is the lattice of order congruences of P, the
kernels of isotone surjections onto chains (Jenča–Sarkoci, after
Körtesi–Radeleczki–Szilágyi and Czédli–Lenkehegyi; CITED in [Thm]). It is
closed under the partition meet ([Thm, Lemma lattice(i)]) and contains 1̂,
so it is a closure system (Moore family) in Π_n.

**Assessment.**
- *Closure systems in Π_n in general: no theorem.* Any meet-closed family
  in Π_n containing 0̂ and 1̂ is a lattice, and such lattices can have
  arbitrary homotopy type. So "closure system" is too weak to imply a wedge
  of spheres or a Lie module. What makes OP(P) special is that it is
  Λ(C_P), a lattice of supports of a convex cone (Theorem 1).
- *Congruence lattices of finite algebras:* no analogue was found in which
  the top homology carries a Lie-type representation. The relevant feature
  is convexity in an arrangement, not a universal-algebra property.
- *Combinatorial version of (a) (CONJECTURED).* Theorems 1 and 2 should hold
  verbatim for every T-convex set of topes of a (possibly non-realizable)
  oriented matroid. Only three ingredients are used:
  - the regular cell structure (topological representation theorem);
  - Lemma 0.2, the contractibility of convex sets that are not
    "subspaces";
  - the localization of Lemma 0.1(c).

  The second needs an oriented-matroid proof, e.g. via shellability of
  T-convex sets. This is the only lattice-level generalization that we
  propose. It sits inside (a).
- *Comodernism.* Schweig–Woodroofe prove OP(P) comodernistic, hence
  CL-shellable (CITED in [Nov2]). Whether every Λ(V) is comodernistic is
  open (CONJECTURED plausible, not tested). That would strengthen Theorem 1
  to shellability.
- *Fixed-point lattices.* The Möbius side of [Thm] is Hanlon's hinge and its
  complements ([Nov2, §2]), handled by Weisner's theorem in OP(P)^g. A
  general version would compute μ(Λ(V)^g) for a reflection group acting on
  a cone. Baclawski–Björner 1981 (*Fixed points and complements in finite
  lattices*), still unread, is the candidate prior art. This is a
  proof-technique question inside (a), not a separate framework.

**Verdict.** (c) gives no general statement beyond (a). Its useful content is
the oriented-matroid version of Theorem 1 and the open fixed-point formula.

## 4. Other frameworks considered

- **Varchenko–Gelfand rings and COMs** (Dorpalen-Barry's thesis *Cones of
  hyperplane arrangements*, 2021; Dorpalen-Barry–Proudfoot–Wang,
  arXiv:2208.04855; both found by search, **not read**). They attach a
  filtered ring to a cone whose associated graded is governed by L^int(K).
  If its top graded piece, or a dual Orlik–Solomon-type algebra built from
  Λ(V), were isomorphic to H̃(Λ̄(V)) ⊗ det equivariantly, that would give a
  third, cohomological model in Conjecture G\*. Not investigated. It is a
  natural second step after G\*.
- **Koszul-duality / operadic** (Fresse, Vallette, Delcroix-Oger–Dupont).
  This is the right language for (b2), and it sits under (b).

## 5. Ranked recommendation

**1. Pursue (a): the Lie theory of cones of real hyperplane arrangements.**
- *Why.* It already proves general theorems (1, 2 and Prop. 3) that contain
  the homotopy and dimension part of poset JKS (Jenča–Sarkoci) as the braid
  case. It isolates all of the remaining content in one conjecture, G\*,
  which holds in the pointed, full and braid cases and on 6,826 computed
  cones.
- It explains the poset-specific features:
  - lineality = components;
  - lunes in V = shuffles over unions of components;
  - the bottom multiplicity of Σ_L = e_C.
- The type-A-only part, Klyachko's e_ζ model and the cyclic character
  formula, is cleanly separated out.
- *First theorem to attack.* **Conjecture G\* in the form (ii): for every
  top-cone V, the chamber cycles span H̃_{d−2}(Λ̄(V)).** Equivalently, the
  map f_* : H_{d−2}(skeleton) → H_{d−2}(Λ̄(V)) of Theorem 1's proof is
  onto. Suggested route: induction on dim lin V.
  - Peel off one line X ⊆ L. By (1.1), its fiber term is
    S^0 ∗ Λ̄(V_X), and the lunes of X inside V give explicit cycles
    Σ_{C∈lune} ∂C there.
  - Show that these lune cycles span the extra summands of (1.1). That is a
    lune-PBW statement: dim span{lunes in V} = Σ_{0≠X⊆L} m(V_X).
  - Then f_* is onto by rank count.
  - The restriction maps E_h of [Cone, Lemma E] (PROVEN, audited) give the
    induction step on the Lie side, as in [Cone, Thm 5.2].
  - What is missing is the analogue of the first-block basis B_P of
    [Thm, Thm S(a)] for the lunes of the lineality flats. For the braid
    arrangement it exists, so the general lemma should be modelled on it.
- *Equivariant upgrade.* Once (ii) holds, G\*-eq follows from the
  W-equivariance of the ambient Φ_A, so it needs no separate argument. The
  det twist is then automatic, and it is confirmed computationally (§1.5).
- *What would refute it.*
  - (1) A single top-cone, in any real arrangement, with q(V) < m(V). By
    Prop. 3(b) a failure must be a strict inequality in this direction, so
    the search is a finite rank computation. The best places to look are
    rank ≥ 4 non-reflection or non-simplicial arrangements: random 7–8
    planes in R^4, all cones of B_4 and D_4, and samples of H_4. None of
    these is fully tested.
  - (2) A cone and g ∈ Stab(V) with χ_H(g) ≠ det(g) χ_Q(g).
  - (3) For the combinatorial generalization, a T-convex set of a
    non-realizable oriented matroid where Λ̄ is not a wedge of spheres.
    This would refute the §3 conjecture, not G\*.

**2. (b) Hopf monoids: write up, do not research further on its own.**
Theorems 6–8 settle [Glob]'s filtration and local-PBW conjectures and give
the P-graded bracket. They belong in a paper as the algebraic face of (a)'s
braid case. Further work in (b) should go through (b1), Aguiar–Mahajan
bimonoids for arbitrary arrangements, which is (a) again. The cooperad (b2)
is a side question.

**3. (c) Lattices: no independent program.** Keep only the oriented-matroid
version of Theorems 1–2, as a remark or a later generalization, and the
fixed-point Möbius formula for reflection-group stabilizers of cones, as a
sub-problem of (a)'s equivariant side.

**Publication shape.** "Lie modules of cones of hyperplane arrangements". The
main theorem would be G\*: H̃(Λ̄(V)) ≅ det ⊗ (Lie[A]|_V)^*. Proven parts:
Theorems 1–2, Prop. 3, the pointed, full and braid cases, and poset JKS with
Klyachko's model as the type-A corollary. The braid-arrangement chapter
would carry Theorems 6–8.

## 6. Status table

| Claim | Status | Depends on |
|---|---|---|
| Lemma 0.1, 0.2 | PROVEN | elementary convexity |
| Theorem 1 (cone wedge) | PROVEN | BWW poset fiber theorem; regular CW facts; Hall (CITED) |
| Cor. 1.1 / Theorem 2 (cone Zaslavsky) | PROVEN; COMPUTED `[zas]` | Thm 2: regular CW facts only |
| Lemma 1.3 (component formula, Foata) | PROVEN; COMPUTED `[foata]` n ≤ 6 | elementary |
| Cor. 1.4 (J–S reproved) | PROVEN | Thm 1, Thm 2, Lemma 1.3, [Cone, Prop. 2.2] |
| Prop. 3(a) | PROVEN | [Cone, Lemma L] |
| Prop. 3(b), q ≤ m | PROVEN; COMPUTED `[brown]` | Brown (CITED) |
| Prop. 3(c) | PROVEN given Saliola (property not re-checked) | Saliola (CITED) |
| Conjecture G\* numerical | CONJECTURED; PROVEN for pointed / full / braid; COMPUTED `[q=m]` 6,826 cones | — |
| Conjecture G\* equivariant | CONJECTURED; PROVEN for braid given Prop. Φ; COMPUTED `[eq]` (new) | — |
| Lemma 2.1, Theorem 7 | PROVEN; COMPUTED `[prim]` | Thm S(b), Ree, ψ_P, Thm main |
| Theorem 8 (filtration) | PROVEN | CMM–PBW for species (CITED) for the equality |
| Theorem 6 (local PBW) | PROVEN; COMPUTED `[pbw]`, `[pbw-eq]` | Thm S(b), Lemma 1.3, ψ_P, Thm main |
| (b1), (b2), OM version, comodernism | CONJECTURED | — |

Not re-checked against sources: BWW Thm 1.1 (statement as recalled),
Brown's simple modules, Saliola's idempotent property, AM Thm 14.32, and the
Malvenuto–Reutenauer product convention. Not read: Margolis–Saliola–Steinberg
arXiv:1508.05446, Dorpalen-Barry–Proudfoot–Wang, Baclawski–Björner 1981.
Read (arXiv text, grep): Dorpalen-Barry–Kim–Reiner arXiv:1906.00036.

## Reproduce

From `compute/` (plain Python 3; it imports `cone_lie.py` and
`poset_jks_check.py`):

    python3 general_theory.py > output/general_theory.txt   # ~25 s, ALL CHECKS PASSED, exit 0
    python3 general_theory.py --quick                        # ~1 s: no A4/D4, posets n <= 4
    python3 -m unittest test_general_theory                  # < 1 s, includes the negative controls

The archived output is `compute/output/general_theory.txt`.
