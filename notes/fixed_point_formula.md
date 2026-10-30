# The fixed-point character formula for cones of arrangements

This note answers the first open problem of `notes/general_theory.md` §5
("[GT]"). That problem asks for a formula for μ(Λ(V)^g), g ∈ Stab_W(V), the
general analogue of [Thm, eq. closed] (`notes/poset_jks_theorem.tex`). By
Theorem G\* of [GT, §1.5], this Möbius number is the character of
H̃_{d−2}(Λ̄(V)) ≅ det ⊗ (Lie[A]|_V)^\*.

The answer is a closed formula (Theorem CF) over the g-stable flats inside
the lineality space. It comes from an equivariant form of the cone
Zaslavsky theorem (Theorem EZ), which is the character form of a PBW
decomposition of C[V]. Both are proved for **every** finite real central
arrangement and **every** finite-order linear symmetry g of A with gV = V.
g does not have to lie in a reflection group.

Notation and conventions are those of [GT, §0]. In particular:
- flats are ordered by inclusion, with bottom 0 and top R^d;
- L = lin V;
- V_X is the localization of V at a flat X ⊆ L (Lemma 0.1(c) of [GT]);
- m(V) = (−1)^d μ(Λ(V)).

Tags: **PROVEN** (full proof here, inputs named), **COMPUTED** (checked by
`compute/fixed_point_formula.py`, see Reproduce), **CITED**, **CONJECTURED**,
**OPEN**.

## Verdict

| # | Claim | Status | Inputs |
|---|---|---|---|
| EZ | #V^g = Σ_{X ⊆ L, gX = X} χ_{V_X}(ḡ) (equivariant cone Zaslavsky) | **PROVEN**; COMPUTED on all 7,200 pairs (V, g) | cell facts of [GT, §0], Hopf trace formula, [GT] Lemmas 0.1–0.2 |
| EZ′ | C[V] ≅ ⊕_{[X]} Ind_{G_X}^{G} Lie(V_X) as G = Stab(V)-modules (cone PBW) | **PROVEN** given [GT] Thm 1; with G\* the Lie(V_X) are (Γ+Lune)/Lune | EZ, Theorem 1, Theorem G\* |
| CF | χ_V(g) = Σ_{Y ∈ 𝓛^g} μ_{𝓛^g}(0, Y) · #{chambers K of A_Y in \|V\| with gK = K} | **PROVEN**; COMPUTED on all 7,200 pairs | EZ, Lemma F |
| F | fixed chambers of A_Y ↔ chambers of A_Y restricted to Fix(g) | **PROVEN** | convexity |
| P | pointed V: χ_V(g) = #V^g; for g ∈ W∖1, μ(Λ(V)^g) = 0 and H̃_{d−2}(Λ̄(V)) is a free C[Stab_W(V)]-module | **PROVEN** | CF, [GT] Thm 1 |
| Full | V = all chambers: χ_A(g) = Σ_{Y ∈ L(A)^g} μ(0, Y) · #chambers(A_Y\|_{Fix g}) | **PROVEN** | CF, F |
| V | if one hyperplane of A contains both L and Fix(g), then μ(Λ(V)^g) = 0 | **PROVEN**; COMPUTED. Sufficient, not necessary | CF, F |
| W | Weisner recursion: if Fix(g) is a flat and g ≠ 1, Σ_{X ∈ 𝓛^g, X ∩ Fix g = 0} χ_{V_X}(ḡ) = 0 | **PROVEN**; COMPUTED. The flat hypothesis is needed (fails on 382 of 1,336 tested pairs without it) | Weisner, averaging |
| Braid | CF for C_P is a formula over Π(components)^g; it agrees with [Thm, eq. closed] | **PROVEN** (both sides proven); COMPUTED for every poset with n ≤ 6 and every g ∈ Aut(P) | CF, [Thm] |
| BB | Baclawski–Björner 1981 as prior art | **inaccessible** (full text behind a paywall); its reported content is about complements, not fixed-point Möbius formulas | §6 |
| — | an exact criterion for χ_V(g) ≢ 0 (cf. "all cycles of equal length" for braid) | **OPEN**; data in §5 | — |

"7,200 pairs" means every top-cone V, up to W-conjugacy, and every element
of its stabilizer, for A_2–A_5, B_2–B_4, D_4 and H_3: 4,661 pairs with
g ∈ W and 2,539 with g in the larger symmetry group G ⊋ W (−W for type A,
W(F_4) for D_4). The pairs come from 215,725 top-cones.

---

## 1. Setting

Throughout:
- A is a finite central essential arrangement in R^d, with d ≥ 1;
- V is a top-cone of A, and L = lin V;
- g is a linear automorphism of R^d of finite order, with gA = A and
  gV = V.

The reflection case is g ∈ Stab_W(V) for the reflection group W of A. Write:
- Fix(g) = ker(g − 1);
- 𝓛 = {flats Y of A with Y ⊆ L}, ordered by inclusion, with bottom 0;
- 𝓛^g = {Y ∈ 𝓛 : gY = Y}. Every Y ∈ 𝓛 lies in Λ(V) ([GT, Lemma 0.1(b)]);
- for a g-stable flat X, ḡ for the map induced on R^d/X, and
  det(g) = det(g|_X) · det(ḡ).

Since ⟨g⟩ is finite, fix a ⟨g⟩-invariant inner product and let S be its unit
sphere. The cell facts of [GT, §0] hold for any Euclidean structure, so the
faces F ≠ O of A give a regular CW structure on S, and g acts on S by
cellular homeomorphisms.

**Definition.** For any (A, V, g) as above,

  χ_V(g) := (−1)^d det(g) μ(Λ(V)^g),

where Λ(V)^g is the subposet of g-stable flats, with bottom 0 and top R^d.
For rank 0, Λ is a point and χ = 1.

**Why χ_V is the character we want (PROVEN, given [GT] Theorem 1 and
Hall/Hopf as in [Thm, Lemma homchar]).** The argument of [Thm, Lemma
homchar] applies verbatim to Λ(V), since Λ(V)^g contains 0 and R^d and Theorem 1
concentrates the homology in degree d − 2. It gives, for d ≥ 2,

  tr(g | H̃_{d−2}(Λ̄(V))) = (−1)^d μ(Λ(V)^g).

So χ_V is the character of Lie(V) := det ⊗ H̃_{d−2}(Λ̄(V)). For d = 1 the
proper part is empty, H̃_{−1} = C, and the same formula holds.

By Theorem G\* of [GT], Lie(V) ≅ (Γ_V + Lune)/Lune. G\* is stated there
for Stab_W(V). The proof outline in [GT, §1.5] uses only
g·ρ_C = det(g) ρ_{gC} for linear g, so we read it as holding for any linear
symmetry; that reading has not been re-audited. In the braid case χ_{C_P}(g) is the left side
of [Thm, eq. closed]: there det = sgn and d = n − 1, so
(−1)^d = (−1)^{n−3}.

**Lemma A (equivariant localization; PROVEN).** Let X ∈ 𝓛 be g-stable.
- ḡ preserves A_X/X and V_X.
- Y ↦ Y/X is a g-equivariant isomorphism [X, R^d]_{Λ(V)} → Λ(V_X).
- Hence [X, R^d]_{Λ(V)^g} ≅ Λ(V_X)^ḡ, and

  μ_{Λ(V)^g}(X, R^d) = μ(Λ(V_X)^ḡ).

*Proof.* g permutes the hyperplanes containing X, and it maps the cone
|V| = X + |V| to itself, so ḡ preserves A_X/X and the image V_X. The map of
[GT, Lemma 0.1(c)] is Y ↦ Y/X, which commutes with g. The g-fixed elements
of an interval are the interval of the fixed subposet. ∎

---

## 2. Theorem EZ: the equivariant cone Zaslavsky theorem

**Theorem EZ (PROVEN; inputs: the cell facts of [GT, §0], the Hopf trace
formula, and [GT] Lemmas 0.1–0.2).** For every (A, V, g) as in §1,

  #V^g = Σ_{X ∈ 𝓛^g} χ_{V_X}(ḡ),                                   (EZ)

where #V^g is the number of chambers C ∈ V with gC = C. The term X = R^d
occurs only when V is all chambers, and it equals 1.

At g = 1 this is [GT, Theorem 2]. For g ∈ W ∖ 1 the left side is 0, since W
acts freely on chambers.

*Proof.*

*Step 1: a Lefschetz count on each flat.* Let Y ∈ Λ(V)^g. Put
K_Y = |V| ∩ Y ∩ S. It is a subcomplex whose cells are F ∩ S, for F ≠ O a
face of V with F ⊆ Y. Let C̃_•(K_Y) be its augmented cellular chain complex,
with the face O in degree −1. g maps K_Y to itself and acts on C̃_• by
g·[F] = ε_g(F)[gF], where ε_g(F) = ±1 is the orientation sign.

*Claim:* if gF = F, then ε_g(F) = det(g|_{span F}).
- Average a linear form that is positive on F̄ ∖ 0 over ⟨g⟩. This gives a
  g-invariant linear form ℓ that is still positive on F̄ ∖ 0.
- Radial projection identifies the closed cell F̄ ∩ S with the compact
  convex set P = F̄ ∩ {ℓ = 1}, g-equivariantly.
- On P, g acts as the restriction of the linear map g|_{span F}. It fixes
  the point p ∈ relint P obtained by averaging any interior point.
- span F = R·p ⊕ (ker ℓ ∩ span F) is a g-stable splitting, and g is 1 on
  the first summand. So the local degree of g on P at p is
  sign det(g|_{ker ℓ ∩ span F}) = det(g|_{span F}). (g has finite order, so
  this determinant is ±1.)

Define

  f_g(Y) := Σ_{F ⊆ |V| ∩ Y, gF = F} (−1)^{dim F} det(g|_{span F}).

Here F runs over the faces of V, including O, with det = 1 on the zero
space. A cell F ∩ S has dimension i = dim F − 1, and off-diagonal permutation
entries contribute no trace. So

  f_g(Y) = −Σ_{i ≥ −1} (−1)^i tr(g | C̃_i(K_Y)) = −Σ_i (−1)^i tr(g | H̃_i(K_Y)),

by the Hopf trace formula for the chain map g (an algebraic identity for an
endomorphism of a finite-dimensional chain complex; Munkres, *Elements of
Algebraic Topology*, Thm 22.1, CITED as in [Thm, input (C)]). The
identification of cellular with singular homology is natural for cellular
maps.

Now evaluate the homology. Since Y ∈ Λ(V), dim(|V| ∩ Y) = dim Y
([GT, Lemma 0.1(a)]). By [GT, Lemma 0.2], and as in Step 2 of the proof of
[GT, Theorem 1] (|V| ∩ Y = Y iff Y ⊆ L), there are three cases.
- Y = 0. K_Y = ∅ and H̃_{−1} = C, with trivial action. So f_g(0) = 1.
- Y ≠ 0, Y ⊄ L. K_Y is contractible and H̃ = 0. So f_g(Y) = 0.
- Y ≠ 0, Y ⊆ L. K_Y is the unit sphere of Y, of dimension k − 1 where
  k = dim Y, and g acts on H̃_{k−1} by its degree det(g|_Y). So
  f_g(Y) = −(−1)^{k−1} det(g|_Y).

In all cases

  f_g(Y) = [Y ⊆ L] · (−1)^{dim Y} det(g|_Y).                         (2.1)

*Step 2: Möbius inversion on Λ(V)^g.*
- If F is a g-stable face of V with F ⊆ Y, then X = span F is g-stable,
  lies in Λ(V) ([GT, Lemma 0.1(a)]), and X ⊆ Y.
- So f_g(Y) = Σ_{X ∈ Λ(V)^g, X ⊆ Y} h_g(X), where

    h_g(X) = (−1)^{dim X} det(g|_X) · #{faces F of V : span F = X, gF = F}.

- Möbius inversion in the finite poset Λ(V)^g, evaluated at Y = R^d, gives
  h_g(R^d) = Σ_{X ∈ Λ(V)^g} μ_{Λ(V)^g}(X, R^d) f_g(X).
- h_g(R^d) = (−1)^d det(g) #V^g.
- By (2.1), only X ∈ 𝓛^g contribute. Hence

  (−1)^d det(g) #V^g = Σ_{X ∈ 𝓛^g} (−1)^{dim X} det(g|_X) μ_{Λ(V)^g}(X, R^d).     (2.2)

*Step 3: rewrite.*
- By Lemma A, μ_{Λ(V)^g}(X, R^d) = μ(Λ(V_X)^ḡ).
- By definition, μ(Λ(V_X)^ḡ) = (−1)^{d − dim X} det(ḡ) χ_{V_X}(ḡ).
- So the X-term of (2.2) is (−1)^d det(g|_X) det(ḡ) χ_{V_X}(ḡ) =
  (−1)^d det(g) χ_{V_X}(ḡ).
- Dividing by (−1)^d det(g) gives (EZ). ∎

**Remark.** Step 1 is the proof of [GT, Theorem 2], with Euler
characteristics replaced by Lefschetz numbers. The only new inputs are the
orientation sign det(g|_{span F}) and the degree det(g|_Y) on the sphere of
a lineality flat. The det(ḡ) in χ_{V_X} is forced. Dropping it breaks (EZ)
on cones of B_3 (test `test_ez_needs_det_twist`).

**Corollary EZ′ (cone PBW; PROVEN given [GT] Theorem 1).** Let G be a
finite group of linear symmetries of A with GV = V, and G_X the setwise
stabilizer of X in G. For a flat X ∈ 𝓛 of codimension c, let Lie(V_X) be the
G_X-module

- det_{R^d/X} ⊗ H̃_{c−2}(Λ̄(V_X); C) if c ≥ 1 (for c = 1 this is
  det_{R^d/X});
- the trivial module if c = 0.

Then, as G-modules,

  C[V] ≅ ⊕_{[X] ∈ 𝓛/G} Ind_{G_X}^{G} Lie(V_X).

Given Theorem G\* for each V_X, Lie(V_X) ≅ (Γ_{V_X} + Lune)/Lune, which
makes this a PBW decomposition of the chamber space of V into restricted Lie
modules.

*Proof.* By Theorem 1 for V_X and the homchar argument of §1, the character
of Lie(V_X) at ḡ is χ_{V_X}(ḡ). The induced character formula gives
(Ind_{G_X}^G Lie(V_X))(g) = Σ_{X′ ∈ G·X, gX′ = X′} χ_{V_{X′}}(ḡ), with the
summands transported along G. Summing over orbits gives the right side of
(EZ). The left side is the permutation character of C[V]. Representations
over C with equal characters are isomorphic. ∎

In the braid case, 𝓛 ≅ Π(components)^op and V_X = Π_B C_{P|_B}, so EZ′ is the
local PBW theorem [GT, Theorem 6] (C[Lin P] ≅ ⊕_σ ⊗_B Lie(P|_B)) as an
Aut(P)-module statement. For V = all chambers and G = W, EZ′ decomposes the
regular representation of W over the W-orbits of flats. For W = S_n this is
the classical PBW decomposition of C[S_n] into higher Lie modules. We did
not search for the general-W case in the literature (§6).

---

## 3. Theorem CF: the closed formula

**Lemma F (fixed chambers; PROVEN).** Let B be a central arrangement in a
real space U, and h a finite-order linear map with hB = B.
- If some H ∈ B contains Fix(h), no chamber of B is h-fixed.
- Otherwise K ↦ K ∩ Fix(h) is a bijection from the h-fixed chambers of B
  onto the chambers of the restriction B|_{Fix h} = {H ∩ Fix(h) : H ∈ B} in
  Fix(h).

*Proof.*
- If hK = K, averaging a point of K over ⟨h⟩ gives a point of
  K ∩ Fix(h), and that point lies on no H ∈ B. This proves the first claim.
  It also shows K ∩ Fix(h) is a nonempty set of points of Fix(h) with K's
  sign vector, that is, a chamber of B|_{Fix h}.
- Conversely, a chamber of B|_{Fix h} has a sign vector with no zeros. That
  sign vector defines a chamber K of B, and K contains h-fixed points.
  Hence hK ∩ K ≠ ∅, so hK = K.
- The two maps are inverse, since a chamber is determined by its sign
  vector. ∎

**Theorem CF (PROVEN; same inputs as EZ).** For every (A, V, g) as in §1,

  χ_V(g) = Σ_{Y ∈ 𝓛^g} μ_{𝓛^g}(0, Y) · c(Y, g),                        (CF)

  c(Y, g) := #{chambers K of the localization A_Y with K ⊆ |V| and gK = K}.

Equivalently, μ(Λ(V)^g) = (−1)^d det(g) Σ_{Y ∈ 𝓛^g} μ_{𝓛^g}(0, Y) c(Y, g).
By Lemma F, c(Y, g) is 0 if some hyperplane through Y contains Fix(g).
Otherwise it is the number of chambers of the restricted arrangement
A_Y|_{Fix g} that lie in |V| ∩ Fix(g).

Here A_Y = {H ∈ A : H ⊇ Y}, and its chambers are open cones in R^d. Since
Y ⊆ L, every hyperplane in S_max(V) contains Y, so |V| is a union of closed
chambers of A_Y.

*Proof.*
- Fix Y ∈ 𝓛^g and apply (EZ) to (A_Y/Y, V_Y, ḡ). This is a top-cone of an
  essential arrangement in R^d/Y with a finite-order symmetry.
- lin V_Y = L/Y, because |V| + Y = |V|.
- The flats of A_Y/Y inside L/Y are the Z/Y with Z a flat of A and
  Y ⊆ Z ⊆ L: a flat Z ⊇ Y of A is the intersection of hyperplanes that all
  contain Y. The ḡ-stable ones correspond to the g-stable ones.
- (V_Y)_{Z/Y} = V_Z, compatibly with the induced maps on
  (R^d/Y)/(Z/Y) = R^d/Z. Both are the image of |V| in R^d/Z, for the
  arrangement A_Z/Z. So χ_{(V_Y)_{Z/Y}} = χ_{V_Z}.
- The chambers of V_Y are the images of the chambers of A_Y in |V|. Hence
  (EZ) for V_Y reads

    c(Y, g) = Σ_{Z ∈ 𝓛^g, Z ⊇ Y} χ_{V_Z}(ḡ).

- Möbius inversion on the finite poset 𝓛^g, evaluated at the bottom
  element 0, gives χ_V(g) = χ_{V_0}(g) = Σ_Y μ_{𝓛^g}(0, Y) c(Y, g). ∎

**What the formula buys.** It replaces the Möbius function of Λ(V)^g, the
whole support lattice of the cone, by that of 𝓛^g. 𝓛^g is the fixed lattice
of the intersection lattice of the restriction A^L, a geometric lattice that
depends only on L and not on the shape of V. The shape of V enters only
through the counts c(Y, g). These are fixed-chamber counts of localizations,
or chamber counts of the fixed subarrangement A_Y|_{Fix g} inside V. This
covers two of the three candidate shapes named in the work item:
- an expression in the g-orbit structure of the lineality flats;
- a formula via the fixed subarrangement restricted to V.

The third candidate, the Weisner form, is Proposition W in §4.

At g = 1, CF is [GT, Prop. 3(b)]: Σ_{X ⊆ L} μ(0, X) c_X = m(V), Brown's
bottom multiplicity. So CF is the equivariant version of that formula, and
EZ is the equivariant version of Theorem 2.

### 3.1 Special cases

**Corollary P (pointed cones; PROVEN).** If V is pointed (L = 0), then
χ_V(g) = #V^g. For g ∈ W ∖ 1, μ(Λ(V)^g) = 0. Hence (given [GT] Thm 1)
Lie(V), and therefore H̃_{d−2}(Λ̄(V)), is a free C[Stab_W(V)]-module of rank
#V / |Stab_W(V)|.

*Proof.* 𝓛^g = {0}, and c(0, g) = #V^g. So Lie(V) has the permutation
character of C[V], and Lie(V) ≅ C[V]. W acts freely on chambers, so C[V] is
a free C[Stab_W(V)]-module, and so is H̃_{d−2}(Λ̄(V)) ≅ det ⊗ C[V]. ∎

In the braid case, pointed means P connected, and this is [Thm,
Cor. connected].

**Corollary Full (V = all chambers; PROVEN).** Here L = R^d and
𝓛 = Λ(V) = L(A). So

  (−1)^d det(g) μ(L(A)^g) = Σ_{Y ∈ L(A)^g} μ_{L(A)^g}(0, Y) · #{chambers of A_Y|_{Fix g}},

where the Y-term is 0 when a hyperplane through Y contains Fix(g). The
term Y = R^d is μ_{L(A)^g}(0, R^d) · 1. Both sides contain μ(L(A)^g). For
g ∈ W with g ≠ 1 the identity therefore expresses μ(L(A)^g) through the
smaller intervals [0, Y], Y ≠ R^d, as long as (−1)^d det(g) ≠ 1.

**Corollary V (vanishing; PROVEN).** If some hyperplane H ∈ A contains both
L and Fix(g), then χ_V(g) = 0, that is, μ(Λ(V)^g) = 0.

*Proof.* For every Y ∈ 𝓛^g we have H ⊇ L ⊇ Y, so H ∈ A_Y, and H ⊇ Fix(g).
By Lemma F, c(Y, g) = 0. ∎

For g ∈ W ∖ 1 with V pointed, Fix(g) ≠ R^d is a flat (Steinberg), so it lies
in a hyperplane, and Corollary V recovers Corollary P. In the braid case
the hypothesis says that some g-cycle meets some component of P in two
points. Corollary V is sufficient but not necessary for vanishing (§5).

**Corollary CF-braid (PROVEN).** Let P be a poset on [n], K its set of
components, and g ∈ Aut(P). Then

  sgn(g)(−1)^{n−3} μ(OP(P)^g) = Σ_{σ ∈ Π(K)^g} μ_{Π(K)^g}(σ, 1̂) · Π_{[B] ∈ σ/⟨g⟩} [g^{|[B]|} fixes B pointwise] · |Lin(P|_B)|.

- Π(K)^g is the g-stable partitions of the component set, ordered by
  refinement.
- The product runs over the ⟨g⟩-orbits [B] of blocks, with one block B
  chosen per orbit.
- |[B]| is the length of the orbit, and B is read as a subset of [n].

*Proof.* Apply CF to V = C_P, essentialized in R^n/R·1 (d = n − 1,
det = sgn).
- By [GT, §1.3], 𝓛 is the partitions σ of K, with Y_σ ⊆ Y_τ iff σ is
  coarser than τ. So 0 = Y_{1̂} and μ_{𝓛^g}(0, Y_σ) = μ_{Π(K)^g}(σ, 1̂).
- A chamber of A_{Y_σ} in |C_P| is a tuple of linear extensions, one of
  each P|_B, B ∈ σ.
- g fixes such a tuple iff the stabilizer ⟨g^{|[B]|}⟩ of each block B fixes
  the linear extension of B. An automorphism of a finite set that preserves
  a total order is the identity, so this needs g^{|[B]|}|_B = 1. In that
  case the extension on one block of each orbit can be chosen freely and
  determines the others. ∎

At g = 1 this is [Thm, Cor. eC], since μ_Π(σ, 1̂) = (−1)^{|σ|−1}(|σ|−1)!.

CF-braid and [Thm, eq. closed] are both proven formulas for the same number,
so they agree. COMPUTED (independently of the arrangement code, from the
order-preserving partitions, Π(K)^g and linear extensions): for every poset
P with n = 3, 4, 5, 6, up to relabelling, and every g ∈ Aut(P), we have
μ(Λ(C_P)^g) = μ(OP(P)^g), [Thm, eq. closed] holds, and CF-braid holds.
That is 2,456 pairs: 12, 59, 325 and 2,060 for n = 3, 4, 5, 6. This is
the requested positive control. Eq. closed itself has the extra structure
of the braid case: a single term μ(o) and e_C on one block. We have no
direct combinatorial derivation of it from CF-braid.

---

## 4. Proposition W: the Weisner recursion

This is the "Weisner / complement formula" candidate. It generalizes the
recursion (W) in the proof of [Thm, Prop. Mside].

**Lemma B (PROVEN).** Let X ∈ Λ(V) be g-stable.
- (a) X ∩ Fix(g) is a subspace of X that meets the relative interior of
  X ∩ |V|. If a ∈ Λ(V)^g contains Fix(g) and is a flat, then
  X ∩ a ∈ Λ(V)^g.
- (b) If X ∩ Fix(g) = 0, then X ⊆ L.

*Proof.*
- (a) X ∩ |V| is a convex cone of dimension dim X, mapped to itself by g.
  Average a point of its relative interior (relative to X) over ⟨g⟩. The
  result p̄ lies in that relative interior and in Fix(g). Then p̄ ∈ X ∩ a,
  and a neighbourhood of p̄ in X ∩ a lies in |V|. So the flat X ∩ a meets
  |V| in full dimension, and X ∩ a ∈ Λ(V) by [GT, Lemma 0.1(a)].
- (b) Now p̄ = 0 lies in the relative interior of the cone X ∩ |V|, so the
  cone is all of X. Thus X ⊆ |V| ∩ −|V| = L. ∎

**Lemma C (PROVEN).** Λ(V) is a lattice, and Λ(V)^g is a lattice.

*Proof.*
- For faces F, G of V, the Tits product FG is the face containing f + εg
  for f ∈ F, g ∈ G and small ε > 0. It lies in |V| by convexity.
- Its zero set is Z(F) ∩ Z(G), so span FG = span F ∨ span G in L(A). Hence
  Λ(V) is closed under the join of L(A). It contains 0, so it is a lattice.
- g acts by lattice automorphisms, so Λ(V)^g is join-closed and contains 0
  and R^d. So it is a lattice too. ∎

**Proposition W (PROVEN).** Assume g ≠ 1 and Fix(g) is a flat of A. This
holds for every g ∈ W, by Steinberg's theorem: Fix(g) is the intersection of
the reflecting hyperplanes containing it. Then

  Σ_{X ∈ 𝓛^g, X ∩ Fix(g) = 0} χ_{V_X}(ḡ) = 0,

that is,

  μ(Λ(V)^g) = −Σ_{0 ≠ X ∈ 𝓛^g, X ∩ Fix(g) = 0} μ(Λ(V_X)^ḡ).

*Proof.*
- a := Fix(g) is a g-stable flat, and it lies in Λ(V) by Lemma B(a) with
  X = R^d. Also a ≠ R^d, since g ≠ 1.
- The dual Weisner theorem holds in the finite lattice M = Λ(V)^g
  (Lemma C): for a ≠ 1̂, Σ_{x ∧ a = 0̂} μ(x, 1̂) = 0. This is [Thm, Lemma
  weisner] applied to M^op.
- By Lemma B(a), the meet in M of X and a is X ∩ a.
- By Lemma B(b), X ∩ a = 0 forces X ∈ 𝓛^g. Conversely, every X ∈ 𝓛^g with
  X ∩ a = 0 qualifies.
- Lemma A converts μ_M(X, R^d) into μ(Λ(V_X)^ḡ).
- For the χ form, note det(g|_X) = (−1)^{dim X − dim X^g} for a finite-order
  real map. So X^g = 0 gives (−1)^{dim X} det(g|_X) = 1, and the sign
  bookkeeping of EZ Step 3 applies term by term. ∎

**Braid case.** X ∩ Fix(g) = 0 is exactly x ∈ X(P, g) of [Thm, Lemma
lattice(iv)], so Proposition W is (W) there. In the braid case the
localizations V_X are products of cones permuted cyclically by g, and a
second Möbius inversion closes the recursion to eq. closed. In general V_X
is not such a product, and ḡ is not in the reflection group W_X of A_X: it
lies in N_W(X) and may fix a chamber of A_X. So the recursion leaves the
class "reflection group element". That is why the general closed form is
obtained through EZ, which holds for all finite-order symmetries, rather
than through Weisner.

**The flat hypothesis is needed (COMPUTED).** For symmetries g ∉ W whose
fixed space is not a flat (−w in type A, triality-type elements for D_4), the
sum in Proposition W is nonzero on 382 of 1,336 tested pairs:
- A_2: 5 of 5;
- A_3: 11 of 20;
- A_4: 36 of 108;
- A_5: 80 of 561;
- D_4: 250 of 642.

The same proof, with a = cl(Fix g) (the smallest flat containing Fix(g)),
gives a valid identity whenever cl(Fix g) ≠ R^d, because Lemma B covers any
flat a ⊇ Fix(g). Its index set is {X ∈ 𝓛^g : X ∩ cl(Fix g) = 0}, which is
smaller than {X ∈ 𝓛^g : X^g = 0}. This variant is PROVEN by that remark but
was not computed. EZ and CF need no such hypothesis.

---

## 5. Data (COMPUTED)

`compute/fixed_point_formula.py`; exact arithmetic (rationals, and Q(√5) for
H_3); no imports from the other scripts.

| type | top-cones | W-orbits | pairs (V, g), g ∈ W | g ≠ 1 with χ ≠ 0 | zero by Cor. V | zero otherwise | pairs with g ∈ G∖W |
|---|---|---|---|---|---|---|---|
| A_2 | 19 | 5 | 12 | 2 | 2 | 3 | 8 |
| A_3 | 219 | 16 | 59 | 4 | 18 | 21 | 37 |
| A_4 | 4,231 | 63 | 325 | 24 | 134 | 104 | 153 |
| A_5 | 130,023 | 318 | 2,060 | 183 | 962 | 597 | 922 |
| B_2 | 33 | 7 | 18 | 9 | 2 | 0 | — |
| B_3 | 941 | 35 | 134 | 47 | 36 | 16 | — |
| B_4 | 60,201 | 266 | 1,224 | 378 | 436 | 144 | — |
| D_4 | 12,313 | 110 | 531 | 172 | 185 | 64 | 1,419 |
| H_3 | 7,745 | 93 | 298 | 38 | 79 | 88 | — |

On every row:
- [EZ], [CF] and [VC] hold on every pair, for g ∈ W and for g ∈ G ∖ W;
- [WR] holds on every pair where Fix(g) is a flat;
- χ_V restricted to Stab_W(V) has nonnegative integer multiplicities of the
  trivial and det characters on every cone, a consistency check that χ_V is
  a character.

Positive controls:
- the top-cone counts 19, 219, 4,231, 33 and 941 match [GT];
- the W-orbit counts 5, 16, 63 and 318 for A_{n−1} are the numbers of
  unlabelled posets on n = 3, …, 6 points (OEIS A000112);
- on all chambers of A_3, χ is the Lie_4 character (6, −2, 0, 0, 0 at 1,
  (12)(34), (12), (123), (1234));
- the braid control of §3.1.

The cones of D_4 are now covered in full; [GT, §1.5] used 150 sampled cones.

Negative controls (tests):
- [CF] fails on some cone of B_3 if c(Y, g) counts all chambers of A_Y in
  |V| instead of the g-fixed ones;
- [EZ] fails without det(ḡ);
- [WR] fails without the flat hypothesis.

**When does χ_V(g) vanish? (OPEN.)** Corollary V explains only part of the
zeros. In the braid case the exact answer is known, [FPM (a)] and eq.
closed: μ(OP(P)^g) = 0 unless g has all cycles of one length d, and ⟨g⟩
acts freely on the components (F(P, g) ≠ ∅). Below we list the elements of
W on which χ_V(g) = 0 for **every** cone. They are grouped by the type
(dim Fix(g^k))_{k=1..o}, where o is the order of g. The type determines the
characteristic polynomial up to Galois conjugacy; in H_3 it does not
separate the two classes of order 5 or the two of order 10.

| type | classes on which χ_V ≡ 0 for all V |
|---|---|
| A_4 | all except 1 and the 5-cycle |
| A_5 | all except 1, (12)(34)(56), (123)(456) and the 6-cycle |
| B_2 | none |
| B_3 | orders 3 and 6 with Fix(g) of dim 1 resp. 0 |
| B_4 | four types, all of order 3 or 6: [2,2,4], [0,2,0,2,0,4], [1,2,1,2,1,4], [1,2,3,2,1,4] |
| D_4 | (dim Fix) [2,2,4] (order 3) and [0,2,0,2,0,4] (order 6) |
| H_3 | every element of order 3, 5, 6 or 10 |

The type A rows (and A_2, A_3 in the output) are exactly what eq. closed
predicts. g is nonvanishing on some cone iff all its cycles have one length
o with μ(o) ≠ 0, and the antichain realizes every such class. For example,
the 4-cycle of S_4 vanishes because μ(4) = 0. In types B, D and H, reflections and other
non-regular elements do not vanish identically. So the naive guess
"χ_V(g) ≢ 0 only for Springer-regular g" is **false** for proper cones:
in B_2 every class is nonvanishing on some cone.

A sharp general vanishing criterion would generalize [FPM (a)]. It remains
open. Natural candidates are a Crapo complementation argument in 𝓛^g (as
in [FPM]), or Hanlon-type vanishing of μ of fixed geometric lattices.

---

## 6. Prior art

- **Baclawski–Björner, *Fixed points and complements in finite lattices*,
  J. Combin. Theory Ser. A 30 (1981) 335–338.** The full text was **not
  accessible** (ScienceDirect returned HTTP 403). As reported by a search
  summary of its MathSciNet / AMS record (MR 618539; not read by us), its
  result is a non-evasiveness (hence collapsibility) statement for the
  proper part of a finite lattice with a set of elements removed that
  contains all complements of an element x. That is a homotopy
  strengthening of Crapo-type complementation. Nothing in the record
  suggests a formula for μ(L^g) of a group-fixed sublattice, and we could
  not check the text. Its bearing on this note is at most on the OPEN
  vanishing question of §5, via complements in 𝓛^g or Λ(V)^g. Their 1979
  paper (*Fixed points in partially ordered sets*, Adv. Math. 31, 263–287)
  concerns the fixed-point property of order-preserving self-maps, a
  different sense of "fixed point".
- **Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96
  (1981)** (CITED from memory, not re-checked) computes μ(Π_n^σ). By
  Corollary CF-braid, Π(K)^g is the lattice 𝓛^g of the braid case, so
  Hanlon's formula evaluates the coefficients in CF-braid for P an
  antichain.
- **V = all chambers, g ∈ W.** EZ′ is a decomposition of the regular
  representation of W indexed by flats. For S_n this is classical (PBW for
  higher Lie modules). For general W, related decompositions of C[W] into
  modules induced from normalizers of parabolics exist in the literature on
  the Lehrer–Solomon conjecture and Solomon's descent algebra
  (Douglass–Pfeiffer–Röhrle; NOT CHECKED; named from memory). We do not
  claim novelty for the case V = all chambers.
- **Proper cones.** EZ, CF, Corollaries P and V and Proposition W for
  proper cones were not found. No systematic search was made beyond the
  above. A prior-art check like [NovGT] is recommended before these are
  stated as new.

## 7. Corrections and pointers for existing notes (not applied)

Per the standing constraints, no existing note was edited. Suggested changes:
- [GT] §1.5 (last paragraph), §3 ("Fixed-point lattices") and §5 ("First
  open problem"): the fixed-point formula is now Theorem CF here, with
  EZ/EZ′ as its equivariant Zaslavsky/PBW form. The equivariant character of
  H̃_{d−2}(Λ̄(V)) is given for all finite-order symmetries, not only W.
- [GT] §3 and §6: "Baclawski–Björner 1981, still unread" should read "full
  text inaccessible; per its MR record a complementation/non-evasiveness
  result, not a fixed-point Möbius formula" (§6 above).
- [GT] §1.5 COMPUTED `[eq]`: D_4 is now covered in full (12,313 cones, 110
  W-orbits) for the Möbius side.
- [GT] §1.5 says the equivariant form of Theorem G\* is for Stab_W(V). The
  proof there uses only linearity of g, so the statement holds for any
  linear symmetry of A preserving V. This note uses that wider form only in
  the remark after the Definition in §1, and not in EZ, CF or W.

## Reproduce

From `compute/` (plain Python 3; no third-party packages):

    python3 fixed_point_formula.py > output/fixed_point_formula.txt   # ~45 s, ALL CHECKS PASSED, exit 0
    python3 fixed_point_formula.py --quick                             # < 1 s: A2, A3, B2, B3
    python3 fixed_point_formula.py --types D4,H3                       # any subset
    python3 -m unittest test_fixed_point_formula                       # < 1 s, positive and negative controls

The archived output is `compute/output/fixed_point_formula.txt`.

References: [GT] = `notes/general_theory.md`; [Thm] =
`notes/poset_jks_theorem.tex`; [FPM] = `notes/fixed_point_mobius_identity.md`;
[NovGT] = `notes/novelty_general_theory.md`.
