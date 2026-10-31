# Theorem E: the equivariant wedge for pointed cones

**Verdict.** Candidate Theorem E of `notes/mo17370_wedges_of_spheres.md` §3 is
**PROVEN** below, for every rank d ≥ 2 (d = 2 and d = 3 included), given standard cited
inputs, and independently **AUDITED** ([Aud]: it holds). The proof closes all the gaps
that §3 marked:
- Step 1 needs no equivariant homeomorphism. It applies the ordinary Quillen fiber lemma
  to each fixed subposet, using the restricted arrangement on Fix(H). This is exactly how
  Thévenaz–Webb prove their Theorem 1, which we re-read.
- The low ranks have their own arguments: a tree-lifting argument for graphs (d = 3) and
  a direct one for d = 2.
- The integral freeness of H̃_{d−2} comes from the chambers, and it is really needed: the
  fixed-set hypotheses alone give only a stably free module.

Both hypotheses are necessary:
- **Freeness is necessary.** For a non-free action, Δ(Λ̄(V)) is not a permutation wedge
  in general. It can even have *no* G-fixed point (orthant of ℝ^3, G = S_3). What does
  hold for every finite G is **Theorem S**: after one unreduced suspension, Δ(Λ̄(V)) is
  G-equivalent to a wedge of *representation spheres*, one for each chamber. Whether this
  wedge desuspends when every chamber stabilizer has a fixed line besides the chamber's
  own is **OPEN** (Question E♯).
- **Pointedness is necessary**, even when G acts freely on the chambers (Π̄_4 with S_4,
  and the poset of two 2-chains with its swap).

**Poset case (PROVEN, AUDITED).** For P connected with n ≥ 3 elements,
Δ(L̄) ≃_{Aut P} Aut(P)_+ ∧ ⋁^{e(P)/|Aut P|} S^{n−3}, where e(P) = |Lin P|. In particular
H̃_{n−3}(Δ(L̄); ℤ) is a free ℤ[Aut P]-module. [Thm] has this only over ℂ.

**Audit status.** Independently audited in [Aud] = `notes/audit_theorem_e.md`, with its
own code. Theorem E (all d ≥ 2), Lemma F, Corollaries F1 and F2, the poset corollary,
Theorem S and (S1)–(S4) **HOLD**. The audit's fixable items R1 (§2.3 wording), R2
(Theorem S step 5 wording) and R3 (the Π̄_4 example of §3.3) are applied below, as are
its optional items (May's statement of (W); the "⇐" step of Lemma F(c)). The audit also
proves the case e_H = 3 of (S4) by a planar-collapse argument ([Aud, §4.2]). That proof
has **not been independently checked**, so it is recorded as "proved in the audit, not
independently checked", not as audited.

**Prior art** ([PA] = `notes/prior_art_theorem_e.md`; all verdicts are search results,
not proofs of novelty).
- Theorem E for general pointed cones: **NOT FOUND**.
- The poset corollary for the claw K_n (one minimum below n − 1 maximal elements, and its
  dual) is **KNOWN**. There OP(K_n) = Π_n and Aut(K_n) = Σ_{n−1}, and the corollary reads
  |Π̄_n| ≃_{Σ_{n−1}} Σ_{n−1,+} ∧ S^{n−3}: Arone 2015, Examples 1.4; Arone–Brantner 2021,
  the Example after Thm 5.10; Donau 2012. The poset corollary **generalizes** this known
  case. For every other connected P it is **NOT FOUND**.
- Theorem S: **NOT FOUND**. The same shape (a G-equivalence, after an unreduced
  suspension, to a wedge of induced representation spheres) occurs for partition
  complexes under Young subgroups: Arone 2015, Thm 1.2; Arone–Brantner 2021, Thm 5.10.
  Those are a different object and do not contain Theorem S ([PA, §2.2]).
- Step 1 (Corollary F1) is the known technique of Thévenaz–Webb 1991, Thm 1, restated as
  Björner–Wachs–Welker 2005, Cor. 7.2. The fiber computation, Lemma F, was not found.

Tags:
- **PROVEN**: a proof is given here; the cited inputs are named.
- **CITED**: a published result. We say whether we re-read it.
- **COMPUTED**: checked by `compute/theorem_e_equivariant_wedge.py` (see Reproduce). The
  output is archived in `compute/output/theorem_e_equivariant_wedge.txt`.
- **OPEN**: not proved.
- **AUDITED**: re-derived by the independent audit [Aud].

Abbreviations: [GT] = `notes/general_theory.md`, [MO] = `notes/mo17370_wedges_of_spheres.md`,
[Thm] = `notes/poset_jks_theorem.tex`, [TW] = Thévenaz–Webb (below),
[Aud] = `notes/audit_theorem_e.md`, [PA] = `notes/prior_art_theorem_e.md`.

---

## 0. Setting and cited inputs

As in [GT §0]:
- A is a finite real central essential arrangement in ℝ^d.
- V is a top-cone, |V| is its closed cone, and the faces of V are the faces F of A with
  F ⊆ |V|.
- Λ(V) = {span F}, and Λ̄(V) is its proper part. Put T := Δ(Λ̄(V)).
- V is **pointed** if lin V = |V| ∩ −|V| = 0.
- G is a finite group of linear maps of ℝ^d that preserve A and |V|. So G permutes the
  faces, the flats, Λ(V) and the chambers of V.
- For H ≤ G write Fix(H) = {x : hx = x for all h ∈ H} and e_H = dim Fix(H). Write m_H for
  the number of chambers of V fixed by H, and G_C for the stabilizer of a chamber C.

Posets that occur:
- P_Z = the set of faces F ≠ O of V.
- Q′ = P_Z minus the chambers.
- f : Q′ → Λ̄(V), f(F) = span F. This is the face map of [GT, Thm 1 Step 1], and it is
  G-equivariant.
- X = Δ(Q′) and K = Δ(P_Z).

**Free G-wedge.** For k ≥ 0 and r ≥ 1, W_r(S^k) := G_+ ∧ ⋁^r S^k. This is |G|·r copies of
S^k, wedged at a G-fixed base point, and G permutes the copies freely. Up to
G-homeomorphism it does not depend on any choices, because every copy has trivial
stabilizer. This is the meaning of "⋁_{C∈V} S^{d−2} with G permuting the summands as it
permutes the chambers" when the action on chambers is free.

**Cited inputs.**
- **(Q) Quillen's fiber lemma** (Quillen 1978, Prop. 1.6; standard, as used throughout the
  repo). Let φ : P → Q be a poset map such that Δ(φ^{-1}(Q_{≤y})) is contractible for
  every y. Then Δ(φ) is a homotopy equivalence.
- **(W) The equivariant Whitehead theorem**, as stated in [TW, (1.3)], which attributes it
  to Bredon (*Equivariant cohomology theories*, LNM 34, §II) and to tom Dieck
  (*Transformation Groups*, II.2.7). Let X, Y be G-CW-complexes and φ : X → Y a
  G-equivariant cellular map. Then φ is a G-homotopy equivalence iff φ^H : X^H → Y^H is a
  homotopy equivalence for every subgroup H ≤ G.
  - **CITED.** The statement was re-read in [TW]. Bredon and tom Dieck were *not* re-read.
    The audit re-read it in J. P. May et al., *Equivariant homotopy and cohomology
    theory*, CBMS Regional Conf. Ser. Math. 91 (AMS 1996), Ch. I, Thm 3.2 and
    **Cor. 3.3** ([Aud, §2]). There cellularity is *not* a hypothesis.
  - Every map we feed into (W) is in fact cellular, but by May's statement this is not
    needed.
- **[TW] Thévenaz–Webb**, *Homotopy equivalence of posets with a group action*, J. Combin.
  Theory Ser. A 56 (1991) 173–181.
  - **CITED, re-read** in the open-access typescript on EPFL Infoscience (record 130437).
    It is 6 pages; its numbering is Theorem 1 and (1.1)–(1.6).
  - Theorem 1 states: let φ : X → Y be a map of G-posets such that for all y ∈ Y,
    φ^{-1}(Y_{≤y}) is G_y-contractible (or dually with Y_{≥y}). Then φ is a G-homotopy
    equivalence.
  - Its proof (1.4) is: apply (Q) to φ^H : X^H → Y^H for each H, using
    (φ^H)^{-1}(Y^H_{≤y}) = (φ^{-1}(Y_{≤y}))^H, then apply (W).
  - **Note.** [TW] assumes G_y-contractibility, but its proof uses only the
    contractibility of the H-fixed fiber for every H ≤ G_y. We use that weaker
    hypothesis, and we run the argument of (1.4) directly. So we need only (Q) and (W);
    the statement of [TW, Thm 1] itself is not used.
- **(C) The cell facts of [GT §0].** The faces F ≠ O of a closed pointed polyhedral cone
  that is a union of faces of an essential arrangement, intersected with the unit sphere,
  form a regular CW complex. The order complex of its face poset is homeomorphic to it.
  These are CITED as in [GT §0], and [AudC §A.1] re-checked them. We use them only
  non-equivariantly.
- **Lemma 0.2 of [GT]** (PROVEN there). If C ⊆ Y is a closed convex cone with
  dim C = dim Y and C ≠ Y, then C ∩ S is contractible.
- **Order complexes are admissible (PROVEN).** Let G act on a poset by automorphisms. If g
  maps a chain to itself, then g fixes the chain pointwise, since an order-preserving
  bijection of a finite chain is the identity. Hence:
  - Δ(P) is a G-CW complex whose open cells are the open simplices;
  - |Δ(P)|^H = |Δ(P^H)|, a full subcomplex;
  - a poset map induces a simplicial, hence cellular, G-map.

---

## 1. The fixed-point lemma

**Lemma F (PROVEN, AUDITED).** Let V be pointed and H ≤ G, and put U = Fix(H).
- (a) A face F of A is H-stable (hF = F for all h ∈ H) iff F ∩ U ≠ ∅.
- (b) F ↦ F ∩ U is an order isomorphism from the H-stable faces of A onto the faces of the
  restricted arrangement A^U = {h ∩ U : h ∈ A, h ⊉ U} in U. A^U is essential in U.
- (c) Let Y ∈ Λ(V) be H-stable and Y ≠ 0. Let 𝓕(Y)^H be the poset of H-stable faces
  F ≠ O of A with F ⊆ |V| ∩ Y. Then Δ(𝓕(Y)^H) is contractible.

*Proof.*
- (a) If x ∈ F ∩ U, then for h ∈ H the face hF contains hx = x. Faces are disjoint, so
  hF = F. Conversely, let F be H-stable and x ∈ F. Then x̄ = |H|^{-1} Σ_h hx lies in F,
  because F is convex and H-stable. It is H-fixed, so F ∩ U ≠ ∅.
- (b), the bijection. Let σ be the sign vector of F. Then F ∩ U is the set of points of
  U with sign vector σ. Hyperplanes containing U have sign 0 on all of U, so this set is
  a face of A^U, and every face of A^U arises this way from a unique F, which meets U and
  is therefore H-stable by (a).
- (b), the order. We need F ⊆ cl F′ ⟺ F ∩ U ⊆ cl(F′ ∩ U).
  - For a relatively open convex set F′ that meets the subspace U, cl(F′ ∩ U) =
    cl F′ ∩ U: join a point of F′ ∩ U to a point of cl F′ ∩ U by a segment.
  - "⇒" is then immediate.
  - "⇐": F ∩ U ⊆ cl F′ gives F ∩ cl F′ ≠ ∅. A face that meets a closed face lies in it,
    so F ⊆ cl F′.
- (b), essentiality. The intersection of A^U is U ∩ ⋂_{h ⊉ U} h, which is contained in
  ⋂_{h ∈ A} h = 0.
- (c), the poset. Put K_Y = |V| ∩ Y ∩ U. It is a closed convex cone, a union of faces of
  A^U (because |V| and Y are unions of faces of A), and pointed (because |V| is). By (b),
  𝓕(Y)^H is isomorphic to the poset of nonzero faces of A^U contained in K_Y. (For an
  H-stable F, F ⊆ |V| ∩ Y iff F ∩ U ⊆ K_Y. For "⇐": F ∩ U ≠ ∅ meets the union of faces
  |V| ∩ Y, so F lies in it ([Aud, §1.1]).) K_Y ∩ S is a subcomplex of the regular CW
  sphere S(U) given by A^U, so by (C) applied in U, Δ(𝓕(Y)^H) ≅ K_Y ∩ S.
- (c), contractibility. K_Y ≠ 0: take 0 ≠ x ∈ |V| ∩ Y, which exists because
  dim(|V| ∩ Y) = dim Y ≥ 1 ([GT, Lemma 0.1(a)]). Its H-average is H-fixed and lies in
  |V| ∩ Y. It is nonzero, because a sum of vectors of a pointed cone vanishes only if
  every summand does: take a linear form positive on |V| ∖ 0. So K_Y is a nonzero pointed
  cone, K_Y ≠ span K_Y, and K_Y ∩ S is contractible by [GT, Lemma 0.2] applied in
  span K_Y. ∎

The averaging trick and the convexity in §3 of [MO] are the heart of this. Lemma F is
the written-out form of [MO] gap (i). It replaces the equivariant homeomorphism
|Δ(face poset)| ≅ |V| ∩ Y ∩ S by a non-equivariant homeomorphism applied once for each H.

**Corollary F1 (PROVEN, AUDITED; pointed V, any finite G).** Δ(f) : X → T is a G-homotopy
equivalence.

*Proof.* Fix H ≤ G and Y ∈ Λ̄(V)^H. The fiber of f^H : Q′^H → Λ̄(V)^H over Y is
{F ∈ Q′^H : span F ⊆ Y}. This is the poset 𝓕(Y)^H of Lemma F(c): no chamber has
span ⊆ Y, since Y ≠ ℝ^d. It is contractible, so (Q) makes f^H a homotopy equivalence.
Since X^H = Δ(Q′^H) and T^H = Δ(Λ̄(V)^H) (admissibility), (W) applies. ∎

**Corollary F2 (PROVEN, AUDITED; pointed V).** Let H ≤ G fix no chamber of V. Then T^H is
nonempty and contractible.

*Proof.* Q′^H is the poset of all H-stable faces ≠ O of V, because no chamber is
H-stable. This is 𝓕(ℝ^d)^H, which is contractible by Lemma F(c) with Y = ℝ^d. Then
T^H ≃ X^H = Δ(Q′^H) by Corollary F1. ∎

If G acts freely on chambers, every H ≠ 1 fixes no chamber. This settles steps 1–2 of the
sketch in [MO §3] and the "fixed sets for EVERY subgroup" requirement.

---

## 2. Theorem E

**Theorem E (PROVEN, AUDITED; given (Q), (W), (C) and the Hurewicz and Whitehead
theorems).** Let V be a pointed top-cone of a finite real central essential arrangement of rank d ≥ 2. Let
G be a finite group of linear maps preserving A and V that acts freely on the chambers
of V. Then

  Δ(Λ̄(V)) ≃_G W_r(S^{d−2}) = G_+ ∧ ⋁^r S^{d−2},  r = #V / |G|,

and H̃_{d−2}(Δ(Λ̄(V)); ℤ) is a free ℤG-module of rank r.

For G = 1 this is the pointed case of [GT, Thm 1]. Assume G ≠ 1 from now on.

### 2.1 Integral freeness of H̃_{d−2} (PROVEN)

Let Z = |V| ∩ S with its regular cell structure (C). Its top cells are the chambers, and X
realizes its (d − 2)-skeleton.

**A small fact used throughout.** Δ(Q′) realizes the (d − 2)-skeleton of Z, and Δ(P_Z)
realizes Z, by (C). We need the homeomorphism only non-equivariantly. Every G-equivariant
statement below is made about the order complexes themselves.

- [GT, Thm 1 Step 4]: V is pointed, so Z is contractible (V is not all chambers, since
  |V| ≠ ℝ^d). Hence the connecting map ∂ : H_{d−1}(Z, X) → H̃_{d−2}(X) is an
  isomorphism.
- It is G-equivariant, being natural. Here G acts on the pair through any G-equivariant
  model. Concretely, use the simplicial pair (K, X) = (Δ(P_Z), Δ(Q′)), which realizes
  (Z, X) by (C).
- H_{d−1}(K, X) = ⊕_{C ∈ V} H_{d−1}(star C, ∂_C), where ∂_C := Δ(proper nonzero faces of
  C) is the link of the vertex C:
  - each chamber C is a maximal element of P_Z;
  - the closed stars of different chambers meet only inside X;
  - each H_{d−1}(star C, ∂_C) = H_{d−1}(cone, base) ≅ H̃_{d−2}(∂_C) ≅ ℤ, as
    ∂_C ≅ ∂C̄ ∩ S ≅ S^{d−2} by (C).
- g ∈ G carries the summand of C isomorphically onto the summand of gC.
- Choose one chamber C_i in each G-orbit (i = 1, …, r) and a generator u_i of its
  summand. Then {g u_i : g ∈ G, i ≤ r} is a ℤ-basis of H_{d−1}(K, X): by freeness g u_i
  generates the summand of gC_i, and (g, i) ↦ gC_i is a bijection onto V. G permutes this
  basis freely, so H_{d−1}(K, X) ≅ ℤG^r.
- Transport it through ∂ and through the G-isomorphism H̃_{d−2}(X) ≅ H̃_{d−2}(T) of
  Corollary F1. ∎

*Why this step is needed (PROVEN, remark).* The fixed-set data alone do not give freeness.
Suppose T ≃ ⋁ S^k, dim T = k and T^H is contractible for every H ≠ 1. Collapse the
singular set as in §2.3. The reduced cellular chain complex of the quotient is then a
finite complex of free ℤG-modules with homology only in its top degree k. Splitting it
off from the bottom shows that H̃_k is stably free. Stably free ℤG-modules need not be
free (Swan, CITED from memory, not re-read). So the chamber basis carries real
information.

### 2.2 The case d ≥ 4 (PROVEN)

Put k = d − 2 ≥ 2.
- By [GT, Thm 1], T ≃ ⋁^{#V} S^k. So T is (k − 1)-connected and simply connected.
- G ≠ 1 fixes no chamber, so T^G ≠ ∅ by Corollary F2. Choose a vertex x_0 ∈ T^G, i.e. a
  G-stable proper flat.
- Let b_1, …, b_r be a ℤG-basis of H_k(T) (§2.1). By Hurewicz, π_k(T, x_0) ≅ H_k(T).
  Represent b_i by a based map φ_i : S^k → T, cellular after non-equivariant cellular
  approximation rel base point.
- Define Φ : W_r(S^k) → T by Φ(g, i, s) = g·φ_i(s). It is well defined because the base
  point goes to the G-fixed point x_0, and it is a cellular G-map.
- **H = 1.** H_k(Φ) sends the ℤG-basis e_i of H_k(W_r) ≅ ℤG^r to b_i, and it is
  ℤG-linear. So it is an isomorphism. Both spaces are simply connected CW complexes with
  homology only in degree k, so Φ is a homotopy equivalence (Whitehead).
- **H ≠ 1.** W_r^H = {x_0}, since G acts freely off the base point, and T^H is
  contractible by Corollary F2. So Φ^H is a homotopy equivalence.
- By (W), Φ is a G-homotopy equivalence. ∎

### 2.3 The case d = 3: graphs (PROVEN)

Here T is a connected graph, by [GT, Thm 1]. Simple connectivity is not available, so we
argue combinatorially.
- **The singular part is a tree.** Let T_s = ⋃_{H ≠ 1} T^H. Each T^H is a contractible
  subgraph, i.e. a tree (Corollary F2). Any two meet in T^{⟨H,H′⟩}, which is again a
  tree. By induction on r, a union of r such trees is a tree:
  - (T^{H_1} ∪ … ∪ T^{H_r}) ∩ T^{H_{r+1}} = ⋃_i T^{⟨H_i, H_{r+1}⟩}, which is a tree by
    induction, so in particular nonempty and connected;
  - a union of two trees whose intersection is a tree is connected with Euler
    characteristic 1 + 1 − 1 = 1, hence a tree.

  So T_s is a G-invariant tree.
- **Collapsing T_s.** The quotient q : T → T_1 := T/T_s is a cellular G-map, and T_1 is a
  G-CW graph whose cells other than the base point * all have trivial stabilizer. For
  H ≠ 1, T_1^H = {*} (a point outside T_s has trivial stabilizer), and q^H collapses the
  tree T^H to the point. For H = 1, collapsing a tree is a homotopy equivalence. By (W),
  T ≃_G T_1.
- **A G-invariant spanning tree.** Let Γ = T_1/G, a finite connected graph, and choose a
  spanning tree τ̄ of Γ. Lift τ̄ to a tree τ ⊆ T_1 through *, edge by edge away from [*]:
  - an edge of τ̄ from p to q (p ≠ q, p nearer the root) is a free orbit of edges;
  - choose an edge of that orbit incident to the chosen lift of p. If p ≠ [*] it is
    unique, because G acts freely on that orbit and on the vertex orbit of p. If p = [*],
    all |G| edges of the orbit meet *, and any one of them will do ([Aud, §3.3, R1]).

  τ contains * and exactly one vertex of each free vertex orbit.
- The translates gτ meet pairwise only in *: if v ∈ gτ ∩ τ, v ≠ *, then v and g^{-1}v
  lie in τ and in the same orbit, so they are equal, and g = 1. So F = ⋃_g gτ is a
  G-invariant tree containing every vertex.
- **Collapsing F.** T_1 → T_1/F is a cellular G-map. It is a homotopy equivalence
  (collapsing a tree), and on H-fixed points (H ≠ 1) it is {*} → {*}. By (W),
  T_1 ≃_G T_1/F.
- T_1/F has one vertex, and G permutes its loops freely. Choosing one loop per orbit
  gives T_1/F ≅_G W_r(S^1), with r|G| = rank H_1(T) = #V. ∎

Here the freeness of H_1 over ℤG comes out of the argument. §2.1 is not needed for d = 3.

### 2.4 The case d = 2 (PROVEN)

T is the set of rays of A in |V|; there are #V + 1 of them, because V is pointed.
- For H ≠ 1, T^H is a single point (Corollary F2), so T^H = T^G = {x_0}.
- G acts freely on T ∖ {x_0}.
- Hence T ≅_G {x_0} ⊔ G × {1, …, r} = W_r(S^0). ∎

(Concretely, G is 1 or a reflection of order 2. For the reflection, #V must be even, and
x_0 is the middle ray.)

### 2.5 The poset case (PROVEN, AUDITED)

Let P be connected with n ≥ 3 elements, let A be the braid arrangement essentialized in
ℝ^n/ℝ·1 (so d = n − 1), let V = C_P, and let G = Aut(P) act by permuting coordinates.
- V is pointed, because lin C_P = ℝ·1 ([MO §3]).
- G acts freely on Lin P ([Thm], cor:connected). In fact Aut(P) acts freely on Lin P for
  *every* finite P (σ·L = L forces σ to be an automorphism of a chain), so connectedness
  is used only for pointedness ([Aud, §3.5]). This is also COMPUTED for every case
  below by an assertion in the script.
- Λ(C_P) ≅ OP(P)^op equivariantly: a flat is a set partition, and Aut(P) permutes blocks.
  The order complex of the opposite poset is the same complex.

So Theorem E gives

  Δ(L̄) ≃_{Aut P} Aut(P)_+ ∧ ⋁^{e(P)/|Aut P|} S^{n−3},

and H̃_{n−3}(Δ(L̄); ℤ) is a free ℤ[Aut P]-module. [Thm, cor:connected] states this over ℂ
only. The integral statement is a direct consequence of §2.1.

**Prior art ([PA, §2]).** For the claw K_n (and its dual), OP(K_n) = Π_n and
Aut(K_n) = Σ_{n−1} acts simply transitively on the (n − 1)! linear extensions, so the
statement reads |Π̄_n| ≃_{Σ_{n−1}} Σ_{n−1,+} ∧ S^{n−3}. This is **KNOWN**: Arone 2015,
Examples 1.4 (where it is called well known); Arone–Brantner 2021, the Example after
Thm 5.10; Donau 2012. The claw and its dual are the only connected posets with
OP(P) = Π_n ([PA, §2.2]). So the poset corollary **generalizes** this known case. For
every other connected P, neither the homotopy statement nor the integral freeness was
found in the sources read (NOT FOUND, a search result).

### 2.6 Computations (COMPUTED)

`[POS]`: every connected poset P with 4 ≤ n ≤ 6 and |Aut P| > 1 (191 posets up to
isomorphism), G = Aut(P), and every subgroup H ≤ G. The script builds Λ̄(C_P) from the
ordered set partitions, independently of the repo code.
- For H ≠ 1, T^H is acyclic over F_2, F_3, F_5, F_7 and F_{2^31−1}. Its Stong core (beat
  points deleted) is a single point, which certifies contractibility: 1,199 of 1,199
  pairs.
- For H = 1, the Betti numbers are #Lin P in degree n − 3. This was computed on all but
  27 posets with n = 6 and #Lin P > 40, where Theorem 1 is used instead.
- In total the prediction holds on 1,363 of 1,363 computed pairs.

`[GEN]`: general arrangements, using every subgroup of the stabilizer of each cone in the
signed-permutation group.
- **B_3**: 298 pointed cones with nontrivial stabilizer. Every subgroup acts freely on
  chambers, because W(B_3) acts simply transitively on all chambers. On all 446 pairs
  with H ≠ 1, T^H is acyclic with Stong core one point.
- **Boolean ℝ^3, ℝ^4**: these are the non-free cases; see §3.

---

## 3. Is "free" needed? Is "pointed" needed?

### 3.1 Without freeness: Theorem S (PROVEN)

For a chamber C, let p_C be a G_C-fixed point in the interior of C (an average). Let U_C
be the G_C-representation ℝ^d / ℝ p_C, and S^{U_C} its one-point compactification, a
(d − 1)-sphere with G_C acting.

**Theorem S (PROVEN, AUDITED; given (Q), (W), (C); V pointed, G any finite group
preserving A and V).** Let Σ^u denote unreduced suspension. Then

  Σ^u Δ(Λ̄(V)) ≃_G ⋁_{[C] ∈ V/G} G_+ ∧_{G_C} S^{U_C},

a wedge of representation spheres indexed by the chambers, with G permuting them.

*Prior art ([PA, §1.1]).* NOT FOUND (a search result). The same shape occurs for the
partition complex under Young subgroups (Arone 2015, Thm 1.2; Arone–Brantner 2021,
Thm 5.10), a different object; neither statement contains the other ([PA, §2.2]).

*Proof.*
1. **Reduction to X.** Δ(f) : X → T is a G-homotopy equivalence (Corollary F1, which
   does not need freeness), hence so is Σ^u X → Σ^u T.
2. **K is G-contractible.** For every H, K^H = Δ(P_Z^H) = Δ(𝓕(ℝ^d)^H) is contractible
   by Lemma F(c). Apply (W) to K → pt.
3. **Σ^u X ≃_G K/X.** Here K/X := (K ∪ CX)/CX, so K/∅ = K_+. Both maps
   - K ∪ CX → K/X, collapsing the cone CX, and
   - K ∪ CX → Σ^u X = CX/X, collapsing K

   are cellular G-maps of admissible complexes.
   - On H-fixed points they collapse C(X^H), respectively K^H. Both are contractible
     subcomplexes (C(∅) is the cone point), so each restriction is a homotopy
     equivalence.
   - We use (K/A)^H = K^H/A^H, which holds because points outside a G-subcomplex keep
     their stabilizers.
   - By (W), both maps are G-homotopy equivalences.
4. **K/X is a wedge of suspensions.** K = X ∪ ⋃_C star(C), where the closed stars of
   distinct chambers meet only in X, and star(C) ∩ X = ∂_C. So
   - K/X = ⋁_C star(C)/∂_C ≅ ⋁_C Σ^u ∂_C;
   - g carries the summand of C to that of gC;
   - so K/X ≅_G ⋁_{[C]} G_+ ∧_{G_C} Σ^u ∂_C.
5. **∂_C ≅_{G_C} S(U_C), the unit sphere.** This is the only place where an equivariant
   homeomorphism is needed. It concerns a single closed chamber. (Chambers of a general
   arrangement need not be simplicial, and nothing below uses that they are; [Aud, R2].)
   - Fix a G-invariant inner product and a G_C-invariant linear form φ > 0 on C̄ ∖ 0
     (an average).
   - For a nonzero face F ≤ C̄, put b(F) := β/φ(β), where β is the sum of the unit
     vectors on the extreme rays of F̄. Then b(gF) = g b(F), and b(F) lies in the
     relative interior of F.
   - The simplexwise-linear map Δ(faces F with 0 ≠ F < C) → ∂Q, where
     Q = C̄ ∩ {φ = 1}, chain ↦ conv{b(F_i)}, is a homeomorphism. Proof by induction on the
     faces: each face Q_F of Q is the cone from its relative-interior point b(F) over
     ∂Q_F. It is G_C-equivariant.
   - Radial projection from b(C), (x ↦ (x − b(C))/‖x − b(C)‖), is a G_C-homeomorphism
     ∂Q → S(ker φ), because Q is compact and convex with b(C) in its interior. Also
     ker φ ≅ U_C as G_C-representations.
   - Finally Σ^u S(U) ≅ S^U. ∎

**Consequences (PROVEN, AUDITED, except (S4) for e_H = 3; see there).**
- (S1) H̃_*(T^H; ℤ) ≅ ℤ^{m_H}, concentrated in degree e_H − 2, for every H ≤ G. Indeed
  (S^{U_C})^H = S^{U_C^H} has dimension e_H − 1 when H ≤ G_C, and dim U_C^H = e_H − 1
  because p_C ∈ Fix(H). Also H̃_{j+1}(Σ^u Y) = H̃_j(Y).
  - **COMPUTED** on every subgroup of every stabilizer: 48 pairs for Boolean ℝ^3, 480 for
    Boolean ℝ^4, 744 for B_3, and all type-A pairs.
  - Of these, 504 pairs have H ≠ 1 fixing a chamber.
- (S2) **T^H = ∅ iff Fix(H) is a line meeting the interior of a chamber of V**, i.e.
  e_H = 1 and m_H ≥ 1. This is (S1) in degree −1. COMPUTED: T^H = ∅ on 16 Boolean-ℝ^3
  pairs and 144 Boolean-ℝ^4 pairs.
- (S3) H̃_{d−2}(T; ℤ) ≅ ⊕_{[C]} Ind_{G_C}^G(det), the det-twisted chamber module. This is
  consistent with the det twist of [GT, Thm G\*].
- (S4) The homotopy type of T^H itself, not only its homology:
  - contractible if m_H = 0 (Corollary F2);
  - ≃ ⋁^{m_H} S^{e_H−2} if e_H ≥ 4. Reason: K^H = X^H ∪ (m_H cones on ∂_C^H ≅ S^{e_H−2}),
    so π_1(X^H) = π_1(K^H) = 1, and then Hurewicz and Whitehead apply;
  - for e_H ≤ 2, clear from dimension;
  - for e_H = 3 with m_H ≥ 1: T^H ≃ ⋁^{m_H} S^1, by a planar-collapse argument
    (X^H is a 2-dimensional straight-line complex in a plane, so it collapses to a
    graph). This is **proved in the audit ([Aud, §4.2]), not independently checked**.
    Until it is, this case is not audited; the homology is known by (S1).

### 3.2 Non-free counterexamples (PROVEN by hand; COMPUTED)

Let A be the coordinate arrangement in ℝ^3, V the positive orthant (one chamber, pointed),
and d = 3. Λ̄(V) consists of the six coordinate subspaces of dimensions 1 and 2, so T is a
hexagon, ≅ S^1.
- **G = S_3**, permuting coordinates. The only S_3-stable coordinate subspaces are 0 and
  ℝ^3, so **T^G = ∅**. Every based G-space, and in particular every wedge, has a G-fixed
  base point. So T is not G-homotopy equivalent to *any* wedge of spheres, with any
  actions on the summands.

  Theorem S gives instead Σ^u T ≃_G S^{U}, where U = ℝ^3/ℝ(1,1,1) is the reduced
  standard representation; in fact T ≅_G S(U).
- **G = ⟨(12)⟩.** T^G = {span e_3, span(e_1, e_2)} ≅ S^0. A "permutation wedge" with
  trivial action on its summands (one circle, since m = 1) would have fixed set S^1. So
  T is not a permutation wedge in the naive sense.

  It *is* a wedge of a representation sphere: T ≅_G S^{σ}, the one-point
  compactification of the sign line, a circle with a reflection fixing two points.
- COMPUTED (`[NEG]`): T^G = ∅ for S_3 on ℝ^3 and for S_4 on ℝ^4. The trivial-action
  prediction "ℤ^{m_H} in degree d − 2" fails on 5 subgroups of S_3 and on 29 of S_4,
  while (S1) holds on all of them.

**Answer to "is free needed?"**
- Yes, for the statement as posed: without freeness the fixed sets are spheres of the
  smaller dimension e_H − 2, not points, and T^G can be empty.
- The free hypothesis can be replaced by the representation-sphere wedge of Theorem S,
  at the price of one suspension.

**Question E♯ (OPEN).** Suppose V is pointed and every chamber stabilizer G_C has
dim Fix(G_C) ≥ 2, so that U_C = ℝ ⊕ U′_C, with U′_C well defined up to isomorphism by
cancellation of real representations. Is

  Δ(Λ̄(V)) ≃_G ⋁_{[C]} G_+ ∧_{G_C} S^{U′_C}?

- The hypothesis is necessary, by (S2).
- Both sides have the same fixed-set homology, by (S1).
- Theorem E is the case G_C = 1.
- The ⟨(12)⟩ example above is a positive instance.

### 3.3 Is "pointed" needed? Yes (COMPUTED; PROVEN by the counts)

- **Π̄_4**: all chambers of A_3, not pointed, d = 3. G = S_4 acts simply transitively,
  so freely, on chambers.
  - T ≃ ⋁^6 S^1 ([GT, Thm 1]: m = 3! = 6).
  - |S_4| = 24 does not divide 6, so no free wedge is possible.
  - COMPUTED: on 6 subgroups H ≠ 1, T^H is not acyclic. These are the three
    ⟨double transposition⟩ and V_4, where T^H has three components, so
    H̃_0(T^H) = ℤ^2, and A_4 and S_4, where T^H = ∅. For a transposition, T^H is a tree
    with 5 vertices, hence contractible. (This corrects an earlier wrong instance;
    [Aud, §5, R3].)
- **P = two 2-chains {a < b} ⊔ {c < d}** (n = 4, d = 3) with the swap g = (ac)(bd).
  - g acts freely on the 6 linear extensions, and C_P is not pointed.
  - m(C_P) = e_C(P) = 5. This is COMPUTED as Betti numbers (0, 0, 5) and agrees with
    [GT, Thm 1].
  - 5 is odd, so the swap cannot permute the spheres freely, and T^g ≅ S^0 is not
    contractible.

In the non-pointed case, Theorem E's count #V is already wrong non-equivariantly
(m(V) < #V), and the fixed sets are not contractible. This matches [MO §2.4] (Π̄_3). The
general equivariant question for non-pointed cones stays **OPEN** ([MO §3]).

---

## 4. Status of the [MO §3] gaps

| Gap in [MO §3] | Resolution | Tag |
|---|---|---|
| (i) equivariant homeomorphism; G-CW structure | Not needed for Theorem E: Lemma F applies (C) non-equivariantly on Fix(H) for each H; order complexes are admissible G-CW complexes | PROVEN |
| (ii) re-read Thévenaz–Webb; exact Whitehead statement | [TW] Thm 1 and (1.3), (1.4) re-read; we use (Q) and (W) as in (1.4); Bredon and tom Dieck not re-read | CITED |
| (iii) low rank | d = 3 by tree lifting (§2.3), d = 2 directly (§2.4) | PROVEN |
| Free ℤG-module (step 3) | chamber basis (§2.1); needed, since stably free ≠ free in general | PROVEN |
| Fixed sets for every H | Corollary F2; COMPUTED on 1,199 type-A and 446 B_3 pairs | PROVEN, COMPUTED |
| (iv) literature | [PA]: Theorem E for general pointed cones and Theorem S NOT FOUND; poset corollary KNOWN for the claw K_n (Arone 2015, Ex. 1.4; Arone–Brantner 2021, Ex. after Thm 5.10; Donau 2012), NOT FOUND for other connected P; Step 1 is the Thévenaz–Webb / BWW Cor. 7.2 technique | done (search result) |
| (v) audit | [Aud]: everything HOLDS; R1–R3 applied; (S4) e_H = 3 proved in [Aud, §4.2], not independently checked | AUDITED |

---

## 5. Audit targets

These were the targets of the audit, now done in [Aud], which finds every item HOLDS
(with the wording fixes R1–R3 applied above). They are kept as the record of what was
checked.
1. **Lemma F(b)–(c)**: the H-stable faces ↔ faces of A^U correspondence, the order
   isomorphism (closure step), and the use of (C) for a pointed cone in a possibly
   smaller subspace U.
2. **The use of (W)**: cellularity of every map (Φ in §2.2; the quotient maps in §2.3
   and Theorem S), admissibility, and the identities (K/A)^H = K^H/A^H and
   |Δ(P)|^H = |Δ(P^H)|. Re-read (W) in Bredon or tom Dieck, which we have not done.
3. **§2.3 tree lifting**: one lift per orbit, and gτ ∩ τ = {*}. Also the claim that T_s
   is a tree, including that T^H ∩ T^{H′} = T^{⟨H,H′⟩}.
4. **§2.1**: the G-equivariance of H_{d−1}(K, X) ≅ ℤ̃[V] and of the boundary map, and
   the identification of Δ(Q′) and Δ(P_Z) with the skeleton and with Z (non-equivariant
   only).
5. **Theorem S step 5**: the barycentric homeomorphism with equivariant choices b(F).
6. **The script**: that `[GEN]`/`[POS]` build Λ(V) correctly. The controls are B̄_3 = S^1,
   the crown, the chain, the wrong-degree rejection, and the non-free and non-pointed
   failures. Check also the subgroup enumeration (joins of cyclic subgroups).

---

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process, imports nothing
from the repo):

    python3 theorem_e_equivariant_wedge.py --nmax 6 > output/theorem_e_equivariant_wedge.txt   # ~65 s, ends "ALL CHECKS PASS: True", exit 0
    python3 theorem_e_equivariant_wedge.py --nmax 5                                              # ~2 s

Output lines:
- `[CTL]`: instrument controls.
- `[NEG]`: wrong-degree rejection, non-free orthants, Π̄_4, two 2-chains.
- `[GEN]`: Boolean ℝ^3, ℝ^4 and B_3.
- `[POS]`: type A, one line per poset, then a summary.

Homology is computed as reduced Betti numbers modulo 2, 3, 5, 7 and 2^31 − 1, not as an
integral Smith normal form. Contractibility is certified by a Stong core of size 1
(Stong 1966, CITED as in [MO]).
