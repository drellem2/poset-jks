# Audit of `notes/theorem_e_equivariant_wedge.md` (Theorem E, Lemma F, Theorem S)

This is an independent, adversarial audit of `notes/theorem_e_equivariant_wedge.md`
("[E-note]", merged d9d92e6). Every proof was re-derived line by line. The equivariant
Whitehead theorem was checked against a primary source (§2). All computation is new
code, `compute/audit_theorem_e.py` ("[AUD]"). It imports nothing from the repository,
and in particular nothing from `compute/theorem_e_equivariant_wedge.py` ("[E-script]").
It builds faces from lattice points, not from cocircuits or ordered set partitions, and it
enumerates subgroups by a different method.

## Verdict

| Claim | Verdict | Notes |
|---|---|---|
| **Lemma F(a)** (H-stable ⟺ F ∩ Fix(H) ≠ ∅) | **HOLDS** | §1.1 |
| **Lemma F(b)** (F ↦ F ∩ U is an order isomorphism onto the faces of A^U; A^U essential) | **HOLDS** | The closure identity cl(F′ ∩ U) = cl F′ ∩ U is correct (§1.1). COMPUTED: the H-stable faces equal the sign vectors of points of Fix(H) on 1,224 B_3 (cone, H) pairs, on every free type-A pair with n ≤ 5, and on the orthant, with no failures |
| **Lemma F(c)** (Δ(𝓕(Y)^H) contractible) | **HOLDS** | (C) is used correctly for a cone that need not be full-dimensional in U: K_Y ∩ S(U) is a subcomplex of the regular cell structure on S(U) (§1.1). COMPUTED: Stong core one point on 13,776 B_3 triples (cone, H, Y). A non-pointed control (a half-space) fails on 30 triples, as it must |
| **Corollary F1** (Δ(f) is a G-homotopy equivalence; pointed V, any G) | **HOLDS** | §1.2 |
| **Corollary F2** (H fixes no chamber ⇒ T^H nonempty and contractible) | **HOLDS** | §1.2 |
| **(W) and its use** | **HOLDS** | Re-read in May, CBMS 91, Ch. I §3 (Thm 3.2, Cor 3.3). Cellularity is *not* a hypothesis, so the note's "made cellular by construction" is harmless but unnecessary. Admissibility, \|Δ(P)\|^H = \|Δ(P^H)\| and (K/A)^H = K^H/A^H were all re-proved (§2) |
| **Theorem E, §2.1** (H̃_{d−2} is free over ℤG via the chamber basis) | **HOLDS** | §3.1. COMPUTED integrally mod p: on every cyclic p-subgroup the restriction is free, 351 tests on posets and all B_3 cones, with no failures. The non-free and non-pointed controls fail, as they must |
| **Theorem E, "stably free is not enough" remark** | **HOLDS** (as a remark) | The argument gives "projective and stably free" correctly. Swan's examples are cited from memory in [E-note], and here too (§3.1) |
| **Theorem E, §2.2** (d ≥ 4) | **HOLDS** | §3.2 |
| **Theorem E, §2.3** (d = 3, tree lifting) | **HOLDS; FIXABLE** (wording) | "Exactly one edge of the orbit is incident to the lift of p" is false when p = [∗]: then all \|G\| edges of the orbit meet ∗. One must *choose* one, and the argument is unchanged (§3.3, R1). T_s is a tree, and T^H ∩ T^{H′} = T^{⟨H,H′⟩} is correct. COMPUTED: T_s is acyclic in every free case |
| **Theorem E, §2.4** (d = 2) | **HOLDS** | §3.4 |
| **Poset corollary** (Aut(P)-equivariant free wedge; integral freeness) | **HOLDS** | Aut(P) acts freely on Lin P for *every* P. Connectedness is used only for pointedness (§3.5). COMPUTED on all 191 connected posets with 4 ≤ n ≤ 6 and \|Aut P\| > 1 (and the 2 with n = 3), for every subgroup: 1,199/1,199 fixed sets with H ≠ 1 have Stong core one point, and H = 1 has Betti number #Lin P in degree n − 3 on *every* poset, including the 27 the note skipped |
| **Theorem S** (one suspension gives a wedge of representation spheres; any finite G) | **HOLDS** | Steps 1–5 re-derived (§4). Step 5 is correct. The phrase "simplicial-type cone" is misleading but unused: chambers need not be simplicial, and the proof never uses that they are (R2) |
| **(S1), (S2), (S3)** | **HOLD** | COMPUTED for (S1): 48 + 480 Boolean, 744 B_3, 1,390 free type-A pairs, and 413 pairs in 37 non-free type-A groups ⟨Aut P, −α⟩. No failures |
| **(S4)** | **HOLDS**; the OPEN case e_H = 3 **closes** | A planar-collapse argument gives T^H ≃ ⋁^{m_H} S^1 when e_H = 3 (§4.2). Proposed here and checked by hand; it is not in [E-note] |
| **§3.2 non-free orthant examples** | **HOLDS** | T^{S_3} = ∅ and T^{⟨(12)⟩} ≅ S^0 recomputed. The prediction fails on 5/6 and 29/30 subgroups, and (S1) holds on all of them |
| **§3.3 Π̄_4 example** | **FIXABLE** (one wrong instance; the conclusion stands) | "For a transposition, H̃_1(T^H) = ℤ^2" is wrong. For a transposition, T^H is a tree with 5 vertices, which is contractible. The 6 bad subgroups are the three ⟨double transposition⟩ and V_4, where H̃_0 = ℤ^2, and A_4 and S_4, where T^H = ∅ (§5, R3) |
| **§3.3 two 2-chains** | **HOLDS** | Betti (0, 0, 5) and T^g ≃ S^0 recomputed. Mod 2, H_1 is not free over 𝔽_2C_2 (fixed dimension 3 ≠ 5/2) |
| **§2.6 counts and the script** | **HOLDS** | Every count in [E-note] §2.6, §3.1 and §3.2 was reproduced by independent code: 191; 1,199; 298 / 446 / 744; 48 / 480; 16 / 144; 5 / 29; 6. [E-script]'s constructions are correct (§6) |

**In one line.** Theorem E (all d ≥ 2), Lemma F, Corollaries F1/F2, the poset corollary and
Theorem S hold as stated. There are two wording fixes (R1, R2) and one wrong illustrative
instance in §3.3 (R3). The OPEN case e_H = 3 of (S4) can be closed (§4.2).

---

## 1. Lemma F and its corollaries

Notation is that of [E-note] §0. Faces are relatively open sign-vector cells.

### 1.1 Lemma F

**(a).** If x ∈ F ∩ U, then hF is a face (G preserves A) containing hx = x, so hF = F.
Conversely, the H-average of a point of an H-stable convex F lies in F ∩ U. **Correct.**

**(b), the bijection.** For x ∈ U, σ_x(h) = 0 whenever h ⊇ U. Two hyperplanes with the
same trace on U have proportional forms on U, so their signs on U agree up to a fixed
sign. Hence the full A-sign vector of x ∈ U is determined by its A^U-sign vector, and
conversely. So the sets {x ∈ U : σ_x = σ} are exactly the faces of A^U, and the nonempty
ones are indexed by the faces of A that meet U, which are the H-stable ones by (a).
**Correct.**

**(b), the order.** F′ is relatively open and convex, so F′ = ri(cl F′). For x ∈ F′ ∩ U
and y ∈ cl F′ ∩ U, the segment [x, y) lies in F′ ∩ U. So cl(F′ ∩ U) = cl F′ ∩ U.
- "⇒" follows by intersecting with U.
- "⇐": F meets cl F′, and a closed face is a union of faces, so F ⊆ cl F′.

The order on faces of A^U is again the sign-vector order. **Correct.**

**(b), essentiality.** This is immediate. **Correct.**

**(c), the use of (C).** This was risk item 1. The point is that K_Y = |V| ∩ Y ∩ U
need not be full-dimensional in U.
- (C) is needed only in this form: the nonzero faces of an essential arrangement give a
  regular CW decomposition of the unit sphere, and the order complex of a regular CW
  complex is homeomorphic to it.
- K_Y is closed and a union of faces of A^U. So K_Y ∩ S(U) is a *subcomplex* of the
  regular CW sphere S(U). A subcomplex of a regular CW complex is regular, so Björner's
  homeomorphism applies to it.
- Pointedness is not needed for the cell structure: every nonzero face of an essential
  arrangement is a pointed cone, so it meets S in an open ball. Pointedness is needed only
  for contractibility.
- The poset identification needs "F ⊆ |V| ∩ Y ⟺ F ∩ U ⊆ K_Y". The direction "⇐" holds
  because F ∩ U ≠ ∅ meets the union of faces |V| ∩ Y. [E-note] leaves this step implicit.
  It is one line.

**(c), contractibility.** A nonzero x exists in any face F with span F = Y. Its H-average
is nonzero, because a positive form on |V| ∖ 0 exists for a pointed closed cone. A nonzero
pointed closed cone C has C ≠ span C, so [GT, Lemma 0.2] applies in span K_Y. **Correct.**

**COMPUTED** ([LEMF] lines).
- (a)–(b): for every pointed B_3 cone and every subgroup of its stabilizer (1,224 pairs),
  for every free type-A pair with n ≤ 5 (Aut P), and for the orthant with S_3, the set of
  H-stable faces equals the set of sign vectors of lattice points of Fix(H).
  Completeness of the sample is certified by the Euler characteristic of S(U).
- (c): Stong core one point on all 13,776 B_3 triples (cone, H, Y ≠ 0 H-stable), and on
  all type-A triples with n ≤ 5. Type-A (a)–(b) pairs and (c) triples together number
  2,730.
- Positive control: for the half-space {x_1 ≥ 0} of B_3, which is not pointed, (c) fails
  already for H = 1, as it must.

### 1.2 Corollaries F1, F2

- **F1.** The fiber (f^H)^{-1}(Λ̄(V)^H_{≤Y}) is {F ∈ Q′^H : F ⊆ Y}. A face F ≠ O inside
  Y ≠ ℝ^d is not a chamber, so the fiber is 𝓕(Y)^H. If Λ̄(V)^H = ∅, then Q′^H = ∅ too
  (f is defined on all of Q′), and the statement is vacuous. (Q) applies to f^H, and (W)
  applies by admissibility. **Correct.** This step is exactly [TW] (1.4) with the weaker
  hypothesis, as the note says.
- **F2.** If H fixes no chamber, Q′^H = P_Z^H = 𝓕(ℝ^d)^H, which is contractible.
  **Correct.**

---

## 2. The equivariant Whitehead theorem (W)

This was risk item 2.

**Source read.** J. P. May et al., *Equivariant homotopy and cohomology theory*, CBMS
Regional Conf. Ser. Math. 91 (AMS 1996), Ch. I, §3, read in the author's PDF.
- The definition there: a G-CW complex is built from cells G/H × D^n attached along
  G-maps G/H × S^{n−1} → X^{n−1}. G is a compact Lie group, and H runs over closed
  subgroups. For G finite, every subgroup is closed.
- A G-map e is a ν-equivalence if e^H is a ν(H)-equivalence for all H.
- **Theorem I.3.2** (Whitehead): if e : Y → Z is a ν-equivalence, then
  e_* : [X, Y]_G → [X, Z]_G is bijective for every G-CW complex X of dimension < ν.
- **Corollary I.3.3:** a ν-equivalence between G-CW complexes of dimension < ν is a
  G-homotopy equivalence.

With ν ≡ ∞, this is exactly (W): a G-map between G-CW complexes that is a weak
equivalence on all fixed-point sets is a G-homotopy equivalence.

Hypotheses checked:
- **Cellularity is not required.** May proves cellular approximation separately
  (Thm I.3.4) and does not assume it in I.3.2–3.3. The note's care to make every map
  cellular is therefore unnecessary. It is harmless, and every claimed cellularity is true
  in any case.
- **Fixed sets.** All fixed-set maps in the note are maps of finite CW complexes. A weak
  equivalence between them is the same as a homotopy equivalence.
- **Bredon and tom Dieck** (II.2.7) were not available to this audit either. May's
  statement is the standard one, and it suffices.

**Admissibility (re-proved).** g ∈ Aut(P) mapping a chain onto itself is an
order-preserving bijection of a finite chain, so it is the identity.
- So stabilizers are constant on open simplices, and Δ(P) is a G-CW complex with cells
  G/G_σ × Δ^k.
- A point in an open simplex σ is H-fixed iff Hσ = σ, iff every vertex of σ lies in P^H.
  So |Δ(P)|^H = |Δ(P^H)|, the full subcomplex.
- The same argument covers the cone K ∪ CX, with a G-fixed apex added as a new maximum
  over X.

**(K/A)^H = K^H/A^H (re-proved).**
- A point outside the G-subcomplex A keeps its stabilizer in K/A, and the base point is
  fixed. So the canonical map K^H/A^H → (K/A)^H is a continuous bijection.
- Both spaces are compact Hausdorff, so it is a homeomorphism.
- With the convention K/∅ = K_+, this is also right when A^H = ∅.

The quotient of a G-CW complex by a G-subcomplex is a G-CW complex. **Correct.**

---

## 3. Theorem E

### 3.1 §2.1, integral freeness

This was risk item 4.
- K = Δ(P_Z) is contractible: this is Lemma F(c) with H = 1 and Y = ℝ^d, so (C) is not
  even needed here. Hence ∂ : H_{d−1}(K, X) → H̃_{d−2}(X) is an isomorphism, and it is
  natural for simplicial G-maps.
- Every simplex of K not in X contains exactly one chamber, because chambers are pairwise
  incomparable maxima. So K = X ∪ ⋃_C C ∗ ∂_C with C ∗ ∂_C ∩ X = ∂_C, and
  K/X = ⋁_C Σ^u ∂_C.
- Each summand is ℤ by (C) for the single closed chamber. Step 5 of Theorem S gives the
  same thing without (C).
- g carries the summand of C to that of gC. Under a free action, {g u_i} is a ℤ-basis
  that G permutes freely. Signs are irrelevant: whatever generator g u_i is, h(g u_i) =
  (hg) u_i.

The identification with the (d − 2)-skeleton of Z is needed only to say "top cells =
chambers". The argument above uses only the simplicial pair (K, X). **Correct.**

**Why stably free is not enough.**
- T_s = ⋃_{H≠1} T^H is a finite union of contractible subcomplexes, closed under
  intersection, since T^H ∩ T^{H′} = T^{⟨H,H′⟩}. By the nerve lemma it is contractible.
- The reduced cellular chain complex of T/T_s is free over ℤG, of length k, and exact
  except in degree k. So H̃_k is projective and stably free.
- Stably free ℤG-modules need not be free: Swan, for generalized quaternion groups. This
  is cited from memory here, as in [E-note].

So the chamber basis is genuinely needed. **Correct as a remark.**

**COMPUTED** (free-test fields, [POS], [GEN]).
- H_{d−2}(T; ℤ) is the top cycle group. It is a direct summand of the chains, because the
  cokernel embeds in C_{d−3}.
- So H_{d−2}(T; ℤ) ⊗ 𝔽_p = Z_{d−2}(T; 𝔽_p). The script checks this by comparing the
  boundary rank mod p with the rank mod 1000003.
- A ℤG-free module restricts to a free 𝔽_p⟨g⟩-module for every g of order p^k. This
  holds iff dim ker(g − 1) = dim / p^k.
- This was tested for a representative of every conjugacy class of nontrivial
  prime-power-order elements: 351 tests on the posets, and every B_3 cone. There were no
  failures.

The test distinguishes ℤC_2 from ℤ_+ ⊕ ℤ_−, which have the same character, so it carries
integral information beyond the ℂ-statement of [Thm]. Controls:
- the orthant with S_3 and S_4 fails, with fixed dimension 1 ≠ 1/p;
- the two 2-chains fail (3 ≠ 5/2).

### 3.2 §2.2, d ≥ 4

- Hurewicz applies to the (k − 1)-connected T with k ≥ 2.
- Φ(g, i, s) = gφ_i(s) is well defined and a G-map.
- H_k(Φ) is ℤG-linear and sends a ℤG-basis to a ℤG-basis.
- Whitehead applies to simply connected complexes with homology only in degree k. The free
  wedge has (W_r)^H = {∗} for H ≠ 1.

**Correct.**

### 3.3 §2.3, d = 3

This was risk item 3.
- **T_s is a tree.** The induction is valid: the family {T^H : H ≠ 1} is closed under
  ⟨·,·⟩, every member is a tree, and a union of two subtrees meeting in a tree has
  χ = 1 and is connected. **Correct.**
- **Collapse.** Points outside T_s have trivial stabilizer, so (T/T_s)^H = {∗} for
  H ≠ 1. **Correct.**
- **Lifting.**
  - Admissibility rules out edge inversions, and edges outside T_s have trivial
    stabilizer, so every edge orbit is free.
  - For a tree edge from p to q ≠ p: if p ≠ [∗], exactly one edge of the orbit meets the
    chosen lift p̃.
  - **If p = [∗], every edge of the orbit meets ∗.** [E-note]'s "exactly one … (or
    p = [∗])" is wrong in that case. One simply chooses one. **R1 (FIXABLE, wording).**
  - The lift τ then has one vertex per free vertex orbit, and the proof of gτ ∩ τ = {∗}
    is correct. An edge in gτ ∩ τ would have both endpoints in it, so it would be a loop
    at ∗, and τ has none.
- **Final count.** #loops = rank H_1(T) = #V by [GT, Thm 1], so there are r loop orbits.
  **Correct.**

COMPUTED: T_s is acyclic (mod 2, 3, 1000003) for every free poset case (n ≤ 6) and every
B_3 cone with nontrivial stabilizer.

### 3.4 §2.4, d = 2

- |V| is a sector of angle < π. Its #V + 1 rays span distinct lines, because the cone is
  pointed.
- A finite group preserving a pointed sector permutes its two extreme rays. An element
  fixing both is the identity, since it has finite order and positive eigenvalues. So
  |G| ≤ 2, and the nontrivial element is a reflection.
- T ∖ {x_0} has free action, and H̃_0 = ker(augmentation) has free basis {t − x_0}.

**Correct.**

### 3.5 Poset case

- Aut(P) acts faithfully on ℝ^n/ℝ1 for n ≥ 3.
- It acts freely on Lin P for every finite P: σ·L = L forces σ to be an automorphism of
  a chain.
- lin C_P = ℝ1 iff P is connected.
- Λ(C_P) is the set of set partitions with acyclic quotient. [AUD] builds it as the zero
  sets of the faces of C_P instead, and the counts agree with #Lin P.

**Correct.**

COMPUTED ([POS]).
- 3 + 10 + 44 + 238 connected posets for n = 3, …, 6, of which 2 + 6 + 30 + 155 have
  |Aut P| > 1 (191 for 4 ≤ n ≤ 6, matching [E-note]).
- Every subgroup was checked: 1,390 pairs for 4 ≤ n ≤ 6, including H = 1 on all
  posets. That is 27 more than [E-note]'s 1,363, which skipped 27 large H = 1 cases.
- H ≠ 1: 1,199 pairs, all acyclic mod 2, 3, 5, 7, 1000003, with Stong core one point.
- H = 1: Betti numbers #Lin P in degree n − 3 only.

---

## 4. Theorem S and its consequences

### 4.1 Steps 1–5

This was risk item 5.
- **Steps 1–2.** These follow from F1 and Lemma F(c). Note that K^H ≠ ∅ for every H.
  **Correct.**
- **Step 3.** K ∪ CX is admissible, and both collapses are of contractible subcomplexes
  on every fixed set. Σ^u X = CX/X needs X ≠ ∅, which holds for d ≥ 2. **Correct.**
- **Step 4.** This is the decomposition of §3.1, now G-equivariantly:
  K/X ≅_G ⋁_{[C]} G_+ ∧_{G_C} (C ∗ ∂_C)/∂_C. **Correct.**
- **Step 5.**
  - The nonzero faces of A in C̄ are exactly the relatively open faces of the polyhedral
    cone C̄, a standard fact for chambers.
  - With a G-invariant inner product, g ∈ G_C maps extreme-ray unit vectors to
    extreme-ray unit vectors. So b(gF) = g b(F), and b(F) ∈ ri F (a positive combination
    of all generators of a pointed cone).
  - The choice of interior points b(F) gives a derived subdivision of the polytope
    Q = C̄ ∩ {φ = 1}. This is the standard homeomorphism Δ(proper faces) ≅ ∂Q, and it is
    equivariant because the b(F) are.
  - Radial projection from b(C) ∈ int Q commutes with G_C, since g b(C) = b(C) and g is
    orthogonal.
  - ker φ is a G_C-complement of ℝ p_C, so ker φ ≅ U_C. Finally Σ^u S(U) ≅_G S^U.

  **Correct.** **R2:** "simplicial-type cone" should be deleted, because chambers of a
  general arrangement are not simplicial. Nothing uses simpliciality.
- **(S1).** (S^{U})^H = S^{U^H}, and U_C^H = Fix(H)/ℝp_C by exactness of fixed points
  over ℝ. The H-fixed summands are indexed by the chambers fixed by H. **Correct.**
  - When e_H = 1, Fix(H) is a line, and a line meets the interiors of at most 2 chambers,
    which are opposite. Pointedness allows only one of them in V, so m_H ≤ 1, consistent
    with Σ^u.
  - [AUD] confirms (S1) on every pair it computed. In 37 non-free type-A groups
    G = ⟨Aut P, −α⟩ (α an anti-automorphism, chosen so that some g ≠ 1 fixes a
    chamber), 58 pairs have H ≠ 1 fixing a chamber.
- **(S2), (S3).** Correct.
  - (S3) uses that the suspension isomorphism is G-equivariant, which holds because G
    fixes both cone points.
  - det = (−1)^{d − e_g} for a finite-order orthogonal g, matching the Lefschetz numbers.
- **(S4), e_H ≥ 4 and e_H ≤ 2.** Correct.
  - For e_H ≥ 4: K^H is X^H with m_H cones attached along spheres S^{e_H−2}, which are
    simply connected. So π_1(X^H) = π_1(K^H) = 1 by van Kampen, since X^H is connected
    (degree e_H − 2 ≠ 0).
  - For e_H = 2: X^H is ≤ 1-dimensional, so it is a graph determined by its homology.

### 4.2 (S4) with e_H = 3 closes

**Claim.** If e_H = 3, then T^H ≃ ⋁^{m_H} S^1.

*Proof.*
- **X^H is planar.** By Lemma F(b), Q′^H is a down-closed subposet of the faces of A^U in
  K = |V| ∩ U, with U = Fix(H) and dim U = 3. K is a pointed cone, so its slice
  K ∩ {φ = 1} is a convex polygon in an affine plane, subdivided into convex cells by
  A^U. Placing a vertex at a relative-interior point of each cell realizes X^H = Δ(Q′^H)
  as a straight-line 2-dimensional subcomplex L of the plane.
- **L collapses to a graph.** Let D be the union of the closed 2-simplices of L, and let Ω
  be the unbounded component of ℝ^2 ∖ D. ∂Ω is a nonempty union of edges of D. An edge
  e ⊆ ∂Ω has Ω on one side, so it lies in exactly one 2-simplex. So e is a free face, and
  an elementary collapse removes that 2-simplex. Induct on the number of 2-simplices.
- **Conclusion.** L is a connected graph (H̃_0 = 0 by (S1), since e_H − 2 = 1) with
  H_1 = ℤ^{m_H}. So T^H ≃ X^H ≃ ⋁^{m_H} S^1. ∎

So (S4) holds for every e_H, and the only open homotopy question left in [E-note] is
Question E♯ (desuspension), which this audit does not address.

---

## 5. The necessity examples

- **Orthant ℝ^3, S_3** (HOLDS).
  - T is the hexagon. T^{S_3} = T^{A_3} = ∅, and T^{⟨(12)⟩} = {span e_3, span(e_1, e_2)}
    ≅ S^0.
  - T ≅_G S(U) is step 5 itself, since V is a single chamber.
  - [AUD] shows Theorem S holds on 6/6 subgroups, and the Theorem E prediction fails on
    5/6. For S_4 on ℝ^4: Theorem S holds on 30/30, and the prediction fails on 29/30.
- **Π̄_4, S_4** (FIXABLE, R3).
  - T ≃ ⋁^6 S^1 and 24 ∤ 6: correct.
  - The 6 subgroups H ≠ 1 with T^H not acyclic are the three ⟨(ab)(cd)⟩ and V_4, where
    T^H has three components, so H̃_0 = ℤ^2, and A_4 and S_4, where T^H = ∅.
  - For a **transposition** (12), the stable proper partitions are
    12|3|4, 1|2|34, 12|34, 123|4, 124|3. The only relation not involving 12|3|4 is
    1|2|34 < 12|34, so T^H is a tree, which is contractible.
  - So "for a transposition, H̃_1(T^H) = ℤ^2" is wrong in both the subgroup and the
    degree. [E-script]'s own output reads [0, 2, 0], i.e. H̃_0 = ℤ^2, on order-2
    subgroups.
  - Replace it with: "for H = ⟨(12)(34)⟩, T^H has three components, so H̃_0(T^H) = ℤ^2."
    The necessity claim is unaffected.
- **Two 2-chains, swap** (HOLDS).
  - Betti numbers (0, 0, 5) and H̃_0(T^g) = ℤ were recomputed. e_g = 1, and T^g ≅ S^0.
  - 𝔽_2-freeness fails, with fixed dimension 3 on a 5-dimensional H_1.

---

## 6. [E-script] (risk item 6)

The script was read, not run or imported.
- `covectors_from_normals` builds covectors as compositions of cocircuits (the rays).
  This is the standard oriented-matroid description of the covector set, so it is
  correct.
- `hyperplane_action` uses n ↦ Mn for orthogonal M, and `act` uses
  σ_{gx}(t) = ε σ_x(e). These are consistent.
- `Cone.faces` takes the covectors conformal to a chamber of V, which is "F ⊆ |V|".
- `all_subgroups` iterates joins with cyclic subgroups until closure. This is complete,
  because every subgroup is a finite join of cyclic subgroups, and each partial join is
  reached.
- [AUD] uses a different enumeration (BFS over ⟨K, g⟩ from the trivial group) and gets
  the same counts: S_3: 6, S_4: 30, W(B_3): 98, and the per-cone counts behind 744 and 480.
- The Stong core is computed only where contractibility is predicted, and that is the
  right place.

No defect found.

---

## 7. Required revisions

- **R1** (§2.3). Replace "exactly one edge of that orbit is incident to the chosen lift
  of p, because G acts freely … (or p = [∗])" with: "choose an edge of that orbit
  incident to the lift of p. It is unique if p ≠ [∗], and if p = [∗] any of the |G|
  edges will do."
- **R2** (Theorem S step 5). Delete "a simplicial-type cone". Chambers need not be
  simplicial, and nothing uses it.
- **R3** (§3.3). Replace the transposition example as in §5 above.
- **Optional.**
  - (S4) e_H = 3 can be moved from OPEN to PROVEN by §4.2.
  - In (W), cite May CBMS 91, Cor. I.3.3, and drop the cellularity remarks.
  - In Lemma F(c), add the one-line "⇐" for F ⊆ |V| ∩ Y (§1.1).

---

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process, imports nothing
from the repo):

    python3 audit_theorem_e.py --nmax 6 > output/audit_theorem_e.txt   # ~2.5 min, ends "ALL AUDIT CHECKS PASS: True", exit 0
    python3 audit_theorem_e.py --nmax 4 --quick                        # ~3 s, skips Lemma F sampling
    python3 -m unittest test_audit_theorem_e                           # controls

Output tags:
- `[CTL]`: instrument controls. Subgroup counts 6/30/98; RP^2 torsion is seen mod 2 and
  not mod 3; the crown's Stong core is not a point.
- `[NEG]`: positive controls that must fail Theorem E: the non-free orthants, Π̄_4, and
  the two 2-chains.
- `[GEN]`: Boolean and B_3.
- `[LEMF]`: Lemma F, including the non-pointed control.
- `[POS]`: type A, free.
- `[NONFREE]`: type A, G = ⟨Aut P, −α⟩.

Homology is computed modulo 2, 3, 5, 7 and 1000003. Contractibility is certified by a
Stong core of one point.
