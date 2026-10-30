# Cone/lune Lie theory for the order cone C_P

Work item: mg-3ab4a. This addresses the program in the seed note, §"Potential
proof via hyperplane-arrangement Lie theory", steps 1–4, as re-scoped after
`notes/literature_novelty_jks_maps.md` (the "literature note"). Conjecture S
is now proved in `notes/conjecture_s_splitting_cycles_span.md` (the
"Conjecture S note"). Its Theorems A, B, C are used below and referred to by
those names.

Every claim is tagged PROVEN, COMPUTED, CITED or CONJECTURED.

Audited in `notes/audit_cone_lune_lie_theory.md` (mg-52a16). The hypothesis
"essential" (assumed in §1) is now stated in the headings of §§3, 5, 7, and
the tags of Theorem 4.1(c) and (G3) now carry their conditions (audit rows 9
and 12). No mathematics was changed.

## Verdict

| Step | Verdict |
|---|---|
| 1. F(P) as the LRB of C_P | **Applies directly** (PROVEN, §2). F(P) is exactly the set of braid faces in C_P, and it is a sub-left-regular band of the Tits monoid. The same holds for every top-cone of every real arrangement. |
| 2. Support semilattice = OP(P) | **Applies directly** (PROVEN, §2). |
| 3. A "maximal-support Lie/Peirce component" for the cone | **Does not apply.** (i) Aguiar–Mahajan have no cone theory (literature note §4.3). (ii) The intrinsic LRB analogue, built from F(P) acting on its own chambers, is **zero** for every proper order cone (PROVEN for the chain, COMPUTED in general, §6). It cannot produce H_P, which is nonzero. The correct object is ambient: the restriction of the arrangement's Lie[A] to the chambers of the cone. |
| 4. Inclusion lands on W_P e_ζ | **Does not apply with that target** (literature note, Prop. C). **Applies with target "W_P modulo top-lunes"**, after Lemma L (§3). This is exactly Theorem C of the Conjecture S note, restated in lune language as Theorem 4.1. |

The cone-restriction statement needed in step 4 is isolated in §4:

> Γ_V ∩ Lune = span{top-lunes contained in V},

together with dim H̃_top(Λ(V)) = dim Γ_V/(Γ_V ∩ Lune). For the order cones of
the braid arrangement this is PROVEN (it is Theorem B / C of the Conjecture S
note). New here:

- **§3, Lemma L (PROVEN, any finite real central essential arrangement).** A top-lune L(H, D) lies in a
  top-cone V iff D ∈ V and H lies in the lineality space of V. For C_P this
  means the blocks of H are unions of components of P.
- **§5, Lemma E and Theorem 5.2 (PROVEN, any finite real central essential arrangement).**
  - Restriction to a hyperplane maps lunes to lunes.
  - Consequently, the chambers of a **pointed** top-cone are linearly
    independent modulo top-lunes.
  - For the braid arrangement this is the connected case (Cor. A′) of the
    Conjecture S note, with a geometric proof.
- **§5.3, Conjecture G (CONJECTURED; COMPUTED for every top-cone of A_2, A_3,
  A_4, B_2, B_3, several non-reflection arrangements, and samples of D_4,
  B_4).** The cone-restriction statement holds for every top-cone of every
  real central arrangement. Moreover the chamber cycles of V span
  H̃_top(Λ(V)), which is the general form of Conjecture S.
- **§7, corrected Topics Ex. 10.9 (PROVEN, any finite real central essential arrangement).** z is Lie
  iff its coefficient sum vanishes on every **non-pointed** top-cone. The
  printed "non-singleton top-cone" is false (literature note §4.2), and
  pointedness is the exact dividing line.

## 1. Conventions

These are the standard conventions (Aguiar–Mahajan, *Topics in Hyperplane
Arrangements*, Chs. 1–3, as read in the literature note §4.1).

- **Arrangement.** A is a finite central arrangement in R^d, and we assume it
  is essential. A face is given by its sign vector (covector) X ∈ {0, +, −}^A.
- **Tits product.** (XY)_e = X_e if X_e ≠ 0, and Y_e otherwise. The faces
  form the Tits monoid Σ[A], a left regular band (LRB): XX = X and XYX = XY.
  The central face O is the identity.
- **Order and support.** X ≤ Y iff X is a face of Y (X_e ∈ {0, Y_e}). The
  support of X is the flat spanned by X. We record it by its zero set z(X).
- **Chambers.** Chambers are the faces with no zero entry. Γ[A] is their
  linear span.
- **Top-cone.** A top-cone V is a nonempty set of chambers of the form
  {C : C_e = s_e for e ∈ S}. Write S_max(V) for the set of all e on which V
  has constant sign. The closed cone |V| is the union of the closed chambers
  of V. The faces of V are the faces contained in |V|:
  F(V) = {X : X_e ∈ {0, s_e} for e ∈ S_max}.
- **Lineality.** lin(V) = |V| ∩ −|V| = ∩_{e ∈ S_max} h_e. V is **pointed**
  if lin(V) = 0.
- **Top-lune.** For a face H and a chamber D ≥ H, the top-lune is
  L(H, D) = {C : HC = D}. Equivalently, it is the set of chambers C with
  C_e = D_e for all e ∈ z(H). It depends only on the flat z(H) and on
  D|_{z(H)}. It is a singleton iff H = O.
- **Every class is a lune (PROVEN).** For every flat Z ≠ A and every chamber
  D, the class {C : C|_Z = D|_Z} is a top-lune.
  - Pick a face H with z(H) = Z.
  - Then HD is a chamber with HD ≥ H and (HD)|_Z = D|_Z.
  - So the class is L(H, HD).
  - The code uses this description: one class per flat Z ≠ A and per sign
    pattern on Z.
- **Lune span.** Lune = span{Σ_{C ∈ L} C : L a non-singleton top-lune} ⊆ Γ[A].
  - Aguiar–Mahajan's Ree criterion (Topics Lemmas 10.7–10.8, CITED via the
    literature note §4.2) says Lie[A] = Lune^⊥ for the form
    ⟨C, C′⟩ = δ_{CC′}.
  - So Γ/Lune = Lie[A]^*, and for V ⊆ chambers,
    (Γ_V + Lune)/Lune ≅ Γ_V/(Γ_V ∩ Lune) ≅ (Lie[A]|_V)^*.
  - Here Γ_V = span V, and Lie[A]|_V is the image of Lie[A] under
    restriction of coefficients to V.
  - Write q(V) := dim Γ_V/(Γ_V ∩ Lune).
- **Lie as a kernel.** Lie[A] = {z ∈ Γ : Hz = 0 for all H ≠ O} (PROVEN, by
  unwinding). The coefficient of D in Hz is Σ_{C : HC = D} x_C, so this is
  Topics Lemma 10.5 as quoted in the literature note §4.2.

**Braid arrangement.**
- A face is an ordered set partition (composition) F = (F_1 | ⋯ | F_k) of
  [n]. It is the cone {x constant on blocks, x|_{F_i} < x|_{F_j} for i < j}.
- FG = (F_1 ∩ G_1 | F_1 ∩ G_2 | ⋯ | F_k ∩ G_l), with empty blocks deleted.
- The chambers are the words w.
- For H = (B_1 | ⋯ | B_k) ≤ D, the top-lune L(H, D) is the set of shuffles of
  the words D|_{B_1}, …, D|_{B_k}. So Lune = Sh_n (literature note §4.2).
  2-block shuffles suffice, since s_1 ш s_2 ш s_3 = Σ_{x ∈ s_1 ш s_2} x ш s_3.

## 2. Steps 1–2: the LRB of a cone and its support semilattice

**Proposition 2.1 (PROVEN).** Let P be a poset on [n] and
C_P = {x : x_i ≤ x_j whenever i <_P j}.

- (a) A braid face F lies in C_P iff the block-index map
  β_F : [n] → [k] (i ↦ the block containing i) is isotone. So the faces in
  C_P are exactly the elements of F(P) = ⊔_k Sur_iso(P, [k]). The chambers in
  C_P are Lin(P).
- (b) F(P) is a submonoid of the Tits monoid Σ_n: it contains O = ([n]) and
  is closed under the Tits product. It is therefore a sub-LRB.
- (c) The chambers Lin(P) form a two-sided ideal of F(P): FC is a chamber
  and CF = C. In particular Γ_{C_P} = W_P is a left F(P)-module.

*Proof.*
- (a) The points of F satisfy x_i ≤ x_j iff β_F(i) ≤ β_F(j). So F ⊆ C_P iff
  i <_P j implies β_F(i) ≤ β_F(j).
- (b) β_{FG}(i) corresponds to the pair (β_F(i), β_G(i)) under the
  lexicographic order. If i <_P j, then both coordinates weakly increase, so
  the pair weakly increases lexicographically. β_O is constant, hence
  isotone.
- (c) This is standard for any LRB: chambers are the faces C with CX = C for
  all X. ∎

The same holds for any top-cone V of any real arrangement (PROVEN):
- Let x ∈ X and y ∈ Y with X, Y ⊆ |V|. For small ε > 0, the point x + εy
  lies in XY.
- That point lies in the convex cone |V|.
- |V| is a union of faces, so XY ⊆ |V|.

**Proposition 2.2 (PROVEN).** The support semilattice of the LRB F(P) is
OP(P). Its bottom is the one-block partition (the support of O), its top is
the partition into singletons (the support of a chamber), and its join is
common refinement.

*Proof.*
- **Brown's support semilattice.** For an LRB B, Brown's support semilattice
  Λ(B) is B modulo x ~ y ⟺ (xy = x and yx = y), with supp(xy) =
  supp(x) ∨ supp(y). (CITED: K. S. Brown, *Semigroups, rings, and Markov
  chains*, J. Theoret. Probab. 13 (2000), §1 / Appendix B. Read from memory;
  the section number was not re-checked. Only the definition is used.)
- **In the Tits monoid,** xy = x and yx = y iff x and y have the same
  underlying set partition. The relation on the sub-LRB F(P) is the
  restriction of this one.
- **So Λ(F(P)) is the image of F(P) under F ↦ {F_1, …, F_k}.** That image is
  the set of kernels of surjective isotone maps P → [k].
- **These kernels are exactly OP(P).** π is a kernel iff P/π is acyclic: take
  a linear extension of the quotient order. This is the seed note's
  definition of OP(P), and Jenča–Sarkoci Thm 3.3.
- **The join** is supp(FG), the common refinement. ∎

For a general top-cone V we write Λ(V) for the poset of flats z(X),
X ∈ F(V). It is bounded, with bottom z(O) = A and top z(C) = ∅. For V = C_P
we have Λ(V) = OP(P) and H̃_top(Λ(V)) = H_P.

## 3. Which top-lunes lie in a top-cone

**Lemma L (PROVEN, any finite real central essential arrangement).** Let V be a top-cone,
H ≠ O a face and D ≥ H a chamber. Then

    L(H, D) ⊆ V   ⟺   D ∈ V and H ⊆ lin(V)   ⟺   D ∈ V and S_max(V) ⊆ z(H).

*Proof.*
- H ⊆ lin(V) = ∩_{e ∈ S_max} h_e iff H_e = 0 for all e ∈ S_max. This gives
  the second equivalence.
- (⇐) Let C ∈ L(H, D). Then C_e = D_e for e ∈ z(H) ⊇ S_max, and D ∈ V. So
  C_e = s_e on S_max, i.e. C ∈ V.
- (⇒) D ∈ L(H, D) ⊆ V.
  - Suppose some e ∈ S_max has H_e ≠ 0. Then H_e = D_e = s_e.
  - Let H̄ = −H be the opposite face. The chamber D′ = H̄D satisfies
    D′_f = D_f on z(H), so D′ ∈ L(H, D).
  - But D′_e = H̄_e = −s_e, so D′ ∉ V, a contradiction. ∎

**Corollary 3.1 (PROVEN, braid).**
- lin(C_P) consists of the compositions whose blocks are unions of connected
  components of P. So C_P is pointed iff P is connected.
- The top-lunes contained in C_P are exactly the shuffles s_1 ш ⋯ ш s_k,
  where s_i ∈ Lin(P|_{B_i}) and B_1, …, B_k are disjoint unions of components
  covering [n], with k ≥ 2.
- Their span is R_P, as defined in the Conjecture S note §1.

*Proof.*
- H and H̄ (blocks reversed) both lie in C_P iff no comparable pair of P is
  split between two blocks of H, i.e. iff every block is a union of
  components. Then apply Lemma L.
- These shuffles span R_P, since k = 2 suffices (§1). ∎

(COMPUTED: Lemma L holds for every flat, every chamber and every top-cone in
the arrangements of §8, check `[lin]`.)

## 4. Step 4 in lune language

**Theorem 4.1 (this is a restatement of Theorems B and C of the Conjecture S
note).** For every finite poset P (status per part: (a), (b), (d) PROVEN;
(c) PROVEN given Prop. Φ, Lemma D and J–S Thm 4.5, exactly as Theorem C is):

- (a) Γ_{C_P} ∩ Lune = span{top-lunes contained in C_P}.
  - By Cor. 3.1 the right-hand side is R_P. The left-hand side is
    W_P ∩ Sh_n = K_P. So (a) is K_P = R_P, which is Theorem B.
- (b) q(C_P) = e_C(P) = dim H_P (Theorem B with Jenča–Sarkoci Thm 4.5).
- (c) The isomorphism Φ : H̃_{n−3}(Π̄_n) ⊗ sgn → Γ/Lune of the literature
  note (Prop. Φ, the transpose of Wachs's correspondence) restricts to an
  isomorphism

      H_P ⊗ sgn  →  (Γ_{C_P} + Lune)/Lune  ≅  (Lie_n|_{Lin P})^*.

  - In words: under JKS, the inclusion of the cone's support lattice
    OP(P) ↪ Π_n corresponds to restricting Lie elements to the chambers of
    the cone.
  - This is the correct form of step 4 (Theorem C).
- (d) For connected P (C_P pointed), Lie_n → C^{Lin P} is onto.

What is *not* verified: whether Φ agrees, up to a scalar, with Aguiar–Mahajan's
Topics Thm 14.32 isomorphism specialized to the braid arrangement. The
literature note identifies Φ only with Wachs's maps.

The proofs of Theorems A–C are elementary word combinatorics. §5 recasts the
key step geometrically.

## 5. Beyond the braid arrangement

### 5.1 Restriction maps lunes to lunes

Fix a hyperplane h ∈ A with a chosen positive side. The restriction A^h is
the arrangement {h ∩ h′ : h′ ≠ h} in h, which is again essential. Its
chambers are the faces F of A with z(F) = {h}. Define

    E_h : Γ[A] → Γ[A^h],   E_h(C) = C_h · F  if C has a facet F on h,  and 0 otherwise.

For the braid arrangement and h = {x_a = x_x}, A^h is the braid arrangement
on [n] ∖ x, and E_h is the contraction E_{a,x} of the Conjecture S note §2,
up to a global sign.

**Lemma E (PROVEN, any finite real central essential arrangement).** Let H ≠ O and D ≥ H.

- If h ∉ z(H), then E_h(L(H, D)) = 0.
- If h ∈ z(H), then E_h(L(H, D)) = D_h · Σ{F : F a chamber of A^h,
  F_e = D_e for all e ∈ z(H) ∖ h}. The set on the right is either empty or a
  non-singleton top-lune of A^h.
- Hence E_h(Lune[A]) ⊆ Lune[A^h].

*Proof.*
- **Facets.** A chamber C has a facet on h iff F := C with C_h replaced by 0
  is a face. Then F is a chamber of A^h, and its two neighbours are C and
  C′ = C with C_h negated.
- **Case h ∉ z(H).** The lune is defined by conditions on z(H), and h is not
  among them. So C ∈ L iff C′ ∈ L. The two terms ±F cancel.
- **Case h ∈ z(H).** Every C ∈ L has C_h = D_h. Let F be a chamber of A^h.
  Its neighbour on the D_h side is in L iff F_e = D_e for e ∈ z(H) ∖ h.
  - A chamber F of A^h has F_e ≠ 0 for every e ≠ h, so its signs on the
    other hyperplanes are those of its neighbours.
  - The hyperplanes of A^h containing the flat s = span(H) ⊆ h are the
    h ∩ e with e ∈ z(H) ∖ h, because e ∩ h ⊇ s iff e ⊇ s.
  - So the set described is the top-lune of A^h attached to the flat s ≠ 0,
    if it is nonempty. ∎

(COMPUTED: the exact formula of Lemma E, for every h, every flat and every
chamber, in all arrangements of §8, check `[E_h]`.)

### 5.2 Pointed cones

**Theorem 5.2 (PROVEN, any finite real central essential arrangement).** If V is a pointed
top-cone, its chambers are linearly independent modulo Lune:
Γ_V ∩ Lune = 0, so q(V) = |V|. Equivalently, every function on the chambers
of V is the restriction of a Lie element.

*Proof.* Induction on d = rank A.
- **d = 0.** There is one chamber and no non-singleton lune, so Lune = 0.
- **d ≥ 1.** Let X = Σ_{C ∈ V} c_C C ∈ Lune, and extend c by 0 off V.
- Let h be a hyperplane containing a facet F of some chamber of V.
  - Then |V| ∩ h is full-dimensional in h. It is a top-cone V^h of A^h,
    whose chambers are the facets on h of chambers of V. A point in the
    relative interior of such an F lies in |V|, so one of the two chambers
    adjacent to F is in V.
  - V^h is pointed: lin(V^h) = lin(V) ∩ h = 0.
  - By Lemma E, E_h(X) ∈ Lune[A^h]. It is supported on V^h. By induction
    E_h(X) = 0.
  - Reading off the coefficient of F gives c_C = c_{C′} for the two chambers
    C, C′ adjacent along F.
- **Conclusion.**
  - If F is an interior wall of V, then c is equal on both sides.
  - If F is a boundary wall (C′ ∉ V), then c_C = 0.
  - The chamber graph of the convex set |V| is connected. Since d ≥ 1 and V
    is pointed, V is not all of R^d, so V has a boundary wall.
  - Hence c ≡ 0. ∎

For the braid arrangement this is Cor. A′ of the Conjecture S note: connected
P gives W_P ∩ Sh_n = 0. The two proofs are the same argument: their (★) plus
"adjacent swaps connect Lin P" is the wall-crossing above.

### 5.3 The general conjecture

For a non-pointed V, Lemma L gives the obvious relations: the lunes of flats
Z ⊇ S_max(V). Each of them lies in one class of the lineality flat, so
Γ_V = ⊕_K Γ_K over the lunes K of that flat.

**Conjecture G (CONJECTURED; COMPUTED, §8).** For every top-cone V of every
real central arrangement:

- (G1) Γ_V ∩ Lune = span{top-lunes contained in V}.
- (G2) The reduced homology of the proper part of Λ(V) is concentrated in
  degree d − 2, and q(V) = dim H̃_{d−2}(Λ(V)) = |μ_{Λ(V)}(bottom, top)|.
- (G3) For each chamber C, Λ(C) is the face lattice of the cone C, so its
  proper part is a (d − 2)-sphere. Let ρ_C be its fundamental cycle. Then
  {ρ_C : C ∈ V} spans H̃_{d−2}(Λ(V)). This is "Conjecture S for cones".
- (G4, not tested) Aguiar–Mahajan's isomorphism (Topics Thm 14.32) restricts
  to H̃_{d−2}(Λ(V)) ⊗ E^o ≅ (Lie[A]|_V)^*, as Φ does in Theorem 4.1(c).

Status:
- **Braid arrangement.** (G1) and (G2) are PROVEN: they are Theorem 4.1
  together with Jenča–Sarkoci. (G3) is Conjecture S, and is PROVEN given
  Prop. Φ, Lemma D and J–S Thm 4.5.
- **Pointed V.** (G1) is PROVEN by Theorem 5.2. (G2) then reads
  #chambers(V) = |μ(Λ(V))|, a Zaslavsky-type count for pointed cones; it is
  COMPUTED only.
- **Missing in general.** The analogue of the Conjecture S note's
  first-block basis B_P and of its straightening Lemma 6, for the lunes of
  the lineality flat. With them, the argument of Theorem 5.2 would give
  (G1). That is the precise lemma whose absence keeps the general statement
  conjectural.

## 6. LRB representation theory does not see H_P

- **Brown's eigenvalue multiplicities (CITED from memory; Brown 2000 as
  above, main theorem on eigenvalues of LRB random walks; Brown–Diaconis,
  Ann. Probab. 26 (1998), for arrangements).**
  - For an LRB B with chambers, the composition factors of the chamber
    module are the characters χ_X (X ∈ Λ), with χ_X(b) = [supp b ≤ X].
  - Their multiplicities m_X satisfy Σ_{Y ≥ X} m_Y = c_X, where c_X is the
    number of chambers above a fixed element of support X.
  - Hence m_X = Σ_{Y ≥ X} μ(X, Y) c_Y.
- **Bottom component.** The bottom character χ_⊥ kills every b ≠ O.
  - So the "Lie part" {z : bz = 0 for all b ∈ B ∖ O}, which is Aguiar–Mahajan's
    Lie[A] when B = Σ[A], is a sum of copies of χ_⊥.
  - Its dimension is at most m_⊥.
  - For the full arrangement m_⊥ = |μ(Π[A])| = dim Lie[A] (Brown–Diaconis).
- **Intrinsic cone version.** For B = F(V) acting on Γ_V, define
  Lie^int(V) = {z ∈ Γ_V : Hz = 0 for all H ∈ F(V) ∖ O}.
  - **PROVEN for the chain** P = 1 < 2 < ⋯ < n (n ≥ 2). V is one chamber w,
    and Ow = w while Hw = w ≠ 0 for every H ∈ F(V). So Lie^int(V) = 0,
    whereas H_P is 1-dimensional.
  - **COMPUTED.** m_⊥(Γ_V) = Σ_X μ(⊥, X) c_X = 0 for **every** proper
    top-cone in every arrangement of §8. This is the `[brown]` line
    "m_bottom = 0 or V = all: N/N". The full cone gives m_⊥ = |μ| = q. So
    Lie^int(V) = 0 for every tested proper cone. A copy of χ_⊥ inside Γ_V
    is a composition factor, so dim Lie^int(V) ≤ m_⊥.
  - **CONJECTURED.** This holds for every proper top-cone.
- **Interpretation.** The relations that cut W_P down to H_P are the
  top-lunes inside C_P. By Lemma L these are the H-fibres for H in the
  lineality space. Recognizing those uses the opposite involution H ↦ H̄ of
  the ambient arrangement, which the abstract LRB F(P) does not carry.
  - The naive intrinsic relations (H-fibres within V, for every H ∈ F(V))
    are too many.
  - So LRB theory of F(P) alone (Brown; Saliola's quiver and Ext results, for
    which see Saliola, *The quiver of the semigroup algebra of a left regular
    band*, IJAC 17 (2007); Saliola, *The face semigroup algebra of a
    hyperplane arrangement*, Canad. J. Math. 61 (2009);
    Margolis–Saliola–Steinberg, JEMS 17 (2015) — CITED from memory, no
    result of theirs is used) is not the right framework for step 3.
  - The ambient Tits algebra is.
  - Whether the order complex of Λ(F(P)) = OP(P) shows up as an Ext group of
    kF(P) (as top homology of support semilattices does in the
    Saliola / Margolis–Saliola–Steinberg theory) was **not** investigated.
    It would not change the verdict, since the module carrying H_P is not
    intrinsic to F(P).

## 7. Correcting Topics Exercise 10.9

The literature note §4.2 shows that Topics Ex. 10.9, as printed ("z ∈ Lie[A]
iff its coefficient sum vanishes on every non-singleton top-cone"), is false
for the braid arrangement at n = 3. The cone {x_1 ≤ x_2, x_1 ≤ x_3} is a
counterexample. Lemma L and Theorem 5.2 give the exact repair.

**Proposition 7.1 (PROVEN, any finite real central essential arrangement).**
- (a) The chamber sum of a top-cone V lies in Lune iff V is not pointed.
- (b) Hence z ∈ Lie[A] iff the coefficient sum of z vanishes on every
  non-pointed top-cone.

*Proof.*
- (a) Suppose V is not pointed.
  - Let Z = {e : h_e ⊇ lin(V)}. This is the zero set of a face in the
    relative interior of lin(V), and it is a flat ≠ A containing S_max(V).
  - V is a union of classes "C|_Z = const". Each class is a non-singleton
    top-lune (§1), and it is contained in V by Lemma L.
  - So the chamber sum of V lies in Lune. If V is pointed, Theorem 5.2 says its
  chamber sum is nonzero modulo Lune.
- (b) Every non-singleton top-lune is a non-pointed top-cone (its lineality
  contains span H ≠ 0). Conversely every non-pointed top-cone sum lies in
  Lune by (a). Then use Lie = Lune^⊥ (Lemma 10.7). ∎

For the braid arrangement, "non-pointed" means "P disconnected", in
agreement with the literature note's observation.

## 8. Computations (COMPUTED)

Script: `compute/cone_lie.py` (plain Python 3, no dependencies). Tests:
`compute/test_cone_lie.py`.

The script works for an arbitrary list of integer normals:
- cocircuits are computed from exact rational nullspaces;
- covectors are the closure of {O} under the Tits product with cocircuits
  (every covector is a composition of cocircuits: standard oriented-matroid
  fact, e.g. Björner–Las Vergnas–Sturmfels–White–Ziegler, *Oriented
  Matroids*, Ch. 3; the section was not re-checked);
- Lune is computed directly from lune indicator vectors, with no use of Ree
  or Φ.

Positive controls on the face enumeration:
- A_2, A_3, A_4 have 13, 75, 541 faces (the Fubini numbers);
- B_2 and B_3 have 17 and 147 faces;
- the generic arrangement of 5 planes in R^3 has 22 chambers.

Arrangements: A_2, A_3, A_4 (braid, n = 3, 4, 5, essentialized); B_2; B_3;
D_4 and B_4 (150 sampled top-cones each); generic 5 and 6 planes in R^3; a
random non-generic 7-plane arrangement in R^3; a random 6-hyperplane
arrangement in R^4. The last four are not reflection arrangements and have
non-simplicial chambers.

| arrangement | top-cones | pointed |
|---|---|---|
| A_2 | 19 (all) | 12 |
| A_3 | 219 (all) | 146 |
| A_4 | 4231 (all) | 3060 |
| B_2 | 33 (all) | 24 |
| B_3 | 941 (all) | 778 |
| D_4 | 150 (sample) | 81 |
| B_4 | 150 (sample) | 98 |
| generic 5 in R^3 | 163 (all) | 112 |
| generic 6 in R^3 | 337 (all) | 264 |
| random 7 in R^3 | 491 (all) | 392 |
| random 6 in R^4 | 579 (all) | 340 |

The counts 19, 219, 4231 are the numbers of labeled posets on 3, 4, 5
elements (OEIS A001035). This is a positive control that every top-cone of
the braid arrangement is an order cone (Topics §2.7, via the literature
note).

Every check passed on every cone listed (`compute/output/cone_lie.txt`):
- **[Lune]** rank_p(Lune) = #chambers − |μ(flat lattice)|.
- **[E_h]** Lemma E's exact formula.
- **[lrb]** F(V) is closed under the Tits product.
- **[lin]** Lemma L, for every flat and chamber.
- **[K]** (G1).
- **[q]** (G2), including concentration in top degree. The homology part was
  not run for B_4, only q = |μ|.
- **[rho]** (G3), not run for B_4.
- **[pointed]** q = #chambers for pointed V.
- **[full]** q = |μ| for V = all chambers.
- **[brown]** For §6 (reported, not asserted).

Cross-check (`test_braid_q_equals_e_C`): for all 219 top-cones of A_3 the
script's q(V) equals e_C(P), computed by the independent cyclic-class code in
`poset_jks_check.py`.

Rigour of the ranks (prime p = 2^31 − 1):
- **Lune.** Its p-rank is pushed to #chambers − |μ|, which is its rational
  dimension (CITED: Aguiar–Mahajan, Topics Thm 14.32 / Prop. 14.25 with
  Lemma 10.7). So the p-basis is a Q-basis.
- **q.** q_p ≤ q_Q. When [K] passes, rank_Q(lunes in V) ≥ |V| − q_p ≥
  |V| − q_Q = dim_Q(Γ_V ∩ Lune) ≥ rank_Q(lunes in V). So q_p = q_Q, and (G1)
  holds over Q.
- **Homology.** p-Betti numbers are ≥ rational ones, and the Euler
  characteristic does not depend on the field. So concentration mod p
  implies concentration over Q with the same top Betti number |μ|.
- **[rho].** rank_p ≤ rank_Q ≤ dim H_top, so equality mod p gives equality
  over Q.

Positive controls in `test_cone_lie.py`:
- the predicate "D ∈ V" alone fails Lemma L on a half-space of A_2;
- corrupting one chamber's sign vector breaks Lemma E;
- m_⊥ equals |μ| for the full B_2 and 0 for a single chamber;
- a 4-cycle has a one-dimensional cycle space.

## Reproduce

From `compute/`:

    python3 cone_lie.py --quick                    # ~7 s, skips A4, D4, B4
    python3 cone_lie.py > output/cone_lie.txt      # all arrangements
    python3 -m unittest test_cone_lie              # < 1 s

Both runs end with `ALL CHECKS PASSED` (exit 0).
