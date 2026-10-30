# The cone theory for oriented matroids: T-convex sets of topes

This note lifts the cone theory of `notes/general_theory.md` §1 ("[GT]")
from real hyperplane arrangements to oriented matroids (OMs), including
non-realizable ones. The statements are Theorem 1 (wedge of spheres),
Theorem 2 (Zaslavsky count) and Theorem C / G\* (chamber cycles span; q = m;
the det-twisted module identity). The real-case proofs are in [GT] §§0–1,
[AudA] = `notes/audit_general_theory_cones.md` §C (Props. A, B and
Theorem C) and [AudC] = `notes/audit_theorem_c.md`. Prior art already
recorded in [NovGT] = `notes/novelty_general_theory.md` is not repeated.

Tags, as in [GT]: **PROVEN** (full proof here, cited inputs named),
**COMPUTED** (by `compute/oriented_matroid_cones.py`, see Reproduce),
**CITED**, **CONJECTURED**, **REFUTED**.

## Verdict

M is a simple OM of rank r on E, and V is a nonempty T-convex set of topes
(§0).

| Statement | Status |
|---|---|
| **Lemma 0.2-OM** (closed-cone lemma): the closed face complex of V is contractible if V ≠ all topes, and ≃ S^{r−1} if V = all topes; the same for every fibre over a flat | **PROVEN**, by a new elementary argument (deletion and Quillen's fibre lemma; no shellability, no topological representation theorem). The contractible case is also KNOWN, in the stronger form "shellable ball" (Mücksch 2022, Cor. 2.23, from BLSWZ Thm 4.3.3). COMPUTED for every sign condition on four OMs. |
| **Theorem 1-OM**: Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{r−2}, with m(V) = (−1)^r μ_{Λ(V)}(0̂, 1̂) ≥ 0 | **PROVEN.** The homology form (free, concentrated in degree r − 2, rank m(V)) is proven for all r by OM combinatorics alone. The homotopy form is proven for r ≤ 3 the same way; for r ≥ 4 it also uses simple connectivity of tope boundaries, which comes from the cell structure (BLSWZ Thm 4.3.3, i.e. the topological representation theorem). COMPUTED on all 1,295 T-convex sets of non-Pappus. |
| **Theorem 2-OM**: #V = Σ_{flats Z ⊇ S_max(V)} (−1)^{rk Z} μ_{Λ(V)}(Z, 1̂) | **PROVEN** (OM combinatorics and Möbius inversion). COMPUTED. |
| **Prop. 3-OM**: the bottom multiplicity of Σ_L on Γ_V is m(V), and q(V) ≤ m(V) | **PROVEN, given Brown** (an LRB theorem; it uses no geometry). COMPUTED. |
| **Prop. A-OM, Prop. B-OM** (f_* is split onto; Γ/Lune ≅ H̃_{r−2}(L̄(M)) via C ↦ ρ_C) | **PROVEN** (B given Brown). B is COMPUTED at chain level over Z. |
| **Theorem C-OM / G\***: the ρ_C span; q(V) = m(V); (G1); H̃_{r−2}(Λ̄(V)) ≅ det ⊗ (Γ_V + Lune)/Lune as Stab(V)-modules | **PROVEN, given Brown.** det is the orientation character of Aut(M) on H_{r−1}(Δ(L ∖ 0)). COMPUTED on non-Pappus (both orientations) and three realizable controls. |
| "Brown's §7 argument behind Theorem C needs realizability" | **REFUTED.** Brown's §7.2 theorem is stated for an arbitrary finite LRB over an arbitrary field. The covector monoid of any OM satisfies its hypotheses (checked in §5). No step of Theorem C uses realizability. |
| Positive control: the computation reproduces known realizable values | **COMPUTED.** B_3 gives 941 cones, Σ|Stab| = 1680 and "untwisted identity holds on 826/941", exactly as `compute/output/general_theory.txt` [B3]. A_3 gives 219 cones and |μ| = 6. |

**Where realizability is used: nowhere.** Every ingredient of the
real-case proofs is either purely poset-topological, or LRB algebra, or has
an OM proof given below. The one place that needs more than covector
combinatorics is the simple connectivity in Theorem 1 for r ≥ 4. That fact
holds for every OM by the topological representation theorem (§7).

---

## 0. Setting

**Oriented matroids.** M = (E, L) is an OM of rank r, given by its set L of
covectors (sign vectors in {+, 0, −}^E). The order is X ≤ Y iff X_e ∈ {0, Y_e}
for every e. X ∘ Y is the composition, z(X) = {e : X_e = 0} the zero set, and
the topes 𝒯 are the maximal covectors. **Loopless** means that no e has
X_e = 0 for every X ∈ L. **Simple** means loopless with no parallel or
antiparallel pairs. All theorems are stated for simple M, as the task asks.
Every proof uses only looplessness.

**Standard facts used (CITED from Björner–Las Vergnas–Sturmfels–White–
Ziegler, *Oriented Matroids*, 2nd ed., 1999, "BLSWZ"; we did not re-check
the numbering in the book).**
- (O1) Deletion and contraction. For A ⊆ E,
  L(M∖A) = {X|_{E∖A} : X ∈ L} and L(M/A) = {X|_{E∖A} : X ∈ L, X_A = 0}.
  Both are OMs (BLSWZ §3.3).
- (O2) The zero sets z(X) are exactly the flats of the underlying matroid
  (BLSWZ §4.1). Every maximal chain 0 < X_1 < ⋯ < X tope has r + 1
  elements. Put dim X := r − rk z(X). If X < Y, then z(X) ⊋ z(Y), so
  dim X < dim Y.
- (O3) f is a coloop iff some covector has support {f}. If f is not a coloop,
  M∖f has rank r. If f is a coloop, then L(M) = L(M∖f) × {+, 0, −}.
- (O4) Cell facts (BLSWZ Thm 4.3.3, as quoted with this number in Mücksch,
  arXiv:2211.14083, Thm 2.21). L ∖ {0} is the face poset of a shellable
  regular cell decomposition of S^{r−1}. Proposition 4.3.2 (Lawrence, as
  quoted in Delucchi, arXiv:0705.3107, Thm 3.5) says that every linear
  extension of the tope poset T(M, B) induces a recursive coatom ordering of
  the face lattice. The topological representation theorem (Folkman–
  Lawrence, BLSWZ Thm 5.2.1) realizes this cell structure by an
  arrangement of pseudospheres.
  **(O4) is used only once**, in Theorem 1 for r ≥ 4 (§3, Step 5).

Proof that (O3) holds. A covector X with support {f} is minimal nonzero, so
it is a cocircuit, and its zero set E ∖ f is a hyperplane. So
f ∉ cl(E ∖ f), i.e. f is a coloop. The converse reverses this. If f is a
coloop and X ∈ L, then e_f^± ∘ X (with e_f^± the covectors of support {f})
are the lifts of X|_{E∖f} with f-entry ±. Eliminating these two at f gives
the lift with f-entry 0.

**Poset topology used (CITED, standard; all purely combinatorial).**
- Quillen's fibre lemma (Quillen 1978, Prop. 1.6; Björner, *Topological
  methods*, Thm 10.5).
- Quillen's order-homotopy lemma: if f ≤ g pointwise, then Δ(f) ≃ Δ(g). At
  chain level this is the prism operator, proven in [AudC, §B.2].
- The nerve lemma (Björner, *Topological methods*, Thm 10.6).
- P. Hall's theorem μ = χ̃.
- The contractible carrier lemma, proven in [AudC, §A].
- **Gluing.** Let A_1 and A_2 be contractible subcomplexes of a simplicial
  complex with A_1 ∪ A_2 = X and A_1 ∩ A_2 = B. Then X ≃ ΣB (unreduced
  suspension, with Σ∅ = S^0). In particular X is contractible if B is.
  *Proof.* Collapsing a contractible subcomplex is a homotopy equivalence,
  so X ≃ X/A_1 = A_2/B ≃ A_2 ∪ CB ≃ (A_2 ∪ CB)/A_2 = CB/B = ΣB. If B = ∅,
  X is two contractible components. ∎

**Convention for sub-posets.** Every subset of L used below is a down-set
of L ∖ 0. The order complex of a union of down-sets is the union of their
order complexes, because a chain lies in any down-set that contains its top
element. The order complex of an intersection is the intersection.

**T-convex sets.** A set V ⊆ 𝒯 is T-convex if it is an intersection of
half-spaces 𝒯_e^± = {T : T_e = ±}. Equivalently it is geodesically convex in
the tope graph (BLSWZ Prop. 4.2.6, as quoted in Mücksch, Lemma 2.17). Write
V = V(S, s) = {T ∈ 𝒯 : T_S = s} with S ⊆ E and s ∈ {+, −}^S, and put
S_max(V) = {e : all T ∈ V have the same sign at e}. Since every e ∈ S has
constant sign on V, V = V(S_max, s|S_max). These are exactly the "top-cones"
of [GT, §0], with S_max in the same role.

For any S, s define

  K(S, s) = {X ∈ L ∖ 0 : X_e ∈ {0, s_e} for all e ∈ S}.

**Closed faces and supports.**
- F(V) = {X ∈ L : X ≤ T for some T ∈ V}.
- **Claim:** if V = V(S, s) ≠ ∅, then F(V) ∖ 0 = K(S, s).
  - ⊆ is clear.
  - ⊇: take X ∈ K(S, s) and T ∈ V. Then X ∘ T is a tope, it agrees with s
    on S, and X ≤ X ∘ T.

  So F(V) does not depend on the defining pair (S, s). It is the analogue of
  the faces of the closed cone |V|.
- Λ(V) = {z(X) : X ∈ F(V)}, ordered by **reverse** inclusion. Its bottom is
  0̂ = E = z(0) (the "span 0") and its top is 1̂ = ∅ (topes). This is the
  order of [GT]: span F ⊆ span G iff z(F) ⊇ z(G). Write Λ̄(V) for the proper
  part.
- m(V) = (−1)^r μ_{Λ(V)}(E, ∅).
- dim Z = r − rk Z is the "dimension of the span".
- For V = 𝒯, Λ(𝒯) = L(M), the lattice of flats of the underlying matroid
  in reverse order, and L̄(M) is its proper part.

---

## 1. Lemma 0.1-OM (supports and localization) — PROVEN

Let V = V(S, s) ≠ ∅ in a simple OM M of rank r.

- **(a)** For Z ∈ Λ(V), let K_Z = {X ∈ F(V) ∖ 0 : z(X) ⊇ Z}. Restriction
  X ↦ X|_{E∖Z} is an order isomorphism from K_Z onto the set K(S ∖ Z, s)
  of the contraction M/Z. M/Z is loopless of rank dim Z, and its T-convex
  set V(S ∖ Z, s) is nonempty.
- **(b)** Every flat Z ⊇ S lies in Λ(V).
- **(c)** For Z ∈ Λ(V): Z ⊇ S ⟺ Z ⊇ S_max ⟺ K_Z = −K_Z. Hence the flats
  containing S are the flats containing S_max, and cl S = cl S_max =: Z_L.
  This flat is the analogue of the lineality space lin V.
- **(d)** Let Z ⊇ S be a flat, and V|Z = {topes Y of M|_Z : Y_S = s}. This is
  a nonempty T-convex set of the simple OM M|_Z of rank rk Z. Then
  {Z′ ∈ Λ(V) : Z′ ⊆ Z} = Λ(V|Z), with the same order. So the interval
  [Z, 1̂] of Λ(V) is Λ(V|Z), and

    m(V|Z) = (−1)^{rk Z} μ_{Λ(V)}(Z, ∅).

*Proof.*

(a) By (O1), X ↦ X|_{E∖Z} is a bijection from {X ∈ L : X_Z = 0} onto
L(M/Z), and it preserves ≤. The conditions on S ∩ Z hold automatically, and
those on S ∖ Z are unchanged. Z is a flat, so M/Z is loopless, and its rank
is r − rk Z. Since Z ∈ Λ(V), some X ∈ F(V) has z(X) = Z. Then X|_{E∖Z} has
full support, so it is a tope of M/Z, and it equals s on S ∖ Z.

(b) By (O2) there is a covector X with z(X) = Z. Then X_S = 0, so
X ∈ F(V).

(c) If S ⊆ Z, then K_Z is all of L(M/Z) ∖ 0 under (a), which is closed
under negation. If e ∈ S ∖ Z, take X ∈ F(V) with z(X) = Z. Then
X_e = s_e ≠ 0, so −X ∉ K_Z. Both S and S_max are defining sets for V, so
the same holds with S_max. For an arbitrary flat Z ⊇ S, (b) gives
Z ∈ Λ(V), and then Z ⊇ S_max.

(d) M|_Z = M ∖ (E ∖ Z) is simple and has rank rk Z. V|Z contains T|_Z for
every T ∈ V.
- (⊆) Take X ∈ F(V) with z(X) = Z′ ⊆ Z. Then X|_Z ∈ L(M|_Z) satisfies the
  conditions on S ⊆ Z and has zero set Z′.
- (⊇) Take Y ∈ L(M|_Z) with Y_S ∈ {0, s} and zero set Z′ in Z. Write
  Y = X|_Z with X ∈ L, and let W be a covector with z(W) = Z. Then X ∘ W
  restricts to Y on Z and is nonzero off Z, so z(X ∘ W) = Z′. Its S-entries
  are those of Y, so X ∘ W ∈ F(V).
- The order is reverse inclusion on both sides.
- The last formula is the definition of m(V|Z), whose rank is rk Z. ∎

---

## 2. The closed-cone lemma and the sphere lemmas — PROVEN

**Lemma 2.1 (Lemma 0.2-OM).** Let M be a loopless OM of rank r, S ⊆ E,
s ∈ {+, −}^S, and suppose V(S, s) ≠ ∅.
- (a) If S = ∅, then Δ(K(∅)) = Δ(L ∖ 0) ≃ S^{r−1}.
- (b) If S ≠ ∅, then Δ(K(S, s)) is contractible.

*Proof.* Induction on |E ∖ S|, and on |E| for (a). Write K = K(S, s) for M
and K′ = K(S, s) for M∖f.

*Base.*
- (a) with E = ∅: then r = 0, L = {0}, and K = ∅ = S^{−1}.
- (b) with E = S: V ≠ ∅ forces V = {s}, so s is a tope and K = {X ≤ s,
  X ≠ 0} has the top element s. A poset with a top element has a cone as
  its order complex, so it is contractible.

*Step 1: f ∈ E ∖ S is not a coloop. Then Δ(K) ≃ Δ(K′).*

Define π : K → K′ by X ↦ X|_{E∖f}.
- π is well defined: X|_{E∖f} ≠ 0, since otherwise X would have support
  {f}, which (O3) excludes. It lies in L(M∖f) by (O1), and the conditions
  on S are unchanged because f ∉ S.
- π is monotone.
- M∖f is loopless and has rank r by (O3). V(S, s) for M∖f contains T|_{E∖f}
  for each T ∈ V.

For Y ∈ K′, the fibre is F_Y := π^{-1}(K′_{≤Y}) = {X ∈ L ∖ 0 : X|_{E∖f} ≤ Y}.
Any such X lies in K automatically, since f ∉ S. A **lift** of Y is a
covector X with X|_{E∖f} = Y. Write Y^+, Y^0, Y^− for the candidates. For
X ∈ F_Y and any lift Ŷ, the composition X ∘ Ŷ is again a lift, because
X|_{E∖f} ≤ Y gives (X ∘ Ŷ)|_{E∖f} = X|_{E∖f} ∘ Y = Y. Also X ≤ X ∘ Ŷ.

- **Exactly one lift Ŷ.** Then X ∘ Ŷ = Ŷ for every X ∈ F_Y, so X ≤ Ŷ. F_Y
  has the top element Ŷ and is contractible.
- **At least two lifts.** Then all three exist.
  - If Y^+ and Y^− exist, eliminating them at f (axiom (L3)) gives a
    covector that is 0 at f and equals Y elsewhere, namely Y^0.
  - If Y^0 and Y^± exist, then Y^0 ∘ (−Y^±) = Y^∓ on f and Y elsewhere,
    so Y^∓ exists.

  For X ∈ F_Y, X ∘ Y^0 is the lift whose f-entry is X_f. So X ≤ Y^{X_f},
  and Y^0 ≤ Y^±. Hence F_Y = D^+ ∪ D^−, where D^± = {X ∈ F_Y : X ≤ Y^±}.
  - These are down-sets.
  - A chain of F_Y cannot contain elements with f-entries + and −, since
    those are incomparable. So every chain lies in D^+ or in D^−.
  - D^+ ∩ D^− = {X ≠ 0 : X ≤ Y^0}, which has the top Y^0. Note Y^0 ≠ 0
    because Y ≠ 0.
  - Δ(D^±) and Δ(D^+ ∩ D^−) are cones, hence contractible. By gluing,
    Δ(F_Y) is contractible.

All fibres are contractible, so Quillen's fibre lemma gives Δ(K) ≃ Δ(K′).

*Step 2: f ∈ E ∖ S is a coloop. Then Δ(K) ≃ ΣΔ(K′).*
- By (O3), L(M) = L(M∖f) × {+, 0, −}. Split K = K_0 ⊔ K_+ ⊔ K_− by the
  f-entry. Then K_0 ≅ K′ via X ↦ X|_{E∖f}.
- On K_0 ∪ K_+, let φ(X) be X with its f-entry set to +. Then φ(X) is a
  covector in K_0 ∪ K_+, and X ≤ φ(X) ≥ e_f^+, where e_f^+ ∈ K_+ is the
  covector of support {f}.
- By Quillen's order-homotopy lemma, id ≃ φ ≃ const, so Δ(K_0 ∪ K_+) is
  contractible. The same holds for K_0 ∪ K_−.
- No chain meets both K_+ and K_−. Both sets are closed under going down
  within K, and their intersection is K_0.
- Gluing gives Δ(K) ≃ ΣΔ(K′).

*Induction.*
- (b): if S ≠ ∅, then V(S, s) is nonempty for M∖f and S ⊆ E ∖ f. So Δ(K′)
  is contractible by induction, and so is Δ(K) (Step 1), or its suspension
  (Step 2).
- (a): Step 1 keeps the rank and Step 2 lowers it by one. So Δ(L ∖ 0) ≃
  Σ^{c}(∅) = S^{c−1}, where c is the number of coloop steps. Each element is
  removed once, by Step 1 or by Step 2, and the rank is r at the start and
  0 at the end. So c = r. ∎

*Remark (the general trichotomy, COMPUTED only).* For arbitrary (S, s),
including V(S, s) = ∅, K(S, s) is empty, a sphere (exactly when
K = −K) or contractible. Reduce to the contraction by the elements on which
K vanishes, and apply Lemma 2.1. The script checks the homology version
for all 3^n sign conditions ([lem02]). It is not needed below.

**Lemma 2.2 (tope boundaries).** Let M be loopless of rank r ≥ 1 and T a
tope. Put B_T = Δ(L_{(0,T)}).
- (a) Δ(L ∖ {0, T}) is contractible, and Δ(L ∖ 0) ≃ ΣB_T. Hence B_T has
  the integral homology of S^{r−2}.
- (b) Let ω generate H_{r−1}(Δ(L ∖ 0); Z) ≅ Z (Lemma 2.1(a)). Write ω_T
  for the part of ω on the simplices whose top element is T. Then ∂ω_T is
  a cycle of B_T and generates H̃_{r−2}(B_T; Z).
- (c) For every covector X ≠ 0, L_{(0,X)} ≅ L(M/z(X))_{(0,X̄)}, where X̄ is a
  tope of M/z(X). So Δ(L_{(0,X)}) has the homology of S^{dim X − 2}.

*Proof.*

(a) **The cover.** L ∖ {0, T} is covered by the down-sets
K_e := K({e}, −T_e), e ∈ E.
- No K_e contains T.
- Take X ∉ {0, T}. If X ≰ T, some e has X_e = −T_e. If X < T, some e has
  X_e = 0. Either way X ∈ K_e.

**The intersections.** Every intersection K_A = K(A, −T_A), with A ≠ ∅,
contains the tope −T, so V(A, −T_A) ≠ ∅. By Lemma 2.1(b) it is
contractible. So the nerve is the full simplex on E, and by the nerve lemma
Δ(L ∖ {0, T}) is contractible.

**The suspension.** Every chain of L ∖ 0 either lies in L ∖ {0, T} or
consists of T and elements below T. So Δ(L ∖ 0) is the union of the cone
Δ(L_{(0,T]}) and Δ(L ∖ {0, T}), and their intersection is B_T. Gluing gives
Δ(L ∖ 0) ≃ ΣB_T.

(b) The simplices of Δ(L ∖ 0) that contain T occur only in ω_T, so their
faces that contain T cancel in ∂ω = 0. Hence ∂ω_T lies in B_T. The maps

  H_{r−1}(Δ(L∖0)) → H_{r−1}(Δ(L∖0), Δ(L∖{0,T})) ≅ H_{r−1}(Δ(L_{(0,T]}), B_T) → H̃_{r−2}(B_T)

are isomorphisms:
- the first by the long exact sequence, because Δ(L ∖ {0, T}) is
  contractible;
- the second by excision for subcomplexes;
- the third because the cone is contractible.

They send ω ↦ ω_T ↦ ∂ω_T.

(c) Y ≤ X forces Y_{z(X)} = 0. Apply (O1) for the contraction, and (a) to
the loopless OM M/z(X), which has rank dim X. ∎

**Lemma 2.3 (Euler characteristic, PROVEN).** Let P be a finite down-set of
L ∖ 0. Then χ(Δ(P)) = Σ_{X ∈ P} (−1)^{dim X − 1}.

*Proof.* Add the elements of P in a linear extension. Adding a maximal
element X glues the cone Δ(P_{≤X}) along Δ(P_{<X}) = Δ(L_{(0,X)}). By
Lemma 2.2(c) this has χ = χ(S^{dim X − 2}). So χ grows by
1 − χ(S^{dim X−2}) = (−1)^{dim X−1}. ∎

---

## 3. Theorem 1-OM and Proposition A-OM

**Theorem 1-OM.** Let V be a nonempty T-convex set of topes of a simple OM
of rank r ≥ 1.
- (i) (PROVEN) H̃_i(Δ(Λ̄(V)); Z) is zero for i ≠ r − 2 and free of rank
  m(V) ≥ 0 for i = r − 2.
- (ii) (PROVEN for r ≤ 3; PROVEN given (O4) for r ≥ 4)
  Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{r−2}.

*Proof.* For r = 1, M is a single element, Λ(V) = {E, ∅}, the proper part
is empty, m = 1 and ⋁^1 S^{−1} = ∅. Let r ≥ 2.

*Step 1: the map.* Q′ = F(V) ∖ ({0} ∪ V) and f : Q′ → Λ̄(V), X ↦ z(X).
f is monotone. Its values are neither E (since X ≠ 0) nor ∅ (since X is not
a tope).

*Step 2: the fibres.* For Z ∈ Λ̄(V), f^{-1}(Λ̄_{≤Z}) = {X ∈ F(V) ∖ 0 :
z(X) ⊇ Z} = K_Z. No such X is a tope, because Z ≠ ∅. By Lemma 1.1(a) and
Lemma 2.1, Δ(K_Z) is
- ≃ S^{dim Z − 1} if Z ⊇ S, equivalently Z ⊇ S_max (Lemma 1.1(c));
- contractible otherwise.

Either way it is (dim Z − 2)-connected.

*Step 3: Prop. A-OM (PROVEN).* There is a map g : Δ(Λ̄(V)) → Δ(Q′) with
Δ(f) ∘ g ≃ id. The proof of [AudA, §C, Prop. A], re-derived in [AudC, §A],
applies word for word. It uses only:
- the fibres of Step 2;
- the count "a chain of Λ̄_{≤Z} has at most dim Z elements", which holds by
  (O2);
- the contractible carrier lemma.

So H̃_i(Δ(Λ̄(V))) is a direct summand of H̃_i(Δ(Q′)), and
π_1(Δ(Q′)) → π_1(Δ(Λ̄(V))) is onto.

*Step 4: the homology of X := Δ(Q′).*
- Z_V := Δ(F(V) ∖ 0) = Δ(K(S_max, s)). It is contractible if V ≠ 𝒯 (then
  S_max ≠ ∅), and ≃ S^{r−1} if V = 𝒯 (Lemma 2.1).
- Z_V = X ∪ ⋃_{T∈V} Δ(L_{(0,T]}), where each cone meets X in B_T and two
  cones meet inside X. A chain either avoids V, or has a single tope as its
  top element.
- So H_i(Z_V, X) ≅ ⊕_{T∈V} H_i(Δ(L_{(0,T]}), B_T) ≅ ⊕_T H̃_{i−1}(B_T).
  By Lemma 2.2 this is Z^N (N = #V) for i = r − 1, with basis the ω_T, and
  0 otherwise.
- X has dimension ≤ r − 2 by (O2), so H_{r−1}(X) = 0.
- H̃_{r−2}(Z_V) = 0, for every r ≥ 2.
- From the long exact sequence:
  - H̃_i(X) = 0 for i < r − 2;
  - H̃_{r−2}(X) ≅ Z^N / im H_{r−1}(Z_V).
- The image is 0 if V ≠ 𝒯. If V = 𝒯 it is spanned by ω ↦ (ω_T)_T, a
  primitive vector. So H̃_{r−2}(X) is free.
- The connecting map sends ω_T ↦ ∂ω_T. **So H̃_{r−2}(X) is spanned by the
  ∂ω_T, T ∈ V.**

*Step 5: conclusion.*
- (i) H̃_i(Δ(Λ̄(V))) is a direct summand of H̃_i(X). So it is free and
  vanishes for i ≠ r − 2. Its rank is (−1)^{r−2} χ̃ = (−1)^r μ(E, ∅) = m(V),
  by P. Hall's theorem. Hence m(V) ≥ 0.
- (ii), r = 2: a finite set with H̃_0 free of rank m is ⋁^m S^0.
- (ii), r = 3: H̃_0 = 0, so the order complex is a connected graph, hence a
  wedge of H_1-rank many circles.
- (ii), r ≥ 4: we need π_1(Δ(Λ̄(V))) = 1. By Step 3 it suffices that
  π_1(X) = 1.
  - (O4) makes each B_T a sphere S^{r−2}, so B_T is simply connected.
  - So the pair (Z_V, X), which is built by attaching cones on the B_T, is
    2-connected, and π_1(X) ≅ π_1(Z_V) = 1.
  - Hurewicz and Whitehead then give a wedge of (r − 2)-spheres, as in
    [GT, Step 5]. ∎

*What the r ≥ 4 step needs, exactly.* Lemma 2.2 shows combinatorially that
each B_T is a homology (r − 2)-sphere whose suspension is ≃ S^{r−1}. It
does not show that B_T is simply connected. That is the only point at
which (O4) enters this note. Shellability gives it (BLSWZ Thm 4.3.3), and
so does the topological representation theorem.

**Corollary 1.1-OM (rank count).** The Björner–Wachs–Welker decomposition
of [GT, (1.1)] also transfers, since its hypotheses are Step 2. Taking
ranks gives Theorem 2 below. We prove Theorem 2 directly instead.

---

## 4. Theorem 2-OM — PROVEN

**Theorem 2-OM.** For every nonempty T-convex set V of a simple OM of rank r,

  #V = Σ_{Z flat, Z ⊇ S_max(V)} m(V|Z) = Σ_{Z ⊇ S_max} (−1)^{rk Z} μ_{Λ(V)}(Z, ∅).

*Proof.* This is [GT, Thm 2] with each geometric input replaced.
- For Z ∈ Λ(V), put g(Z) = #{X ∈ F(V) : z(X) = Z} and
  f(Z) = Σ_{X ∈ F(V), z(X) ⊇ Z} (−1)^{dim X}.
- Then f(Z) = Σ_{Z′ ≤ Z in Λ(V)} (−1)^{dim Z′} g(Z′).
- Separating X = 0 and using Lemma 2.3 for the down-set K_Z,
  f(Z) = 1 − χ(Δ(K_Z)).
- By Lemma 1.1(a),(c) and Lemma 2.1, this equals:
  - 0 if Z ⊉ S_max (contractible);
  - 1 − (1 + (−1)^{dim Z − 1}) = (−1)^{dim Z} if Z ⊇ S_max and Z ≠ E
    (sphere);
  - 1 if Z = E (K_E = ∅).

  So f(Z) = (−1)^{dim Z} [Z ⊇ S_max].
- Möbius inversion on Λ(V) at the top ∅, with g(∅) = #V and Lemma 1.1(b),
  gives #V = Σ_{Z ⊇ S_max} (−1)^{r − dim Z} μ(Z, ∅).
- Lemma 1.1(d) turns each term into m(V|Z). ∎

Specializations:
- V = 𝒯 gives the Las Vergnas–Zaslavsky count of topes, #𝒯 = Σ_Z |μ(Z, ∅)|
  (§9).
- Pointed V (cl S_max = E) gives #V = m(V).

---

## 5. Proposition 3-OM and Brown's theorem — PROVEN given Brown

Let L_V := {X ∈ L : X_{S_max} = 0} =: Σ_L, the analogue of the faces in
lin V. Γ_V = span V ⊆ Γ = k^𝒯.

**Brown's hypotheses hold for every OM (PROVEN).** (L, ∘) is a monoid with
x ∘ x = x and x ∘ y ∘ x = x ∘ y; these are coordinatewise identities. Take
supp X := z(X) in the lattice of flats ordered by reverse inclusion (join =
intersection). Then:
- (2) z(X ∘ Y) = z(X) ∩ z(Y);
- (3) if z(Y) ⊇ z(X), then X ∘ Y = X.

These are exactly the hypotheses of Brown, *Semigroups, rings, and Markov
chains* (2000), §2.1 (as read in [AudC, §B.4]). Σ_L is closed under ∘, and
supp maps it onto the interval {flats Z ⊇ S_max}, by (O2) and
Lemma 1.1(b). So Brown's §7.2 Theorem 3 and its Corollary (Bidigare;
arbitrary field) apply to kΣ_L. They give one simple module S_Z for each
flat Z ⊇ S_max, with character χ_Z(Y) = [z(Y) ⊇ Z]. **Nothing in that
theorem refers to geometry.** This settles the question of the task: the
step "most likely to need realizability" does not.

**Lemma L-OM (PROVEN).** For a covector H and a tope D ≥ H, the lune is
L(H, D) = {C ∈ 𝒯 : H ∘ C = D} = {C : C_{z(H)} = D_{z(H)}}.
- (i) L(H, D) ⊆ V iff D ∈ V and H ∈ Σ_L.
- (ii) L(H, D) is a singleton iff H = 0.

*Proof.* H ∘ C = D says that C = D on z(H); off z(H) it is forced by H ≤ D.
- (i) ⇐: if S_max ⊆ z(H), every C in the lune agrees with D on S_max.
  ⇒: if e ∈ S_max and H_e ≠ 0, then −H ∘ D lies in the lune and has
  e-entry −D_e, so it is not in V.
- (ii): if H ≠ 0, then −H ∘ D ≠ D lies in the lune. If H = 0, the lune is
  {D}. ∎

Lune = span of the non-singleton lunes in Γ, and q(V) = dim (Γ_V + Lune)/Lune.

**Proposition 3-OM.**
- (a) (PROVEN) Σ_L acts on Γ_V by C ↦ H ∘ C, and the non-singleton lunes in
  V span Lie_L(Γ_V)^⊥, where Lie_L(Γ_V) = {z ∈ Γ_V : Hz = 0 for all
  H ∈ Σ_L ∖ 0}.
- (b) (PROVEN, given Brown) [Γ_V : S_E] = Σ_{Z ⊇ S_max} μ(E, Z) c_Z = m(V),
  where c_Z = #{C ∈ V : C ≥ X} for any X with z(X) = Z. Hence
  q(V) ≤ dim Lie_L(Γ_V) ≤ m(V).

*Proof.* [GT, Prop. 3] with the following substitutions.
- (a) The action: if H ∈ Σ_L and C ∈ V, then H ∘ C agrees with C on S_max.
  The adjoint of C ↦ H ∘ C sends D to the lune L(H, D) if D ≥ H, and to 0
  otherwise. By Lemma L-OM these are exactly the non-singleton lunes in V.
- (b) The trace, or in characteristic p the rank, of the idempotent H on
  Γ_V is #{C ∈ V : H ∘ C = C} = #{C ∈ V : C ≥ H}.
  - C ↦ C|_Z is a bijection from {C ∈ 𝒯 : C ≥ H} to the topes of M|_Z,
    with Z = z(H). It is injective because off Z, C = H. It is surjective
    because a lift Ŷ of a tope Y of M|_Z gives the tope H ∘ Ŷ ≥ H.
  - It carries V onto V|Z. So c_Z = #(V|Z).
  - Brown's rank argument ([AudC, §B.3]) gives c_Y = Σ_{Z ⊆ Y, Z ⊇ S_max}
    [Γ_V : S_Z]; here "Z above Y" means Z ⊆ Y.
  - Theorem 2-OM for V|Z reads #(V|Z) = Σ_{S_max ⊆ Z′ ⊆ Z} m(V|Z′). Here
    we use that the flats of M|_Z containing S_max(V|Z) are the flats Z′ ⊆ Z
    containing S_max(V). This is Lemma 1.1(c) applied to V|Z, which is
    defined by the same S.
  - Möbius inversion on {Z ⊇ S_max} gives [Γ_V : S_E] = m(V).
  - The inequalities are as in [GT]. ∎

---

## 6. Proposition B-OM and Theorem C-OM — PROVEN given Brown

**Chamber cycles.** Fix ω as in Lemma 2.2(b). For a tope C put

  ρ_C := Δ(f)_#(∂ω_C),  f = z(·),

a (r − 2)-chain of Δ(Λ̄(C)) ⊆ Δ(Λ̄(V)) for every V ∋ C. f is injective on
chains by (O2), so no term degenerates. By Lemma 2.2(b), ∂ω_C is a
fundamental cycle of the tope boundary.
- For realizable M, ω can be taken to be the determinant-signed cycle of
  [AudC, §B.1]. That cycle has all coefficients ±1 and is a cycle, and
  H_{r−1} ≅ Z. So the ρ_C here agree with [AudA]'s up to one global sign.

**Proposition B-OM (PROVEN, given Brown).** Let r ≥ 2. The map
φ : kΓ → H̃_{r−2}(Δ(L̄(M)); k), C ↦ ρ_C, has kernel Lune, and
Γ/Lune ≅ H̃_{r−2}(L̄(M)).

*Proof.*

1. **φ is onto.** This is Step 4 of §3 with V = 𝒯, pushed forward along the
   split surjection f_* of Prop. A-OM.
2. **Lune ⊆ ker φ.** Let ℒ = L(H, D) with H ≠ 0.
   - If H is a tope, then ℒ = 𝒯 and Σ_{C∈𝒯} ∂ω_C = ∂ω = 0.
   - Otherwise put z := ∂(Σ_{C∈ℒ} ω_C) = −∂(Σ_{C∉ℒ} ω_C), using ∂ω = 0.
   - A face σ with nonzero coefficient in z is a face both of a simplex
     with top in ℒ and of one with top outside ℒ.
   - So σ contains no tope: a tope in σ would be the top of both. Its top
     element Y is a non-tope with Y ≤ C ∈ ℒ and Y ≤ C′ ∉ ℒ.
   - C and C′ differ at some e ∈ z(H), because C′ ∉ ℒ, and Y ≤ both, so
     Y_e = 0.
   - Hence z is supported on the down-set Q″ = {Y : Y_e = 0 for some
     e ∈ z(H)}.
   - On Q″, let g(Y) = z(Y) ∩ z(H). This is a flat, it is nonempty, so
     g(Y) ≠ 1̂, and it is ≠ E = 0̂ because H ≠ 0. g is monotone, and f ≤ g in
     the reverse-inclusion order.
   - The prism operator of [AudC, §B.2] gives f_#(z) − g_#(z) = ∂(…). Also
     g_#(z) is a cycle in the cone Δ(L̄_{≥z(H)}) with apex z(H), so it is a
     boundary.
   - So Σ_{C∈ℒ} ρ_C = f_#(z) is a boundary in a complex of dimension r − 2.
     It is therefore 0 as a chain.
3. **dim Γ/Lune ≤ |μ(L(M))|.** By Prop. 3-OM(a), Lune = Lie(Γ)^⊥ at
   V = 𝒯, where Σ_L = L. By (b), dim Lie(Γ) ≤ m(𝒯) = |μ(E, ∅)|.
4. **Conclusion.** H̃_{r−2}(L̄(M)) has rank |μ| by Theorem 1-OM(i) at
   V = 𝒯 (or by Folkman, since L(M) is geometric). So the surjection
   Γ/Lune ↠ H̃ is an isomorphism. Over any field, k ⊗ the free integral
   homology has the same dimension. ∎

**Theorem C-OM (G\* for oriented matroids; PROVEN, given Brown).** Let V be
a nonempty T-convex set of topes of a simple OM M of rank r ≥ 2, and k any
field.
- (i) {ρ_C : C ∈ V} spans H̃_{r−2}(Δ(Λ̄(V)); Z).
- (ii) q(V) = m(V).
- (iii) Γ_V ∩ Lune = span{non-singleton lunes in V}, and
  dim Lie_L(Γ_V) = m(V).
- (iv) Let W be a group of signed permutations of E preserving L. Define
  det(g) = ±1 by g·ω = det(g) ω, where g acts on chains of covectors and
  preserves their order. Then g·ρ_C = det(g) ρ_{gC} at chain level. So

    H̃_{r−2}(Δ(Λ̄(V)); k) ≅ det ⊗ (Γ_V + Lune)/Lune

  as k[Stab_W(V)]-modules.

*Proof.* [AudA, Thm C], with the inputs of §§3–6.
- (i) By §3 Step 4, H̃_{r−2}(X) is spanned by the ∂ω_C, C ∈ V. f_* is onto
  (Prop. A-OM), and it sends ∂ω_C to ρ_C.
- (ii) Λ̄(V) is an induced subposet of L̄(M), and both order complexes have
  dimension ≤ r − 2. So H̃_{r−2} is the space of top cycles in each, and the
  inclusion is injective.
  - The span of the ρ_C, C ∈ V, has dimension m(V) in the first, by (i)
    and Theorem 1-OM.
  - In the second it has dimension dim Γ_V/(Γ_V ∩ Lune) = q(V), by
    Prop. B-OM.
- (iii) Prop. 3-OM gives q ≤ dim Lie_L ≤ m, so equality holds by (ii).
  Prop. 3-OM(a) then gives dim span{lunes in V} = #V − m = dim(Γ_V ∩ Lune),
  and one space contains the other.
- (iv) g maps simplices with top C to simplices with top gC. So
  g·ω_C = det(g) ω_{gC}. Also f(gX) = g·z(X). Lune is W-stable, because
  g L(H, D) = L(gH, gD). The rest is as in [AudA, Thm C(iv)]. ∎

For realizable M and W linear, det(g) here is sign det(g): the
determinant-signed ω transforms by sign det ([AudC, §B.5]), and ω is
unique up to sign. The B_3 control in §8 confirms this. It reproduces the
det-twisted counts of `compute/output/general_theory.txt` exactly.

---

## 7. Ingredient ledger

Each ingredient of the real-case proofs ([GT] §§0–1, [AudA] §C, [AudC]),
and what the OM proof uses in its place.

| Ingredient (real case) | Used in | OM status |
|---|---|---|
| Faces = sign vectors, Tits product, face order | everywhere | Definitional: covectors, composition, conformal order. |
| Lemma 0.1 (support criterion, flats in lin V, localization) | Thms 1, 2, C | **New OM proof, elementary** (Lemma 1.1). "lin V" becomes the flat cl S_max, and the localization becomes the restriction M\|_Z. |
| Cell facts: faces ≠ O form a regular CW sphere; order complex ≅ complex | Thm 1 Step 2/4, Thm 2, Prop. A | **Replaced** for every homology statement by Lemmas 2.1(a), 2.2 and 2.3 (covector combinatorics, Quillen, nerve). The full cell structure **transfers via TRT** (O4), and is used only for π_1 in Thm 1, r ≥ 4. |
| Lemma 0.2 (a cone section is a ball or a sphere) | fibres in Thms 1, 2, Prop. A | **New OM proof** (Lemma 2.1, deletion + Quillen). Also KNOWN via shellability (Mücksch, Cor. 2.23). |
| Euler characteristic of the fibres = alternating cell count | Thm 2 | **New OM proof** (Lemma 2.3, from Lemma 2.2(c)). |
| Björner–Wachs–Welker fibre theorem | Thm 1 (optional) | Poset topology; transfers verbatim. Not needed: Prop. A-OM replaces it. |
| Prop. A (section of Δ(f) up to homotopy) | Thm 1, Thm C(i) | Poset topology; transfers verbatim, given the fibres. |
| P. Hall, Hurewicz, Whitehead | Thm 1 | Topology; verbatim. |
| Chamber orientation ε via determinants | ρ_C, Prop. B, Thm C(iv) | **Replaced** by the fundamental cycle ω of Δ(L ∖ 0) (Lemma 2.1(a)) and its pieces ω_C (Lemma 2.2(b)). det becomes the orientation character. |
| Adjacent chambers induce opposite orientations | Prop. B step 2 | **Replaced** by ∂ω = 0 and the support argument of Prop. B-OM step 2. |
| Lemma L (lunes in V iff H ⊆ lin V); non-singleton iff H ≠ O | Prop. 3(a), Prop. B | **New OM proof, one line** (Lemma L-OM). |
| Brown's theorem (simple modules of an LRB algebra; rank argument) | Prop. 3(b), Prop. B, Thm C | **LRB-general; transfers verbatim.** The hypotheses are checked for (Σ_L, ∘, z) in §5. **Does not use realizability.** |
| Saliola's idempotents | Prop. 3(c) only | LRB-general; not needed (Thm C(iii) replaces it). |
| Aguiar–Mahajan Ree criterion (q(V) = dim Lie[A]\|_V) | interpretation only | Not used. Here q(V) is defined as dim (Γ_V + Lune)/Lune. |
| Linear symmetry group W, det | Thm C(iv) | **Replaced** by Aut(M) (signed permutations preserving L) and the orientation character. |

**Genuinely uses realizability: nothing.** The question "does Brown's §7
need realizability?" has the answer no. Bidigare's theorem as stated by
Brown (§7.2, Thm 3: "an algebra surjection kS ↠ k^L whose kernel is
nilpotent", for any LRB S with support lattice L over any field k) is pure
semigroup algebra. The covector monoid of an OM is such an S.

---

## 8. Computations (COMPUTED)

`compute/oriented_matroid_cones.py` builds every OM from a chirotope and
imports nothing from the other scripts. For each OM:
- it checks the chirotope axioms (bases of a matroid and the 3-term
  Grassmann–Plücker relations; BLSWZ §3.6, CITED);
- it generates the covectors from the cocircuits by composition;
- it checks closure under negation and composition, and cocircuit
  elimination;
- it enumerates every T-convex set as V(s), s ∈ {+, 0, −}^E, removing
  duplicates.

Homology ranks are computed over GF(2^31 − 1). Integrality checks are
exact: the cycle ω, the ±1 coefficients, and Prop. B at chain level. q(V) is
computed exactly over Q.

**The non-realizable OMs.** Start from an exact rational realization of the
Pappus configuration: A, B, C on one line, a, b, c on another,
X = Ab·aB, Y = Ac·aC, Z = Bc·bC. Its chirotope vanishes on exactly the 9
Pappus lines (checked). Set χ(X, Y, Z) := ±1 and keep every other value.
- Both choices satisfy the chirotope axioms (checked).
- The zero set is then exactly the other 8 lines ([nonreal]). So the
  underlying matroid is the non-Pappus matroid. By Pappus's theorem it is
  not representable over any field, so neither OM is realizable.
- The control for [nonreal]: the Pappus chirotope itself fails the
  certificate.

**Results** (`compute/output/oriented_matroid_cones.txt`; every check
passes):

| OM | realizable | topes | \|μ(L)\| | T-convex sets | \|Aut M\| | Σ\|Stab\| | untwisted identity holds on |
|---|---|---|---|---|---|---|---|
| A_3 (braid, n = 4) | yes | 24 | 6 | **219** | 48 | 576 | 128/219 |
| B_3 | yes | 48 | 15 | **941** | 48 | **1680** | **826/941** |
| Pappus | yes | 56 | 19 | 1233 | 12 | 1608 | 942/1233 |
| non-Pappus, χ(XYZ) = +1 | **no** | 58 | 20 | 1295 | 2 | 1296 | 1294/1295 |
| non-Pappus, χ(XYZ) = −1 | **no** | 58 | 20 | 1295 | 2 | 1296 | 1294/1295 |

On every row, the following pass on every T-convex set:
- [flatL], [zas] (Theorem 2), [wedge] (Theorem 1);
- [fib] (every fibre K_Z is a sphere of the right dimension or acyclic);
- [brown] (Prop. 3(b)), [rho] (Theorem C(i)), [q=m] (Theorem C(ii)),
  [G1] (Theorem C(iii)), [eq] (Theorem C(iv)).

They also pass:
- [lem02] on all 3^n sign conditions (729 for A_3, 19,683 otherwise);
- [sphere]: Δ(L ∖ 0) is a homology S^2 with a ±1 integral fundamental
  cycle, and every tope boundary is a homology S^1;
- [propB]: rank |μ|, and every lune killed at chain level;
- [eq-rho]: g·ρ_C = det(g) ρ_{gC} for every g ∈ Aut M.

**Positive controls.**
- B_3: its combinatorial automorphism group is W(B_3) (order 48, −I
  included). The run reproduces the values of `compute/output/
  general_theory.txt` [B3] exactly: 941 cones, sum of stabiliser orders
  1680, and the untwisted identity holding on 826/941 cones, i.e. failing on
  115. That computation used linear algebra in R^3; this one uses only the
  chirotope. So the combinatorial det of §6 equals sign det on W(B_3).
- A_3: 219 cones (A001035(4)) and |μ| = 6, as in [A3]. Here Aut M = S_4 ×
  {±1} has order 48, whereas [A3] used W = S_4. That is why Σ|Stab| is 576,
  not 384, and why the untwisted count differs.
- [chi]: flipping one basis sign of A_3 is rejected (test).
- [zas]: summing over all of Λ(V) instead of over the flats containing
  S_max gives the wrong count on some non-Pappus cone (test).
- The det twist is detected on non-Pappus: at V = 𝒯 with g = −1,
  det(−1) = −1 for r = 3, and the untwisted identity fails there.

**Limitations.**
- The automorphism group of both non-Pappus OMs is only {±1}. The
  perturbation breaks the Pappus symmetry, and our Pappus realization has
  only 12 signed automorphisms. So on non-Pappus the equivariant identity
  is exercised by a single non-trivial element.
- Rank 3 does not exercise the π_1 step of Theorem 1 (r ≥ 4). No rank-4
  non-realizable OM was tested.

---

## 9. COMs and LRBs: what is and is not natural

- **The closed face set F(V) is not a COM** when V ≠ 𝒯, in the OM setting
  too. Take a wall e of V (so e ∈ S_max), X ∈ F(V) with X_e = 0, and a tope
  Y ∈ V. Then X ∘ (−Y) has e-entry −s_e, so it is not in F(V), and face
  symmetry fails. This is the argument of [NovGT, §2.2]; it uses no
  geometry. F(V) does satisfy strong elimination, since it is closed under
  composition and the elimination of two of its elements stays in F(V).
  It is also not a CW LRB. The faces above X correspond, by restriction to
  z(X), to K(S_max ∩ z(X), s) in M|_{z(X)}. If X is a boundary face
  (S_max ∩ z(X) ≠ ∅), this is contractible by Lemma 2.1(b), not a sphere.
- **The open cone L^+(V) = {X : X_S = s} is a COM** (Margolis–Saliola–
  Steinberg, Prop. 2.13; Bandelt–Chepoi–Knauer). Its support semilattice is
  {z(X) : X_S = s}, the OM analogue of L^int(K). For COMs, the statements
  that are natural, and known, are MSS Thm 1.1(3) (Cohen–Macaulay
  intervals) and Thm 9.3 (the Zaslavsky-type count). [NovGT, §2] records
  that they do not give Theorems 1 and 2.
- **So the closed-cone theorems are OM statements, not COM statements.**
  They need the antipodal tope −T, which a COM lacks (Lemma 2.2's nerve
  argument and the ⇒ of Lemma L-OM both use it). They also need the bottom
  0̂ = z(0) of Λ(V), and a COM has no zero covector.
  - A COM version would have to say what "closed T-convex subset of a COM"
    and its support poset are; we do not propose one.
  - Brown's theorem (§5) is LRB-general, and the face monoid of a COM is an
    LRB (MSS). But Prop. 3(b) identifies the multiplicity with m(V) through
    Theorem 2-OM, and Prop. B needs Theorem 1 for the whole sphere. Neither
    has a COM counterpart.

---

## 10. Prior art (beyond [NovGT])

Searched for this note:
- two web searches ("oriented matroid T-convex set of topes closure
  contractible ball shellable Edmonds Mandel"; "non-Pappus oriented matroid
  chirotope");
- full-text greps of Mücksch, *Modular flats of oriented matroids and poset
  quasi-fibrations*, arXiv:2211.14083;
- Delucchi, *Shelling-type orderings of regular CW-complexes and acyclic
  matchings of the Salvetti complex*, arXiv:0705.3107;
- Hochstättler–Welker, *The Varchenko determinant for oriented matroids*,
  arXiv:1805.07183.

BLSWZ itself was not opened. Its theorem numbers are cited as quoted in
those papers.

| Statement | Status | Source |
|---|---|---|
| Lemma 0.2-OM, contractible case | **KNOWN**, stronger | Mücksch, Cor. 2.23 (read): for a nonempty convex Q ⊆ 𝒯, Q ≠ 𝒯, the subcomplexes L(Q) and L(𝒯 ∖ Q) are shellable balls. The proof combines BLSWZ Thm 4.3.3 (linear extensions of T(M, B) are shellings), Prop. 4.7.26 (initial segments of a shelling of a sphere are balls) and the fact that Q is an order ideal of T(M, B) for B ∈ Q. L(Q) is our F(V). Our deletion proof (Lemma 2.1) is independent of shellability; we did not find it in the sources read. |
| Contractibility of related tope posets | KNOWN, related (different posets) | Hochstättler–Welker, arXiv:1805.07183, Thm 1.2 (read): a nonempty T-convex set ("supertope"), as a subposet of the tope poset T_R, is contractible. Their proof uses only covector elimination, and they remark that it should extend to COMs. That poset is the tope poset, not the face complex F(V) ∖ 0, so it does not give Lemma 0.2-OM. Also BLSWZ Lemma 4.3.11, as quoted there (Lemma 2.5): the filters F_R(P) of (0, P) are contractible for P ≠ ±R. |
| L ∖ 0 is a sphere | KNOWN | BLSWZ Thm 4.3.3 (Folkman–Lawrence; Edmonds–Mandel). Lemma 2.1(a) reproves the homotopy type combinatorially. |
| Theorem 1-OM, V = 𝒯 | KNOWN | L(M) is a geometric lattice, so Folkman's theorem applies. |
| Theorem 2-OM, V = 𝒯 | KNOWN | Las Vergnas (1975) and Zaslavsky (1975): #topes = Σ \|μ\| (CITED from memory of BLSWZ §4.6, not re-checked). For proper V, the OM form of Zaslavsky's 1977 dissection theorem would need TRT to apply; our proof does not. |
| Theorem 1-OM, Theorem 2-OM for proper V; Theorem C-OM | **NOT FOUND** | MSS cover the open cone only ([NovGT, §2.2]); no source read states a closed-cone support lattice for OMs. |
| Brown/Bidigare for OM face monoids | KNOWN in substance | Brown's theorem is LRB-general (read in [AudC, §B.4]). We did not check whether Brown or Bidigare name OMs explicitly. |

---

## 11. Corrections to existing notes (reported, not edited)

1. **`notes/general_theory.md` §3, "Combinatorial version of (a)".** It says
   that Lemma 0.2 "needs an oriented-matroid proof, e.g. via shellability
   of T-convex sets".
   - It is KNOWN via shellability (Mücksch, Cor. 2.23, above).
   - It also has the elementary proof of Lemma 2.1 here.
   - The paragraph's CONJECTURED tag for Theorems 1 and 2 can become
     PROVEN, citing this note after audit. Theorem G\* extends too
     (Theorem C-OM).
2. **Same paragraph, "only three ingredients are used".** The full list is
   in §7. Two items are missing:
   - P. Hall / BWW or Prop. A, which are pure poset topology;
   - the simple connectivity of tope boundaries for r ≥ 4, the one point
     where the cell structure (TRT) is needed beyond homology.
3. **`notes/general_theory.md` §1.5 and [AudA, §C]** say the chamber
   orientation comes "by a fixed orientation of R^d". That is correct, but
   the OM form shows that only the integral fundamental cycle of Δ(faces ≠ O)
   is needed. Recording this would make the realizable proofs independent of
   determinants. This is optional and changes no statement.

No error was found in the real-case statements or proofs that were re-used.

---

## Reproduce

From `compute/` (plain Python 3, standard library only):

    python3 oriented_matroid_cones.py > output/oriented_matroid_cones.txt   # ~60 s, ends "ALL PASS", exit 0
    python3 oriented_matroid_cones.py --quick                                # ~30 s: A3, Pappus, one non-Pappus, subsampled [lem02]
    python3 -m unittest test_oriented_matroid_cones                          # ~15 s, includes the controls

The archived output is `compute/output/oriented_matroid_cones.txt`.
