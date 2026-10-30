# Audit of `notes/oriented_matroid_cones.md` (Theorems 1, 2, C for T-convex sets of oriented matroids)

This is an independent, adversarial audit of `notes/oriented_matroid_cones.md`
("[OMC]"). It covers the claims [OMC] tags PROVEN:
- Lemma 0.2-OM;
- Theorem 1-OM;
- Theorem 2-OM;
- Prop. 3-OM, Prop. B-OM and Theorem C-OM;
- the claim that realizability is never used.

The proofs were re-derived by hand and every cited source that could be
opened was read in the source. The computations use new code,
`compute/audit_oriented_matroid_cones.py`, which imports nothing from
`compute/oriented_matroid_cones.py` or from any other script in the
repository.

**Verdict: every audited claim HOLDS. No mathematical error was found.
Realizability is indeed never used: every result of Brown that [OMC]
cites is stated, in the source, for an arbitrary finite left-regular band
over an arbitrary field. One attribution in [OMC] is wrong. It says the
r ≥ 4 step of Theorem 1-OM uses "BLSWZ Thm 4.3.3, i.e. the topological
representation theorem". Thm 4.3.3 is the shellability theorem, not the
topological representation theorem (TRT, BLSWZ Thm 5.2.1). Nothing in
[OMC] needs the TRT, and for r = 4 not even shellability is needed. All
checks pass on seven oriented matroids, among them two rank-4
non-realizable ones, and every rank is checked exactly over Z.**

| Claim of [OMC] | Verdict | Notes |
|---|---|---|
| Lemma 0.2-OM (closed-cone lemma: contractible if V ≠ 𝒯, ≃ S^{r−1} if V = 𝒯; the same for the fibres) | **HOLDS** | Re-derived step by step (§2). The proof is correct and needs only looplessness. It gives the homotopy type of Δ(L ∖ 0) as S^{r−1} without the TRT. |
| Theorem 1-OM (i): homology free, concentrated in degree r − 2, of rank m(V) ≥ 0, for every r | **HOLDS** | Purely combinatorial, as claimed (§3). |
| Theorem 1-OM (ii): Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{r−2}; "needs the TRT only for r ≥ 4" | **HOLDS WITH FIXES** (attribution only) | Nothing for r ≤ 3 uses anything beyond (i) (§3.1). For r ≥ 4 the one extra input is π_1(B_T) = 1 for tope boundaries B_T. That is not the TRT. For r = 4 it follows from OM combinatorics and the classification of surfaces (§3.2). For r ≥ 5 it follows from shellability (BLSWZ Prop. 4.3.2), a combinatorial result (§3.3). Fix the phrase "Thm 4.3.3, i.e. the topological representation theorem". |
| Theorem 2-OM (Zaslavsky count) | **HOLDS** | Re-derived, signs included (§4). |
| Prop. 3-OM ([Γ_V : S_E] = m(V); q ≤ dim Lie ≤ m) | **HOLDS** (given Brown) | Brown's rank argument transfers to the module Γ_V of kΣ_L (§5.2). |
| Prop. A-OM, Prop. B-OM (Γ/Lune ≅ H̃_{r−2}(L̄(M)) via C ↦ ρ_C) | **HOLDS** (B given Brown) | Re-derived, including the support argument of step 2 (§5.3). |
| Theorem C-OM / G\* (ρ_C span; q = m; (G1); det-twisted module identity) | **HOLDS** (given Brown) | (iv) holds at chain level (§5.4). COMPUTED: det(g) equals the chirotope sign c(g) for every automorphism tested. |
| "Realizability is used nowhere"; "Brown's §7 does not need realizability" | **HOLDS** | Brown read in the arXiv source (§1). Theorem 3 (Bidigare), its Corollary, the triangularization at the end of §7.2, and the rank argument in the proof of Theorem 4 are all stated for any finite LRB with identity, over any field. Brown does not name oriented matroids in §7. |
| Citations quoted second-hand (BLSWZ via Mücksch, Delucchi, Hochstättler–Welker) | **HOLD WITH FIXES** | All theorem numbers match the sources (§6). Two fixes: Delucchi does not attribute Prop. 4.3.2 to Lawrence, and Thm 4.3.3 ≠ TRT. BLSWZ itself: **NOT ACCESSIBLE**. |

---

## 1. Is realizability used? Brown's results, read in the source

**Source.** Brown, *Semigroups, rings, and Markov chains*, J. Theoret.
Probab. 13 (2000), arXiv:math/0006145. Read in the arXiv TeX source
(`semigroup.tex`). Theorem and equation numbers were recomputed from the
source: `\setcounter{theorem}{-1}` makes the first theorem Theorem 0, and
the first displayed equation is tagged (D), not numbered.

What [OMC] §5 and §7 cite, and what the source says:

| Cited as | In the source | Stated for |
|---|---|---|
| §2.1, hypotheses (2), (3) | §2.1 "Definition": S is an LRB if there are a lattice L and a surjection supp : S ↠ L with (2) supp xy = supp x ∨ supp y and (3) xy = x if supp y ≤ supp x. The section opens with "Let S be a semigroup (finite, with identity)". | any finite semigroup with identity |
| §7.2 Theorem 3 (Bidigare) | "There is an algebra surjection ψ: kS ↠ k^L whose kernel J is nilpotent. The X-component of ψ is the homomorphism χ_X: kS → k given by χ_X(y) = 1_{supp y ≤ X}." | §7 opens with "Throughout this section S denotes a LRB (finite, with identity)". §7.2 says "We therefore work in the semigroup algebra kS of S over an arbitrary field k." |
| its Corollary | "Every irreducible representation of kS is 1-dimensional. There is one such for each X ∈ L, given by the character χ_X." | same |
| triangularization (end of §7.2) | for any finite-dimensional kS-module, the elements of kS are simultaneously triangularizable, with diagonal entries χ_{X_i}(a) | same |
| rank argument (proof of Theorem 4, §7.3) | "the rank of a projection is the multiplicity of 1 as an eigenvalue" | Theorem 4: "Let S be a finite LRB with identity, let k be a field" |

So every cited statement is LRB-general and field-general. Brown says
explicitly that Bidigare proved the result for hyperplane face semigroups
and that "the proof in general is identical". Bidigare's thesis: **NOT
ACCESSIBLE**. The only mention of oriented matroids in Brown is in
Appendix A, which points to BLSWZ Prop. 4.2.6 for a proof about convex sets
of chambers. So Brown never names OM face semigroups. That does not matter,
because his theorems need only the LRB axioms.

**The hypotheses for OMs, re-checked.** Take the covector monoid (L, ∘),
with identity 0, and supp X := z(X) in the lattice of flats ordered by
reverse inclusion, so that join = intersection.
- Surjective: every flat is a zero set (BLSWZ §4.1, CITED in [OMC] as (O2);
  standard).
- (2): z(X ∘ Y) = z(X) ∩ z(Y), coordinatewise.
- (3): if z(Y) ⊇ z(X), then Y vanishes wherever X does, so X ∘ Y = X.
- The same holds for the sub-monoid Σ_L = {X : X_{S_max} = 0}. Its support
  lattice is the interval {flats ⊇ S_max}, which is a lattice.

[OMC] states (3) in this one-directional form, exactly as Brown does.

**How the rank argument is used.** Brown applies it to the chamber ideal
kC of S. [OMC] Prop. 3-OM(b), via [AudC, §B.3], applies it to the module
Γ_V = k·V of kΣ_L. This is legitimate, since the argument uses only three
things:
- that H ∈ Σ_L acts on Γ_V as an idempotent;
- that its image is spanned by {C ∈ V : C ≥ H}, so its rank is c_{z(H)};
- the triangularization, which Brown proves for every finite-dimensional
  module.

It is Brown's argument applied to a different module, not his Theorem 4
verbatim. [OMC] says "Brown's rank argument", which is accurate.

**Other inputs.** Every remaining input is one of the following:
- OM combinatorics: (O1)–(O3), which [OMC] proves or cites and which
  hold for all OMs;
- poset topology: Quillen's fibre lemma, the order-homotopy lemma, the
  nerve lemma, P. Hall, gluing, the carrier lemma;
- algebraic topology: Hurewicz and Whitehead.

None of these refers to a realization. The only input that is not
covector combinatorics is π_1(B_T) = 1 for r ≥ 4 (§3), and that holds for
every OM. **Verdict: realizability is not used. HOLDS.**

---

## 2. Lemma 0.2-OM, re-derived by hand

Setting: M loopless of rank r, f ∈ E ∖ S, π : K → K′, X ↦ X|_{E∖f}.

**Step 1 (f not a coloop).**
- π is well defined. X|_{E∖f} = 0 would mean that X has support {f}, so
  that f is a coloop. This is the (⇒) of (O3): such an X is a cocircuit
  with zero set E ∖ f, so E ∖ f is a hyperplane. The image lies in
  L(M∖f) by (O1), and the S-conditions are unchanged because f ∉ S.
- The fibre is F_Y = π^{-1}(K′_{≤Y}) = {X ≠ 0 : X|_{E∖f} ≤ Y}.
- For X ∈ F_Y and a lift Ŷ, X ∘ Ŷ restricts to X|_{E∖f} ∘ Y = Y and lies
  above X.
- With exactly one lift Ŷ, every X ∈ F_Y satisfies X ≤ X ∘ Ŷ = Ŷ, so F_Y
  is a cone.
- **At least two lifts.**
  - From Y^+ and Y^−: their separation set is {f}, so elimination at f
    gives a covector that is 0 at f and equals Y^+ ∘ Y^− = Y elsewhere.
    That is Y^0.
  - From Y^0 and Y^±: the composition Y^0 ∘ (−Y^±) equals Y on supp Y,
    equals 0 on z(Y) ∖ f (because −Y^± vanishes there), and equals ∓ at
    f. So Y^∓ exists.
  - For X ∈ F_Y, X ∘ Y^0 is the lift with f-entry X_f. Hence X ≤ Y^{X_f},
    and Y^0 ≤ Y^±.
  - A chain cannot contain f-entries + and −, because such elements are
    incomparable. So every chain lies in D^+ or in D^−.
  - D^+ ∩ D^− = (0, Y^0], with Y^0 ≠ 0 because Y ≠ 0.
  - Three cones; gluing gives a contractible fibre.
- Quillen's fibre lemma applies. **Checked.**

**Step 2 (f a coloop).**
- L(M) = L(M∖f) × {+, 0, −}. The proof via e_f^± ∘ X and elimination at f
  is correct: the separation set of e_f^+ ∘ X and e_f^− ∘ X is {f}.
- φ (set the f-entry to +) is monotone on K_0 ∪ K_+, with X ≤ φ(X) ≥
  e_f^+, and e_f^+ ∈ K because f ∉ S. So id ≃ φ ≃ const.
- K_0 ∪ K_± are down-sets of K, no chain meets both K_+ and K_−, and their
  intersection is K_0 ≅ K′.
- Gluing gives Δ(K) ≃ ΣΔ(K′), with Σ∅ = S^0. **Checked.**

**Induction and base.**
- (b), base E = S: s is a tope and is the top of K.
- (a): the count of coloop steps is right. Each element is deleted once,
  a coloop deletion lowers the rank by 1 and a non-coloop deletion keeps
  it, and the rank goes from r to 0. **Checked.**

**Gluing lemma.** The proof by collapsing contractible subcomplexes is
standard and correct. With B = ∅ the union is two contractible
components, ≃ S^0.

**Remark.** Lemma 2.1(a) is a homotopy statement: Δ(L ∖ 0) ≃ S^{r−1}. The
fibre lemma and gluing give homotopy equivalences, so the homotopy type of
the sphere comes out purely combinatorially, without TRT or shellability.
What it does *not* give is the homotopy type of a single tope boundary
(§3).

**Verdict: HOLDS.** The corollary "the same for every fibre over a flat"
follows from Lemma 1.1(a), re-checked: restriction to E ∖ Z is an order
isomorphism K_Z ≅ K(S ∖ Z, s) of the loopless OM M/Z, and V(S ∖ Z, s) ≠ ∅.
Lemma 1.1(b)–(d) were also re-derived. In (d), (⊇) uses that X ∘ W is
nonzero off Z, because W is; that is correct.

---

## 3. Theorem 1-OM and the r ≥ 4 split

(i) was re-derived. All the steps check:
- the fibres (Lemma 1.1 + Lemma 2.1);
- Prop. A, whose proof in [AudC, §A] uses only the fibre connectivity, the
  chain-length bound (O2) and the carrier lemma;
- Step 4's long exact sequence, including the primitive vector (ω_T)_T for
  V = 𝒯;
- P. Hall.

Lemma 2.2(a)–(c) and Lemma 2.3 were re-derived as well. The nerve
argument uses −T ∈ K(A, −T_A), so every intersection of the cover is
contractible by Lemma 2.1(b).

### 3.1 What is used for r ≤ 3

Nothing beyond (i) and the dimension bound. For r = 2, Δ(Λ̄(V)) is a finite
set with H̃_0 free of rank m. For r = 3 it is a connected graph, since it
has dimension ≤ 1 and H̃_0 = 0, and so it is a wedge of rank-H_1 circles.
**No TRT, no shellability, no cell structure.**

### 3.2 What is used for r ≥ 4, exactly

The proof needs π_1(X) = 1 for X = Δ(Q′). Since Z_V is built from X by
attaching the cones Δ(L_{(0,T]}) along the B_T = Δ(L_{(0,T)}), van Kampen
gives π_1(Z_V) = π_1(X) / ⟨⟨images of π_1(B_T)⟩⟩. So the input needed is
exactly

  **(π) every tope boundary B_T is simply connected (r ≥ 4).**

The rest of the step follows:
- (π) makes the pair (cone, B_T) 2-connected, so π_1(X) ≅ π_1(Z_V) = 1.
- π_1(Δ(Λ̄(V))) is a retract of π_1(X), because Δ(f) ∘ g ≃ id (Prop. A).
- Hurewicz and Whitehead finish.

Lemma 2.2 gives only that B_T is a homology (r − 2)-sphere with ΣB_T ≃
S^{r−1}. That does not imply (π): the suspension of any homology sphere,
for instance Poincaré's, is a homotopy sphere. So [OMC] is right that
something beyond Lemma 2.2 is needed. But it is wrong about what that
something is.

**(π) for r = 4 is elementary (PROVEN here).** B_T is the order complex of
the covectors of dimensions 1, 2, 3 below T, so it is 2-dimensional.
- *Every edge lies in exactly two triangles.* The missing element ranges
  over an interval of length 2 of L. Each such interval [X, Z] is
  isomorphic, by contraction and restriction, to an interval [0, tope] of
  a rank-2 OM, and a rank-2 tope covers exactly two cocircuits.
- *The link of a vertex X is a cycle.*
  - If dim X = 1, the link is Δ((X, T)). It is isomorphic to a tope
    boundary of the rank-3 restriction M|_{z(X)}, so it is a graph with
    the homology of S^1 whose vertices all have degree 2, i.e. one cycle.
  - If dim X = 3, the link is Δ((0, X)), a tope boundary of the rank-3
    contraction M/z(X). Again one cycle.
  - If dim X = 2, the link is the join S^0 ∗ S^0, a 4-cycle.
- So B_T is a closed surface. It is connected, with χ = 2 by Lemma 2.2(a),
  so it is S^2 by the classification of surfaces.

Hence **Theorem 1-OM(ii) holds for r ≤ 4 with no input beyond OM
combinatorics and classical topology.** COMPUTED: every tope boundary of
A_4, N and non-Pappus ⊕ coloop passes this closed-surface test (§7).

**(π) for r ≥ 5.** By the same induction, B_T is a closed PL manifold with
the homology of S^{r−2}, but simple connectivity no longer follows. It does
follow from shellability:
- BLSWZ Prop. 4.3.2: every linear extension of T(M, B) induces a recursive
  coatom ordering of the face lattice. Read as quoted in Delucchi,
  arXiv:0705.3107, Thm 3.5.
- A recursive coatom ordering of L̂ restricts to one of [0, T] (condition
  (1) of the definition, Delucchi Def. 2.2, after Björner–Wachs Def. 5.10).
- So Δ((0, T)) is shellable (Björner; Björner–Wachs, as quoted in
  Delucchi Thm 2.3), hence ≃ a wedge of (r − 2)-spheres, hence ≃ S^{r−2}
  by Lemma 2.2.

Delucchi remarks (Remark 3.9) that "the proofs of [BLSWZ,
Proposition 4.3.1 and 4.3.2] are constructive". That is, they are proofs
from the OM axioms, not from the TRT. The proofs themselves: **NOT
ACCESSIBLE** (BLSWZ not opened).

### 3.3 Fixes (wording; no statement changes)

1. [OMC] Verdict table, Theorem 1 row: "comes from the cell structure (BLSWZ
   Thm 4.3.3, i.e. the topological representation theorem)". Thm 4.3.3 is
   the shellability theorem, as quoted in Mücksch, arXiv:2211.14083, Thm
   2.21: "L ∖ {0} … is isomorphic to the face poset of a shellable regular
   cell decomposition of the (r − 1)-sphere. Furthermore, every linear
   extension of T(M, B) is a shelling". The TRT is BLSWZ Thm 5.2.1
   (Mücksch, Remark 2.4).
   - Suggested: "for r ≥ 5 it also uses simple connectivity of tope
     boundaries, which follows from shellability (BLSWZ Prop. 4.3.2 /
     Thm 4.3.3); for r = 4 it follows from Lemma 2.2 and the classification
     of surfaces".
2. Same fix in §0 (O4) ("(O4) is used only once, in Theorem 1 for
   r ≥ 4"), in §3 ("PROVEN given (O4) for r ≥ 4"), in the §3 paragraph
   "What the r ≥ 4 step needs", and in the §7 ledger row "Cell facts"
   ("transfers via TRT"). (O4) is needed only for r ≥ 5, and only the
   shellability half of it.
3. [OMC] §0 (O4): "Proposition 4.3.2 (Lawrence, as quoted in Delucchi …
   Thm 3.5)". Delucchi's Theorem 3.5 is headed "[Proposition 4.3.2 of
   BLSWZ]" and names no author. Drop "Lawrence", or source it elsewhere.

The tag "PROVEN given (O4) for r ≥ 4" is not wrong, since (O4) is cited
and suffices. It is stronger than needed.

---

## 4. Theorem 2-OM, re-derived

- For Z ∈ Λ(V), the sum f(Z) = Σ_{X ∈ F(V), z(X) ⊇ Z} (−1)^{dim X} is
  1 − χ(Δ(K_Z)): X = 0 gives 1, and Lemma 2.3 gives −χ for the rest.
- By Lemma 1.1 and Lemma 2.1: f = 0 if Z ⊉ S_max (contractible),
  f = 1 − (1 + (−1)^{dim Z − 1}) = (−1)^{dim Z} for a sphere, and f = 1
  at Z = E.
- So f(Z) = (−1)^{dim Z} [Z ⊇ S_max].
- f(Z) = Σ_{Z′ ≤ Z} (−1)^{dim Z′} g(Z′), where ≤ is reverse inclusion.
- Möbius inversion at the top ∅, with g(∅) = #V and dim ∅ = r, gives
  (−1)^r #V = Σ_{Z ⊇ S_max} μ(Z, ∅)(−1)^{dim Z}. Equivalently
  #V = Σ (−1)^{rk Z} μ(Z, ∅).
- Lemma 1.1(b) puts every flat ⊇ S_max in Λ(V).

Lemma 2.3 uses only the homology in Lemma 2.2(c). **HOLDS.**

---

## 5. Prop. 3-OM, Prop. A-OM, Prop. B-OM, Theorem C-OM

### 5.1 Lemma L-OM
Re-derived. In (i)(⇒), H ∘ (−H ∘ D) = (H ∘ −H) ∘ D = H ∘ D = D, so −H ∘ D
lies in the lune, and its e-entry is −D_e. In (ii), −H ∘ D ≠ D when H ≠ 0.
**Checked.**

### 5.2 Prop. 3-OM
- (a): the adjoint of C ↦ H ∘ C sends D to the full lune L(H, D) when
  D ≥ H. It is contained in V by Lemma L-OM(i), and is non-singleton by
  (ii). Orthogonal complements behave because the standard form on k^V is
  nondegenerate.
- (b): c_{z(H)} = #(V|z(H)), by the bijection C ↦ C|_{z(H)}. Its inverse
  is Y ↦ H ∘ Ŷ, and the bijection carries V onto V|Z because S ⊆ z(H).
- Brown's rank argument (§1) gives c_Y = Σ_{S_max ⊆ Z ⊆ Y} [Γ_V : S_Z].
  Theorem 2-OM for V|Y, together with the identification of the flats of
  M|_Y above S_max(V|Y) (Lemma 1.1(c) for V|Y), gives
  #(V|Y) = Σ_{S_max ⊆ Z ⊆ Y} m(V|Z).
- Möbius inversion: [Γ_V : S_Z] = m(V|Z).
- dim Lie_L(Γ_V) ≤ [Γ_V : S_E], because Lie_L is a submodule that is a sum
  of copies of S_E (χ_E(H) = [H = 0]).

**HOLDS** (given Brown).

### 5.3 Prop. A-OM and Prop. B-OM
- Prop. A: the proof in [AudC, §A] uses the fibres of Step 2 (including
  that they are nonempty: Z ∈ Λ(V) is the zero set of some X ∈ F(V) ∖ 0),
  the chain count from (O2), and the carrier lemma. It transfers word for
  word. **Checked.**
- Prop. B, step 2, re-derived:
  - A face σ with nonzero coefficient in z = ∂Σ_{C∈ℒ} ω_C contains no
    tope, because a tope in σ is the top of every simplex containing σ.
  - Its top element Y lies below some C ∈ ℒ and some C′ ∉ ℒ. They differ
    at some e ∈ z(H), so Y_e = 0, and the same holds for every vertex of σ.
  - g(Y) = z(Y) ∩ z(H) is a flat ≠ E, ∅, it is monotone, and f ≤ g.
  - g_#(z) is a cycle in the cone with apex z(H). For r = 2 it has
    augmentation 0, being a boundary.
  - A boundary of top degree r − 2 is 0.

  **Checked.**
- Steps 1, 3 and 4 check. Universal coefficients apply because the
  integral homology is free and concentrated in one degree.

**HOLDS** (B given Brown).

### 5.4 Theorem C-OM
- (i): §3 Step 4 and Prop. A.
- (ii): inclusion of top cycles. Λ̄(V) is an induced subposet of L̄(M),
  both complexes have dimension ≤ r − 2, and for r = 2 the reduced 0-cycles
  still inject.
- (iii): from (ii) and Prop. 3-OM.
- (iv):
  - H_{r−1}(Δ(L ∖ 0)) = Z_{r−1} = Zω, so g·ω = ±ω at chain level.
  - g·ω_C = (g·ω)_{gC} = det(g) ω_{gC}.
  - f is equivariant, so g·ρ_C = det(g) ρ_{gC}.
  - Lune is Aut-stable.
  - The identification Γ_V/(Γ_V ∩ Lune) ≅ H̃_{r−2}(Δ(Λ̄(V))) is
    Stab(V)-equivariant after the det twist.

  **Checked.**

**An observation (COMPUTED, not proven here).** On all 7 OMs tested, 346
automorphisms in total, det(g) equals the chirotope sign c(g) defined by
χ(gB) = c(g) χ(B), where (gB) carries the signs of g. For realizable M
with g induced by a linear map A, a short computation gives
c(g) = sign det A. So this identity explains [OMC]'s remark "det(g) here
is sign det(g)", and extends it to all OMs. It would make (iv) computable
from the chirotope alone. Optional; nothing depends on it.

**HOLDS** (given Brown).

---

## 6. Second-hand citations, checked in the sources

| [OMC] says | Source, as read | Status |
|---|---|---|
| BLSWZ Thm 4.3.3 "as quoted … in Mücksch, arXiv:2211.14083, Thm 2.21" | Mücksch Thm 2.21 = [BLSWZ, Thm 4.3.3]: L ∖ {0} is the face poset of a shellable regular cell decomposition of S^{r−1}, and linear extensions of T(M, B) are shellings. Numbering recomputed from the TeX: theorems share the equation counter within sections, and §2 has no numbered equations before it. | matches |
| BLSWZ Prop. 4.3.2 "(Lawrence, as quoted in Delucchi, arXiv:0705.3107, Thm 3.5)" | Delucchi Thm 3.5 = "[Proposition 4.3.2 of BLSWZ]: every linear extension of the tope poset T_B(M) induces a recursive coatom ordering". No attribution to Lawrence. | number matches; **drop "Lawrence"** |
| TRT = BLSWZ Thm 5.2.1 | Mücksch Remark 2.4 cites [BLSWZ, Thm 5.2.1] for Folkman–Lawrence. | matches |
| BLSWZ Prop. 4.2.6 "as quoted in Mücksch, Lemma 2.17" | Mücksch Lemma 2.17 = [BLSWZ, Prop. 4.2.6] (convexity via geodesics). | matches |
| Mücksch Cor. 2.23 (shellable balls), proof via Thm 4.3.3 and Prop. 4.7.26 | as described. As printed, the corollary does not exclude Q = 𝒯, where L(Q) is the whole sphere. Prop. 2.22 needs k < t. [OMC]'s reading "Q ≠ 𝒯" is the correct one. | matches ([OMC] states it correctly) |
| Hochstättler–Welker Thm 1.2; Lemma 2.5 = BLSWZ Lemma 4.3.11 | Thm 1.2: a nonempty supertope is contractible as a subposet of T_R. Lemma 2.5 is headed "[Lemma 4.3.11 \cite{thebook}]". Numbering recomputed: shared counter, §2 has Prop., Cor., Prop., Situation before it. | matches |
| Brown §2.1, §7.2 Thm 3, Corollary, §7.3 | see §1 | matches |
| BLSWZ book itself; Bidigare's thesis | — | **NOT ACCESSIBLE** (not opened) |

---

## 7. Computations

`compute/audit_oriented_matroid_cones.py`, new code, standard library
only. Each OM is built from a chirotope and certified twice:
- the chirotope axioms: basis exchange + 3-term Grassmann–Plücker
  (BLSWZ Thm 3.6.2, CITED);
- the cocircuit axioms checked directly on all pairs of cocircuits; the
  covectors are then the compositions of cocircuits, and covector
  elimination is also checked on 3000 random pairs.

Cones are enumerated as the distinct nonempty V(s), keyed by S_max. Every
listed check runs on **every** T-convex set of every OM. Only Lemma 0.2 is
sampled in rank 4.

| OM | rank | realizable | covectors | topes | \|μ\| | T-convex sets | \|Aut\| | #det = −1 | Σ\|Stab\| | untwisted identity holds |
|---|---|---|---|---|---|---|---|---|---|---|
| A_3 | 3 | yes | 75 | 24 | 6 | 219 | 48 | 24 | 576 | 128/219 |
| B_3 | 3 | yes | 147 | 48 | 15 | 941 | 48 | 24 | 1680 | 826/941 |
| non-Pappus, χ(XYZ) = +1 | 3 | **no** | 195 | 58 | 20 | 1295 | 2 | 1 | 1296 | 1294/1295 |
| non-Pappus, χ(XYZ) = −1 | 3 | **no** | 195 | 58 | 20 | 1295 | 2 | 1 | 1296 | 1294/1295 |
| A_4 | 4 | yes | 541 | 120 | 24 | 4231 | **240** | 120 | 9360 | 4171/4231 |
| **N** (lifting of non-Pappus) | **4** | **no** | 1737 | 244 | 76 | **12965** | 2 | 0 | 12966 | 12965/12965 |
| **non-Pappus ⊕ coloop** | **4** | **no** | 585 | 116 | 20 | 3885 | 4 | **2** | 5184 | **2588/3885** |

**The rank-4 non-realizable OMs.**
- **N = (M\*[p])\***, where M is non-Pappus (+) and M\*[p] is the
  lexicographic extension [0⁺ 1⁻ 2⁺ 3⁻ 4⁺ 5⁻] of the rank-6 dual.
  - The dual, the extension and N each pass the axioms.
  - N/p equals M up to a global sign (checked). So N contains the
    non-Pappus OM as a minor, and is not realizable, because minors of
    realizable OMs are realizable.
  - The certificate for M: its chirotope vanishes exactly on the 8
    non-Pappus lines. By Pappus's theorem that matroid is not
    representable over any field.
  - p is not a coloop of N, and N is simple.
- **non-Pappus ⊕ coloop** is non-realizable for the same reason. It is
  included because in rank 4 the antipodal map has det = +1, so on N the
  twist is invisible (12965/12965 untwisted). In the coloop sum the
  coloop reflection has det = −1, and the untwisted identity fails on
  1297 cones while the twisted one holds on all of them.

**Checks, all passing on every row** (`compute/output/audit_oriented_matroid_cones.txt`):
- [flatL], [zas] (Theorem 2-OM), [wedge] (Theorem 1-OM(i), GF(p) ranks);
- [brown] (c_Z independent of X; Σ μ(E, Z) c_Z = m: Prop. 3-OM(b));
- [lunL] (Lemma L-OM(i), all (H, D));
- [rho] (Theorem C(i));
- [q=m], computed from lunes alone, with no ρ (Theorem C(ii));
- [G1]: rank of the lunes in V = #V − m = #V − q, and dim Lie_L(Γ_V)
  computed directly as a kernel = m (Theorem C(iii));
- [eq]: for every g ∈ Stab(V), the character of H̃_{r−2}(Δ(Λ̄(V))) equals
  det(g) · tr(g | (Γ_V + Lune)/Lune) (Theorem C(iv)). The left side is
  computed by the Hopf trace formula on the fixed subposet, so this side
  uses no ρ.
- **[Z], exact over Z on every cone:**
  - every boundary map of Δ(Λ̄(V)) has all invariant factors 1, so the
    homology is torsion-free;
  - the ρ_C (C ∈ V) have rank m over Q and all invariant factors 1, so
    they span H̃_{r−2}(Δ(Λ̄(V)); Z), not just a finite-index sublattice;
  - the Lune lattice has rank #𝒯 − |μ| over Q with all invariant
    factors 1.
- **[pi1] (rank 4):** π_1(Δ(Λ̄(V))) = 1 on every cone of A_4, N and
  non-Pappus ⊕ coloop. This is proven by a greedy presentation argument,
  which is sound when it succeeds.
- **[Btope]:** every tope boundary has the homology of S^{r−2}. In rank 4
  every B_T is a closed surface with χ = 2, i.e. S^2: hypothesis (π) on
  these instances.
- [omega]: Δ(L ∖ 0) is thin, and its ±1 fundamental cycle is unique up
  to sign by propagation. ∂ω_C avoids C (Lemma 2.2(b)).
- [propB]: rank C ↦ ρ_C = |μ| = dim Γ/Lune, and every lune is killed at
  chain level.
- [aut]: g·ρ_C = det(g) ρ_{gC} at chain level for every g and C. With det
  removed this fails on every OM that has a det = −1 element.
- [lem02] (Lemma 0.2-OM):
  - every sign condition with V(S, s) ≠ ∅ for the rank-3 OMs (19,683 or
    729 conditions);
  - 1500 random ones plus all with |S| ≤ 1 for the rank-4 OMs.
  - S = ∅ gives a homology S^{r−1}.
  - S ≠ ∅ gives a contractible K. This is shown as a **homotopy**
    statement by beat-point reduction to a single point (Stong) on all
    but a handful: 9214/9215 (non-Pappus), 1011/1035 (N), 732/733
    (coloop sum). The rest are acyclic.
  - The trichotomy remark of [OMC] (empty / sphere iff K = −K / acyclic)
    holds on every tested s.
- [lem22a]: Δ(L ∖ {0, T}) is acyclic for every tope (Lemma 2.2(a)).

**Positive controls.**
- A_3, B_3 and non-Pappus reproduce [OMC]'s table exactly: (cones, |μ|,
  |Aut|, Σ|Stab|, untwisted) = (219, 6, 48, 576, 128), (941, 15, 48, 1680,
  826) and (1295, 20, 2, 1296, 1294). This is with independent code.
- A_4: 4231 cones = A001035(5), the number of labelled posets on 5 points.
  Restricted to the linear group S_5, the run gives Σ|Stab| = 7560 and the
  untwisted identity on 4231/4231, matching `compute/output/
  general_theory.txt` [A4]. There, det(σ) = sgn(σ) for every σ.

**Negative controls (each fires).**
- A chirotope with one basis sign flipped is rejected.
- The Pappus chirotope is realizable: its zero set is its 9 lines, and it
  fails the non-Pappus certificate.
- The torsion detector finds Z/2 in a 6-vertex RP^2. The π_1 and S^2 tests
  reject RP^2 and accept the tetrahedron boundary.
- V = {T, −T} is not T-convex. Its closed face complex has two components,
  and the Zaslavsky-type sum gives 8 (B_3) or 34 (N) instead of 2.
- Summing Theorem 2 over all of Λ(V), instead of over the flats ⊇ S_max,
  gives the wrong count on every cone except V = 𝒯.
- Removing the det twist breaks [eq] or [aut] whenever a det = −1 element
  exists.

**Limitations.**
- The two non-realizable rank-4 OMs have small automorphism groups (2
  and 4). The large-group test (|Aut| = 240) is realizable (A_4). No
  non-realizable OM with a large symmetry group was found cheaply. A
  linear-algebra argument shows that a Pappus realization cannot carry an
  order-3 symmetry preserving the perturbed line.
- Lemma 0.2 in rank 4 is sampled (1520 of 59,049 sign conditions per OM).
- The [pi1] check is greedy; it succeeded everywhere, so no inconclusive
  case arose.
- The chirotope-axiom criterion (BLSWZ Thm 3.6.2) is cited, not opened.
  The direct cocircuit-axiom check is an independent certificate.

---

## 8. Corrections to report (not applied; `notes/oriented_matroid_cones.md` is unchanged)

1. **TRT attribution (§3.3 above).** Wherever [OMC] says the r ≥ 4 step of
   Theorem 1-OM uses "BLSWZ Thm 4.3.3, i.e. the topological
   representation theorem": Verdict table, §0 (O4), §3, §7 ledger, and
   §11 item 2 ("the one point where the cell structure (TRT) is needed").
   Replace with: "simple connectivity of tope boundaries; for r = 4 this
   follows from Lemma 2.2 and the classification of surfaces; for r ≥ 5
   from shellability (BLSWZ Prop. 4.3.2 / Thm 4.3.3)". The headline
   "Where realizability is used: nowhere" stands. The TRT is not used
   either.
2. **"Lawrence"** in (O4): not in Delucchi (§6).
3. **Optional.** §5 could say that the rank argument is Brown's proof of
   Theorem 4, applied to the module Γ_V rather than to kC, and that Brown
   names oriented matroids only in Appendix A. [OMC] §10's last row ("We
   did not check whether Brown or Bidigare name OMs explicitly") can be
   resolved: Brown does not, Bidigare is not accessible, and neither is
   needed.
4. **Optional.** §8 "Limitations" of [OMC] is now addressed: rank-4
   non-realizable OMs, exact integral ranks, and det = −1 in rank 4 are
   all tested here.

Not audited: [OMC] §9 (COMs and LRBs) and the prior-art searches of §10
beyond the citation checks of §6.

---

## Reproduce

From `compute/` (plain Python 3, standard library only; uses
`$AUDIT_WORKERS` worker processes, default 3):

    python3 audit_oriented_matroid_cones.py > output/audit_oriented_matroid_cones.txt   # ~6 min, ends "ALL PASS", exit 0
    python3 audit_oriented_matroid_cones.py --quick     # ~8 s: A3, B3, non-Pappus, N on 400 cones
    python3 -m unittest test_audit_oriented_matroid_cones   # ~5 s

The archived output is `compute/output/audit_oriented_matroid_cones.txt`.
The sources read for §1 and §6 are the arXiv TeX sources of
arXiv:math/0006145, arXiv:2211.14083, arXiv:0705.3107 and arXiv:1805.07183
(`https://arxiv.org/e-print/<id>`).
