# Audit: the fixed-point character formula for cones (EZ, CF, Prop. W)

This is an independent adversarial audit of `notes/fixed_point_formula.md`
("[FP]"). It covers the claims [FP] tags PROVEN:
- Theorem EZ, the equivariant cone Zaslavsky identity;
- Corollary EZ′ (cone PBW);
- Lemma F and Theorem CF, the closed formula for μ(Λ(V)^g);
- Corollaries P, Full, V and CF-braid;
- Lemmas A, B, C and Proposition W, the Weisner recursion;
- the claim that the braid case agrees with [Thm, eq. closed].

Other sources:
- [GT] = `notes/general_theory.md`;
- [Thm] = `notes/poset_jks_theorem.tex`.

Every step was re-derived by hand, and every hypothesis was checked against
the step that uses it. The computations are in
`compute/audit_fixed_point_formula.py`, written for this audit. It imports
nothing from the repository and builds the faces by a method no earlier
script uses (§G). No existing file was changed.

Tags for this audit's own claims: **PROVEN** (proof given here) and
**COMPUTED** (script and command in Reproduce).

## Verdict

**[FP]'s PROVEN claims hold. The fixes are two wording fixes to hypotheses
and some missing routine details in the Hopf-trace step. No conclusion
changes.** The proofs cover every finite-order linear symmetry g with
gA = A and gV = V, including g outside any reflection group and
non-orthogonal g. Prop. W's hypothesis that Fix(g) is a flat is sufficient
but not necessary. This audit proves Prop. W, with the same index set,
under the weaker hypothesis **"Fix(g) lies in some hyperplane of A"**
(§C.3). On every pair tested, that weaker hypothesis is also exactly when
the identity holds.

| Claim | Verdict |
|---|---|
| Lemma A (equivariant localization) | **HOLDS.** |
| Theorem EZ | **HOLDS WITH FIXES.** The Hopf-trace step is correct. It should add three routine facts: the augmentation commutes with g; the sign of a fixed cell is the degree of g on (closed cell, boundary), which does not depend on the orientations chosen; and F̄ is pointed because A is essential. §A.1 gives a second proof of Step 1 with no orientations at all, by restricting to Fix(g). |
| Corollary EZ′ (cone PBW) | **HOLDS**, given [GT] Theorem 1 (for c ≥ 2). |
| Lemma F | **HOLDS.** |
| Theorem CF | **HOLDS.** |
| Corollary P | **HOLDS.** Its second sentence ("g ∈ W ∖ 1 … free C[Stab_W(V)]-module") needs W to be the reflection group of A, with A its reflection arrangement. [FP] §1 assumes this without saying so (§D). |
| Corollary Full | **HOLDS.** The verdict-table line drops the convention that a Y-term is 0 when a hyperplane through Y contains Fix(g); §3.1 states it. |
| Corollary V | **HOLDS.** The remark after it (Steinberg) needs the same hypothesis on W as Cor. P. |
| Corollary CF-braid | **HOLDS.** |
| Lemma B | **HOLDS WITH A FIX.** B(a) assumes a ∈ Λ(V)^g, but Prop. W applies B(a) to *prove* a = Fix(g) ∈ Λ(V), which is circular as written. The proof of B(a) never uses a ∈ Λ(V). The hypothesis should read "a is a g-stable flat containing Fix(g)" (§C.1). |
| Lemma C | **HOLDS.** |
| Proposition W | **HOLDS** (with Lemma B fixed). The hypothesis "Fix(g) is a flat" is **sufficient, not necessary**. [FP] says it "is needed", which overstates. Proposition W′ (§C.3, PROVEN here): the same identity holds whenever g ≠ 1 and Fix(g) lies in a hyperplane of A. COMPUTED: on all 963 tested pairs with Fix(g) not a flat, the identity holds iff Fix(g) lies in a hyperplane (372 hold, 591 fail). The "only if" is not proven. The cl(Fix g) variant of [FP] is also COMPUTED. |
| Braid case vs [Thm, eq. closed] | **HOLDS, as [FP] states it.** Both sides are proven formulas for the same number, so they agree; COMPUTED for every poset with n ≤ 5 and every automorphism. [FP] gives no algebraic reduction of CF-braid to eq. closed and says so. This audit does not supply one either (§E). |

Three specific questions:
1. **Does the Hopf-trace argument need g to act cellularly, with orientation
   conventions spelled out?**
   - g does act cellularly. It permutes the faces of A, and S is the unit
     sphere of a ⟨g⟩-invariant inner product.
   - Only the signs of g-fixed cells enter the trace, and [FP] computes
     those correctly as det(g|_{span F}).
   - The missing details are listed in the table. None is a gap.
   - §A.1 gives an alternative proof that avoids orientations entirely.
2. **Does "every finite-order symmetry" include g ∉ W, and does the proof
   cover it?**
   - Yes. EZ, CF, Lemma F, Cor. V and Prop. W never use W.
   - Only the W-specific sentences need W to be the reflection group of A:
     the second half of Cor. P, and the Steinberg remarks.
   - COMPUTED on two non-reflection arrangements:
     - one whose symmetries include reflections in planes outside A;
     - one with a non-orthogonal rational symmetry of order 6 whose fixed
       line lies in no hyperplane.
3. **Is Prop. W's hypothesis needed or merely sufficient?**
   - Merely sufficient. It can be weakened to "Fix(g) lies in a hyperplane
     of A", that is, cl(Fix g) ≠ R^d, with the same index set
     {X : X ∩ Fix(g) = 0} (Prop. W′, §C.3).
   - On the data the weaker hypothesis is sharp: every tested pair that
     fails it also fails the identity.
   - It cannot be dropped altogether, since it fails on 591 tested pairs.

---

## A. Theorem EZ

**Setting** ([FP] §1):
- A is a finite central essential arrangement in R^d;
- V is a top-cone of A, with L = lin V;
- g is linear of finite order, with gA = A and gV = V.

**Step 1 (the Lefschetz count (2.1)).** Re-derived:
- S is the unit sphere of a ⟨g⟩-invariant inner product.
- The cells F ∩ S (F ≠ O a face) form a regular CW structure for any
  Euclidean structure, since radial projection carries one sphere to
  another face by face.
- g maps faces to faces, so it is a cellular homeomorphism of S. It maps
  K_Y = |V| ∩ Y ∩ S to itself when gY = Y.

The cellular chain map is g·[F] = ε[gF] once an orientation is chosen for
each cell. The trace only sees cells with gF = F. For such a cell the
coefficient is the degree of g on (F̄ ∩ S, ∂), and this degree does not
depend on the orientation chosen. [FP] computes it as follows:
- radially project F̄ ∩ S onto P = F̄ ∩ {ℓ = 1}, with ℓ a g-invariant form
  positive on F̄ ∖ 0;
- g acts on P as an affine automorphism with linear part
  g|_{ker ℓ ∩ span F};
- the degree of an affine automorphism of a compact convex body relative to
  its boundary is the sign of the determinant of its linear part;
- det(g|_{ker ℓ ∩ span F}) = det(g|_{span F}), because g = 1 on R·p.

This is correct. The form ℓ exists because F̄ is pointed, and F̄ is
pointed because A is essential. [FP] does not say this.

Three routine points [FP] leaves implicit:
- The augmented complex needs g to commute with the augmentation C_0 → C.
  It does: 0-cells are points, permuted with sign +1. So g acts trivially
  in degree −1, which is the case Y = 0.
- "The local degree at p" in [FP] should read "the degree of g on (P, ∂P)".
  For a homeomorphism the two agree.
- The Hopf trace formula is applied to a cellular, not simplicial, chain
  map. [FP] says correctly that it is an algebraic identity for any chain
  endomorphism of a finite-dimensional complex. It also cites the
  naturality of cellular ≅ singular homology for cellular maps, which is
  what makes the sphere case (degree det(g|_Y)) legitimate.

The three cases (Y = 0; Y ⊄ L; 0 ≠ Y ⊆ L) and (2.1) follow as [FP] states,
using [GT] Lemma 0.2 on C = |V| ∩ Y. C has full dimension in Y because
Y ∈ Λ(V), and C = Y iff Y ⊆ L because Y = −Y.

### A.1 A second proof of (2.1), with no orientations (PROVEN)

This proof uses Euler characteristics only, as in [GT, Thm 2]. It removes
the need to discuss orientation conventions.

*Facts.*
- (i) det(g|_X) = (−1)^{dim X − dim X^g} for every g-stable subspace X,
  where X^g = X ∩ Fix(g). Indeed g|_X is diagonalizable over C with
  eigenvalues roots of unity. det(g|_X) = (−1)^{m} where m is the
  multiplicity of −1. The eigenvalues other than ±1 come in conjugate
  pairs, so dim X − dim X^g ≡ m (mod 2).
- (ii) Let U = Fix(g) and A^U = {H ∩ U : H ∈ A, H ⊉ U}. This is an
  essential arrangement in U, because ∩A = 0. F ↦ F ∩ U is a bijection from
  the g-stable faces of A onto the faces of A^U.
  - It is well defined: averaging a point of F over ⟨g⟩ gives a point of
    F ∩ U.
  - It is surjective: the face of A with a given sign vector σ meets U, so
    it meets its own image and is g-stable.
  - It is injective because sign vectors determine faces.
  - F is open in span F, so dim(F ∩ U) = dim (span F)^g.
- (iii) Let Y ∈ Λ(V)^g. If Y^g ⊆ L, then Y ⊆ L. Proof: average a point of
  the interior (in Y) of C = |V| ∩ Y. The average p̄ is still interior,
  since that interior is convex and g-stable, and p̄ ∈ Y^g ⊆ L ⊆ |V|. So
  −p̄ ∈ C. For y ∈ Y and small ε, εy = (p̄ + εy) + (−p̄) ∈ C, so C = Y.
  This includes the case Y^g = 0. It is [FP] Lemma B(b) with Y^g in place
  of 0.

*Proof of (2.1).*
- By (i) and (ii), each fixed face F ⊆ |V| ∩ Y contributes
  (−1)^{dim F} det(g|_{span F}) = (−1)^{dim(F ∩ U)}.
- So f_g(Y) = Σ (−1)^{dim G} over the faces G of A^U inside the closed
  cone C′ = |V| ∩ Y^g.
- C′ has full dimension in Y^g: the point p̄ of (iii) is interior.
- Exactly as in the proof of [GT, Thm 2], with [GT] Lemma 0.2 in the
  space Y^g, the sum is:
  - 1 if Y^g = 0;
  - 0 if C′ ≠ Y^g;
  - (−1)^{dim Y^g} if C′ = Y^g, that is, if Y^g ⊆ L.
- By (iii), Y^g ⊆ L iff Y ⊆ L, and Y^g = 0 forces Y ⊆ L.
- So f_g(Y) = [Y ⊆ L](−1)^{dim Y^g} = [Y ⊆ L](−1)^{dim Y} det(g|_Y), by (i).
  This is (2.1). ∎

COMPUTED: (i) on every g-stable flat of every pair tested (`[par]`), and
(2.1) on every Y ∈ Λ(V)^g with determinants computed directly (`[2.1]`).
The negative control replaces det(g|_{span F}) by 1 and fails (§G).

**Steps 2–3.** Re-derived; correct.
- A g-stable face F ⊆ Y has g-stable span X ∈ Λ(V) with X ⊆ Y.
- Grouping by span gives f_g = Σ_{X ≤ Y} h_g(X) on the finite poset
  Λ(V)^g.
- Inversion at R^d gives (2.2). The faces with span R^d are the chambers of
  V.
- Lemma A converts each μ, and the X-term becomes (−1)^d det(g) χ_{V_X}(ḡ),
  because det(g|_X) det(ḡ) = det(g).

The X = R^d term occurs exactly when L = R^d. It equals 1, matching the
rank-0 convention χ = 1.

**Lemma A.** HOLDS:
- Lemma 0.1(c) of [GT] gives [X, R^d]_{Λ(V)} ≅ Λ(V_X) via Y ↦ Y/X;
- this map commutes with g;
- fixed points of an interval form the interval of the fixed subposet.

**Corollary EZ′.** HOLDS given [GT] Thm 1:
- the character of Lie(V_X) at ḡ is χ_{V_X}(ḡ), by Theorem 1 for V_X
  (codimension c ≥ 2), Hall and Hopf;
- for c = 1 the proper part is empty and the claim is direct;
- the induced character Σ_{X′ ∈ G·X, gX′ = X′} χ_{V_{X′}}(ḡ) uses only that
  conjugation by t ∈ G transports (A_X/X, V_X, ḡ) isomorphically;
- summing over orbits gives the right side of EZ.

## B. Lemma F, Theorem CF and the corollaries

**Lemma F.** HOLDS. Re-derived:
- If hK = K, the ⟨h⟩-average of a point of K lies in K ∩ Fix(h) and on no
  hyperplane. So no H ⊇ Fix(h).
- Conversely, a chamber of the restriction is the set of points of Fix(h)
  with a fixed nowhere-zero sign vector over B. It lies in the chamber K
  with that sign vector, and K meets hK.
- Distinct H may restrict to the same hyperplane of Fix(h). That is
  harmless.

COMPUTED (`[F]`): the restricted arrangement is built in coordinates on
Fix(g), and its chambers are enumerated separately.

**Theorem CF.** HOLDS. Re-derived:
- EZ applied to (A_Y/Y, V_Y, ḡ) for Y ∈ 𝓛^g needs:
  - lin V_Y = L/Y, from |V| = |V| + Y;
  - the flats of A_Y/Y inside L/Y are Z/Y with Y ⊆ Z ⊆ L, because every
    hyperplane through Z ⊇ Y lies in A_Y;
  - (V_Y)_{Z/Y} = V_Z, with the same induced map on R^d/Z;
  - the chambers of V_Y are the images of the chambers of A_Y in |V|.
    These are all open chambers of A_Y, and each lies in |V| or misses it,
    because S_max ⊆ A_Y.
- This gives c(Y, g) = Σ_{Z ⊇ Y in 𝓛^g} χ_{V_Z}(ḡ).
- Inversion from above on 𝓛^g (which has bottom 0) at Y = 0 gives CF.

**Corollary P.** The first sentence HOLDS for every g (𝓛^g = {0}). The
second needs W to act freely on the chambers of A, that is, A is the
reflection arrangement of W (§D).

**Corollary Full.** HOLDS. The term Y = R^d is μ(L(A)^g), since
A_{R^d} = ∅ has one chamber. The identity therefore reads
((−1)^d det(g) − 1) μ(L(A)^g) = Σ_{Y ≠ R^d}(…). So it determines μ(L(A)^g)
exactly when (−1)^d det(g) = −1, as [FP] says.

**Corollary V.** HOLDS. If H ⊇ L and H ⊇ Fix(g), then H ∈ A_Y for every
Y ⊆ L, and Lemma F gives c(Y, g) = 0. In the braid case, H_{ij} ⊇ L iff i
and j lie in one component, and H_{ij} ⊇ Fix(g) iff they lie in one
g-cycle. That is [FP]'s translation.

COMPUTED (`[V]`, `[P]`). In Cor. V, "H ⊇ L" means that H is in the
closure of S_max (all hyperplanes through L), not that H ∈ S_max. The two
differ in general, and only the first gives Cor. V. The counts of pairs
that vanish by Cor. V match [FP]'s table on A_3, A_4 and B_3 (§G).

**Corollary CF-braid.** HOLDS. Re-derived:
- 𝓛 ≅ Π(K)^op;
- a chamber of A_{Y_σ} in |C_P| is a tuple of linear extensions of the
  blocks;
- a tuple is fixed iff g^{|[B]|}|_B preserves a total order, i.e. is the
  identity;
- the sign is (−1)^{n−1} sgn(g) = (−1)^{n−3} sgn(g).

## C. Lemmas B, C and Proposition W

### C.1 Lemma B: a circular hypothesis (fix)

B(a) as stated: "If a ∈ Λ(V)^g contains Fix(g) and is a flat, then
X ∩ a ∈ Λ(V)^g." The proof of Prop. W says: "a := Fix(g) … lies in Λ(V) by
Lemma B(a) with X = R^d." With X = R^d the conclusion of B(a) is a ∈ Λ(V)^g,
which is exactly its hypothesis. As written, the step proves nothing.

The proof of B(a) uses only these facts:
- a is a flat, so X ∩ a is a flat;
- a ⊇ Fix(g), so p̄ ∈ X ∩ a;
- ga = a, so X ∩ a is g-stable.

So the fix is to restate B(a) as: **if a is a g-stable flat containing
Fix(g), then X ∩ a ∈ Λ(V)^g.** With that statement, a = Fix(g) (when it is
a flat) and a = cl(Fix g) both lie in Λ(V)^g, and Prop. W's first bullet is
valid. cl(Fix g) is g-stable, because g(cl Fix g) is a flat containing
Fix(g) of the same dimension.

COMPUTED (`[B]`): X ∩ cl(Fix g) ∈ Λ(V) for every X ∈ Λ(V)^g. Here
cl(Fix g) is not assumed to lie in Λ(V).

B(b) HOLDS. If X ∩ Fix(g) = 0, the average p̄ = 0 is interior to X ∩ |V|,
so X ∩ |V| = X.

### C.2 Lemma C and the Weisner step

Lemma C HOLDS:
- span(FG) = span F ∨ span G in L(A), where FG is the Tits product, so
  Λ(V) is a join-subsemilattice of L(A) with bottom 0 and top R^d;
- g acts by lattice automorphisms, so Λ(V)^g is join-closed with 0, hence
  a lattice.

The meet of X and a in M = Λ(V)^g is X ∩ a, by fixed Lemma B(a). The dual
Weisner identity in M with a ≠ 1̂ gives Σ_{X ∧ a = 0} μ_M(X, 1̂) = 0.
- X ∩ Fix(g) = 0 forces X ⊆ L by B(b), so the sum runs over 𝓛^g.
- The χ form uses det(g|_X) = 1 when X^g = 0, by §A.1(i).

### C.3 Is "Fix(g) is a flat" needed? No: Proposition W′

**Proposition W′ (PROVEN here).** Let g ≠ 1, and suppose Fix(g) lies in
some hyperplane of A, that is, a := cl(Fix g) ≠ R^d. Then

  Σ_{X ∈ 𝓛^g, X ∩ Fix(g) = 0} μ_{Λ(V)^g}(X, R^d) = 0,

and so, as in [FP], Σ_{X ∈ 𝓛^g, X ∩ Fix(g) = 0} χ_{V_X}(ḡ) = 0. When
Fix(g) is a flat, a = Fix(g) and this is Prop. W.

*Proof.* Write U = Fix(g) and M = Λ(V)^g.
- a is a g-stable flat containing U. By Lemma B(a), as fixed in §C.1,
  X ∩ a ∈ M for every X ∈ M, and X ∩ a is the meet X ∧ a in M.
- Since U ⊆ a, we have X ∩ U = (X ∩ a) ∩ U. So the condition X ∩ U = 0
  depends only on b = X ∧ a.
- Group the sum by b:
  Σ_{X ∩ U = 0} μ_M(X, 1̂) = Σ_{b ∈ M, b ≤ a, b ∩ U = 0} Σ_{X ∈ M, X ∧ a = b} μ_M(X, 1̂).
- Fix such a b. Every X with X ∧ a = b lies in the interval [b, 1̂] of M,
  which is a finite lattice with bottom b. It contains a, and a ≠ 1̂. The
  dual Weisner theorem in [b, 1̂] ([FP] §4, from [Thm, Lemma weisner]) gives
  Σ_{X ∈ [b, 1̂], X ∧ a = b} μ(X, 1̂) = 0.
- So every inner sum vanishes.
- The terms are in 𝓛^g by Lemma B(b), and the χ form follows from
  §A.1(i), as in [FP]. ∎

[FP]'s proof is the single term b = 0 of this argument, which is
available only when a = U. [FP]'s cl(Fix g) variant, the sum over
X ∩ a = 0, is also the single term b = 0, now with a = cl(U). It is
PROVEN by [FP]'s remark. W′ is a different identity: the two index sets
differ on 235 of the 372 non-flat pairs where both apply (A_3: 7 of 9;
A_4: 65 of 72; D_5: 163 of 291).

**COMPUTED.**
- Prop. W itself, with Fix(g) a flat: holds on every pair (`[W]`).
- W′ (`[Wweak]`) and the cl-variant (`[Wcl]`): each holds on all 6,125
  pairs with g ≠ 1 and cl(Fix g) ≠ R^d.

The pairs with Fix(g) not a flat, cross-tabulated:

| arrangement | Fix(g) not a flat | Fix(g) in a hyperplane: identity holds | Fix(g) in no hyperplane: identity fails |
|---|---|---|---|
| A_3, G = ±W | 20 | 9 of 9 | 11 of 11 |
| A_4, G = ±W | 108 | 72 of 72 | 36 of 36 |
| D_5, G = W(B_5) (sampled) | 356 | 291 of 291 | 65 of 65 |
| tetra7 | 386 | — | 386 of 386 |
| hex6 | 93 | — | 93 of 93 |

The A_3 and A_4 counts reproduce [FP]'s "11 of 20" and "36 of 108". This
explains them: [FP]'s failures are the pairs where Fix(g) lies in no
hyperplane. [FP]'s A_5 and D_4 figures (80 of 561, 250 of 642) were not
re-run here.

**Is the weak hypothesis necessary? (OPEN.)** On every tested pair with
g ≠ 1 and Fix(g) in no hyperplane, the sum is nonzero. In a side
experiment on tetra7, hex6 and A_3 (not part of the archived run),
(−1)^d det(g) times the sum was always a positive integer, between 1 and 3.

A route to a proof:
- Let Q = {X ∈ M : X ∩ Fix(g) ≠ 0}. It is an up-set of M.
- Hall's theorem gives Σ_{X ∩ U = 0} μ_M(X, 1̂) = χ̃(Δ(Q ∖ {1̂})).
- When a ≠ R^d, X ↦ X ∧ a ≤ a is a conical contraction of Q ∖ {1̂}, which
  recovers W′.
- When Fix(g) lies in no hyperplane, Q ∖ {1̂} should be a sphere-like poset.

Not pursued.

## D. Hypotheses: what is and is not needed

| Hypothesis | Where needed | Stated in [FP]? |
|---|---|---|
| A finite, central, real | throughout | yes |
| A essential | F̄ pointed (A step 1); [GT] Lemma 0.1(c) | yes (§1) |
| g of finite order | invariant inner product; det = ±1; averaging (Lemmas F, B) | yes |
| gA = A, gV = V | g acts on Λ(V), on chambers of V | yes |
| g orthogonal | **not needed** (invariant inner product) | correctly not assumed |
| g ∈ W | **not needed** for EZ, CF, F, V, W | correctly not assumed |
| A is the reflection arrangement of W | "W acts freely" (Cor. P second half; EZ remark "for g ∈ W ∖ 1 the left side is 0"); Steinberg (Cor. V remark, Prop. W preamble) | **implicit only**: [FP] §1 says "the reflection group W of A". Should say: when A is the reflection arrangement of a finite reflection group W |
| Fix(g) a flat, g ≠ 1 | Prop. W | yes. g ≠ 1 is needed: at g = 1 the sum is χ_V(1) = m(V) ≥ 1. The flat condition can be weakened to "Fix(g) lies in a hyperplane of A" (Prop. W′, §C.3) |
| a ∈ Λ(V)^g in Lemma B(a) | **not needed**, and circular in use | fix (§C.1) |
| Theorem G\* for g ∉ Stab_W(V) | only the remark after the Definition | [FP] flags it as not re-audited; this audit does not audit it either |

## E. Braid case

CF-braid HOLDS (§B). [FP] claims that it "agrees with [Thm, eq. closed]",
and that claim is correct as stated: both are proven expressions for
sgn(g)(−1)^{n−3} μ(OP(P)^g). [FP] does not claim that CF-braid reduces
algebraically to eq. closed. It says it has "no direct combinatorial
derivation", and this audit does not supply one.

The structural difference:
- eq. closed has a single Möbius value μ(o) and sums over F(P, g);
- CF-braid sums over all of Π(K)^g with products of |Lin(P|_B)|.

Matching them needs the Π(K)^g Möbius function plus the e_C/linear-extension
relation of [GT] Cor. 1.4 (Thm 2 in the braid case).

COMPUTED independently (§G), for every poset on n = 3, 4, 5 points up to
relabelling and every g ∈ Aut(P). Four numbers agree:
- μ(OP(P)^g) from order-preserving partitions;
- μ(Λ(C_P)^g) from the braid arrangement;
- the right side of CF-braid;
- the right side of eq. closed, with e_C from rotation classes of words.

That is 396 pairs (12, 59 and 325 for n = 3, 4, 5). These counts match [FP]'s counts for n ≤ 5.

## F. Minor points (not errors)

- [FP] §1, "Why χ_V is the character we want": for g ∉ W this needs only
  [GT] Thm 1 (concentration in degree d − 2, no group involved), Hall and
  Hopf. So χ_V is a character of ⟨g⟩ for every finite-order symmetry.
  Only the identification with (Γ_V + Lune)/Lune for g ∉ Stab_W(V) rests
  on the unaudited reading of G\*.
- The verdict-table line for Full omits the zero convention that §3.1
  states.
- §5's table of classes on which χ_V ≡ 0 is COMPUTED by [FP]. This audit
  did not re-check it.

## G. Computations (COMPUTED)

`compute/audit_fixed_point_formula.py`. It uses exact rational arithmetic
and imports nothing from the repository.

**Face enumeration.** Faces are built by a method no earlier script uses:
- the cocircuits are the sign vectors of the rays, found as kernels of
  rank-(d − 1) sets of forms;
- the covectors are the closure of {0} ∪ cocircuits under oriented-matroid
  composition X ∘ Y.

By contrast, [FP]'s script takes the W-orbit of the faces of the
fundamental chamber, which needs a reflection group. The audit of Theorem C
used wall-crossing and ray subsets. The same covector closure, run in
coordinates on Fix(g), gives the restricted arrangements of Lemma F.

**What is computed directly rather than through a lemma:**
- det(g|_X), by expressing g on a basis of X;
- det(ḡ) = det(g)/det(g|_X);
- c(Y, g), as the distinct g-fixed restrictions to A_Y of the chambers of V;
- the restricted counts of Lemma F, in coordinates on Fix(g).

[FP]'s script obtains det(g|_X) from the parity formula §A.1(i). This
script checks that formula separately.

**Arrangements.**

| arrangement | symmetry group G | cones | new? |
|---|---|---|---|
| A_3 | ±W(A_3) | all 219, up to W | no; control against [FP]'s table |
| B_3 | W(B_3) | all 941, up to W | no; control |
| A_4 | ±W(A_4) | all 4,231, up to W | no; control |
| tetra7: x_i = 0 and the 4 planes ⊥ (1, ±1, ±1) in R^3 | signed permutations (48); contains reflections in x_i = ±x_j, which are not in A | all | **yes**, non-reflection arrangement |
| hex6: ⟨h⟩-orbits of x + z and y + 2z, plus z = 0, in R^3 | ⟨h, −1⟩ (12), h = [[0,−1,0],[1,1,0],[0,0,1]] of order 6, **not orthogonal** | all | **yes**: non-reflection; non-orthogonal g; Fix(h) in no hyperplane |
| F_4 | W(F_4) | 60 sampled with nontrivial stabilizer, plus all chambers | **yes** |
| D_5 | W(B_5) ⊋ W(D_5), including odd sign changes | 40 sampled | **yes** |
| B_5 | W(B_5) | 25 sampled | **yes** |

The cones of F_4, D_5 and B_5 are sampled so that the stabilizer is
nontrivial. Take g ≠ 1 and a chamber T. Impose T's signs on the ⟨g⟩-orbit
of one to three random hyperplanes, and keep the cone if it is nonempty.
Every element of the full stabilizer in G is then tested.

**Results** (`compute/output/audit_fixed_point_formula.txt`). Every
asserted check holds on every instance:

| arrangement | pairs (V, g) | [EZ], [CF] | [2.1] (Y ∈ Λ(V)^g) | [F] (Y ∈ 𝓛^g, g ≠ 1) | [W] (Fix(g) flat) | [Wweak], [Wcl] |
|---|---|---|---|---|---|---|
| A_3 | 96 | 96 | 612 | 272 | 60 | 69 |
| B_3 | 134 | 134 | 1,314 | 405 | 99 | 99 |
| A_4 | 478 | 478 | 5,992 | 1,921 | 307 | 379 |
| tetra7 | 1,008 | 1,008 | 9,168 | 1,168 | 225 | 225 |
| hex6 | 5,520 | 5,520 | 143,892 | 278 | 66 | 66 |
| F_4 | 2,022 | 2,022 | 39,274 | 16,084 | 1,961 | 1,961 |
| D_5 | 1,490 | 1,490 | 58,900 | 6,036 | 1,094 | 1,385 |
| B_5 | 1,966 | 1,966 | 77,838 | not run | 1,941 | 1,941 |
| total | 12,714 | 12,714 | 336,990 | 26,164 | 5,753 | 6,125 |

Notes on the table:
- [par], [B], [P] and [V] also hold on every instance; the counts are in
  the log.
- 1,586 of the 12,714 pairs have g outside W:
  - every non-identity pair of tetra7 (611) and hex6 (159);
  - 37 pairs of A_3, 153 of A_4 and 626 of D_5.
- In the log, the "W" count for tetra7 and hex6 counts only the identity.
  These arrangements are not the reflection arrangement of any group W.
- In D_5 the 356 pairs with Fix(g) not a flat all come from the odd sign
  changes. This symmetry class is new; [FP] used W(F_4) on D_4.
- [braid]: 396 of 396 pairs (§E).


**Positive controls** (all fire):
- chamber counts 24, 48, 1152, 1920 and 3840 (A_3, B_3, F_4, D_5, B_5);
- top-cone counts 219 and 941;
- face counts 75 and 147 for A_3 and B_3;
- μ(L(F_4)) = 1·5·7·11 = 385;
- poset counts 5, 16 and 63;
- [FP]'s table rows for A_3, B_3 and A_4, reproduced exactly: χ ≠ 0, zero
  by Cor. V, zero otherwise, and the 11 of 20 Prop. W failures in A_3.

**Negative controls** (each must fail somewhere, and each does):
- [2.1] with det(g|_{span F}) replaced by 1: fails on 3,935 of 336,990;
- [EZ] without det(ḡ): fails on 1,030 of 12,714;
- [CF] counting all chambers of A_Y in |V| instead of the g-fixed ones:
  fails on 6,612 of 12,714;
- [W] on pairs where Fix(g) is not a flat: fails on 591 of 963.

## Reproduce

```
cd compute
python3 audit_fixed_point_formula.py            # full run, about 3 min; exit 0
python3 audit_fixed_point_formula.py --quick    # A3, B3, tetra7, hex6, braid n <= 4; a few seconds
python3 -m unittest test_audit_fixed_point_formula
```

Log of the full run: `compute/output/audit_fixed_point_formula.txt` (ends
"ALL CHECKS PASSED").
