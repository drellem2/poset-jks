# Audit: Formula Z, Theorem S and Theorem A (the vanishing criterion for the cone Lie character)

This is an independent adversarial audit of the PROVEN claims of
`notes/vanishing_criterion.md` ("[VC]"). The aim was to find errors, not to
confirm the claims. Every step was re-derived by hand, every cited input was
re-read at its source, and the claims were tested by a new script,
`compute/audit_vanishing_criterion.py`. That script imports nothing from
the repository.

Sources:
- [AudW] = `notes/audit_prop_w_prime.md`, Theorem W″ (§2);
- [AudW2] = `notes/audit_theorem_w2.md`, its independent audit;
- [FP] = `notes/fixed_point_formula.md`: Lemma A, Lemma F, Theorem CF, Cor. P;
- [GT] = `notes/general_theory.md` §0: Lemma 0.1, m(V);
- [FPM] = `notes/fixed_point_mobius_identity.md`, consequence (ii);
- [AudFP] = `notes/audit_fixed_point_formula.md` §A.1(i) (the sign rule).

Notation is that of [VC]: A is a finite central essential arrangement in
R^d, V is a top-cone with L = lin V, g is a finite-order linear map with
gA = A and gV = V, and U = Fix(g). Z(V,g), Z\*(V,g), Z\*(g) and m_X(V) are as
in [VC] §2.

## Verdict

| # | Claim ([VC]) | Verdict |
|---|---|---|
| Z | Formula Z (§2), and μ_{L(A)^g}(0, X) = χ^{full}_{A^X}(g\|_X) | **HOLDS.** Every step re-derives. One degenerate case falls outside the stated range of (W″c). This is X = R^d, which is in Z(V,g) iff U = 0 and V is all chambers. The localization there has rank 0, while W″ is stated for d ≥ 1. The needed identity is 1 = 1 under the rank-0 conventions of [FP] §1 and [GT] §0 (§1.1, step 1). This is a one-line gap, not an error. |
| S | Theorem S (§3), including the witness top-lune | **HOLDS.** (i) ⇒ (ii) and (ii) ⇒ (i) re-derive. The witness V♯ is a g-stable top-cone with S_max(V♯) = A_X and lin V♯ = X, and χ_{V♯}(g) = μ(0, X) when X is minimal (§2). |
| S1 | Pointed cones | **HOLDS.** The Steinberg sentence needs A to be the reflection arrangement of a group W ∋ g. That is implicit in the wording "g in a reflection group W". |
| S2 | Fix g = 0 | **HOLDS.** |
| S3 | Involutions; reflections: "s_α is nonzero on some cone iff Rα is a flat" | **The involution part HOLDS. The reflection bullet HOLDS WITH FIX.** It needs the hypothesis that the mirror Fix(s_α) = α^⊥ is a hyperplane of A, for example s_α ∈ W with A the reflection arrangement of W. Without this hypothesis it FAILS. Counterexample: A = {x = 0, y = 0} in R^2 and s(x, y) = (y, x). Here Rα = R(1, −1) is not a flat, but s fixes the chamber x, y > 0, so χ = 1 on that pointed cone. The B_n sentence argues only the short-root reflection. The long-root case holds too (§3.3). |
| V | Cor. V of [FP] as the case "a hyperplane contains L + U" | **HOLDS.** "On pointed cones every zero is of this kind" is PROVEN by S1, since m(V^U) ≥ 1. It is not only a computed fact. |
| A | Theorem A (A+ and A−), and ord(−w) = lcm(2, ord w) for n ≥ 3 | **HOLDS.** The tight-pair description, the orbit-parity criterion for X_π ∩ U = 0, the necessity and sufficiency arguments, and the equivalence of the "acts freely + μ(ord g)" form with the explicit forms all re-derive. The input (H) states what is used. The order claim fails at n = 2, which is excluded (§4). |
| PC | Corollary PC (§5) | **(a) and (b) HOLD. (c) HOLDS WITH FIX.** The item "every reflection (Z\*(g) ⊆ {Rα})" needs the same mirror hypothesis as S3. Without it, it FAILS inside [VC]'s own data. The cancelling A_2 example of [VC] §5, g = −s_12, is a reflection of R^3_0, which [VC] itself calls "the reflection in the line orthogonal to H_12". Its Z\*(g) = {0, H_12} has μ = +1 and −1, so it is not sign-coherent, and it cancels on the full cone. The same holds for −(2,2) on A_3, and for s(x, y) = (−x, y) on {y = 0, y = ±x} in R^2 (§5). |
| §6 | B_3 Coxeter element; B_2 reflection | **HOLDS.** One step is implicit: P = (1, −1, 1)^⊥ is the only c-stable plane. That holds because c acts on P by a rotation of order 6 with no real eigenvector (§6). |

No proven formula is wrong. The two corrections are hypotheses missing from
the statements about reflections (S3, PC(c)). In both, "reflection" must mean
a reflection whose mirror lies in A. The note's tables use reflections in W,
which satisfy this. But [VC] works throughout with a general finite-order
symmetry, and its own groups ±S_n contain reflections that do not.

---

## 1. Inputs: do they say what [VC] uses?

**(W″c), [AudW] §2.** It is stated for "(A, V, g) as above, with any g,
including g = 1". "As above" means: A is finite, central and essential in
R^d with **d ≥ 1**, V is a top-cone, and g is a finite-order linear map with
gA = A and gV = V. The statement is:

  Σ_{X ∈ 𝓛^g, X ∩ U = 0} χ_{V_X}(ḡ) = m(V^U) if U lies in no hyperplane of A, and 0 otherwise.

This is the formula [VC] §1 quotes. m(V^U) ≥ 1 is part of (b). [AudW2]
audits it and finds that it holds, including for non-pointed V^U and for
k = dim U = 1.

**[FP] Lemma A, and the localization step of the proof of CF.**
- For a g-stable flat X ⊆ L, ḡ preserves A_X/X and V_X.
- lin V_X = L/X.
- The flats of A_X/X inside L/X are the Z/X with Z a flat of A and
  X ⊆ Z ⊆ L. The ḡ-stable ones correspond to the g-stable ones.
- (V_X)_{Z/X} = V_Z, compatibly with the induced maps.

All four are stated in the CF proof, and [VC] §1 uses exactly these.
A_X/X is essential and V_X is a top-cone by [GT] Lemma 0.1(c).

**[FP] Lemma F.** B is any central arrangement in a real space, essential or
not, and h has finite order with hB = B. If no H ∈ B contains Fix h, then
K ↦ K ∩ Fix h is a bijection from the h-fixed chambers onto the chambers of
B|_{Fix h}. [VC] applies it to B = A_X, which is g-stable and in general not
essential. That is allowed.

**[GT] Lemma 0.1.** Part (a) says Y ∈ Λ(V) iff dim(Y ∩ |V|) = dim Y. Part (b)
says flats inside L lie in Λ(V). Part (c) is the localization. As stated.

**[FPM] (ii).** For σ ∈ S_b of type ℓ^r,
μ(Π_b^σ) = (−1)^{r−1} μ(ℓ) ℓ^{r−1}(r−1)!, and μ(Π_b^σ) = 0 for every other σ.
The identity, of type 1^b, is covered by the formula, which gives
(−1)^{b−1}(b−1)!. [VC] (H) is this statement for w̄ acting on the blocks.
COMPUTED `[A-H]`: (H) agrees with a direct Möbius recursion on every fixed
interval, for all ±w with n ≤ 8 and four classes with n = 9.

**Sign rule ([AudFP] §A.1(i)).** For real h of finite order,
det h = (−1)^{dim − dim Fix h}. Proof: the eigenvalues are 1, −1, and pairs
of conjugates. COMPUTED `[sgn]`.

### 1.1 Theorem Z, step by step

1. *Localize.* Let X ∈ Z(V,g), and put (A′, V′, g′) = (A_X/X, V_X, ḡ). By
   Lemma A and [GT] 0.1(c), A′ is essential, V′ is a top-cone of it, and
   g′ is a finite-order symmetry with g′V′ = V′. So (W″c) applies whenever
   codim X ≥ 1. This includes ḡ = 1, which happens when U + X = R^d, and
   g = 1. **Gap:** codim X = 0 means X = R^d. That is possible in Z(V,g)
   only when U = 0 (from X ∩ U = 0) and L = R^d, that is, V = all chambers.
   Then the left side of the localized identity is χ_{V_{R^d}} = 1, by the
   rank-0 convention of [FP] §1. Also R^d ∈ Z\*(V,g), and m_{R^d}(V) is m
   of the empty arrangement in U = 0, which is 1. So step 5 below holds at
   X = R^d, but by the conventions and not by (W″c). One line in [VC] would
   close this. COMPUTED: `[loc]` includes these cases.
2. *Fix(ḡ) = (U + X)/X.* "⊇" is clear. For "⊆": if gx − x ∈ X, then
   g^k x − x = Σ_{j<k} g^j(gx − x) ∈ X. So the average p satisfies
   p − x ∈ X, and p ∈ U. ✓
3. *The index set.* For a g-stable flat Z with X ⊆ Z ⊆ L,
   (Z/X) ∩ Fix ḡ = (Z ∩ (U + X))/X = ((Z ∩ U) + X)/X. This uses the modular
   law with X ⊆ Z. It is 0 iff Z ∩ U ⊆ X, and since Z ∩ U ⊆ U, iff
   Z ∩ U ⊆ X ∩ U = 0. ✓
4. *The right side.* The hyperplanes of A′ are the H/X with H ⊇ X, and
   Fix ḡ ⊆ H/X iff U + X ⊆ H. Any H ⊇ U + X contains X. So "Fix ḡ lies in no
   hyperplane of A′" is exactly "no hyperplane of A contains X + U". **This
   is the right condition.** COMPUTED: dropping it fails 527 of 6,266 pairs
   (`no_transverse`).
   - When X ∩ U = 0, u ↦ u + X maps U isomorphically onto (U + X)/X.
   - For H ⊇ X, it carries H ∩ U onto (H/X) ∩ Fix ḡ, since
     (H ∩ (U + X))/X = ((H ∩ U) + X)/X by the modular law.
   - It carries |V| ∩ U onto |V_X| ∩ Fix ḡ. For "⊇": if u + x ∈ |V| with
     x ∈ X, then u ∈ |V| + X = |V|, because X ⊆ L.
   - m is invariant under linear isomorphisms. So the right side is
     m_X(V) ≥ 1. ✓
   - That V_X^U is a top-cone with support |V| ∩ U, and that its sign
     constraints are consistent, comes from (W″) applied to (A′, V′, g′)
     ([AudW2] §2 step 3). [VC] §2 checks only that the constraints are
     hyperplanes of A_X\|_U, which on its own would not be enough. Since the
     identification of step 4 transports the whole of (W″b), this is
     covered.
5. *The localized identity.* For X ∈ Z(V,g),
   Σ_{Z ∈ Z(V,g), Z ⊇ X} χ_{V_Z}(ḡ) = [X ∈ Z\*(V,g)] m_X(V). ✓
   COMPUTED `[loc]`: 6,708 instances, all equal. Here χ_{V_Z}(ḡ) is
   computed as (−1)^{codim Z} det(ḡ) μ_{Λ(V)^g}(Z, R^d), with det ḡ =
   det g / det(g|_Z) taken from the matrices.
6. *Möbius inversion.* Z(V,g) is a finite poset containing 0. Step 5 holds
   for every element of it. Upper Möbius inversion at 0 gives
   χ_V(g) = Σ_X μ_{Z(V,g)}(0, X) ψ(X). ✓
7. *The down-set claim.* Let Y ⊆ X ∈ Z(V,g) be a g-stable flat. Then
   Y ⊆ X ⊆ L and Y ∩ U ⊆ X ∩ U = 0, so Y ∈ Z(V,g). So [0, X] is the same
   interval in Z(V,g) and in L(A)^g, and the Möbius functions agree. ✓
   COMPUTED `[down]`.
8. *The full character.* The flats of A inside X correspond to the flats of
   A^X = {H ∩ X : H ⊉ X}. A flat Y ⊆ X equals X ∩ ⋂_{H ⊇ Y, H ⊉ X} H. A^X
   is essential in X: the intersection of all its hyperplanes is contained
   in every H ∈ A, hence is 0. The correspondence preserves g-stability.
   Fix(g|_X) = X ∩ U = 0, so det(g|_X) = (−1)^{dim X}, and
   χ^{full}_{A^X}(g|_X) = (−1)^{dim X} det(g|_X) μ = μ. ✓ COMPUTED `[Zfull]`.

Edge cases:
- g = 1 gives Z\* = {0} and χ_V(1) = m(V).
- dim U = 0 is S2.
- The X = 0 term is the right side of (W″c) for V itself.
- In rank 1 (A = {0} ⊂ R, g = −1), Z\*(g) = {R} with μ = −1. Then
  χ_{all}(−1) = −1 and the half-lines give 0. COMPUTED (`rank1`).

## 2. Theorem S (PROVEN; re-derived)

- (i) ⇒ (ii). Z\*(V,g) ⊆ Z\*(g), and every term of (Z) carries a factor
  μ(0, X). ✓
- (ii) ⇒ (i). Take X minimal among the X ∈ Z\*(g) with μ(0, X) ≠ 0.
  - *K exists.* No H ∈ A_X contains U, since H ⊇ U would give H ⊇ X + U.
    A_X is g-stable. Lemma F gives a bijection between the g-fixed chambers
    of A_X and the chambers of A_X|_U, and the latter set is nonempty
    (U ≠ 0 unless A_X = ∅). If X = R^d, then A_X = ∅ and K = R^d, which
    is allowed. ✓
  - *V♯.* V♯ = {C : C_H = K_H for H ⊇ X} is nonempty, because the open
    cone K contains chambers. It is of top-cone form, and g-stable since
    gK = K. ✓
  - *S_max(V♯) = A_X and lin V♯ = X.* Every H ⊇ X is constant on V♯. Since
    K + X = K, X lies in the closure of K, which is |V♯|. A hyperplane
    H ⊉ X takes both signs on X, so it takes both signs on |V♯|. Then
    chambers of V♯ lie on both sides of H, so H ∉ S_max. Hence
    lin V♯ = ⋂_{H ⊇ X} H = X. ✓ COMPUTED: `[Switness]` re-checks
    S_max = A_X and lin = X.
  - *(Z) for V♯.* Z\*(V♯, g) = {X′ ∈ Z\*(g) : X′ ⊆ X}. Every X′ ⊊ X there
    has μ = 0, by minimality. The X-term has m_X(V♯) = m of the cone
    cl(K) ∩ U. That cone is {u ∈ U : K_H α_H(u) ≥ 0, H ⊇ X}, the closure of
    the single chamber K ∩ U of A_X|_U. A single chamber of an essential
    arrangement has m = 1, by [FP] Cor. P at g = 1. So
    χ_{V♯}(g) = μ(0, X). ✓

COMPUTED:
- `[S]`: on all 62 classes of the 9 test arrangements, "some g-stable cone
  has χ ≠ 0" (full enumeration, χ from the definition) agrees with (ii).
- `[Switness]`: 49 minimal witnesses, each with χ_{V♯}(g) = μ(0, X).
- Negative control `nonminimal_witness`: for non-minimal X, χ_{V♯}(g) ≠ μ(0, X)
  in 12 of 12 cases. So minimality is needed.

## 3. Corollaries S1–S3, V

### 3.1 S1, S2, Cor. V

- **S1.** L = 0 forces X = 0, so χ_V(g) = [U in no hyperplane] m(V^U). V^U
  is pointed and m = #chambers = #V^g, by Lemma F. ✓ COMPUTED `[S1]`
  (4,472 pointed pairs).
- **S2.** If U = 0, then X + U = X, and only X = R^d lies in no hyperplane.
  So Z\*(g) = {R^d}, and R^d ⊆ L iff V is all chambers. ✓ COMPUTED `[S2]`.
  Examples: COMPUTED. The Coxeter elements of A_3, B_3 and D_4 have
  μ(L(A)^c) = 0. Those of A_2, A_4, A_5, B_2, B_4 and F_4 have μ = −1, −1,
  1, −1, −1, −1. All have Fix = 0. H_3 was not recomputed here; that
  needs Q(√5).
- **Cor. V.** If H ⊇ L + U, then H ⊇ X + U for every X ⊆ L. ✓ COMPUTED
  `[corV]`. **Status note:** "on pointed cones every zero is of this kind"
  is a consequence of S1 together with m ≥ 1, so it is PROVEN.
  COMPUTED `[S1zero=corV]`.

### 3.2 S3, involutions

- With g² = 1, the projections (1 ± g)/2 preserve X. So
  X = (X ∩ U) ⊕ (X ∩ E), and X ∩ U = 0 gives X ⊆ E. ✓ COMPUTED `[S3inE]`.
- Conversely, every subspace of E is g-stable and meets U in 0.
- g = −1 on X, so every flat below X is g-stable. Hence
  [0, X]_{L(A)^g} = L(A^X), a geometric lattice of rank dim X, and
  μ(0, X) has sign (−1)^{dim X} (Rota). ✓ COMPUTED `[S3mu]`.

### 3.3 S3, reflections: needs a hypothesis

[VC] writes: "For a reflection s_α, E = Rα. So s_α is nonzero on some cone
iff Rα is a flat." Z\*(g) ⊆ {0, Rα}. The term X = 0 is excluded exactly
when U = Fix(s_α) lies in a hyperplane of A. Since U is itself a
hyperplane, that means U ∈ A. [VC] assumes this silently.

- **With U ∈ A** (true for every reflection in W, when A is the reflection
  arrangement of W): Z\*(g) ⊆ {Rα}. The claim holds. COMPUTED `[S3refl]`,
  `[PCc-refl]`.
- **Without it, the claim FAILS.** Take A = {x = 0, y = 0} in R^2 and the
  swap s(x, y) = (y, x).
  - Rα = R(1, −1) is not a flat.
  - U = R(1, 1) lies in no hyperplane, so Z\*(s) = {0}.
  - s fixes the chamber {x, y > 0}, so χ = 1 there.
  COMPUTED (`coord2`; negative control `S3_without_mirror_hyp`).

**Fix:** "For a reflection s_α whose mirror α^⊥ is a hyperplane of A (for
example s_α ∈ W, A the reflection arrangement of W) …". The type-A sentence
is then about the reflections of W = S_n. It would be false for −s_12 ∈ ±S_3
on A_2, whose Rα = R(1, 1, −2) is a flat. That is harmless once the
hypothesis is stated.

**B_n, all n.** [VC] argues only the short root e_1. For the long root
e_1 − e_2, the roots orthogonal to it are ±(e_1 + e_2), ±e_j (j ≥ 3) and
±e_j ± e_k (j, k ≥ 3). They span ⟨e_1 + e_2, e_3, …, e_n⟩ = (e_1 − e_2)^⊥.
So "holds for every reflection of B_n" is PROVEN for all n ≥ 2. ✓

## 4. Theorem A

**Setting.**
- g = εw acts by g e_i = ε e_{w(i)}, so g H_ij = H_{w(i)w(j)}.
- −w ∉ W for n ≥ 3. A permutation acting as −1 on R^n_0 would have to swap
  1 ↔ 2 and also 1 ↔ 3.
- X_π is g-stable iff w(π) = π. ✓
- [0, X_π] in L(A)^g is anti-isomorphic to [π, 1̂]^w in Π_n, which is
  Π_b^{w̄}. Möbius numbers from bottom to top are invariant under order
  reversal. ✓

**ord(−w) = lcm(2, ord w), n ≥ 3.**
- (−w)^j = (−1)^j w^j.
- For odd j this would need w^j = −1 on R^n_0, which is impossible.
- For even j it is w^j, and S_n acts faithfully on R^n_0. ✓
- At n = 2 it fails: −(12) is the identity of R^2_0. This is a negative
  control (`ord_n2`). COMPUTED `[ord]` for n ≤ 7.

**Freeness.** g^j e_i = ε^j e_{w^j(i)}. So the stabilizer of e_i is
generated by g^{k_i} for ε = +1, and by g^{lcm(2, k_i)} for ε = −1, where
k_i is the length of the cycle of i.
- The action is free iff every k_i (ε = +1), or every lcm(2, k_i)
  (ε = −1), equals ord g. ✓
- For ε = −1 with N := ord g: lcm(2, k) = N means k = N, or k = N/2 with
  N/2 odd. μ(N) ≠ 0 with N even forces N = 2m, m odd and squarefree.
- So the explicit form is "cycle lengths in {m, 2m}, m odd squarefree". The
  converse is direct. ✓
- COMPUTED: the two forms agree on every class tested (an assertion inside
  `stated_rule`). The variant with m not required to be odd is wrong: it
  differs on 4 classes (`A-_m_not_odd`).

**(A+).**
- U consists of the sum-zero vectors constant on the cycles. H_ij ⊇ U iff i
  and j lie in one cycle. For two different cycles C, C′, use the vector
  |C′|·1_C − |C|·1_{C′}. ✓
- X_π ∩ U = X_{π ∨ cyc}, which is 0 iff π ∨ cyc = 1̂.
- X_π + U ⊆ H_ij iff i, j share a block and a cycle. ✓
- Let π ∈ Z\*(g).
  - A w̄-orbit of blocks is a union of blocks and of cycles. So it is a
    common coarsening of π and cyc, hence all of [n]. ✓
  - w̄^b = 1, and w^b(i) lies in B and in the cycle of i. π ∧ cyc = 0̂ gives
    w^b(i) = i. ✓
  - b | ord w as an orbit length. Every cycle has length b, since
    w^j(i) = i with 0 < j < b would make w̄^j fix B. ✓
  - The proof shows more: **Z\*(g) = ∅ unless all cycles have one length**,
    and then every coefficient is μ(o). This is the PC(c) claim for S_n.
    COMPUTED `[A+coef]`.
- The converse transversal construction is direct. ✓

**(A−).**
- *Tight pairs.* U is spanned by the alternating vectors of the even
  cycles. Hence H_ij ⊇ U iff i, j ∈ O, or i, j lie in one even cycle at
  even distance. ✓
- *X_π ∩ U.* f(w̄B) = −f(B), and the sum-zero condition is automatic. An
  orbit of odd length forces f = 0 there. An orbit of even length carries
  an alternating f. ✓
- *Necessity.*
  - (H) gives one orbit length ℓ with μ(ℓ) ≠ 0, and ℓ is odd. ℓ | k because
    w^k B = B.
  - For odd k, the k/ℓ points w^{jℓ}(i) are points of O in one block, so
    k = ℓ.
  - For even k, the points w^{jℓ}(i) lie in one block at distances jℓ along
    the cycle. Distance parity is well defined because k is even, and jℓ
    has the parity of j. If k/ℓ ≥ 3, then j = 0 and j = 2 give a tight
    pair. k/ℓ = 1 is impossible because k is even and ℓ is odd. So
    k = 2ℓ. ✓
- *Sufficiency.* The singletons on O and the antipodal pairs on the 2m-cycles
  are w-stable. All block orbits have length m, which is odd. The antipodal
  pairs are at odd distance m, and no block holds two points of O. ✓

COMPUTED:
- `[A-Zchar]`: the combinatorial description of Z\*(g) in both proofs is
  compared with Z\*(g) computed by linear algebra in R^n. That brute force
  solves Fix(±w) in R^n_0 and tests X_π ∩ U = 0 and X_π + U ⊆ H_ij by rank
  and coordinates. It agrees on all 130 classes: every ±w for 3 ≤ n ≤ 8,
  plus −(6,3), −(9), −(3,3,3) and −(6,2,1) at n = 9. Dropping the parity
  condition from the tight pairs breaks it on 17 of 63 classes −w
  (`A-_drop_parity_condition`).
- `[A-part]`: Theorem A agrees with "some X ∈ Z\*(g) has μ(0, X) ≠ 0",
  where μ comes from recursion in the fixed partition lattice and not from
  (H). All 130 classes agree. Examples: −(6,3) is nonzero and −(9) is
  zero, as stated in [VC].
- `[A-root]`: on A_2, A_3 and A_4, Theorem A agrees with the full cone
  enumeration, with χ from the definition (30 classes of ±S_n).

**Verdict: HOLDS.** The edge case n = 3 is covered: −(2,1) is nonzero, and
−(3) is nonzero with m = 3. ord(−w) fails only at the excluded n = 2.

## 5. Corollary PC

- (a) and (b) follow from (Z) and m_X ≥ 1. ✓ COMPUTED `[PCa]` (5,760 pairs
  with χ ≠ 0), `[PCb]` (5,629 sign-coherent pairs with a nonzero term, all
  with χ ≠ 0).
- (c), S_n: Z\*(g) is empty or all of its coefficients are μ(o) (§4). ✓
- (c), Fix g = 0: Z\*(g) ⊆ {R^d}. ✓
- (c), a single flat: trivial. ✓
- **(c), "every reflection (Z\*(g) ⊆ {Rα})": FAILS as stated. It HOLDS for
  reflections whose mirror lies in A** (§3.3). Counterexamples:
  - **[VC]'s own example.** g = −s_12 on A_2 is a reflection of R^3_0, with
    eigenvalue +1 on R(e_1 − e_2) and −1 on R(1, 1, −2). Its mirror
    R(e_1 − e_2) is not a hyperplane of A_2. So Z\*(g) = {0, H_12}, where
    H_12 = R(1, 1, −2) is a line in R^3_0 and a flat. The two μ are +1 and
    −1, and the full cone cancels: [VC] §5 table, row A_2, and the paragraph
    after it. So [VC] §5 contradicts [VC] §5(c) unless "reflection" is
    read as "reflection in W".
  - g = −(12)(34) on A_3 is a reflection of R^4_0 (eigenvalues −1, 1, 1).
    Here Z\*(g) = {0, X_{12|34}}, with μ = +1 and −1. COMPUTED.
  - The non-reflection arrangement {y = 0, y = x, y = −x} with
    s(x, y) = (−x, y) (`tri2`):
    - Fix(s) = the y-axis, not in A;
    - Z\*(s) = {0, x-axis}, with μ = +1 and −1;
    - on V = {y ≥ 0} the terms are (dim X, μ, m_X) = (0, 1, 1) and
      (1, −1, 1), so χ_V(s) = 0;
    - checked from the definition: Λ(V)^s = {0, x-axis, R^2}, a chain, so
      μ = 0.

  Negative control `PCc_without_mirror_hyp`: 4 of the 15 reflections in the
  test arrangements are not sign-coherent. Every one of them has a mirror
  outside A.

**Fix:** in PC(c) and in the Verdict row PC, read "every reflection whose
mirror is a hyperplane of A (e.g. every reflection of W)". The [VC] §5
sentence "In type A every cancelling g is −w with w an involution with a
fixed point" is then consistent with PC(c).

## 6. The hand computations of §6

**B_3, c: e_1 → e_2 → e_3 → −e_1**, so c(x) = (−x_3, x_1, x_2).
- c³ = −1, so the eigenvalues are −1 and e^{±iπ/3}. Fix c = 0, and c has
  order 6.
- c v = −v gives v = (1, −1, 1). R v = {x_1 + x_2 = 0} ∩ {x_2 + x_3 = 0} is
  a flat. ✓
- The c-stable subspaces are the sums of isotypic pieces: 0, ℓ, P = v^⊥ and
  R^3. P carries the rotation part, which has no real eigenvector, so P is
  the only c-stable plane. **This step is implicit in [VC].**
- P has normal (1, −1, 1), which is not a root, so P is not a flat.
- L(A)^c = {0, ℓ, R^3} is a chain, so μ = 0. By S2, c vanishes on every
  cone. ✓
- COMPUTED `[B3c-*]`, also for the product of simple reflections.
- c is Springer-regular (a Coxeter element).

**B_2, s(x, y) = (−x, y).**
- The mirror {x = 0} is in A, and Rα = {y = 0} is a flat, so S3 applies.
- On all chambers: L^s = {0, two axes, R^2}, so μ = 1, and
  χ = (−1)² det(s) μ = −1. ✓
- Through (Z): Z\*(s) = {x-axis}, with μ = −1 and m = 1. ✓
- Not regular: both eigenlines are mirrors.
- COMPUTED `[B2s-*]`.

## 7. Computations (COMPUTED)

`compute/audit_vanishing_criterion.py` uses plain Python 3 and exact
`Fraction` arithmetic. It imports nothing from the repository. Its method
differs from `compute/vanishing_criterion.py`, which builds faces from
parabolic cosets of a Weyl group:
- **Arbitrary arrangements.** An arrangement is a list of integer normals,
  reflection arrangement or not.
- **Flats.** These are closed sets of hyperplanes, found from exact null
  spaces.
- **Faces.** These are sign vectors of explicit rational points. Starting
  from 0, a point p of a face is moved along each ray v of A to p + εv, with
  ε small enough to keep the nonzero signs of p. This is the geometric form
  of "every covector is a composition of cocircuits".
- **Symmetries.** These are rational matrices. Their actions on hyperplanes,
  chambers and flats are computed from the matrices.
- **χ_V(g).** Always from the definition (−1)^d det(g) μ(Λ(V)^g), with Λ(V)
  the spans of the faces lying in |V|.
- **The right side of (Z).**
  - Z\*(V,g) is found by rank computations against a basis of Fix g.
  - μ(0, X) is computed in L(A)^g.
  - m_X(V) is computed by building {H ∩ U : H ⊇ X} **in coordinates on U**
    and computing the support lattice of |V| ∩ U from that arrangement's
    own faces.
- **Pairs.** For every conjugacy class of G, the script takes a
  representative g and every g-stable top-cone. No orbit reduction is done
  on cones.
- **Type A.** It is tested a second time with no arrangement code. Flats are
  set partitions, Fix(±w) and transversality are solved in R^n, and μ comes
  from recursion in the fixed partition lattice.

**Arrangements**:

| name | d | hyperplanes | chambers | top-cones | G | classes | pairs |
|---|---|---|---|---|---|---|---|
| A_2 | 2 | 3 | 6 | 19 | ±S_3, 12 | 6 | 30 |
| A_3 | 3 | 6 | 24 | 219 | ±S_4, 48 | 10 | 300 |
| A_4 | 4 | 10 | 120 | 4,231 | ±S_5, 240 | 14 | 4,634 |
| B_2 | 2 | 4 | 8 | 33 | W, 8 | 5 | 45 |
| B_3 | 3 | 9 | 48 | 941 | W, 48 | 10 | 1,106 |
| rank1 | 1 | 1 | 2 | 3 | ±1 | 2 | 4 |
| coord2: x = 0, y = 0 | 2 | 2 | 4 | 9 | dihedral, 8 | 5 | 17 |
| tri2: y = 0, y = ±x | 2 | 3 | 6 | 19 | Klein four-group | 4 | 28 |
| coordsum3: x_i = 0, Σx_i = 0 | 3 | 4 | 14 | 71 | S_3 × ±1, 12 | 6 | 102 |

The archived run is `compute/output/audit_vanishing_criterion.txt`. Every
asserted check passes:

| check | statement | checks | fails |
|---|---|---|---|
| `[Z]` | χ_V(g) (definition) = right side of (Z) | 6,266 | 0 |
| `[loc]` | step 5 of the proof, for every X ∈ Z(V,g) | 6,708 | 0 |
| `[m>=1]` | m_X(V) ≥ 1, with a consistent restricted cone | 5,947 | 0 |
| `[down]` | Z(V,g) is a down-set of L(A)^g | 877 | 0 |
| `[Zfull]` | det(g\|_X) = (−1)^{dim X} on Z\*(g) | 67 | 0 |
| `[sgn]` | (−1)^d det g = (−1)^{dim Fix g} | 62 | 0 |
| `[S]` | some cone has χ ≠ 0 ⇔ (ii) | 62 classes | 0 |
| `[Switness]` | minimal witness top-lune: g-stable, S_max = A_X, lin = X, χ = μ(0, X) | 49 | 0 |
| `[S1]`, `[S1zero=corV]` | pointed: χ = #V^g; zero ⇔ Cor. V | 4,472 each | 0 |
| `[S2]` | Fix g = 0 | 21 | 0 |
| `[corV]` | Cor. V ⇒ Z\*(V,g) = ∅ and χ = 0 | 406 | 0 |
| `[S3inE]`, `[S3mu]` | involutions: X ⊆ E, sign of μ is (−1)^{dim X} | 42, 31 | 0 |
| `[S3refl]`, `[PCc-refl]` | reflections with mirror in A | 10 each | 0 |
| `[PCa]`, `[PCb]` | Cor. PC (a), (b) | 5,760, 5,629 | 0 |
| `[A-part]`, `[A-Zchar]`, `[A-H]` | Theorem A, the Z\* descriptions and (H) by set partitions | 130 each | 0 |
| `[A+coef]` | g ∈ S_n: every coefficient is μ(o) | 63 | 0 |
| `[A-root]` | Theorem A against full cone enumeration (A_2–A_4) | 30 | 0 |
| `[ord]` | ord(−w) = lcm(2, ord w), 3 ≤ n ≤ 7 | 41 | 0 |
| `[B3c-*]`, `[B2s-*]`, `[cox-*]` | §6 and the S2 Coxeter examples | 20 | 0 |

**Positive controls** (all pass):
- the chamber and top-cone counts 6/19, 24/219, 120/4,231, 8/33, 48/941,
  as in [GT] and [FP];
- the Lie_4 character 6, 0, −2, 0, 0 on the classes 1, (2,1,1), (2,2),
  (3,1), (4), on all chambers of A_3;
- Folkman: |μ(L(A))| = 15, 45 and 385 for B_3, D_4 and F_4.

**Negative controls.** Each deliberately wrong variant must fail at least
once, and each does:
- (Z) with m_X := 1: 5,410 of 6,266 pairs differ;
- (Z) without "X ∩ U = 0": 1,498 differ;
- (Z) without "X + U in no hyperplane": 527 differ;
- (Z) with μ_{L(A)}(0, X) in place of μ_{L(A)^g}(0, X): 21 differ;
- the witness for non-minimal X: 12 of 12 differ;
- S3 without the mirror hypothesis: fails on `coord2`;
- PC(c) without the mirror hypothesis: 4 of 15 reflections are not
  sign-coherent;
- the (A−) tight-pair description without the parity condition: 17 of 63
  differ;
- (A−) with m not required odd: 4 of 63 differ;
- ord(−w) = lcm(2, ord w) at n = 2: fails.

**Not covered here:**
- H_3, which needs Q(√5);
- the tables of [VC] §5 and §7;
- the per-cone type-A remark of [VC] §4 (Z\*(C_P, g) = F(P, g));
- the conjectural and open rows CR, PC′ and PC″.

## 8. Corrections to [VC] (not applied)

No existing note was edited.
1. **§3.1 S3, reflection bullet, and Verdict row S3.** Add the hypothesis
   "whose mirror α^⊥ is a hyperplane of A (e.g. s_α ∈ W, A the reflection
   arrangement of W)". Without it the claim fails: A = {x = 0, y = 0},
   s = swap.
2. **§5 Cor. PC(c), and Verdict row PC ("for reflections").** The same
   hypothesis is needed. Without it the claim fails on [VC]'s own example
   −s_12 on A_2, and on −(12)(34) on A_3.
3. **§2, proof of Theorem Z, step 1.** Add: "If X = R^d, which happens only
   when U = 0 and V is all chambers, the localized identity is 1 = 1 by the
   rank-0 conventions; (W″c) is used only for codim X ≥ 1."
4. **§3.1 Cor. V.** "On pointed cones every zero is of this kind" is PROVEN
   by S1 (m(V^U) ≥ 1), not only computed.
5. **§3.1 S3, B_n.** Add the long-root case: (e_1 − e_2)^⊥ is spanned by
   e_1 + e_2, e_3, …, e_n.
6. **§6, B_3.** Add that v^⊥ is the only c-stable plane, because c rotates it
   with order 6.

## Reproduce

From `compute/` (plain Python 3, no third-party packages):

    python3 audit_vanishing_criterion.py > output/audit_vanishing_criterion.txt   # ~75 s, ends "ALL CHECKS PASSED", exit 0
    python3 audit_vanishing_criterion.py --quick                                  # ~2 s: no A4, type A n <= 5, no Section 6 block
    python3 -m unittest test_audit_vanishing_criterion                            # ~1 s, positive and negative controls

The archived log is `compute/output/audit_vanishing_criterion.txt`.
