# When does the cone Lie character vanish?

This note takes up the open problem of `notes/general_theory.md` §5 and
`notes/fixed_point_formula.md` §5 ("When does χ_V(g) vanish? (OPEN.)"). The
problem is to describe the triples (A, V, g) with χ_V(g) = 0, where

  χ_V(g) = (−1)^d det(g) μ(Λ(V)^g)

is the character of H̃_{d−2}(Λ̄(V)) ≅ det ⊗ (Lie[A]|_V)^\* at a finite-order
symmetry g of (A, V).

Notation and conventions are those of `notes/fixed_point_formula.md`
("[FP]", §1) and `notes/general_theory.md` ("[GT]", §0). Throughout:
- A is a finite central essential arrangement in R^d;
- V is a top-cone with L = lin V;
- g is a finite-order linear map with gA = A and gV = V, and U = Fix(g);
- 𝓛^g is the set of g-stable flats inside L, and L(A)^g the set of all
  g-stable flats, both ordered by inclusion.

[AudW] is `notes/audit_prop_w_prime.md`. It proves Theorem W″, which
`notes/audit_theorem_w2.md` ("[AudW2]") audited independently.

Tags:
- **PROVEN**: a full proof is given here, with its inputs named.
- **COMPUTED**: checked by `compute/vanishing_criterion.py` (see Reproduce).
- **CITED**.
- **CONJECTURED**.
- **OPEN**.

## Verdict

| # | Claim | Status | Inputs |
|---|---|---|---|
| Z | **Formula Z.** χ_V(g) = Σ_{X ∈ Z\*(V,g)} μ_{L(A)^g}(0, X) · m_X(V). Here Z\*(V,g) is the set of g-stable flats X ⊆ L with X ∩ U = 0 such that no hyperplane contains X + U. m_X(V) ≥ 1 is the bottom multiplicity of the cone \|V\| ∩ U for the arrangement {H ∩ U : H ⊇ X}. Also μ_{L(A)^g}(0, X) = χ^{full}_{A^X}(g\|_X), with g\|_X fixed-point-free | **PROVEN** (§2); audit: [AudVC]; COMPUTED on all 2,762 pairs | W″ (audited) applied to every localization; Möbius inversion |
| S | **Some-cone criterion.** χ_V(g) ≠ 0 for some g-stable top-cone V iff some X ∈ Z\*(g) has μ_{L(A)^g}(0, X) ≠ 0. Here Z\*(g) is the set of g-stable flats X with X ∩ Fix g = 0 such that no hyperplane contains X + Fix g. For a minimal such X, a g-stable top-lune with lineality X has χ = μ(0, X) | **PROVEN** (§3); audit: [AudVC]; COMPUTED on every class of every type, with the witness cone checked | Formula Z, Lemma F of [FP] |
| S1 | Pointed V: χ_V(g) = #V^g. Some pointed cone has χ ≠ 0 iff Fix(g) lies in no hyperplane | **PROVEN** (§3.1); COMPUTED `[P]` | [FP] Cor. P, Lemma F |
| S2 | Fix(g) = 0: χ_V(g) = 0 for every V other than all chambers. Some cone has χ ≠ 0 iff μ(L(A)^g) ≠ 0 | **PROVEN** (§3.1); COMPUTED `[E]` | Formula Z |
| S3 | g an involution: some cone has χ ≠ 0 iff some flat X in the (−1)-eigenspace of g has X + Fix(g) in no hyperplane. For a reflection s_α: iff the line Rα is a flat | **PROVEN** (§3.1); COMPUTED `[I]` | Theorem S, Rota's sign theorem |
| V | Cor. V of [FP] is the case "a hyperplane contains L + Fix g". Under it Z\*(V,g) = ∅ | **PROVEN** (§3.1) | Formula Z |
| A | **Type A, all of ±S_n.** For g = ±w acting on the braid arrangement of A_{n−1} (n ≥ 3), some cone has χ ≠ 0 iff ⟨g⟩ acts freely on {±e_1, …, ±e_n} and μ(ord g) ≠ 0. For +w this is the known rule "all cycles of one length o, μ(o) ≠ 0". For −w it reads: the cycle lengths of w lie in {m, 2m} for one odd squarefree m | **PROVEN** (§4); audit: [AudVC]; COMPUTED for all ±w with n ≤ 8 and five classes with n = 9 | Theorem S, μ(Π_n^σ) ([FPM] (ii); Hanlon) |
| PC | Per cone: χ_V(g) ≠ 0 implies that Z\*(V,g) carries a nonzero μ. The converse holds whenever the nonzero μ(0, X), X ∈ Z\*(g), all have one sign: for g ∈ S_n, for Fix g = 0, for reflections | **PROVEN** (§5) | Formula Z, Theorem A |
| PC′ | The converse fails in general: there are 26 cancelling pairs. These are −w for w an involution with a fixed point (A_2–A_5), and the two F_4 classes of order 6 with dim Fix = (1, 2, 1, 4) on all chambers | **COMPUTED** (§5) | — |
| PC″ | An exact per-cone criterion beyond "the sum of Formula Z is ≠ 0" | **OPEN** | — |
| R | Springer regularity is neither necessary nor sufficient for "χ ≠ 0 on some cone": the Coxeter element of B_3 vanishes on every cone, and a reflection of B_2 does not | **PROVEN** by hand (§6), given Theorem S; COMPUTED for every class | Theorem S |
| CR | For X ∈ Z\*(g): if [0, X] in L(A)^g has an element with no complement, then μ(0, X) = 0 (Crapo). The converse holds on all 191 X tested (16 with μ = 0) | "if": **PROVEN** (CITED Crapo); "only if": **CONJECTURED**, COMPUTED | Crapo's complementation theorem |
| T | The classes vanishing on every cone, by type (§7). This reproduces the table of [FP] §5 for A_4, A_5, B_2, B_3, B_4, D_4 and H_3, and adds F_4 and the classes outside W | **COMPUTED** | — |

[AudVC] is `notes/audit_vanishing_criterion.md`, the independent audit of
Z, S and A.

**In one line.** Which g vanish on every cone is decided by the g-stable flats
X that meet Fix(g) only in 0 and are "transverse" to it, and by the Möbius
numbers μ(0, X) of their fixed lattices. These numbers are the full Lie
characters of the restrictions A^X at the fixed-point-free maps g|_X. Whether
χ_V(g) vanishes on a given cone is decided by the sum of Formula Z. That sum
can cancel, but only when its terms have mixed signs.

---

## 1. Inputs

Write U = Fix(g). Proposition W′ and Theorem W″ ([AudW, §2], independently
audited in [AudW2]) together give, for **every** (A, V, g) as above,
including g = 1:

  Σ_{X ∈ 𝓛^g, X ∩ U = 0} χ_{V_X}(ḡ) = m(V^U) if U lies in no hyperplane of A, and 0 otherwise.      (W″c)

Here V^U is the top-cone of the restriction A^U = {H ∩ U} with
|V^U| = |V| ∩ U, and m(V^U) ≥ 1 ([AudW, §2], "m(V^U) ≥ 1"). This is
[AudW, Thm W″(c)].

We also use:
- [FP] Lemma A and the localization step of the proof of [FP] Theorem CF. For
  a g-stable flat X ⊆ L, (A_X/X, V_X, ḡ) is again a top-cone of an essential
  arrangement with a finite-order symmetry. Its lineality flats are the Z/X
  with Z ⊇ X a flat inside L, and (V_X)_{Z/X} = V_Z compatibly with the
  induced maps.
- [FP] Lemma F (fixed chambers).
- The sign rule det(h) = (−1)^{dim − dim Fix h} for a real finite-order h
  ([AudFP] §A.1(i)).

## 2. Formula Z

**Definitions.** Let
- Z(V,g) = {X ∈ 𝓛^g : X ∩ U = 0};
- Z\*(V,g) = {X ∈ Z(V,g) : no hyperplane of A contains X + U}.

For X ∈ Z\*(V,g), let A_X|_U = {H ∩ U : H ∈ A, H ⊇ X}. Then:
- this is an arrangement of hyperplanes of U, since no H ⊇ X contains U;
- it is essential, since ∩_{H ⊇ X} H ∩ U = X ∩ U = 0;
- V_X^U is its top-cone with |V_X^U| = |V| ∩ U. The constraints of |V| are
  hyperplanes of S_max(V), and each contains L ⊇ X.

Put m_X(V) = m(V_X^U). Finally write Z\*(g) = Z\*(all chambers, g), so that
Z\*(V,g) = {X ∈ Z\*(g) : X ⊆ L}.

**Theorem Z (PROVEN; inputs (W″c), [FP] Lemma A, the localization step of
[FP] CF).** For every (A, V, g),

  χ_V(g) = Σ_{X ∈ Z\*(V,g)} μ_{L(A)^g}(0, X) · m_X(V),   with m_X(V) ≥ 1.      (Z)

Moreover, for X ∈ Z\*(g),

  μ_{L(A)^g}(0, X) = μ(L(A^X)^g) = χ^{full}_{A^X}(g|_X),

the Lie character of the full restriction A^X = {H ∩ X : H ⊉ X} (an
essential arrangement in X) at g|_X, which has no nonzero fixed vector.

*Proof.*
1. *Localize.* Let X ∈ Z(V,g). Apply (W″c) to (A_X/X, V_X, ḡ). Its
   lineality flats are the Z/X with Z ∈ 𝓛, Z ⊇ X, and Z/X is ḡ-stable iff Z
   is g-stable.
2. *Fixed space of ḡ.* Fix(ḡ) = (U + X)/X. If gx − x ∈ X, then the average
   p = (1/o) Σ_k g^k x lies in U, and p − x ∈ X, because
   g^k x − x = Σ_{j<k} g^j(gx − x) and X is g-stable.
3. *The index set.* For a g-stable flat Z ⊇ X, (Z/X) ∩ Fix(ḡ) = 0 iff
   Z ∩ (U + X) = X. By the modular law (X ⊆ Z) this is (Z ∩ U) + X = X, that
   is Z ∩ U ⊆ X ∩ U = 0. So the sum of (W″c) for V_X runs over
   {Z ∈ Z(V,g) : Z ⊇ X}.
4. *The right side.* Fix(ḡ) lies in a hyperplane H/X of A_X/X iff
   H ⊇ U + X. So the right side vanishes unless X ∈ Z\*(V,g).
   - Let X ∈ Z\*(V,g). Since U ∩ X = 0, u ↦ u + X is an isomorphism
     U → (U + X)/X.
   - It carries {H ∩ U : H ⊇ X} onto the restriction of A_X/X to Fix(ḡ).
   - It carries |V| ∩ U onto |V_X| ∩ Fix(ḡ). If u + x ∈ |V| with u ∈ U and
     x ∈ X, then u ∈ |V|, because −x ∈ X ⊆ L and |V| + L = |V|.
   - So the right side is m_X(V).
5. Hence, for every X ∈ Z(V,g),

     Σ_{Z ∈ Z(V,g), Z ⊇ X} χ_{V_Z}(ḡ) = ψ(X),   where ψ(X) = [X ∈ Z\*(V,g)] m_X(V).

6. *Invert.* Möbius inversion in the finite poset Z(V,g), which contains 0,
   gives χ_V(g) = χ_{V_0}(g) = Σ_{X ∈ Z(V,g)} μ_{Z(V,g)}(0, X) ψ(X).
7. *The Möbius function.* Z(V,g) is a down-set of L(A)^g. If Y ⊆ X ∈ Z(V,g)
   is a g-stable flat, then Y ⊆ L and Y ∩ U = 0. So
   μ_{Z(V,g)}(0, X) = μ_{L(A)^g}(0, X). This gives (Z).
8. *The full character.* The flats of A inside X are the flats of A^X, so
   [0, X]_{L(A)^g} = L(A^X)^g. By definition,
   χ^{full}_{A^X}(g|_X) = (−1)^{dim X} det(g|_X) μ(L(A^X)^g). Since
   X ∩ U = 0, the sign rule gives det(g|_X) = (−1)^{dim X}. ∎

**Checks of the statement.**
- At g = 1: U = R^d, Z\* = {0}, and (Z) reads χ_V(1) = m(V).
- The X = 0 term is [U in no hyperplane] m(V^U), the right side of (W″c).
- In the braid case Z\*(C_P, g) is the set F(P, g) of [Thm, eq. closed], and
  μ(0, X) = μ(o) (§4).

**What (Z) changes.** CF ([FP] §3) is a sum over all of 𝓛^g. Its counts
c(Y, g) are nonnegative, but its Möbius coefficients have both signs, and
most terms cancel. (Z) keeps only the flats transverse to Fix(g). It has
positive multiplicities and, for each g, a fixed list of coefficients
μ(0, X) that do not depend on V. The cone enters only through which X fit
inside L, and through the m_X(V).

COMPUTED: (Z) equals CF, and CF equals the definition (−1)^d det(g)
μ(Λ(V)^g), on all 2,762 pairs (V, g) of §7. Here m_X(V) is computed
independently, from the support lattice of the restricted cone (the zero
sets of the g-stable faces of V). Negative controls: (Z) fails if the
condition "X + U in no hyperplane" or "X ∩ U = 0" is dropped, or if m_X is
replaced by 1 (tests `test_z_needs_*`).

## 3. Theorem S: nonzero on some cone

**Theorem S (PROVEN; inputs Theorem Z, [FP] Lemma F).** Let g be a
finite-order linear symmetry of A and U = Fix(g). The following are
equivalent:
- (i) χ_V(g) ≠ 0 for some g-stable top-cone V;
- (ii) some X ∈ Z\*(g) has μ_{L(A)^g}(0, X) ≠ 0, that is,
  χ^{full}_{A^X}(g|_X) ≠ 0.

If X is minimal among the flats in (ii), let K be a g-fixed chamber of the
localization A_X (one exists), and V♯ = {chambers C of A : C ⊆ K}. Then V♯
is a g-stable top-cone (a top-lune of [Cone, §1] with zero set
{H : H ⊇ X}), lin V♯ = X, and χ_{V♯}(g) = μ_{L(A)^g}(0, X).

*Proof.*
- (i) ⇒ (ii). Z\*(V,g) ⊆ Z\*(g). If every μ(0, X), X ∈ Z\*(g), is 0, then
  (Z) gives χ_V(g) = 0 for every V.
- (ii) ⇒ (i). Take X minimal in (ii).
  - *K exists.* No hyperplane of A_X contains U, since X ∈ Z\*(g). By
    [FP] Lemma F, applied to the arrangement A_X and h = g, the g-fixed
    chambers of A_X correspond to the chambers of A_X|_U, so there is at
    least one.
  - *V♯ is a g-stable top-cone.* It is the top-cone {C : C_e = K_e for H_e ⊇ X},
    and it is g-stable because gK = K.
  - *lin V♯ = X.* |V♯| is the closure of K. Every hyperplane H ⊉ X cuts
    X ⊆ |V♯|, so S_max(V♯) = A_X, and lin V♯ = ∩_{H ⊇ X} H = X.
  - *Evaluate (Z).* The flats of Z\*(V♯, g) are the X′ ∈ Z\*(g) with
    X′ ⊆ X. By minimality, every X′ ⊊ X there has μ(0, X′) = 0.
  - *The X-term.* V♯_X is the single chamber K/X of A_X/X. So |V♯| ∩ U =
    closure(K) ∩ U is the closure of the single chamber K ∩ U of A_X|_U
    (Lemma F). A pointed cone with one chamber has m = 1.
  - Hence χ_{V♯}(g) = μ(0, X) ≠ 0. ∎

So "nonzero on some cone" is a property of g alone. It depends only on U and
on the fixed lattice L(A)^g. A top-lune always realizes it.

COMPUTED: on every conjugacy class of G (the symmetry group used, §7) for
A_2–A_5, B_2–B_4, D_4 and H_3, "χ_V(g) ≠ 0 for some cone in the full
enumeration" matches (ii). For F_4 (sampled) the witness top-lune is checked
for every class satisfying (ii), and no sampled cone is nonzero for a class
failing it. A negative control (`test_witness_must_be_minimal`) uses a
rotation by π in H_3. Z\*(g) consists of four lines with μ = −1 inside a
plane with μ = 5, and the top-lune of the plane has χ = 5 − 4 = 1, not 5.

### 3.1 Corollaries

**S1 (pointed cones; PROVEN).** If L = 0, then Z\*(V, g) ⊆ {0} and (Z) reads
χ_V(g) = [U in no hyperplane] m(V^U) = #V^g ([FP] Cor. P). So χ_V(g) ≠ 0
iff g fixes a chamber of V. Some pointed cone has χ ≠ 0 iff U lies in no
hyperplane: take V = a g-fixed chamber, by Lemma F. For g in a reflection
group W with g ≠ 1, U is a proper flat (Steinberg), so this never happens.
COMPUTED `[P]`.

**S2 (Fix g = 0; PROVEN).** If U = 0, then X + U = X lies in no hyperplane
only for X = R^d. So Z\*(g) ⊆ {R^d}, and:
- χ_V(g) = 0 for every V other than all chambers;
- χ_{all}(g) = μ(L(A)^g).

COMPUTED `[E]`. Examples:
- −1, which preserves every central arrangement: μ(L(A)) ≠ 0, so χ(−1) ≠ 0
  on all chambers.
- The Coxeter elements of A_3, B_3, D_4 and H_3 vanish on every cone. For
  B_3 and H_3 the fixed lattice is a chain 0 < ℓ < R^3 (§6).
- The Coxeter elements of A_2, A_4, A_5, B_2, B_4 and F_4 do not.

**S3 (involutions; PROVEN; input Rota's theorem that the Möbius function of
a geometric lattice alternates in sign, so μ(0̂, 1̂) ≠ 0).** Let g² = 1 and
E = ker(g + 1).
- A g-stable X with X ∩ U = 0 is a subspace of E, because
  X = (X ∩ U) ⊕ (X ∩ E).
- g acts as −1 on X, so [0, X]_{L(A)^g} is all of L(A^X), a geometric
  lattice, and μ(0, X) = μ(L(A^X)) has sign (−1)^{dim X}, nonzero.

Hence an involution g is nonzero on some cone iff some flat X ⊆ E has
X + U in no hyperplane.
- For a reflection s_α, E = Rα. So s_α is nonzero on some cone iff Rα is a
  flat, that is, iff the roots orthogonal to α span α^⊥.
- This fails for every reflection of A_{n−1}, n ≥ 3 (the roots ⊥ e_1 − e_2
  span only n − 3 dimensions of the (n − 2)-dimensional α^⊥ in R^n_0).
- It holds for every reflection of B_n, D_4, F_4 and H_3 (COMPUTED). For
  example, in B_n the roots ⊥ e_1 are ±e_j, ±e_j ± e_k (j, k ≥ 2), which
  span e_1^⊥.
- COMPUTED `[I]`: every X ∈ Z\*(g) of an involution has μ ≠ 0.

**Cor. V of [FP] (PROVEN).** If a hyperplane H contains both L and U, then
H ⊇ X + U for every X ⊆ L, so Z\*(V, g) = ∅ and χ_V(g) = 0. Conversely,
χ_V(g) ≠ 0 forces L + U to lie in no hyperplane. On pointed cones every
zero is of this kind (§7).

## 4. Type A: all of ±S_n

Let A be the braid arrangement of A_{n−1}, n ≥ 3, in R^n_0 = {Σ x_i = 0},
with hyperplanes H_ij = {x_i = x_j}. Its flats are
X_π = {x ∈ R^n_0 constant on the blocks of π}, for set partitions π of [n].
- dim X_π = |π| − 1.
- X_π ⊆ X_ρ iff π is coarser than ρ.
- H_ij ⊇ X_π iff i, j lie in one block of π.

For w ∈ S_n and ε = ±1, the map g = εw acts by (gx)_{w(i)} = ε x_i. It
preserves A. Both signs give finite-order symmetries, and −w ∉ W for n ≥ 3.
- X_π is g-stable iff π is w-stable, since −1 fixes every subspace.
- [0, X_π] in L(A)^g is the set of w-stable coarsenings of π, which is the
  fixed lattice Π(π)^{w̄} of the permutation w̄ that w induces on the blocks.
- So μ_{L(A)^g}(0, X_π) = μ(Π_b^{w̄}), b = |π|.
- By [FPM] (ii) (PROVEN there; Hanlon, Thm 4, CITED in [FP] §6), this is 0
  unless all cycles of w̄ have one length ℓ, and then it equals
  (−1)^{r−1} μ(ℓ) ℓ^{r−1} (r−1)!, with r = b/ℓ.        (H)

For n ≥ 3, ord(−w) = lcm(2, ord w). (−1)^j w^j = 1 on R^n_0 forces j even,
because no permutation acts as −1 on R^n_0 when n ≥ 3.

**Theorem A (PROVEN; inputs Theorem S, (H)).** Let n ≥ 3 and g = εw. Then
some top-cone V has χ_V(g) ≠ 0 iff ⟨g⟩ acts freely on {±e_1, …, ±e_n} and
μ(ord g) ≠ 0. Explicitly:
- (A+) ε = +1: iff all cycles of w have one length o and μ(o) ≠ 0.
- (A−) ε = −1: iff there is an odd squarefree m such that every cycle of w
  has length m or 2m. Then ord g = 2m.

Since g^j(e_i) = ε^j e_{w^j(i)}, ⟨g⟩ acts freely on {±e_i}:
- for ε = +1, iff every cycle length equals ord w;
- for ε = −1, iff lcm(2, k) is the same for every cycle length k.

With μ(ord g) ≠ 0 (and ord g = lcm(2, ord w) even for ε = −1), these are the
two explicit forms.

*Proof of (A+).* Here U is the set of sum-zero functions constant on the
cycles of w. Let cyc be the partition of [n] into cycles.
- H_ij ⊇ U iff i, j lie in one cycle.
- X_π ∩ U = 0 iff π ∨ cyc = 1̂. A function constant on the blocks of π and
  on the cycles is constant on the blocks of π ∨ cyc.
- X_π + U lies in no hyperplane iff π ∧ cyc = 0̂: no block holds two
  points of one cycle.

So Z\*(g) = {w-stable π : π ∨ cyc = 1̂, π ∧ cyc = 0̂}.

Let π ∈ Z\*(g).
- The union of a w̄-orbit of blocks is a union of blocks and of cycles, so
  it is all of [n]. Hence w̄ is transitive on the b blocks.
- For i ∈ B, w^b(i) ∈ B lies in the cycle of i, so w^b(i) = i. Then
  w^b = 1 on B, hence on every block, and ord w | b.
- b | ord w, as an orbit length. So b = o := ord w.
- If w^j(i) = i with 0 < j < o, then w^j B = B for the block B ∋ i,
  against freeness of the transitive action of Z/o on o blocks. So every
  cycle has length o.
- By (H), with ℓ = o and r = 1, μ(0, X_π) = μ(o).

Conversely, if every cycle has length o, choose one point of each cycle to
form B_0 and set π = {w^j B_0 : 0 ≤ j < o}. Then π ∈ Z\*(g) and μ = μ(o).
This is the braid criterion of [FPM] (a) and [Thm, eq. closed], now
obtained from Theorem S.

*Proof of (A−).* Here U = {x ∈ R^n_0 : x_{w(i)} = −x_i}. Such an x
alternates in sign along each cycle, so it vanishes on the odd cycles. Let
O be the union of the odd cycles (fixed points included). Then:

- **Tight pairs.** H_ij ⊇ U iff i, j ∈ O, or i, j lie in one even cycle at
  even distance. If i lies in an even cycle C, take u ∈ U supported on C
  with u_i = 1: then u_j = 0 off C, and u_j = −1 at odd distance.
- **X_π ∩ U.** It is the set of functions f on the blocks with
  f(w̄B) = −f(B). Such an x = f is automatically sum-zero, since
  x_{w(i)} = −x_i gives Σ x = −Σ x. On a w̄-orbit of length ℓ this forces
  f = (−1)^ℓ f, and any alternating f on an orbit of even length works.
  So X_π ∩ U = 0 iff every w̄-orbit of blocks has odd length.

Hence Z\*(g) is the set of w-stable π such that:
- every w̄-orbit of blocks has odd length;
- no block contains two points of O;
- no block contains two points of one even cycle at even distance.

*Necessity.* Let π ∈ Z\*(g) with μ(0, X_π) ≠ 0.
- By (H), all w̄-orbits have one length ℓ, with ℓ odd and μ(ℓ) ≠ 0.
- Let i ∈ B, with cycle length k. Since w^k(i) = i, w̄^k B = B, so ℓ | k.
- The points w^{jℓ}(i), 0 ≤ j < k/ℓ, all lie in B.
  - If k is odd, at most one point of O lies in B, so k = ℓ.
  - If k is even, the distance between w^{jℓ}(i) and i has the parity of
    j, because ℓ is odd and k is even. j = 0 and j = 2 would give two
    points of B at even distance. So k/ℓ ≤ 2, and k/ℓ = 1 is impossible
    (k even, ℓ odd). So k = 2ℓ.
- So every cycle has length m = ℓ or 2m, with m odd squarefree.

*Sufficiency.* Given such m, let π consist of:
- the singletons {i}, i ∈ O (all odd cycles have length m);
- the antipodal pairs {i, w^m(i)} in each even cycle (length 2m), at odd
  distance m.

Then π is w-stable, and all w̄-orbits have length m (odd). No block holds a
tight pair. By (H), μ(0, X_π) = (−1)^{r−1} μ(m) m^{r−1} (r−1)! ≠ 0. ∎

COMPUTED `[A+]`, `[A−]`:
- the rule matches Theorem S on every class of ±S_n for A_2–A_5, in the
  root-system code;
- by set partitions, on all 126 classes ±w with 3 ≤ n ≤ 8 (plus five
  classes −w with n = 9, among them −(6,3), which is nonzero, and −(9),
  which is zero);
- by the full cone enumeration (§7) for A_2–A_5.

Examples:
- −(3,3), −(6) and −(2,2,1,1) are nonzero on some cone;
- −(4), −(3,1) and −(3,3,1) are zero on every cone.

**Remark (per cone, type A).** For ε = +1, Z\*(C_P, g) is the set of
π ∈ Z\*(g) whose blocks are unions of components of P. That is F(P, g) of
[Thm], and every coefficient is μ(o). So (Z) has one sign, and
χ_{C_P}(g) ≠ 0 iff μ(o) ≠ 0 and ⟨g⟩ acts freely on the components. This is
[Thm, eq. closed] and the known per-cone criterion. For ε = −1 the
coefficients (−1)^{r−1} μ(m) m^{r−1}(r−1)! change sign with the number r of
block orbits, and (Z) can cancel (§5).

## 5. Per cone

**Corollary PC (PROVEN; input Theorem Z).**
- (a) If χ_V(g) ≠ 0, then some X ∈ Z\*(g) with X ⊆ L has μ(0, X) ≠ 0.
- (b) Call g *sign-coherent* if the nonzero μ(0, X), X ∈ Z\*(g), all have
  one sign. Then (a) is an equivalence for g, since every m_X(V) ≥ 1.
- (c) Sign-coherent classes include:
  - every g ∈ S_n in type A (all coefficients μ(o), §4);
  - every g with Fix g = 0 (one term, S2);
  - every reflection (Z\*(g) ⊆ {Rα});
  - every g whose Z\*(g) is a single flat.

**Cancellation does occur (COMPUTED).** On 26 of the 2,762 pairs, Z\*(V, g)
carries nonzero μ but χ_V(g) = 0:

| type | pairs | class (all cones) | example terms (dim X, μ(0,X), m_X) |
|---|---|---|---|
| A_2 | 2 | −(2,1) | (0, 1, 1), (1, −1, 1) |
| A_3 | 2 | −(2,1,1) | (1, −1, 1), (1, −1, 1), (2, 2, 1) |
| A_4 | 8 + 2 | −(2,2,1), −(2,1,1,1) | (0, 1, 3), (1, −1, 3) |
| A_5 | 8 + 2 | −(2,2,1,1), −(2,1,1,1,1) | ten terms summing to 0 (output) |
| F_4 | 2 | the two classes of order 6 with (dim Fix g^k)_{k\|6} = (1,2,1,4), on all chambers | (2, −1, 1), (3, 1, 1) |

In type A every cancelling g is −w with w an involution with a fixed
point. The smallest example is the full cone of A_2 with g = −s_{12}, the
reflection in the line orthogonal to H_12. There U = R(e_1 − e_2) lies in no
hyperplane, and Z\* = {0, H_12}. The X = 0 term is +m(V^U) = 1 and the
X = H_12 term is −1. Indeed −s_{12} fixes two chambers, and by EZ of [FP]
2 = χ_A(g) + χ_{A_{H_12}}(ḡ) + 1 = 0 + 1 + 1.

In B_2–B_4, D_4 (with triality) and H_3, no pair cancels in the full
enumeration, although some classes there are not sign-coherent. So in
those types (a) is an equivalence on every pair tested (COMPUTED).

**Open (PC″).** Characterize cancellation, that is, give an exact per-cone
criterion that does not pass through the signed sum (Z). The output lists
the terms (dim X, μ(0, X), m_X) of the first cancelling pairs of each type.
In those listed, the cancelling terms have equal multiplicities m_X, which
suggests looking for a sign-reversing involution on Z\*(V, g). This is an
observation on the listed examples only.

## 6. The candidates of the problem statement

- **Springer regularity: refuted, both directions (PROVEN by hand, given
  Theorem S).**
  - *B_3, Coxeter element c* (signed 3-cycle with one sign change, order 6,
    regular). Fix c = 0, and c^3 = −1. The (−1)-eigenline ℓ = R(1, −1, 1)
    is the flat {x_1 = −x_2 = x_3}. The complementary c-stable plane
    x_1 − x_2 + x_3 = 0 is not a hyperplane of B_3, so it is not a flat.
    So L(A)^c = {0, ℓ, R^3}, a chain, and μ = 0. By S2, c vanishes on every
    cone.
  - The same holds for the Coxeter elements of H_3 (fixed lattice
    0 < 5-fold axis < R^3) and of D_4 (COMPUTED).
  - *B_2, reflection s* (s(x, y) = (−x, y), not regular). Rα = x-axis is a
    flat, so by S3 s is nonzero on some cone. On all chambers χ = −1.
  - Per type, regular-and-vanishing / non-regular-and-nonvanishing classes
    of W: A_2 1/0, A_3 2/0, A_4 2/0, A_5 1/0, B_2 0/2, B_3 2/6, B_4 0/12,
    D_4 2/4, H_3 6/2, F_4 0/16 (COMPUTED; regularity by a floating-point
    eigenvector test).
- **Eigenvalues of g on the lineality space.** Not the right invariant.
  The cone enters (Z) only through which X ∈ Z\*(g) fit inside L. Two cones
  with the same L have the same Z\*(V, g) (and both are zero or not when
  g is sign-coherent).
- **Fix(g) relative to the flats of lin V.** This is the answer. The
  relevant flats are those X ⊆ L with X ∩ Fix g = 0 and X + Fix g in no
  hyperplane, a transversality condition. Cor. V is the degenerate case in
  which no such X can exist.
- **A μ-function condition generalizing μ(o) ≠ 0.** This is
  μ_{L(A)^g}(0, X) ≠ 0 for some X ∈ Z\*(g). In type A it is μ(o) (§4).
  In general it is the full Lie character of A^X at the fixed-point-free
  g|_X, so the cone question reduces to the full-arrangement question for
  restrictions.
- **Crapo complementation (CR).** If some g-stable flat strictly inside X
  has no g-stable complement in [0, X], then μ(0, X) = 0 (Crapo's
  complementation theorem, CITED; this is the mechanism of [FPM] case (a)).
  CONJECTURED converse: COMPUTED on all 191 X ∈ Z\*(g) of all classes of all
  types here, of which 16 have μ = 0, each with an uncomplemented element.
  For example, the B_3 Coxeter element's ℓ has no complement.

## 7. Data (COMPUTED)

`compute/vanishing_criterion.py`, exact arithmetic (Fractions; Q(√5) for
H_3), no imports from other scripts. G is the symmetry group used:
- ±W for type A;
- W(D_4) ⋊ S_3 (order 1,152, the triality extension) for D_4;
- W otherwise (−1 ∈ W).

Pairs are (V, g) with V a W-orbit representative of the top-cones, and g a
representative of a conjugacy class of Stab_G(V). The numbers differ from
[FP] §5, which counts elements, not classes. F_4 is sampled: all chambers,
12 random g-stable cones per class (constraints from a g-stable face,
closed under ⟨g⟩, seed 1) and the witness top-lunes.

| type | top-cones | W-orbits | classes of G | pairs | χ ≠ 0 | zero by Cor. V | zero, Z\*(V) carries no nonzero μ | zero by cancellation |
|---|---|---|---|---|---|---|---|---|
| A_2 | 19 | 5 | 6 | 19 | 14 | 2 | 1 | 2 |
| A_3 | 219 | 16 | 10 | 56 | 35 | 13 | 6 | 2 |
| A_4 | 4,231 | 63 | 14 | 180 | 83 | 72 | 15 | 10 |
| A_5 | 130,023 | 318 | 22 | 873 | 406 | 419 | 38 | 10 |
| B_2 | 33 | 7 | 5 | 20 | 18 | 2 | 0 | 0 |
| B_3 | 941 | 35 | 10 | 93 | 64 | 27 | 2 | 0 |
| B_4 | 60,201 | 266 | 20 | 668 | 379 | 283 | 6 | 0 |
| D_4 | 12,313 | 110 | 25 | 503 | 324 | 174 | 5 | 0 |
| H_3 | 7,745 | 93 | 10 | 174 | 110 | 58 | 6 | 0 |
| F_4 | sampled | — | 25 | 176 | 68 | 104 | 2 | 2 |

Positive controls:
- the top-cone and orbit counts match [GT] and [FP];
- the Lie_4 character 6, −2, 0, 0, 0 on all chambers of A_3;
- m(all chambers) = |μ(L(A))|: 15, 105, 45, 45, 385 for B_3, B_4, D_4,
  H_3, F_4;
- B_2: every class is nonzero on some cone ([FP] §5);
- the braid rule (A+).

**By lineality type.** The output lists the pairs by (dim L, W-orbit of L).
Summed over orbits of L:
- On pointed cones (dim L = 0) every zero is a Cor. V zero, as S1 predicts.
- "Z\*(V) carries no nonzero μ" zeros occur only for dim L ≥ 2.
- Cancellations occur only on non-pointed cones in type A, and only on all
  chambers in F_4.

**Classes vanishing on every cone** (by Theorem S; the same classes as the
full enumeration). Labels: cycle type for A (− for −w), signed cycle type
for B, otherwise order o and (dim Fix g^k)_{k | o}.

| type | classes in W vanishing on every cone | classes in G ∖ W vanishing on every cone |
|---|---|---|
| A_2 | (2,1) | none |
| A_3 | (2,1,1), (3,1), (4) | −(3,1), −(4) |
| A_4 | all except 1 and (5) | −(3,1,1), −(4,1), −(3,2) |
| A_5 | all except 1, (2,2,2), (3,3), (6) | −(3,1,1,1), −(4,1,1), −(3,2,1), −(5,1), −(4,2) |
| B_2 | none | — |
| B_3 | [3+], [3−] | — |
| B_4 | [3+ 1+], [3+ 1−], [3− 1+], [3− 1−] | — |
| D_4 | o=3 (2,4); o=6 (0,2,0,4) | o=6 (1,2,1,4) (one of two classes); o=6 (1,2,3,4) (one of two) |
| H_3 | both classes of order 5, the class of order 3, the class of order 6, both classes of order 10 | — |
| F_4 | the two classes of order 6 with (1,2,3,4) | — |

These rows agree with the table of [FP] §5 for the types it covers. F_4
is new. In F_4 the elements of order 3 with dim Fix = 2 are nonzero on
some cone, unlike in B_4 and D_4. For both F_4 classes of order 3 with
(2, 4), the orthogonal plane of Fix g is a g-stable flat transverse to it.

## 8. Remarks on other notes (not applied)

- `notes/fixed_point_formula.md`, Verdict row "—" and §5 ("When does χ_V(g)
  vanish? (OPEN.)"). The "nonzero on some cone" half is now Theorem S
  (PROVEN). The per-cone half is Formula Z with Cor. PC, and the remaining
  open part is PC″. Its type-A sentence "g is nonvanishing on some cone iff
  all its cycles have one length o with μ(o) ≠ 0" is correct for g ∈ S_n.
  For g = −w the rule is (A−).
- `notes/general_theory.md` §5 lists this problem as open. It can point
  here.
- No correction to an existing claim was found. The [FP] §5 vanishing table
  is reproduced exactly.

## 9. Prior art

Not searched for this note. For V = all chambers and g ∈ W, χ_A(g) is, up
to the det twist and duality, the character of W on the top Orlik–Solomon
degree. Character formulas there (Lehrer; Orlik–Solomon) may overlap with
the full-cone case of (Z) and with S2. That has not been checked. Theorem S,
Formula Z for proper cones, and Theorem A for −w were not found in the
sources read for [FP] ([NovFP]), but no search specific to them was made.

## Reproduce

From `compute/` (plain Python 3, no third-party packages):

    python3 vanishing_criterion.py --n9 > output/vanishing_criterion.txt   # ~35 s, ALL CHECKS PASSED, exit 0
    python3 vanishing_criterion.py --quick                                 # ~1 s: A2, A3, B2, B3; type A n <= 6
    python3 vanishing_criterion.py --types D4,H3                           # any subset; F4 is sampled (--samples k)
    python3 -m unittest test_vanishing_criterion                           # ~3 s, positive and negative controls

The archived output is `compute/output/vanishing_criterion.txt`.

References: [FP] = `notes/fixed_point_formula.md`; [GT] =
`notes/general_theory.md`; [Thm] = `notes/poset_jks_theorem.tex`; [FPM] =
`notes/fixed_point_mobius_identity.md`; [Cone] =
`notes/cone_lune_lie_theory.md`; [AudFP] =
`notes/audit_fixed_point_formula.md`; [AudW] =
`notes/audit_prop_w_prime.md`; [AudW2] = `notes/audit_theorem_w2.md`;
[NovFP] = `notes/novelty_fixed_point_formula.md`; [AudVC] =
`notes/audit_vanishing_criterion.md` (the independent audit of this note).
