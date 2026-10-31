import PosetJKS.MainTheorem
import PosetJKS.ChainTools
import PosetJKS.ConeRetract
import PosetJKS.Complement

/-!
# Positive controls for the definitions, and two counterexamples

Evaluations of the definitions of `Basic.lean`, `OrderComplex.lean` and `Milestone.lean` on
small concrete posets, compared with `compute/output/character_table.tsv` (labels `1, …, n`
there are `0, …, n-1` here). Controls are kernel-checked (`decide +kernel` or a proof), except
the `#guard` lines (compiled evaluation): the `n = 4` order-preserving counts (the same certified
Boolean procedure, with its certificate `closedB` checked inline) and the mirror Möbius
computation, which is a transcription, not the Lean definition, and is labelled as such.

* `|Lin P|` and `e_C(P)`: the definitions are classical (`open Classical`), so they are first
  rewritten, by proved lemmas (`natCard_linExt`, `eC_eq`, `fixedClassSum_eq`), into the same
  expressions with computable instances, and then evaluated by `decide +kernel`.
* `IsOrderPreserving` is not decidable as written (`Relation.ReflTransGen`). For a partition given
  as the kernel of a labelling `f`, `isOrderPreserving_ker_iff` reduces it, under a certificate
  that is itself checked by `decide`, to a Boolean acyclicity test. The test then runs on every
  restricted growth function, i.e. on every set partition.
* `muFixed` is not computable (Mathlib's `IncidenceAlgebra.mu` on a subtype of `Setoid α`). It is
  checked by a proved value on the 2-chain, and by a mirror computation (`#guard`) on the same
  partition lists for the other posets.
* `PLie` and `HP` are spans/quotients and not computable. Checked by proved lemmas: the
  eigenvalue relation `relabel g (w e_ζ) = ζ^r w e_ζ` (fixes the `ζ` and rotation convention
  against `classRot`), `∂ ∘ ∂ = 0` for `bd`, and the augmentation `bd 0`.
* Counterexamples at the empty poset (`n = 0`): without the hypothesis `0 < Fintype.card α`,
  `corPsi_bijective` and `trace_PLie` would be false. These lemmas are why both statements
  (and `corPsi`) carry `h0 : 0 < Fintype.card α`, the note's implicit `n ≥ 1`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace PosetJKS.Test

/-! ### Concrete finite posets on `Fin n` -/

/-- A partial order on `Fin n`, given by a Boolean table. -/
structure FinPoset (n : ℕ) where
  le : Fin n → Fin n → Bool
  refl : ∀ a, le a a = true
  antisymm : ∀ a b, le a b = true → le b a = true → a = b
  trans : ∀ a b c, le a b = true → le b c = true → le a c = true

/-- The carrier of a `FinPoset` (a type synonym of `Fin n`, so that it carries the new order). -/
def FinPoset.T {n : ℕ} (_ : FinPoset n) : Type := Fin n

section Instances

variable {n : ℕ} (P : FinPoset n)

instance : Fintype P.T := inferInstanceAs (Fintype (Fin n))
instance : DecidableEq P.T := inferInstanceAs (DecidableEq (Fin n))
instance : PartialOrder P.T where
  le a b := P.le a b = true
  le_refl := P.refl
  le_trans := P.trans
  le_antisymm := P.antisymm
instance : DecidableRel (α := P.T) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (P.le a b = true))
instance : DecidableRel (α := P.T) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (P.le a b = true ∧ ¬ P.le b a = true))

theorem card_T : Fintype.card P.T = n := Fintype.card_fin n

/-- The identity labelling `Fin n ≃ P`. -/
def toT : Fin n ≃ P.T := Equiv.refl _

/-- The word `σ(0) σ(1) ⋯ σ(n-1)` (letters `0, …, n-1` of `P`). -/
def mkWord (σ : Equiv.Perm (Fin n)) : Word P.T := (finCongr (card_T P)).trans (σ.trans (toT P))

/-- An automorphism of `P` from a permutation of `Fin n` that preserves the table. -/
def mkAut (σ : Equiv.Perm (Fin n)) (h : ∀ a b, P.le (σ a) (σ b) = P.le a b) : P.T ≃o P.T where
  toEquiv := σ
  map_rel_iff' {a b} := by
    change P.le (σ a) (σ b) = true ↔ P.le a b = true
    rw [h]

end Instances

/-- The poset on `Fin n` whose strict relations are the pairs in `lt` (assumed transitive). -/
def ofLt (n : ℕ) (lt : List (Fin n × Fin n))
    (h1 : ∀ a b, (a = b || (a, b) ∈ lt) = true → (b = a || (b, a) ∈ lt) = true → a = b)
    (h2 : ∀ a b c, (a = b || (a, b) ∈ lt) = true → (b = c || (b, c) ∈ lt) = true →
      (a = c || (a, c) ∈ lt) = true) : FinPoset n where
  le a b := a = b || (a, b) ∈ lt
  refl a := by simp
  antisymm := h1
  trans := h2

/-- The 3-antichain (`n3_000`). -/
def anti3 : FinPoset 3 := ofLt 3 [] (by decide) (by decide)
/-- The 3-chain `0 < 1 < 2` (`n3_004`). -/
def chain3 : FinPoset 3 := ofLt 3 [(0, 1), (1, 2), (0, 2)] (by decide) (by decide)
/-- The `2 + 1` poset `0 < 1`, `2` isolated (`n3_001`). -/
def p21 : FinPoset 3 := ofLt 3 [(0, 1)] (by decide) (by decide)
/-- The 4-antichain (`n4_000`). -/
def anti4 : FinPoset 4 := ofLt 4 [] (by decide) (by decide)
/-- The 4-chain (`n4_015`). -/
def chain4 : FinPoset 4 := ofLt 4 [(0, 1), (1, 2), (2, 3), (0, 2), (1, 3), (0, 3)] (by decide) (by decide)
/-- The N poset `0 < 2`, `0 < 3`, `1 < 2` (`n4_007`). -/
def pN : FinPoset 4 := ofLt 4 [(0, 2), (0, 3), (1, 2)] (by decide) (by decide)
/-- Two 2-chains `0 < 3`, `1 < 2` (`n4_006`). -/
def twoChains : FinPoset 4 := ofLt 4 [(0, 3), (1, 2)] (by decide) (by decide)
/-- The 2-chain `0 < 1` (`n2_001`). -/
def chain2 : FinPoset 2 := ofLt 2 [(0, 1)] (by decide) (by decide)

end PosetJKS.Test

namespace PosetJKS

/-! ### Bridge lemmas: the classical definitions equal computable expressions -/

section DecInst

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableRel (α := α) (· < ·)]

/-- `Lin(P)` membership is decidable when `<` is. -/
@[reducible] def decidablePredIsLinExt : DecidablePred (IsLinExt α) := fun w =>
  inferInstanceAs (Decidable (∀ i j, w i < w j → i < j))

/-- Being a union of components is decidable when `≤` is. -/
@[reducible] def decidableIsUnionOfComponents [DecidableRel (α := α) (· ≤ ·)] (S : Finset α) :
    Decidable (IsUnionOfComponents S) :=
  inferInstanceAs (Decidable (∀ x y : α, x ≤ y → (x ∈ S ↔ y ∈ S)))

attribute [local instance] decidablePredIsLinExt decidableIsUnionOfComponents in
/-- `B_P` membership, decided through the bounded form of the prefix quantifier. -/
@[reducible] def decidablePredInB [DecidableRel (α := α) (· ≤ ·)] (x₀ : α) : DecidablePred (InB x₀) :=
  fun w => decidable_of_iff (IsLinExt α w ∧ ∀ k < Fintype.card α + 1, 0 < k →
      IsUnionOfComponents (prefixSet w k) → x₀ ∈ prefixSet w k)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun k hk hkn hU => h2 k (Nat.lt_succ_of_le hkn) hk hU⟩,
     fun ⟨h1, h2⟩ => ⟨h1, fun k hkn hk hU => h2 k hk (Nat.le_of_lt_succ hkn) hU⟩⟩

end DecInst

-- File-local, so that importing `PosetJKS` does not change any instance used elsewhere.
attribute [local instance] decidablePredIsLinExt decidableIsUnionOfComponents decidablePredInB

section Bridge

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableRel (α := α) (· < ·)]

theorem natCard_linExt :
    Nat.card {w : Word α // IsLinExt α w} = (univ.filter (IsLinExt α)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cyc_eq : cyc α = (univ.filter (IsLinExt α)).image coset := by
  unfold cyc
  congr 1
  exact Finset.filter_congr_decidable _ _ _

theorem eC_eq : eC α = ((univ.filter (IsLinExt α)).image coset).card := by
  rw [eC, cyc_eq]

theorem fixedClassSum_eq (ζ : ℂ) (g : α ≃o α) :
    fixedClassSum ζ g =
      ∑ C ∈ ((univ.filter (IsLinExt α)).image coset).filter
        (fun C => C.image (fun w => w.trans g.toEquiv) = C), ζ ^ classRot g C := by
  rw [fixedClassSum, cyc_eq]

end Bridge

section ClassRot

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- `classRot g C = r` as soon as `r` is the least rotation realised in `C`. -/
theorem classRot_eq_of {g : α ≃o α} {C : Finset (Word α)} {r : ℕ}
    (hr : r < Fintype.card α ∧ ∃ w ∈ C, w.trans g.toEquiv = rot w r)
    (hmin : ∀ m < r, ¬ (m < Fintype.card α ∧ ∃ w ∈ C, w.trans g.toEquiv = rot w m)) :
    classRot g C = r := by
  classical
  unfold classRot
  rw [dif_pos ⟨r, hr⟩, Nat.find_eq_iff]
  exact ⟨hr, hmin⟩

end ClassRot

namespace Test

/-! ### `|Lin P|` and `e_C(P)` (expected values from `character_table.tsv`) -/

-- `|Lin P|`: 6, 1, 3, 24, 1, 5, 6.
example : Nat.card {w : Word anti3.T // IsLinExt _ w} = 6 := by rw [natCard_linExt]; decide +kernel
example : Nat.card {w : Word chain3.T // IsLinExt _ w} = 1 := by rw [natCard_linExt]; decide +kernel
example : Nat.card {w : Word p21.T // IsLinExt _ w} = 3 := by rw [natCard_linExt]; decide +kernel
example : Nat.card {w : Word anti4.T // IsLinExt _ w} = 24 := by rw [natCard_linExt]; decide +kernel
example : Nat.card {w : Word chain4.T // IsLinExt _ w} = 1 := by rw [natCard_linExt]; decide +kernel
example : Nat.card {w : Word pN.T // IsLinExt _ w} = 5 := by rw [natCard_linExt]; decide +kernel
example : Nat.card {w : Word twoChains.T // IsLinExt _ w} = 6 := by rw [natCard_linExt]; decide +kernel

-- `e_C(P)`: 2, 1, 2, 6, 1, 5, 5.
example : eC anti3.T = 2 := by rw [eC_eq]; decide +kernel
example : eC chain3.T = 1 := by rw [eC_eq]; decide +kernel
example : eC p21.T = 2 := by rw [eC_eq]; decide +kernel
example : eC anti4.T = 6 := by rw [eC_eq]; decide +kernel
example : eC chain4.T = 1 := by rw [eC_eq]; decide +kernel
example : eC pN.T = 5 := by rw [eC_eq]; decide +kernel
example : eC twoChains.T = 5 := by rw [eC_eq]; decide +kernel

/-- Mismatch control: the same instrument separates posets with different values. The 2+1
poset has `e_C = 2`; the 3-chain, which differs by one relation, does not. -/
example : eC chain3.T ≠ 2 := by rw [eC_eq]; decide +kernel
example : Nat.card {w : Word p21.T // IsLinExt _ w} ≠ 6 := by rw [natCard_linExt]; decide +kernel

/-- Mismatch control on the direction of `Lin(P)`: the reversed condition `w_i < w_j → j < i`
(linear extensions of the dual poset) has the same size, 3, for the 2+1 poset but is a different
set of words, and the instrument sees the difference. -/
example : (univ : Finset (Word p21.T)).filter (IsLinExt _) ≠
    (univ : Finset (Word p21.T)).filter (fun w => ∀ i j, w i < w j → j < i) := by decide +kernel

/-! ### `B_P` (Theorem S(a) count `|B_P| = e_C(P)`), on the 2+1 poset -/


-- `Lin = {012, 021, 201}`. First blocks: `012 ↦ {0,1}`, `021 ↦ {0,2,1}`, `201 ↦ {2}`.
-- Base point `0`: `B_P = {012, 021}`; base point `2`: `B_P = {021, 201}`. Both have `e_C = 2`.
example : ((univ : Finset (Word p21.T)).filter (InB (toT p21 0))).card = 2 := by decide +kernel
example : ((univ : Finset (Word p21.T)).filter (InB (toT p21 2))).card = 2 := by decide +kernel

/-! ### `classRot`, `fixedClassSum`, `sgnC` on the 3-antichain with `g = (0 1 2)` -/

/-- `g : 0 ↦ 1 ↦ 2 ↦ 0`. -/
def g3 : anti3.T ≃o anti3.T := mkAut anti3 (finRotate 3) (by decide)

/-- The transposition `(1 2)`. -/
def t12 : anti3.T ≃o anti3.T := mkAut anti3 (Equiv.swap 1 2) (by decide)

def w012 : Word anti3.T := mkWord anti3 (Equiv.refl _)
def w021 : Word anti3.T := mkWord anti3 (Equiv.swap 1 2)

/-- `g (w_i) = w_{i+1}` for `w = 012`: the note's `r_g(C) = 1` (`(gw)_i = g(w_i) = w_{i+r}`). -/
theorem classRot_g3_012 : classRot g3 (coset w012) = 1 :=
  classRot_eq_of (by decide +kernel) (by decide +kernel)

/-- For `w = 021`: `g(0) = 1 = w_2`, so `r = 2`. -/
theorem classRot_g3_021 : classRot g3 (coset w021) = 2 :=
  classRot_eq_of (by decide +kernel) (by decide +kernel)

/-- Mismatch control: the opposite rotation convention `(gw)_i = w_{i-r}` would give `2` for
the class of `012`; the definition gives `1`. -/
example : classRot g3 (coset w012) ≠ 2 := by rw [classRot_g3_012]; decide

/-- The `g3`-fixed classes are exactly the two classes, with rotations `1` and `2`; so
`∑_{gC=C} ζ^{r_g(C)} = ζ + ζ²` (`character_table.tsv`, `n3_000`, `(1 2 3)`: `1^1,2^1`). -/
theorem fixedClassSum_g3 (ζ : ℂ) : fixedClassSum ζ g3 = ζ + ζ ^ 2 := by
  rw [fixedClassSum_eq]
  have hset : ((univ.filter (IsLinExt anti3.T)).image coset).filter
      (fun C => C.image (fun w => w.trans g3.toEquiv) = C) = {coset w012, coset w021} := by
    decide +kernel
  have hne : coset w012 ≠ coset w021 := by decide +kernel
  rw [hset, sum_pair hne, classRot_g3_012, classRot_g3_021, pow_one]

/-- With `ζ` a primitive cube root of unity the Lie side is `-1`, as in the table
(`lhs = rhs = -1`). -/
theorem fixedClassSum_g3_prim {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : fixedClassSum ζ g3 = -1 := by
  rw [fixedClassSum_g3]
  have h := hζ.geom_sum_eq_zero (by norm_num)
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

theorem sgnC_g3 : sgnC g3 = 1 := by
  have h : Equiv.Perm.sign g3.toEquiv = 1 := by decide +kernel
  simp [sgnC, h]

/-- `(1 2)` fixes no class (`character_table.tsv`, `n3_000`, `(2 3)`: 0 fixed classes). -/
theorem fixedClassSum_t12 (ζ : ℂ) : fixedClassSum ζ t12 = 0 := by
  rw [fixedClassSum_eq]
  have hset : ((univ.filter (IsLinExt anti3.T)).image coset).filter
      (fun C => C.image (fun w => w.trans t12.toEquiv) = C) = ∅ := by
    decide +kernel
  rw [hset, sum_empty]

theorem sgnC_t12 : sgnC t12 = -1 := by
  have h : Equiv.Perm.sign t12.toEquiv = -1 := by decide +kernel
  simp [sgnC, h]

end Test

/-! ### The `ζ` convention: `w e_ζ` is a `ζ`-eigenvector of rotation -/

section Eigen

variable {α : Type*} [Fintype α] [DecidableEq α]

-- `finRotate_pow_apply`, `rot_rot`, `rot_zero`, `rot_card` and `wEζ_rot` are in
-- `PosetJKS/Bridge.lean`.

/-- The trace convention behind `trace_PLie` and `fixedClassSum`: if `g w = w γ^r` (the relation
that defines `classRot`), then `g · (w e_ζ) = ζ^r (w e_ζ)`, so the class contributes `ζ^r`, not
`ζ^{-r}`. -/
theorem relabel_wEζ_of_rot [PartialOrder α] {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1) (g : Equiv.Perm α)
    (w : Word α) (r : ℕ) (h : w.trans g = rot w r) :
    relabel g (wEζ ζ w) = ζ ^ r • wEζ ζ w := by
  rw [relabel_wEζ, h, wEζ_rot hζ]

end Eigen

/-! ### Order-preserving partitions: a certified decision procedure for `IsOrderPreserving` -/

section OPDecide

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] [DecidableRel (α := α) (· ≤ ·)]

/-- One step of `P/π` for `π = ker f`, as a Boolean: `a ≤ b` or `f a = f b`. -/
def opRelB {β : Type*} [DecidableEq β] (f : α → β) (a b : α) : Bool :=
  decide (a ≤ b) || decide (f a = f b)

/-- One squaring of a relation: `x r y` or `x r z r y`. -/
def sqB (r : α → α → Bool) (x y : α) : Bool :=
  r x y || decide (∃ z, r x z = true ∧ r z y = true)

/-- `k` squarings. -/
def closB (r : α → α → Bool) : ℕ → α → α → Bool
  | 0 => r
  | k + 1 => sqB (closB r k)

theorem closB_sound {R : α → α → Prop} {r : α → α → Bool}
    (hr : ∀ a b, r a b = true → Relation.ReflTransGen R a b) :
    ∀ k a b, closB r k a b = true → Relation.ReflTransGen R a b := by
  intro k
  induction k with
  | zero => exact hr
  | succ k ih =>
    intro a b h
    simp only [closB, sqB, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨z, h1, h2⟩
    · exact ih a b h
    · exact (ih a z h1).trans (ih z b h2)

theorem closB_complete {R : α → α → Prop} {r : α → α → Bool} {k : ℕ}
    (hsub : ∀ a b, R a b → closB r k a b = true)
    (hrefl : ∀ a, closB r k a a = true)
    (htrans : ∀ a b c, closB r k a b = true → closB r k b c = true → closB r k a c = true)
    {a b : α} (h : Relation.ReflTransGen R a b) : closB r k a b = true := by
  induction h with
  | refl => exact hrefl a
  | tail _ hbc ih => exact htrans _ _ _ ih (hsub _ _ hbc)

theorem closB_sub (r : α → α → Bool) (k : ℕ) (a b : α) (h : r a b = true) :
    closB r k a b = true := by
  induction k with
  | zero => exact h
  | succ k ih => simp [closB, sqB, ih]

variable {β : Type*} [DecidableEq β]

/-- The closure of `opRelB f` after `|α|` squarings. -/
def reachB (f : α → β) : α → α → Bool := closB (opRelB f) (Fintype.card α)

/-- Certificate: the computed relation is reflexive and transitive. -/
def closedB (f : α → β) : Bool :=
  decide (∀ a, reachB f a a = true) &&
    decide (∀ a b c, reachB f a b = true → reachB f b c = true → reachB f a c = true)

/-- Acyclicity of `P/ker f`: mutually reachable points have the same label. -/
def acycB (f : α → β) : Bool :=
  decide (∀ x y, reachB f x y = true → reachB f y x = true → f x = f y)

theorem opRelB_iff (f : α → β) (a b : α) : opRelB f a b = true ↔ opStep (Setoid.ker f) a b := by
  simp [opRelB, opStep, Setoid.ker_def]

theorem reachB_iff (f : α → β) (hc : closedB f = true) (x y : α) :
    reachB f x y = true ↔ Relation.ReflTransGen (opStep (Setoid.ker f)) x y := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq] at hc
  constructor
  · exact closB_sound (fun a b h => Relation.ReflTransGen.single ((opRelB_iff f a b).1 h)) _ x y
  · exact closB_complete (fun a b h => closB_sub _ _ a b ((opRelB_iff f a b).2 h)) hc.1 hc.2

/-- On a certified labelling, `IsOrderPreserving (ker f)` is exactly the Boolean test. -/
theorem isOrderPreserving_ker_iff (f : α → β) (hc : closedB f = true) :
    IsOrderPreserving (Setoid.ker f) ↔ acycB f = true := by
  simp only [IsOrderPreserving, acycB, decide_eq_true_eq, Setoid.ker_def, ← reachB_iff f hc]

/-- `f` is a restricted growth function: every label below `f i` occurs before position `i`.
These enumerate the set partitions of `Fin n` once each (by first occurrence). -/
def IsRGF {n : ℕ} (f : Fin n → Fin n) : Prop := ∀ i, ∀ k : Fin n, k < f i → ∃ j < i, f j = k

instance {n : ℕ} : DecidablePred (IsRGF (n := n)) := fun f =>
  inferInstanceAs (Decidable (∀ i, ∀ k : Fin n, k < f i → ∃ j < i, f j = k))

end OPDecide

namespace Test

/-- The labellings of `P` that are restricted growth functions: one per set partition. -/
def rgfs {n : ℕ} (P : FinPoset n) : Finset (P.T → Fin n) :=
  (univ : Finset (Fin n → Fin n)).filter IsRGF

/-- The number of set partitions (Bell numbers 5 and 15): the enumeration is complete. -/
example : (rgfs anti3).card = 5 := by decide +kernel
example : (rgfs anti4).card = 15 := by decide +kernel

/-- The certificate holds for every partition, so on these lists `acycB` *is*
`IsOrderPreserving` (by `isOrderPreserving_ker_iff`). -/
example : ∀ f ∈ rgfs chain3, closedB f = true := by decide +kernel
example : ∀ f ∈ rgfs p21, closedB f = true := by decide +kernel
example : ∀ f ∈ rgfs anti3, closedB f = true := by decide +kernel

/-- `|OP(P)|` = number of order-preserving set partitions: 4, 5, 5 (`character_table.tsv`). -/
example : ((rgfs chain3).filter (fun f => acycB f = true)).card = 4 := by decide +kernel
example : ((rgfs p21).filter (fun f => acycB f = true)).card = 5 := by decide +kernel
example : ((rgfs anti3).filter (fun f => acycB f = true)).card = 5 := by decide +kernel

-- `n = 4`: 15 (antichain), 8 (chain), 14 (N), 14 (two 2-chains). Evaluated by the compiler.
#guard ((rgfs anti4).filter (fun f => closedB f && acycB f)).card = 15
#guard ((rgfs chain4).filter (fun f => closedB f && acycB f)).card = 8
#guard ((rgfs pN).filter (fun f => closedB f && acycB f)).card = 14
#guard ((rgfs twoChains).filter (fun f => closedB f && acycB f)).card = 14
#guard ∀ f ∈ rgfs pN, closedB f = true

/-- A labelling of the points of `P` (fixes the carrier type to `P.T`). -/
def lab {n : ℕ} (P : FinPoset n) (f : Fin n → Fin n) : P.T → Fin n := f

/-- Hand-proved positive control on the 3-chain `0 < 1 < 2`: the partition `{0,1} | {2}` is
order-preserving (an interval partition). -/
theorem op_chain3_01_2 : IsOrderPreserving (Setoid.ker (lab chain3 ![0, 0, 1])) := by
  rw [isOrderPreserving_ker_iff _ (by decide +kernel)]
  decide +kernel

/-- Mismatch control: `{0,2} | {1}` on the 3-chain is *not* order-preserving (`0 < 1 < 2 ~ 0`
is a directed cycle through two blocks). The definition rejects it; on the 3-antichain the same
partition is accepted. -/
theorem not_op_chain3_02_1 : ¬ IsOrderPreserving (Setoid.ker (lab chain3 ![0, 1, 0])) := by
  rw [isOrderPreserving_ker_iff _ (by decide +kernel)]
  decide +kernel

theorem op_anti3_02_1 : IsOrderPreserving (Setoid.ker (lab anti3 ![0, 1, 0])) := by
  rw [isOrderPreserving_ker_iff _ (by decide +kernel)]
  decide +kernel

/-- Instrument control. A type ascription does not change the inferred type: the labelling
`(![0, 1, 0] : anti3.T → Fin 3)` still has type `Fin 3 → Fin 3`, so its kernel is a setoid on
`Fin 3` and `IsOrderPreserving` is then taken for `Fin`'s *linear* order. In a first draft of
this file the antichain control `op_anti3_02_1` failed for exactly this reason; the labellings
above go through `lab`, which fixes the carrier. This records the wrong reading. -/
example : ¬ IsOrderPreserving (Setoid.ker (![0, 1, 0] : Fin 3 → Fin 3)) := by
  rw [isOrderPreserving_ker_iff _ (by decide +kernel)]
  decide +kernel

/-! ### `μ(OP(P)^g)`: mirror computation (not the Lean definition) -/

/-- Refinement `ker f ≤ ker f'` (Mathlib's order on `Setoid`: `Setoid.le_def`). -/
def refinesB {n : ℕ} {P : FinPoset n} (f f' : P.T → Fin n) : Bool :=
  decide (∀ x y, f x = f y → f' x = f' y)

/-- `ker f` is `g`-stable. -/
def fixedB {n : ℕ} {P : FinPoset n} (g : P.T → P.T) (f : P.T → Fin n) : Bool :=
  decide (∀ x y, f x = f y ↔ f (g x) = f (g y))

/-- Mirror of `μ(0̂, x)` on a list `L` of labellings ordered by refinement, by the defining
recursion `μ(0̂,x) = -∑_{0̂ ≤ y < x} μ(0̂,y)` (fuel bounds the chain length). -/
def muMirror {n : ℕ} {P : FinPoset n} (L : Multiset (P.T → Fin n)) (bot : P.T → Fin n) :
    ℕ → (P.T → Fin n) → ℤ
  | 0, _ => 0
  | k + 1, x =>
    if refinesB x bot then 1 else
      -((L.filter fun y => refinesB bot y && refinesB y x && !refinesB x y).map
          (muMirror L bot k)).sum

/-- `μ(OP(P)^g)` by the mirror, with `0̂ = ` discrete and `1̂ = ` one block. -/
def muFixedMirror {n : ℕ} (P : FinPoset (n + 1)) (g : P.T → P.T) : ℤ :=
  let L := ((rgfs P).filter fun f => closedB f && acycB f && fixedB g f).val
  muMirror L (fun x => (x : Fin (n + 1))) (n + 2) (fun _ => 0)

-- `g = id`: `μ = (-1)^{n-3} e_C(P)`: 2, 1, 2, -6, -1, -5, -5.
#guard muFixedMirror anti3 id = 2
#guard muFixedMirror chain3 id = 1
#guard muFixedMirror p21 id = 2
#guard muFixedMirror anti4 id = -6
#guard muFixedMirror chain4 id = -1
#guard muFixedMirror pN id = -5
#guard muFixedMirror twoChains id = -5
-- `g ≠ id` (table `mu_OP_g`): 3-antichain `(1 2 3)`: -1, `(2 3)`: 0; 4-antichain
-- `(1 2)(3 4)`: 2, `(1 2 3 4)`: 0; two 2-chains `(1 2)(3 4)`: 1.
#guard muFixedMirror anti3 (finRotate 3) = -1
#guard muFixedMirror anti3 (Equiv.swap (1 : Fin 3) 2) = 0
#guard muFixedMirror anti4 ⇑(Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) = 2
#guard muFixedMirror anti4 (finRotate 4) = 0
#guard muFixedMirror twoChains ⇑(Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) = 1
-- Mismatch control: with the order of the 3-chain the mirror gives `1`, not the antichain's `2`.
#guard muFixedMirror chain3 id ≠ 2

end Test

/-! ### `muFixed` itself, on the 2-chain -/

namespace Test

theorem setoid_fin2 (s : Setoid chain2.T) : s = ⊥ ∨ s = ⊤ := by
  by_cases h : s (0 : Fin 2) (1 : Fin 2)
  · right
    ext x y
    simp only [Setoid.top_def, Pi.top_apply, Prop.top_eq_true, iff_true]
    have h' : s (1 : Fin 2) (0 : Fin 2) := s.symm h
    change Fin 2 at x y
    fin_cases x <;> fin_cases y
    · exact s.refl _
    · exact h
    · exact h'
    · exact s.refl _
  · left
    ext x y
    rw [Setoid.bot_def]
    constructor
    · intro hxy
      change Fin 2 at x y
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd hxy h
      · exact absurd (s.symm hxy) h
      · rfl
    · rintro rfl; exact s.refl _

/-- `μ(OP(Q)) = -1` for the 2-chain `Q` (note, Lemma `lem:small`; table `n2_001`: `-1`). -/
theorem muFixed_chain2 : muFixed (OrderIso.refl chain2.T) = -1 := by
  classical
  have hne := OPFixed.bot_ne_top (OrderIso.refl chain2.T) (by decide)
  have hIco : Ico (OPFixed.bot (OrderIso.refl chain2.T)) (OPFixed.top _) =
      {OPFixed.bot _} := by
    ext x
    simp only [mem_Ico, mem_singleton]
    constructor
    · rintro ⟨-, hlt⟩
      rcases setoid_fin2 x.1 with h | h
      · exact Subtype.ext h
      · exact absurd (Subtype.ext h) hlt.ne
    · rintro rfl
      exact ⟨le_rfl, lt_of_le_of_ne (fun _ _ _ => trivial) hne⟩
  unfold muFixed
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne, hIco, sum_singleton, IncidenceAlgebra.mu_self]

open Classical in
/-- Mismatch control: with the arguments swapped, Mathlib's `μ(1̂, 0̂)` is `0`, not `-1`. -/
example : IncidenceAlgebra.mu ℤ (OPFixed.top (OrderIso.refl chain2.T)) (OPFixed.bot _) = 0 := by
  classical
  have hne := OPFixed.bot_ne_top (OrderIso.refl chain2.T) (by decide)
  apply IncidenceAlgebra.apply_eq_zero_of_not_le
  intro hle
  exact hne (le_antisymm (fun _ _ _ => trivial) hle)

/-! ### `M̃(P, g)` (`Mt`) and Theorem A, against `character_table.tsv` -/

/-- `M̃(Q, 1) = (-1)^{n+1} sgn(1) μ(OP(Q)) = 1` for the 2-chain, from the definitions
(table `n2_001`, `id`: `mu_OP_g = -1`, `e_C = 1`, `lhs = 1`). -/
theorem Mt_chain2 : Mt (OrderIso.refl chain2.T) = 1 := by
  have hs : Equiv.Perm.sign (OrderIso.refl chain2.T).toEquiv = 1 := Equiv.Perm.sign_one
  rw [Mt, muFixed_chain2, hs, card_T]
  norm_num

/-- Mismatch control: the note's exponent `n - 3` taken in `ℕ` (`2 - 3 = 0`) would give the
wrong sign at `n = 2`; `Mt` uses `n + 1`, which has the parity of `n - 3`. -/
example : (-1 : ℤ) ^ (Fintype.card chain2.T - 3) * muFixed (OrderIso.refl chain2.T) = -1 := by
  rw [muFixed_chain2, card_T]
  norm_num

/-- Theorem A on the 3-antichain: `μ(OP(Q)) = (-1)^2 e_C(Q) = 2` (table `n3_000`, `id`:
`mu_OP_g = 2`, `e_C = 2`). -/
example : muFixed (OrderIso.refl anti3.T) = 2 := by
  have he : eC anti3.T = 2 := by rw [eC_eq]; decide +kernel
  rw [show OrderIso.refl anti3.T = 1 from rfl, mu_OP_eq (by rw [card_T]; norm_num), card_T, he]
  norm_num

end Test

/-! ### The chain complex: `∂ ∘ ∂ = 0`, and `∂_0` is the augmentation -/

section Boundary

variable (L : Type*) [PartialOrder L]

theorem face_face {m : ℕ} (c : Fin (m + 2) ↪o L) (i : Fin (m + 2)) (j : Fin (m + 1)) :
    face (face c i) j = face (face c (i.succAbove j)) (j.predAbove i) := by
  ext k
  simp only [face, RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_succAbove_succAbove_predAbove]

/-- `∂_m ∘ ∂_{m+1} = 0`: `bd` is a differential, so `redHom` is homology. -/
theorem bd_comp_bd (m : ℕ) : bd L m ∘ₗ bd L (m + 1) = 0 := by
  refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
  change bd L m (bd L (m + 1) (Finsupp.single c 1)) = 0
  unfold bd
  erw [Finsupp.linearCombination_single]
  rw [one_smul, map_sum]
  simp only [map_smul, Chains.single]
  erw [Finset.sum_congr rfl fun i _ => congrArg _ (Finsupp.linearCombination_single ℂ _ _)]
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · rintro ⟨i, j⟩ -
    simp only
    rw [← face_face]
    simp only [one_mul, ← pow_add]
    rw [Fin.neg_one_pow_succAbove_add_predAbove, neg_smul, add_neg_cancel]
  · rintro ⟨i, j⟩ - -
    exact fun h => Fin.succAbove_ne i j (congrArg Prod.fst h)
  · rintro ⟨i, j⟩ -
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

/-- The empty chain (the `(-1)`-dimensional face). -/
def emptyChain : Fin 0 ↪o L := ⟨⟨Fin.elim0, fun a => a.elim0⟩, fun {a} => a.elim0⟩

/-- `∂_0` sends every vertex to the empty chain: it is the augmentation `ε`, so
`redHom L 0 = ker ε / im ∂_1` is reduced `H̃_0`. -/
theorem bd_zero_single (c : Fin 1 ↪o L) :
    bd L 0 (Chains.single L c) = Chains.single L (emptyChain L) := by
  unfold bd Chains.single
  erw [Finsupp.linearCombination_single]
  rw [one_smul, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  congr 1
  ext i
  exact i.elim0

end Boundary

/-! ### Counterexamples at `n = 0` (the empty poset `Fin 0`) -/

namespace Test

theorem wEζ_fin0 (ζ : ℂ) (w : Word (Fin 0)) : wEζ ζ w = 0 := by
  simp [wEζ]

theorem PLie_fin0 (ζ : ℂ) : PLie (Fin 0) ζ = ⊥ := by
  rw [PLie, Submodule.span_eq_bot]
  rintro x ⟨w, -, rfl⟩
  exact wEζ_fin0 ζ w

/-- The unique word of the empty poset. -/
def w0 : Word (Fin 0) := finCongr (by simp)

theorem R_fin0 : R (Fin 0) = ⊥ := by
  rw [R, Submodule.span_eq_bot]
  rintro x ⟨S, -, -, hne, -⟩
  exact absurd hne (by simp [Finset.eq_empty_of_isEmpty S])

theorem wd_w0_mem_W : wd w0 ∈ W (Fin 0) :=
  Submodule.subset_span ⟨w0, fun i => i.elim0, rfl⟩

theorem MP_fin0_ne : (RinW (Fin 0)).mkQ ⟨wd w0, wd_w0_mem_W⟩ ≠ 0 := by
  rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, RinW, R_fin0,
    Submodule.mem_comap, Submodule.mem_bot]
  simp only [Submodule.subtype_apply]
  unfold wd
  exact Finsupp.single_ne_zero.2 one_ne_zero

/-- **`corPsi_bijective` needs `h0 : 0 < n`: without it, it fails at `n = 0`.** `ζ = 0` is a
primitive `0`-th root of unity in Mathlib, `PLie(∅) = 0` (the sum defining `w e_ζ` is empty), but
`ℂ[Lin ∅]/R_∅ = ℂ`. -/
theorem corPsi_bijective_false :
    IsPrimitiveRoot (0 : ℂ) (Fintype.card (Fin 0)) ∧ ¬ Function.Bijective (psi (Fin 0) 0) := by
  refine ⟨by simpa using IsPrimitiveRoot.zero, fun hb => MP_fin0_ne ?_⟩
  obtain ⟨y, hy⟩ := hb.2 ((RinW (Fin 0)).mkQ ⟨wd w0, wd_w0_mem_W⟩)
  have : y = 0 := by
    have hy0 : (y : Alg (Fin 0)) ∈ (⊥ : Submodule ℂ (Alg (Fin 0))) := PLie_fin0 0 ▸ y.2
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hy0)
  rw [← hy, this, map_zero]

theorem cyc_fin0 : cyc (Fin 0) = {∅} := by
  rw [cyc_eq]
  decide

/-- **`trace_PLie` needs `h0 : 0 < n`: without it, it fails at `n = 0`.** The empty word's
coset `(range 0).image _` is empty, so `Cyc(∅) = {∅}` and `fixedClassSum = ζ^0 = 1`, while
`PLie(∅) = 0` has trace `0`. -/
theorem trace_PLie_false (ζ : ℂ) :
    LinearMap.trace ℂ (PLie (Fin 0) ζ) (actPLie ζ (OrderIso.refl _)) ≠
      fixedClassSum ζ (OrderIso.refl (Fin 0)) := by
  have hsub : Subsingleton (PLie (Fin 0) ζ) := Submodule.subsingleton_iff_eq_bot.2 (PLie_fin0 ζ)
  have h0 : actPLie ζ (OrderIso.refl (Fin 0)) = 0 := Subsingleton.elim _ _
  have hfix : fixedClassSum ζ (OrderIso.refl (Fin 0)) = 1 := by
    rw [fixedClassSum, cyc_fin0]
    have hr : classRot (OrderIso.refl (Fin 0)) ∅ = 0 := by
      unfold classRot
      rw [dif_neg]
      rintro ⟨r, -, w, hw, -⟩
      simp at hw
    simp [hr]
  rw [h0, map_zero, hfix]
  exact zero_ne_one

end Test

/-! ### Chain tools: a two-point antichain has `H̃_0 ≠ 0`

Positive control for `subsingleton_redHom_iff`: on the antichain `Unit ⊕ Unit`, the difference
of the two points is a `0`-cycle, and there are no 2-element chains, so it is not a boundary.
(For the empty poset `subsingleton_redHom_of_isEmpty` gives vanishing in every degree.) -/

namespace Test

instance : IsEmpty (Fin 2 ↪o Unit ⊕ Unit) := ⟨fun c => by
  have h : c 0 < c 1 := c.lt_iff_lt.2 (by decide)
  rcases h0 : c 0 with u | u <;> rcases h1 : c 1 with v | v <;> rw [h0, h1] at h
  · exact lt_irrefl u (Subsingleton.elim u v ▸ Sum.inl_lt_inl_iff.1 h)
  · exact Sum.not_inl_lt_inr h
  · exact Sum.not_inr_lt_inl h
  · exact lt_irrefl u (Subsingleton.elim u v ▸ Sum.inr_lt_inr_iff.1 h)⟩

theorem redHom_antichain2_ne : ¬ Subsingleton (redHom (Unit ⊕ Unit) 0) := by
  rw [subsingleton_redHom_iff]
  intro h
  let z : Chains (Unit ⊕ Unit) 1 :=
    Chains.single _ (ptChain (Sum.inl ())) - Chains.single _ (ptChain (Sum.inr ()))
  have hz : bd _ 0 z = 0 := by
    simp only [z, map_sub, bd_single_ptChain, sub_self]
  obtain ⟨b, hb⟩ := h z hz
  have hb0 : b = 0 := Subsingleton.elim (α := (Fin 2 ↪o Unit ⊕ Unit) →₀ ℂ) b 0
  rw [hb0, map_zero] at hb
  have hne : ptChain (Sum.inl () : Unit ⊕ Unit) ≠ ptChain (Sum.inr ()) :=
    fun he => Sum.inl_ne_inr (ptChain_injective he)
  have := congrArg (fun f : (Fin 1 ↪o Unit ⊕ Unit) →₀ ℂ => f (ptChain (Sum.inl ()))) hb
  change (0 : (Fin 1 ↪o Unit ⊕ Unit) →₀ ℂ) (ptChain (Sum.inl ())) =
    (Finsupp.single (ptChain (Sum.inl ())) (1 : ℂ) - Finsupp.single (ptChain (Sum.inr ())) 1 :
      (Fin 1 ↪o Unit ⊕ Unit) →₀ ℂ) (ptChain (Sum.inl ())) at this
  erw [Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg hne.symm] at this
  norm_num at this


/-! Controls for Lemma K (`ConeRetract.lean`, Route C slice S2). -/

/-- The two-point antichain fails the hypotheses of Lemma K directly: `p x ≤ x` forces
`p x = x`, and then `p x ≤ t` forces `x = t` for both points. -/
theorem isEmpty_coneRetraction_antichain2 : IsEmpty (ConeRetraction (Unit ⊕ Unit)) := by
  refine ⟨fun K => ?_⟩
  have hanti : ∀ a b : Unit ⊕ Unit, a ≤ b → a = b := by
    rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h <;> simp_all
  have ht : ∀ x : Unit ⊕ Unit, x = K.t := fun x => by
    have h1 := hanti _ _ (K.le_self x)
    exact h1 ▸ hanti _ _ (K.le_t x)
  exact Sum.inl_ne_inr ((ht (Sum.inl ())).trans (ht (Sum.inr ())).symm)

/-- The same failure, forced by Lemma K: a cone retraction would make `H̃_0 = 0`, but
`H̃_0 ≠ 0` (`redHom_antichain2_ne`). -/
theorem isEmpty_coneRetraction_antichain2' : IsEmpty (ConeRetraction (Unit ⊕ Unit)) :=
  ⟨fun K => redHom_antichain2_ne (K.exact_of_retract 0)⟩

/-- A cone retraction that is not the identity: on `V = {⊥ < a, ⊥ < b}` (the cone over the
two-point antichain), `t = ⊥` and `p ≡ ⊥`. -/
def vRetraction : ConeRetraction (WithBot (Unit ⊕ Unit)) where
  t := ⊥
  p := fun _ => ⊥
  monotone := fun _ _ _ => le_rfl
  le_self := fun _ => bot_le
  le_t := fun _ => le_rfl
  eq_of_le := fun _ hx => (le_bot_iff.1 hx).symm

/-- Lemma K on `V`: adding a cone point kills the `H̃_0` of the antichain. -/
theorem redHom_V_subsingleton (d : ℕ) : Subsingleton (redHom (WithBot (Unit ⊕ Unit)) d) :=
  vRetraction.exact_of_retract d

/-! Control for Proposition C (`Complement.lean`, Route C slice S3). -/

/-- On the two-point antichain with `A = {inl}`, every hypothesis of `propC_zero` holds except
the nonemptiness of `(inl, ·)`: `A` consists of minimal elements and `L ∖ A = {inr}` is a cone.
The conclusion fails (`H̃_0 ≠ 0`, `redHom_antichain2_ne`), so that hypothesis is needed. -/
theorem propC_zero_control :
    (∀ x ∈ ({Sum.inl ()} : Set (Unit ⊕ Unit)), IsMin x) ∧
      Subsingleton (redHom {x : Unit ⊕ Unit // x ∉ ({Sum.inl ()} : Set (Unit ⊕ Unit))} 0) ∧
      IsEmpty (Upper (Sum.inl () : Unit ⊕ Unit)) ∧ ¬ Subsingleton (redHom (Unit ⊕ Unit) 0) := by
  have hanti : ∀ a b : Unit ⊕ Unit, a ≤ b → a = b := by
    rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h <;> simp_all
  refine ⟨fun x _ y hy => (hanti _ _ hy).ge, ?_, ⟨fun y => y.2.ne (hanti _ _ y.2.le)⟩,
    redHom_antichain2_ne⟩
  have hQ : ∀ x : {x : Unit ⊕ Unit // x ∉ ({Sum.inl ()} : Set (Unit ⊕ Unit))},
      x = ⟨Sum.inr (), by simp⟩ := by
    rintro ⟨(⟨⟩ | ⟨⟩), hx⟩
    · exact absurd rfl hx
    · rfl
  let K : ConeRetraction {x : Unit ⊕ Unit // x ∉ ({Sum.inl ()} : Set (Unit ⊕ Unit))} :=
    { t := ⟨Sum.inr (), by simp⟩
      p := id
      monotone := monotone_id
      le_self := fun _ => le_rfl
      le_t := fun x => (hQ x).le
      eq_of_le := fun _ _ => rfl }
  exact K.exact_of_retract 0

end Test

end PosetJKS
