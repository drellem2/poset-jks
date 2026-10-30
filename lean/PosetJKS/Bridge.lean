import PosetJKS.Words

/-!
# From words `Fin n ≃ α` to lists

The theorems of `Milestone.lean` are stated for words `w : Fin n ≃ α` and the free vector space
`Alg α` on them. Their proofs (`Words.lean`) work with lists. This file transfers between the two:

* `toL w = [w 0, …, w (n-1)]`, injective, with image the lists that are words on `univ`;
* `toLmap : Alg α → (List α →₀ ℂ)`, the induced injective linear map; it sends `shuffle S u v`
  to `L.shq` and `Sh α` into `L.ShL univ`;
* `rot`, `prefixSet`, `coset`, `IsLinExt`, `IsUnionOfComponents` in terms of lists;
* rotation identities `rot_rot`, `rot_card`, `wEζ_rot` (`(w γ^r) e_ζ = ζ^r (w e_ζ)`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Rotations -/

section Rot

variable {α : Type*} [Fintype α] [DecidableEq α]

open Fin.NatCast in
theorem finRotate_pow_apply (m j : ℕ) (i : Fin (m + 1)) :
    (finRotate (m + 1) ^ j) i = i + (j : Fin (m + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_succ_apply, Nat.cast_succ, add_assoc]

theorem rot_rot (w : Word α) (r j : ℕ) : rot (rot w r) j = rot w (r + j) := by
  ext i
  simp only [rot, Equiv.trans_apply, pow_add, Equiv.Perm.mul_apply]

theorem rot_zero (w : Word α) : rot w 0 = w := by ext; simp [rot]

open Fin.NatCast in
theorem finRotate_pow_self (k : ℕ) : finRotate k ^ k = 1 := by
  cases k with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    ext i
    rw [finRotate_pow_apply, Fin.natCast_self, add_zero, Equiv.Perm.one_apply]

theorem rot_card (w : Word α) : rot w (Fintype.card α) = w := by
  ext i
  simp [rot, finRotate_pow_self]

/-- `(w γ) e_ζ = ζ (w e_ζ)` when `ζ^n = 1`: the note's `γ e_ζ = ζ e_ζ`. -/
theorem wEζ_rot_one {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1) (w : Word α) :
    wEζ ζ (rot w 1) = ζ • wEζ ζ w := by
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · simp [wEζ, h0]
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hζ
    exact zero_ne_one hζ
  set F : ℕ → Alg α := fun j => (((Fintype.card α : ℂ))⁻¹ * (ζ ^ j)⁻¹) • wd (rot w j) with hF
  have hterm : ∀ j, (((Fintype.card α : ℂ))⁻¹ * (ζ ^ j)⁻¹) • wd (rot (rot w 1) j) =
      ζ • F (j + 1) := by
    intro j
    rw [hF, rot_rot, add_comm 1 j, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hshift : ∑ j ∈ range (Fintype.card α), F (j + 1) =
      ∑ j ∈ range (Fintype.card α), F j := by
    have h1 := sum_range_succ' F (Fintype.card α)
    have h2 := sum_range_succ F (Fintype.card α)
    have hFn : F (Fintype.card α) = F 0 := by
      simp only [hF, hζ, rot_card, rot_zero, pow_zero]
    rw [h2, hFn] at h1
    exact (add_right_cancel h1).symm
  simp only [wEζ]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.smul_sum, hshift]

theorem wEζ_rot {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1) (w : Word α) (r : ℕ) :
    wEζ ζ (rot w r) = ζ ^ r • wEζ ζ w := by
  induction r with
  | zero => simp [rot_zero]
  | succ r ih =>
    rw [← rot_rot, wEζ_rot_one hζ, ih, smul_smul, pow_succ, mul_comm]


lemma val_finRotate_pow (n j : ℕ) (i : Fin n) : ((finRotate n ^ j) i : ℕ) = (i + j) % n := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [finRotate_pow_apply, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

end Rot

/-! ### Words as lists -/

section Lists

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! `Alg α` is a `def`, so the `Finsupp` evaluation lemmas are restated for it. -/

noncomputable instance : Module.Finite ℂ (Alg α) :=
  inferInstanceAs (Module.Finite ℂ (Word α →₀ ℂ))

lemma alg_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Alg α) (z : Word α) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := Finsupp.finset_sum_apply _ _ _

lemma alg_smul_apply (c : ℂ) (X : Alg α) (z : Word α) : (c • X) z = c * X z := rfl

lemma alg_add_apply (X Y : Alg α) (z : Word α) : (X + Y) z = X z + Y z := rfl

lemma alg_sub_apply (X Y : Alg α) (z : Word α) : (X - Y) z = X z - Y z := rfl

lemma alg_zero_apply (z : Word α) : (0 : Alg α) z = 0 := rfl

lemma alg_ext {X Y : Alg α} (h : ∀ z, X z = Y z) : X = Y := Finsupp.ext h

lemma wd_apply (w z : Word α) : wd w z = if w = z then 1 else 0 := Finsupp.single_apply

/-- The list of letters of a word. -/
def toL (w : Word α) : List α := List.ofFn w

lemma toL_injective : Function.Injective (toL (α := α)) := fun w w' h =>
  Equiv.ext fun i => congrFun (List.ofFn_inj.1 h) i

lemma length_toL (w : Word α) : (toL w).length = Fintype.card α := List.length_ofFn

lemma isWordOn_toL (w : Word α) : IsWordOn univ (toL w) := by
  refine ⟨List.nodup_ofFn_ofInjective w.injective, ?_⟩
  ext b
  simp only [toL, List.mem_toFinset, List.mem_ofFn, mem_univ, iff_true]
  exact w.surjective b

lemma exists_toL {l : List α} (h : IsWordOn univ l) : ∃ w : Word α, toL w = l := by
  have hlen : l.length = Fintype.card α := by
    rw [← List.toFinset_card_of_nodup h.1, h.2, Finset.card_univ]
  let f : Fin (Fintype.card α) → α := fun i => l[i.1]'(by rw [hlen]; exact i.2)
  have hinj : Function.Injective f := fun i j hij =>
    Fin.ext ((List.Nodup.getElem_inj_iff h.1).1 hij)
  have hb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp⟩
  refine ⟨Equiv.ofBijective f hb, List.ext_getElem (by simp [toL, hlen]) fun i h1 h2 => ?_⟩
  simp [toL, f, List.getElem_ofFn]

lemma toL_rot (w : Word α) (j : ℕ) : toL (rot w j) = (toL w).rotate j := by
  apply List.ext_getElem (by simp [toL])
  intro i h1 h2
  rw [List.getElem_rotate]
  simp only [toL, List.getElem_ofFn, rot, Equiv.trans_apply, List.length_ofFn]
  congr 1
  ext
  rw [val_finRotate_pow]

lemma prefixSet_eq (w : Word α) (k : ℕ) : prefixSet w k = ((toL w).take k).toFinset := by
  ext b
  simp only [prefixSet, mem_image, mem_filter, mem_univ, true_and, List.mem_toFinset,
    List.mem_take_iff_getElem, toL, List.getElem_ofFn, List.length_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, lt_min hi i.2, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨_, (lt_min_iff.1 hj).1, rfl⟩

lemma restrict_eq (w : Word α) (S : Finset α) :
    restrict w S = (toL w).filter (fun b => decide (b ∈ S)) := rfl

lemma restrict_compl (w : Word α) (S : Finset α) :
    restrict w Sᶜ = (toL w).filter (fun b => !decide (b ∈ S)) := by
  simp only [restrict_eq, Finset.mem_compl, decide_not]

lemma isWordOn_univ_append {S : Finset α} {u v : List α} (hu : IsWordOn S u)
    (hv : IsWordOn Sᶜ v) : IsWordOn univ (u ++ v) := by
  refine ⟨List.nodup_append.2 ⟨hu.1, hv.1, fun a ha b hb hab => ?_⟩, ?_⟩
  · have h1 : a ∈ S := hu.2 ▸ List.mem_toFinset.2 ha
    have h2 : b ∈ Sᶜ := hv.2 ▸ List.mem_toFinset.2 hb
    exact Finset.mem_compl.1 h2 (hab ▸ h1)
  · rw [List.toFinset_append, hu.2, hv.2, Finset.union_compl]

/-! ### The linear map `ℂ[S_n] → ℂ[lists]` -/

/-- `toLmap`: `wd w ↦ [toL w]`, extended linearly. -/
noncomputable def toLmap : Alg α →ₗ[ℂ] (List α →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ toL

lemma toLmap_apply_toL (X : Alg α) (w : Word α) : toLmap X (toL w) = X w :=
  Finsupp.mapDomain_apply toL_injective X w

lemma toLmap_injective : Function.Injective (toLmap (α := α)) :=
  Finsupp.mapDomain_injective toL_injective

lemma toLmap_wd (w : Word α) : toLmap (wd w) = Finsupp.single (toL w) 1 :=
  Finsupp.mapDomain_single

lemma toLmap_support {X : Alg α} {l : List α} (h : toLmap X l ≠ 0) :
    ∃ w, toL w = l ∧ X w ≠ 0 := by
  by_cases hl : ∃ w, toL w = l
  · obtain ⟨w, rfl⟩ := hl
    exact ⟨w, rfl, by rwa [toLmap_apply_toL] at h⟩
  · exact absurd (Finsupp.mapDomain_notin_range X l (by rintro ⟨w, rfl⟩; exact hl ⟨w, rfl⟩)) h

lemma shuffle_apply (S : Finset α) (u v : List α) (z : Word α) :
    shuffle S u v z = if restrict z S = u ∧ restrict z Sᶜ = v then 1 else 0 := by
  unfold shuffle
  rw [alg_sum_apply]
  simp only [wd_apply]
  rw [Finset.sum_ite_eq']
  simp

lemma toLmap_shuffle {S : Finset α} {u v : List α} (hu : IsWordOn S u) (hv : IsWordOn Sᶜ v) :
    toLmap (shuffle S u v) = L.shq (fun b => decide (b ∈ S)) u v := by
  ext l
  by_cases hl : ∃ w, toL w = l
  · obtain ⟨w, rfl⟩ := hl
    rw [toLmap_apply_toL, shuffle_apply, L.shq_apply, restrict_eq, restrict_compl]
  · rw [show toLmap (shuffle S u v) l = 0 from Finsupp.mapDomain_notin_range (f := toL) _ l
      (by rintro ⟨w, rfl⟩; exact hl ⟨w, rfl⟩), L.shq_apply, if_neg]
    rintro ⟨h1, h2⟩
    have hp : l.Perm (u ++ v) := by
      rw [← h1, ← h2]; exact (List.filter_append_perm _ l).symm
    exact hl (exists_toL (L.isWordOn_perm hp.symm (isWordOn_univ_append hu hv)))

lemma map_Sh_le : (Sh α).map toLmap ≤ L.ShL (univ : Finset α) := by
  rw [Sh, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨S, u, v, hne, huniv, hu, hv, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, toLmap_shuffle hu hv]
  exact Submodule.subset_span ⟨S, u, v, Finset.subset_univ _, hne, huniv, hu,
    by rwa [← Finset.compl_eq_univ_sdiff], rfl⟩

/-! ### Spans of words -/

lemma support_of_mem_span {P : Word α → Prop} {X : Alg α}
    (hX : X ∈ Submodule.span ℂ {x | ∃ w, P w ∧ x = wd w}) {z : Word α} (hz : X z ≠ 0) : P z := by
  induction hX using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [wd_apply] at hz
    split_ifs at hz with h
    · exact h ▸ hw
    · exact absurd rfl hz
  | zero => exact absurd rfl hz
  | add x y _ _ hx hy =>
    by_cases h : x z = 0
    · refine hy ?_
      intro h'; apply hz; change x z + y z = 0; rw [h, h', add_zero]
    · exact hx h
  | smul c x _ hx =>
    refine hx ?_
    intro h'; apply hz; change c * x z = 0; rw [h', mul_zero]

/-- Words are linearly independent modulo `M` as soon as every combination of them lying in
`M` vanishes. -/
lemma linIndep_mkQ_wd {P : Word α → Prop} {M : Submodule ℂ (Alg α)}
    (h : ∀ X ∈ M, (∀ w, X w ≠ 0 → P w) → X = 0) :
    LinearIndependent ℂ (fun w : {w // P w} => M.mkQ (wd w.1)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set X : Alg α := ∑ j ∈ s, g j • wd j.1 with hX
  have hXM : X ∈ M := by
    rw [← Submodule.Quotient.mk_eq_zero M]
    have : M.mkQ X = 0 := by rw [hX, map_sum]; simpa only [map_smul] using hg
    exact this
  have hcoef : ∀ z : Word α, X z = ∑ j ∈ s, g j * (if j.1 = z then 1 else 0) := by
    intro z
    rw [hX, alg_sum_apply]
    simp only [alg_smul_apply, wd_apply]
  have hX0 := h X hXM fun z hz => by
    rw [hcoef] at hz
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    split_ifs at hj with hjz
    · exact hjz ▸ j.2
    · simp at hj
  have := hcoef i.1
  rw [hX0, alg_zero_apply, Finset.sum_eq_single i (fun j _ hji => by
    rw [if_neg (fun h => hji (Subtype.ext h)), mul_zero]) (fun h => absurd hi h)] at this
  simpa using this.symm

lemma finrank_span_wd (P : Word α → Prop) :
    Module.finrank ℂ (Submodule.span ℂ {x | ∃ w, P w ∧ x = wd w}) = Nat.card {w // P w} := by
  classical
  have hli : LinearIndependent ℂ (fun w : {w // P w} => wd w.1) := by
    refine LinearIndependent.of_comp (⊥ : Submodule ℂ (Alg α)).mkQ ?_
    refine linIndep_mkQ_wd fun X hX _ => ?_
    exact (Submodule.mem_bot ℂ).1 hX
  have hset : {x | ∃ w, P w ∧ x = wd w} = Set.range (fun w : {w // P w} => wd w.1) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  rw [hset, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

/-! ### Cyclic classes -/

lemma mem_coset_iff (h0 : 0 < Fintype.card α) {w z : Word α} :
    z ∈ coset w ↔ (toL w).IsRotated (toL z) := by
  constructor
  · intro h
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨j, (toL_rot w j).symm⟩
  · rintro ⟨j, hj⟩
    refine Finset.mem_image.2 ⟨j % Fintype.card α, Finset.mem_range.2 (Nat.mod_lt _ h0), ?_⟩
    apply toL_injective
    rw [toL_rot, ← hj]
    have := List.rotate_mod (toL w) j
    rwa [length_toL] at this

lemma coset_eq_of_mem (h0 : 0 < Fintype.card α) {w z : Word α} (h : z ∈ coset w) :
    coset z = coset w := by
  have hr := (mem_coset_iff h0).1 h
  ext y
  rw [mem_coset_iff h0, mem_coset_iff h0]
  exact ⟨fun h' => hr.trans h', fun h' => hr.symm.trans h'⟩

lemma self_mem_coset (h0 : 0 < Fintype.card α) (w : Word α) : w ∈ coset w :=
  (mem_coset_iff h0).2 (List.IsRotated.refl _)

end Lists

/-! ### Posets -/

section Poset

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

lemma isUnionOfComponents_iff (U : Finset α) :
    IsUnionOfComponents U ↔ L.UoC (· < ·) univ U := by
  constructor
  · intro h p _ q _ hpq; exact h p q hpq.le
  · intro h p q hpq
    rcases hpq.lt_or_eq with hlt | rfl
    · exact h p (mem_univ _) q (mem_univ _) hlt
    · exact Iff.rfl

lemma isLinExt_iff (w : Word α) : IsLinExt α w ↔ L.LinL (· < ·) univ (toL w) := by
  refine ⟨fun h => ⟨isWordOn_toL w, List.pairwise_ofFn.2 fun i j hij hji => ?_⟩, fun h => ?_⟩
  · exact absurd (h j i hji) (not_lt.2 hij.le)
  · intro i j hij
    have hpw := List.pairwise_ofFn.1 h.2
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact hlt
    · exact absurd hij (lt_irrefl _)
    · exact absurd hij (hpw hgt)

end Poset

end PosetJKS
