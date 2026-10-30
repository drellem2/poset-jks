import PosetJKS.Milestone

/-!
# The character of `PLie(P)` (Lemma `lem:liechar` of `notes/poset_jks_theorem.tex`)

Choose one linear extension `w_C ∈ C` in each cyclic class. Then `{w_C e_ζ}` is a basis of
`PLie(P)` (`basisPLie`), `g ∈ Aut(P)` maps `w_C e_ζ` to `ζ^j w_{gC} e_ζ`, and so
`tr(g | PLie(P)) = ∑_{gC = C} ζ^{r_g(C)}` (`trace_actPLie`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Distinct rotations `r, s < n` of a word are distinct. -/
lemma rot_injective {w : Word α} {r s : ℕ} (hr : r < Fintype.card α) (hs : s < Fintype.card α)
    (h : rot w r = rot w s) : r = s := by
  have h0 : 0 < Fintype.card α := by omega
  have := congrArg (fun u : Word α => u ⟨0, h0⟩) h
  simp only [rot, Equiv.trans_apply] at this
  have h' := congrArg Fin.val (w.injective this)
  rw [val_finRotate_pow, val_finRotate_pow] at h'
  simpa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using h'

/-- `g (w C_n) = (g w) C_n`. -/
lemma coset_image_trans (g : Equiv.Perm α) (w : Word α) :
    (coset w).image (fun z => z.trans g) = coset (w.trans g) := by
  rw [coset, coset, Finset.image_image]
  rfl

variable [PartialOrder α]

/-- The rotation `r_g(C)` is realised by every word of a `g`-stable class:
`g w = w γ^{r_g(C)}` for all `w ∈ C`. -/
lemma classRot_spec (h0 : 0 < Fintype.card α) (g : α ≃o α) {C : Finset (Word α)}
    (hC : C ∈ cyc α) (hg : C.image (fun w => w.trans g.toEquiv) = C) {w : Word α}
    (hw : w ∈ C) :
    classRot g C < Fintype.card α ∧ w.trans g.toEquiv = rot w (classRot g C) := by
  classical
  have hex : ∃ r, r < Fintype.card α ∧ ∃ w ∈ C, w.trans g.toEquiv = rot w r := by
    have hgw : w.trans g.toEquiv ∈ C := hg ▸ Finset.mem_image_of_mem _ hw
    rw [cyc_eq_coset h0 hC hw] at hgw
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.1 hgw
    exact ⟨j, Finset.mem_range.1 hj, w, hw, hj'.symm⟩
  have hdef : classRot g C = Nat.find hex := by
    rw [classRot, dif_pos hex]
  obtain ⟨hlt, w₀, hw₀, hrot⟩ := Nat.find_spec hex
  rw [hdef]
  refine ⟨hlt, ?_⟩
  have hw' : w ∈ coset w₀ := cyc_eq_coset h0 hC hw₀ ▸ hw
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw'
  rw [← rot_trans, hrot, rot_rot, rot_rot, add_comm]

/-- The cyclic class of a linear extension, as an element of `Cyc(P)`. -/
noncomputable def classOf {w : Word α} (hw : IsLinExt α w) : cyc α :=
  ⟨coset w, by classical exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨mem_univ _, hw⟩, rfl⟩⟩

lemma exists_rep (h0 : 0 < Fintype.card α) (C : cyc α) : ∃ w, w ∈ C.1 ∧ IsLinExt α w := by
  classical
  obtain ⟨w, hw, hC⟩ := Finset.mem_image.1 C.2
  exact ⟨w, hC ▸ self_mem_coset h0 w, (Finset.mem_filter.1 hw).2⟩

/-- A chosen linear extension `w_C` in each cyclic class. -/
noncomputable def rep (h0 : 0 < Fintype.card α) (C : cyc α) : Word α :=
  (exists_rep h0 C).choose

lemma rep_mem (h0 : 0 < Fintype.card α) (C : cyc α) : rep h0 C ∈ C.1 :=
  (exists_rep h0 C).choose_spec.1

lemma rep_linExt (h0 : 0 < Fintype.card α) (C : cyc α) : IsLinExt α (rep h0 C) :=
  (exists_rep h0 C).choose_spec.2

/-- Every word of a class is a rotation `w_C γ^j`, `j < n`, of the chosen representative. -/
lemma exists_rot_rep (h0 : 0 < Fintype.card α) (C : cyc α) {w : Word α} (hw : w ∈ C.1) :
    ∃ j < Fintype.card α, w = rot (rep h0 C) j := by
  have h := cyc_eq_coset h0 C.2 (rep_mem h0 C) ▸ hw
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
  exact ⟨j, Finset.mem_range.1 hj, rfl⟩

lemma linearIndependent_wEζ_rep (h0 : 0 < Fintype.card α) (ζ : ℂ) :
    LinearIndependent ℂ (fun C : cyc α => wEζ ζ (rep h0 C)) := by
  classical
  have hn : ((Fintype.card α : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast h0.ne')
  -- the coefficient of `w_D` in `w_C e_ζ` is `n⁻¹ [C = D]`
  have hcoef : ∀ C D : cyc α, wEζ ζ (rep h0 C) (rep h0 D) =
      if C = D then ((Fintype.card α : ℂ))⁻¹ else 0 := by
    intro C D
    rw [wEζ, alg_sum_apply]
    simp only [alg_smul_apply, wd_apply, mul_ite, mul_one, mul_zero]
    by_cases hCD : C = D
    · subst hCD
      rw [if_pos rfl, Finset.sum_eq_single 0]
      · simp [rot_zero]
      · intro j hj hj0
        rw [if_neg]
        intro h
        exact hj0 (rot_injective (Finset.mem_range.1 hj) h0 (h.trans (rot_zero _).symm))
      · intro h; exact absurd (Finset.mem_range.2 h0) h
    · rw [if_neg hCD]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [if_neg]
      intro h
      apply hCD
      have hmem : rep h0 D ∈ coset (rep h0 C) := h ▸ Finset.mem_image_of_mem _ hj
      apply Subtype.ext
      rw [cyc_eq_coset h0 C.2 (rep_mem h0 C), cyc_eq_coset h0 D.2 (rep_mem h0 D),
        coset_eq_of_mem h0 hmem]
  refine Fintype.linearIndependent_iff.2 fun c hc D => ?_
  have := congrArg (fun X : Alg α => X (rep h0 D)) hc
  simp only [alg_sum_apply, alg_smul_apply, hcoef, mul_ite, mul_zero, alg_zero_apply] at this
  rw [Finset.sum_ite_eq' univ D] at this
  simpa [hn] using this

lemma PLie_eq_span_rep (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1) :
    PLie α ζ = Submodule.span ℂ (Set.range fun C : cyc α => wEζ ζ (rep h0 C)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [PLie, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, -, hj⟩ := exists_rot_rep h0 (classOf hw) (self_mem_coset h0 w)
    rw [hj, wEζ_rot hζ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨classOf hw, rfl⟩)
  · rintro _ ⟨C, rfl⟩
    exact Submodule.subset_span ⟨rep h0 C, rep_linExt h0 C, rfl⟩

/-- The basis `{w_C e_ζ}_{C ∈ Cyc(P)}` of `PLie(P)`; in particular `dim PLie(P) = e_C(P)`. -/
noncomputable def basisPLie (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1) :
    Module.Basis (cyc α) ℂ (PLie α ζ) :=
  (Module.Basis.span (linearIndependent_wEζ_rep h0 ζ)).map
    (LinearEquiv.ofEq _ _ (PLie_eq_span_rep h0 hζ).symm)

lemma basisPLie_apply (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1)
    (C : cyc α) : (basisPLie h0 hζ C : Alg α) = wEζ ζ (rep h0 C) := by
  simp [basisPLie, Module.Basis.span_apply]

lemma finrank_PLie (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1) :
    Module.finrank ℂ (PLie α ζ) = eC α := by
  rw [Module.finrank_eq_card_basis (basisPLie h0 hζ), eC, Fintype.card_coe]

/-- **Lemma `lem:liechar`**: `tr(g | PLie(P)) = ∑_{gC=C} ζ^{r_g(C)}`. -/
theorem trace_actPLie (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : ζ ^ Fintype.card α = 1)
    (g : α ≃o α) :
    LinearMap.trace ℂ (PLie α ζ) (actPLie ζ g) = fixedClassSum ζ g := by
  classical
  set b := basisPLie h0 hζ
  -- `g w_C = w_{gC} γ^{j}`
  have hD : ∀ C : cyc α, ∃ j < Fintype.card α,
      (rep h0 C).trans g.toEquiv = rot (rep h0 (classOf (isLinExt_trans g (rep_linExt h0 C)))) j :=
    fun C => exists_rot_rep h0 _ (self_mem_coset h0 _)
  choose j hjlt hj using hD
  set D : cyc α → cyc α := fun C => classOf (isLinExt_trans g (rep_linExt h0 C)) with hDdef
  have hact : ∀ C, actPLie ζ g (b C) = ζ ^ j C • b (D C) := by
    intro C
    apply Subtype.ext
    rw [Submodule.coe_smul, basisPLie_apply]
    change relabel g.toEquiv (b C : Alg α) = _
    rw [basisPLie_apply, relabel_wEζ, hj C, wEζ_rot hζ]
  -- `gC = C` iff `D C = C`
  have hfix : ∀ C : cyc α, D C = C ↔ C.1.image (fun w => w.trans g.toEquiv) = C.1 := by
    intro C
    rw [cyc_eq_coset h0 C.2 (rep_mem h0 C), coset_image_trans, ← Subtype.val_inj]
    change coset ((rep h0 C).trans g.toEquiv) = C.1 ↔ _
    rw [← cyc_eq_coset h0 C.2 (rep_mem h0 C)]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hact, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [fixedClassSum, Finset.sum_filter, ← Finset.sum_coe_sort (cyc α)]
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases hC : D C = C
  · rw [if_pos hC, if_pos ((hfix C).1 hC)]
    obtain ⟨hr, hgr⟩ := classRot_spec h0 g C.2 ((hfix C).1 hC) (rep_mem h0 C)
    have hjC := hj C
    change (rep h0 C).trans g.toEquiv = rot (rep h0 (D C)) (j C) at hjC
    rw [hC, hgr] at hjC
    rw [rot_injective (hjlt C) hr hjC.symm]
  · rw [if_neg hC, if_neg (fun h => hC ((hfix C).2 h))]

end PosetJKS
