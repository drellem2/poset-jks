import PosetJKS.Bridge

/-!
# First milestone: the homology-free presentation `PLie(P) ≅ ℂ[Lin P]/R_P`

Statements and proofs of `notes/poset_jks_theorem.tex`:

* Theorem S (a), (b) (`thmS_a`, `thmS_b`): pure word combinatorics modulo shuffles;
* Theorem Ψ (`thmPsi`): admissible class sums are independent modulo `Sh_n`;
* Corollary Ψ.1 (`corPsi_bijective`, `corPsi_equivariant`): the truncation map
  `ψ_P : PLie(P) → ℂ[Lin P]/R_P` is an `Aut(P)`-isomorphism, for every finite poset `P` with
  `n ≥ 1`.

None of these uses homology, the Jenča–Sarkoci theorem, P. Hall, or the Hopf trace formula.
The inductions (Theorem A, Theorem Ψ through the contraction `E_{a,x}`) are done on lists in
`Words.lean`; `Bridge.lean` transfers them to words `Fin n ≃ α`. Here: Lemma 4 (`card_inB`),
Lemma 6 (`wd_mem_SB_sup_R`), `pr_P(w e_ζ) = s_ζ(w)/n` (`pr_wEζ`), and the theorems.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-! ### Theorem S -/

/-- `w ∈ B_P` for the base component containing `x₀`: `w ∈ Lin(P)` and the first block of `w`
(the shortest nonempty prefix whose letter set is a union of components) contains `x₀`.
Equivalently, `x₀` lies in every nonempty union-prefix, since union-prefixes are nested. -/
def InB (x₀ : α) (w : Word α) : Prop :=
  IsLinExt α w ∧ ∀ k, 0 < k → k ≤ Fintype.card α →
    IsUnionOfComponents (prefixSet w k) → x₀ ∈ prefixSet w k


lemma inB_iff (x₀ : α) (w : Word α) : InB x₀ w ↔ L.InBL (· < ·) univ x₀ (toL w) := by
  constructor
  · rintro ⟨hlin, hB⟩
    refine ⟨(isLinExt_iff w).1 hlin, fun s t hst hs hU => ?_⟩
    have hk : (toL w).take s.length = s := by rw [hst]; simp
    have hlen : s.length ≤ Fintype.card α := by
      rw [← length_toL w, hst, List.length_append]; omega
    have := hB s.length (List.length_pos_iff.2 hs) hlen
      (by rw [isUnionOfComponents_iff, prefixSet_eq, hk]; exact hU)
    rwa [prefixSet_eq, hk, List.mem_toFinset] at this
  · rintro ⟨hlin, hB⟩
    refine ⟨(isLinExt_iff w).2 hlin, fun k hk hkn hU => ?_⟩
    rw [prefixSet_eq, List.mem_toFinset]
    refine hB _ _ (List.take_append_drop k _).symm ?_
      (by rw [← prefixSet_eq, ← isUnionOfComponents_iff]; exact hU)
    intro h
    rcases List.take_eq_nil_iff.1 h with h | h
    · omega
    · have := congrArg List.length h; rw [length_toL] at this; simp at this; omega

/-- Theorem A on words: a combination of words of `B_P` lying in `Sh_n` vanishes. -/
lemma eq_zero_of_inB (x₀ : α) {X : Alg α} (hX : X ∈ Sh α) (hB : ∀ w, X w ≠ 0 → InB x₀ w) :
    X = 0 := by
  apply toLmap_injective
  rw [map_zero]
  refine L.eq_zero_of_inBL univ (· < ·) x₀ _ (map_Sh_le (Submodule.mem_map_of_mem hX))
    fun l hl => ?_
  obtain ⟨w, rfl, hw⟩ := toLmap_support hl
  exact (inB_iff x₀ w).1 (hB w hw)

/-- **Lemma 4** (`notes/conjecture_s_splitting_cycles_span.md` §3): `|B_P| = e_C(P)`; every
cyclic class contains exactly one word of `B_P`. -/
theorem card_inB (x₀ : α) : Nat.card {w : Word α // InB x₀ w} = eC α := by
  classical
  have h0 : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨x₀⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, eC, cyc]
  refine Finset.card_bij (fun w _ => coset w) ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨mem_univ _,
      (Finset.mem_filter.1 hw).2.1⟩, rfl⟩
  · intro w hw w' hw' h
    have hw := (Finset.mem_filter.1 hw).2
    have hw' := (Finset.mem_filter.1 hw').2
    have hmem : w' ∈ coset w := by
      rw [show coset w = coset w' from h]; exact self_mem_coset h0 w'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hmem
    have hj' := Finset.mem_range.1 hj
    have hB := (inB_iff x₀ w).1 hw
    have hB' := (inB_iff x₀ _).1 hw'
    rw [toL_rot, List.rotate_eq_drop_append_take (by rw [length_toL]; omega)] at hB'
    have := L.rotate_eq_zero_of_inBL hB (by rw [length_toL]; exact hj') hB'
    subst this
    exact (rot_zero w).symm
  · intro C hC
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hC
    have hlin := (isLinExt_iff w).1 (Finset.mem_filter.1 hw).2
    have hk : L.muL (· < ·) univ x₀ (toL w) ≤ (toL w).length := L.muL_spec.1
    refine ⟨rot w (L.muL (· < ·) univ x₀ (toL w)), Finset.mem_filter.2 ⟨mem_univ _,
      (inB_iff x₀ _).2 ?_⟩, ?_⟩
    · rw [toL_rot, List.rotate_eq_drop_append_take hk]
      exact L.inBL_rotate_muL (mem_univ x₀) hlin
    · exact coset_eq_of_mem h0 ((mem_coset_iff h0).2 ⟨_, (toL_rot w _).symm⟩)

/-- Theorem S(a). -/
theorem thmS_a (x₀ : α) :
    LinearIndependent ℂ (fun w : {w : Word α // InB x₀ w} => (Sh α).mkQ (wd w.1)) ∧
    Nat.card {w : Word α // InB x₀ w} = eC α ∧
    (IsConnectedPoset α → W α ⊓ Sh α = ⊥) := by
  refine ⟨linIndep_mkQ_wd fun X hX hB => eq_zero_of_inB x₀ hX hB, card_inB x₀, fun hconn => ?_⟩
  rw [eq_bot_iff]
  intro X hX
  rw [Submodule.mem_bot]
  obtain ⟨hW, hSh⟩ := Submodule.mem_inf.1 hX
  refine eq_zero_of_inB x₀ hSh fun w hw => ⟨support_of_mem_span hW hw, fun k hk hkn hU => ?_⟩
  rcases hconn.2 _ hU with h | h
  · have hmem : w ⟨0, by omega⟩ ∈ prefixSet w k :=
      Finset.mem_image.2 ⟨⟨0, by omega⟩, Finset.mem_filter.2 ⟨mem_univ _, hk⟩, rfl⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · rw [h]; exact mem_univ _


variable (α) in
/-- `span(B_P)`. -/
noncomputable abbrev SB (x₀ : α) : Submodule ℂ (Alg α) :=
  Submodule.span ℂ {x | ∃ w, InB x₀ w ∧ x = wd w}

lemma shuffle_mem_W {S : Finset α} {u v : List α} (hS : IsUnionOfComponents S)
    (hu : IsLinExtOn S u) (hv : IsLinExtOn Sᶜ v) : shuffle S u v ∈ W α := by
  unfold shuffle
  refine Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, ?_, rfl⟩
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hw).2
  refine (isLinExt_iff w).2 (L.linL_of_filter (isWordOn_toL w)
    ((isUnionOfComponents_iff S).1 hS) ?_ ?_)
  · rw [← restrict_eq, h1]; exact hu.2
  · rw [← restrict_compl, h2]; exact hv.2

lemma R_le_W : R α ≤ W α := by
  rw [R, Submodule.span_le]
  rintro _ ⟨S, u, v, -, -, hS, hu, hv, rfl⟩
  exact shuffle_mem_W hS hu hv

lemma R_le_Sh : R α ≤ Sh α := by
  rw [R, Submodule.span_le]
  rintro _ ⟨S, u, v, hne, huniv, -, hu, hv, rfl⟩
  exact Submodule.subset_span ⟨S, u, v, hne, huniv, hu.1, hv.1, rfl⟩

lemma SB_le_W (x₀ : α) : SB α x₀ ≤ W α := by
  rw [SB, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  exact Submodule.subset_span ⟨w, hw.1, rfl⟩

lemma filter_append_toFinset {s t : List α} (h : (s ++ t).Nodup) :
    (s ++ t).filter (fun b => decide (b ∈ s.toFinset)) = s ∧
      (s ++ t).filter (fun b => !decide (b ∈ s.toFinset)) = t := by
  have hd := (List.nodup_append.1 h).2.2
  rw [List.filter_append, List.filter_append, List.filter_eq_self.2 (by simp),
    List.filter_eq_nil_iff.2 (fun b hb => by simpa using fun hs => hd b hs b hb rfl),
    List.filter_eq_nil_iff.2 (by simp), List.filter_eq_self.2
      (fun b hb => by simpa using fun hs => hd b hs b hb rfl)]
  simp

/-- **Lemma 6** (`notes/conjecture_s_splitting_cycles_span.md` §5): every linear extension lies
in `span(B_P) + R_P`. Induction on the length `μ` of the longest union-prefix avoiding `x₀`. -/
lemma wd_mem_SB_sup_R (x₀ : α) {w : Word α} (hw : IsLinExt α w) : wd w ∈ SB α x₀ ⊔ R α := by
  classical
  induction hk : L.muL (· < ·) univ x₀ (toL w) using Nat.strong_induction_on generalizing w with
  | _ k ih =>
  have hlin := (isLinExt_iff w).1 hw
  by_cases hk0 : k = 0
  · exact Submodule.mem_sup_left (Submodule.subset_span
      ⟨w, (inB_iff x₀ w).2 (L.inBL_iff_muL.2 ⟨hlin, hk ▸ hk0⟩), rfl⟩)
  obtain ⟨hk1, hkU, hkx, -⟩ := L.muL_spec (r := (· < ·)) (A := univ) (x₀ := x₀) (l := toL w)
  rw [hk] at hk1 hkU hkx
  set s := (toL w).take k with hs
  set t := (toL w).drop k with ht
  set S := s.toFinset with hS
  have hst : toL w = s ++ t := (List.take_append_drop k _).symm
  have hwst : IsWordOn univ (s ++ t) := hst ▸ isWordOn_toL w
  have hpw := List.pairwise_append.1 (hst ▸ hlin.2)
  have hsne : s ≠ [] := by
    intro h
    rcases List.take_eq_nil_iff.1 h with h | h
    · exact hk0 h
    · have := congrArg List.length h; rw [length_toL] at this; simp at this
      exact absurd (this ▸ Fintype.card_pos_iff.2 ⟨x₀⟩) (lt_irrefl 0)
  have hsh : shuffle S s t ∈ R α := by
    refine Submodule.subset_span ⟨S, s, t, ?_, ?_, (isUnionOfComponents_iff S).2 hkU,
      ⟨⟨(List.nodup_append.1 hwst.1).1, rfl⟩, hpw.1⟩, ⟨⟨(List.nodup_append.1 hwst.1).2.1, ?_⟩,
        hpw.2.1⟩, rfl⟩
    · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil s hsne
      exact ⟨b, List.mem_toFinset.2 hb⟩
    · intro h; apply hkx; rw [← List.mem_toFinset, ← hS, h]; exact mem_univ _
    · rw [L.toFinset_right hwst, Finset.compl_eq_univ_sdiff]
  -- `s ⧢ t = w + (the other words)`
  have hwF : w ∈ univ.filter (fun z : Word α => restrict z S = s ∧ restrict z Sᶜ = t) := by
    refine Finset.mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [restrict_eq, restrict_compl, hst]
    exact filter_append_toFinset hwst.1
  have hsum : wd w = shuffle S s t - ∑ z ∈ (univ.filter
      (fun z : Word α => restrict z S = s ∧ restrict z Sᶜ = t)).erase w, wd z := by
    rw [shuffle, ← Finset.add_sum_erase _ _ hwF, add_sub_cancel_right]
  rw [hsum]
  refine sub_mem (Submodule.mem_sup_right hsh) (Submodule.sum_mem _ fun z hz => ?_)
  obtain ⟨hzw, hzF⟩ := Finset.mem_erase.1 hz
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hzF).2
  have key := L.muL_lt_of_shuffle (r := (· < ·)) hlin (z := toL z)
    (by rw [hk, ← hS, ← restrict_eq, h1]) (by rw [hk, ← hS, ← restrict_compl, h2])
    (fun h => hzw (toL_injective h))
  rw [hk] at key
  exact ih _ key.2 ((isLinExt_iff z).2 key.1) rfl

/-- Theorem S(b): `W_P = span(B_P) ⊕ R_P`, `W_P ∩ Sh_n = R_P`, `dim R_P = |Lin P| - e_C(P)`. -/
theorem thmS_b (x₀ : α) :
    Submodule.span ℂ {x | ∃ w, InB x₀ w ∧ x = wd w} ⊔ R α = W α ∧
    Disjoint (Submodule.span ℂ {x | ∃ w, InB x₀ w ∧ x = wd w}) (R α) ∧
    W α ⊓ Sh α = R α ∧
    Module.finrank ℂ (R α) = Nat.card {w : Word α // IsLinExt α w} - eC α := by
  have hsup : SB α x₀ ⊔ R α = W α := by
    refine le_antisymm (sup_le (SB_le_W x₀) R_le_W) ?_
    rw [W, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact wd_mem_SB_sup_R x₀ hw
  have hdisj : Disjoint (SB α x₀) (R α) := by
    rw [Submodule.disjoint_def]
    intro x hx hR
    exact eq_zero_of_inB x₀ (R_le_Sh hR) fun w hw => support_of_mem_span hx hw
  refine ⟨hsup, hdisj, ?_, ?_⟩
  · refine le_antisymm (fun x hx => ?_) (le_inf R_le_W R_le_Sh)
    obtain ⟨hW, hSh⟩ := Submodule.mem_inf.1 hx
    rw [← hsup] at hW
    obtain ⟨b, hb, r, hr, rfl⟩ := Submodule.mem_sup.1 hW
    have hb0 : b = 0 := eq_zero_of_inB x₀ (by
        have := sub_mem hSh (R_le_Sh hr); rwa [add_sub_cancel_right] at this)
      fun w hw => support_of_mem_span hb hw
    rw [hb0, zero_add]; exact hr
  · have h := Submodule.finrank_sup_add_finrank_inf_eq (SB α x₀) (R α)
    rw [hsup, disjoint_iff.1 hdisj, finrank_bot, add_zero, W, finrank_span_wd, SB,
      finrank_span_wd, card_inB] at h
    omega

/-! ### Theorem Ψ -/

/-- `λ : α → ℂ` is admissible: `λ([n]) = 1` and `λ(U) ≠ 1` for every nonempty proper union of
components `U`, where `λ(U) = ∏_{x ∈ U} λ(x)`. (`λ([n]) = 1` forces `λ` to take values in
`ℂˣ`, as in the note.) -/
def IsAdmissible (lam : α → ℂ) : Prop :=
  ∏ a, lam a = 1 ∧
    ∀ U : Finset α, U.Nonempty → U ≠ univ → IsUnionOfComponents U → ∏ a ∈ U, lam a ≠ 1

open Classical in
/-- `s_λ(w) = ∑_{k a cut of w} λ(w_1 ⋯ w_k)⁻¹ w γ^k`. -/
noncomputable def sLam (lam : α → ℂ) (w : Word α) : Alg α :=
  ∑ k ∈ (range (Fintype.card α)).filter (IsCut w), (∏ a ∈ prefixSet w k, lam a)⁻¹ • wd (rot w k)


lemma prod_prefixSet (lam : α → ℂ) (w : Word α) (k : ℕ) :
    ∏ a ∈ prefixSet w k, lam a = L.lamL lam ((toL w).take k) := by
  rw [prefixSet_eq, L.lamL_eq_prod lam ((isWordOn_toL w).1.sublist (List.take_sublist _ _))]

open Classical in
lemma mem_cuts_iff (w : Word α) (k : ℕ) :
    k ∈ (range (Fintype.card α)).filter (IsCut w) ↔
      k < (toL w).length ∧ L.UoC (· < ·) univ ((toL w).take k).toFinset := by
  rw [Finset.mem_filter, Finset.mem_range, IsCut, length_toL, isUnionOfComponents_iff,
    prefixSet_eq]
  tauto

open Classical in
lemma toLmap_sLam (lam : α → ℂ) (w : Word α) :
    toLmap (sLam lam w) = ∑ k ∈ (range (Fintype.card α)).filter (IsCut w),
      (L.lamL lam ((toL w).take k))⁻¹ • Finsupp.single ((toL w).rotate k) (1 : ℂ) := by
  simp only [sLam, map_sum, map_smul, toLmap_wd, toL_rot, prod_prefixSet]

open Classical in
lemma sLam_apply (lam : α → ℂ) (w z : Word α) :
    sLam lam w z = ∑ k ∈ (range (Fintype.card α)).filter (IsCut w),
      (∏ a ∈ prefixSet w k, lam a)⁻¹ * (if rot w k = z then 1 else 0) := by
  simp only [sLam, alg_sum_apply, alg_smul_apply, wd_apply]

lemma sLam_self (lam : α → ℂ) (w : Word α) (h0 : 0 < Fintype.card α) : sLam lam w w = 1 := by
  classical
  rw [sLam_apply, Finset.sum_eq_single 0]
  · simp [prefixSet, rot_zero]
  · intro k hk hk0
    rw [if_neg, mul_zero]
    intro h
    have hkn := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
    have hne : toL w ≠ [] := by
      intro h'; have := congrArg List.length h'; rw [length_toL] at this; simp at this; omega
    have := List.Nodup.rotate_congr (isWordOn_toL w).1 hne k 0
      (by rw [← toL_rot, h, List.rotate_zero])
    rw [length_toL, Nat.mod_eq_of_lt hkn, Nat.zero_mod] at this
    exact hk0 this
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_range.2 h0, h0, fun x y _ => by
      simp [prefixSet]⟩) h

lemma sLam_eq_zero_of_not_mem (lam : α → ℂ) {w z : Word α} (h : z ∉ coset w) :
    sLam lam w z = 0 := by
  classical
  rw [sLam_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [if_neg, mul_zero]
  rintro rfl
  exact h (Finset.mem_image.2 ⟨k, (Finset.mem_filter.1 hk).1, rfl⟩)

lemma cyc_eq_coset (h0 : 0 < Fintype.card α) {C : Finset (Word α)} (hC : C ∈ cyc α)
    {z : Word α} (hz : z ∈ C) : C = coset z := by
  obtain ⟨w₀, -, rfl⟩ := Finset.mem_image.1 hC
  exact (coset_eq_of_mem h0 hz).symm

/-- Theorem Ψ: for admissible `λ`, the class sums `s_λ(C)`, one for each cyclic class `C`
(computed from any representative `w ∈ C ∩ Lin(P)`), are linearly independent modulo `Sh_n`. -/
theorem thmPsi (lam : α → ℂ) (hlam : IsAdmissible lam) (rep : cyc α → Word α)
    (hrep : ∀ C, rep C ∈ C.1 ∧ IsLinExt α (rep C)) :
    LinearIndependent ℂ (fun C => (Sh α).mkQ (sLam lam (rep C))) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg C hC
  have h0 : 0 < Fintype.card α := by
    obtain ⟨w₀, -, hw₀⟩ := Finset.mem_image.1 C.2
    have := hw₀ ▸ (hrep C).1
    obtain ⟨j, hj, -⟩ := Finset.mem_image.1 this
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_range.1 hj)
  set X : Alg α := ∑ C ∈ s, g C • sLam lam (rep C) with hX
  have hXSh : X ∈ Sh α := by
    rw [← Submodule.Quotient.mk_eq_zero (Sh α)]
    have : (Sh α).mkQ X = 0 := by rw [hX, map_sum]; simpa only [map_smul] using hg
    exact this
  have hlamw : ∀ w : Word α, L.lamL lam (toL w) = 1 := fun w => by
    rw [L.lamL_eq_prod lam (isWordOn_toL w).1, (isWordOn_toL w).2]; exact hlam.1
  have hX0 : X = 0 := by
    apply toLmap_injective
    rw [map_zero]
    have hTX : toLmap X = ∑ C ∈ s, g C • toLmap (sLam lam (rep C)) := by
      rw [hX, map_sum]; simp only [map_smul]
    refine L.eq_zero_of_eqL univ (· < ·) lam _ (map_Sh_le (Submodule.mem_map_of_mem hXSh))
      ?_ ?_ ?_
    · intro l hl
      rw [hTX, Finsupp.finset_sum_apply] at hl
      obtain ⟨C', -, hC'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
      rw [Finsupp.smul_apply, smul_eq_mul] at hC'
      have hne := right_ne_zero_of_mul hC'
      rw [toLmap_sLam] at hne
      exact L.linL_of_classSum ((isLinExt_iff _).1 (hrep C').2) _ (mem_cuts_iff _) hne
    · rw [hTX]
      refine L.eqL_sum _ _ fun C' _ => L.eqL_smul _ ?_
      rw [toLmap_sLam]
      exact L.eqL_classSum (isWordOn_toL _) (hlamw _) _ (mem_cuts_iff _)
    · intro U _ hne hU hUoC
      exact hlam.2 U hne hU ((isUnionOfComponents_iff U).2 hUoC)
  -- read off the coefficient of `rep C`
  have hcoef := congrArg (fun Y : Alg α => Y (rep C)) hX0
  simp only [hX, alg_sum_apply, alg_smul_apply, alg_zero_apply] at hcoef
  rw [Finset.sum_eq_single C, sLam_self lam _ h0, mul_one] at hcoef
  · exact hcoef
  · intro C' _ hC'
    rw [sLam_eq_zero_of_not_mem, mul_zero]
    intro hmem
    apply hC'
    apply Subtype.ext
    rw [cyc_eq_coset h0 C'.2 (hrep C').1, cyc_eq_coset h0 C.2 (hrep C).1]
    exact (coset_eq_of_mem h0 hmem).symm
  · intro h; exact absurd hC h

/-! ### Corollary Ψ.1: the truncation isomorphism `ψ_P : PLie(P) ≅ ℂ[Lin P]/R_P` -/

open Classical in
variable (α) in
/-- The coordinate truncation `pr_P : ℂ[S_n] → W_P` to `Lin(P)`. -/
noncomputable def pr : Alg α →ₗ[ℂ] Alg α :=
  ∑ w ∈ univ.filter (IsLinExt α), Finsupp.lsingle w ∘ₗ Finsupp.lapply w

theorem pr_mem_W (y : Alg α) : pr α y ∈ W α := by
  classical
  rw [pr, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun w hw => ?_
  have : (Finsupp.lsingle w ∘ₗ Finsupp.lapply w : Alg α →ₗ[ℂ] Alg α) y = y w • wd w := by
    change Finsupp.single w (y w) = y w • Finsupp.single w (1 : ℂ)
    rw [Finsupp.smul_single_one]
  rw [this]
  exact Submodule.smul_mem _ (y w)
    (Submodule.subset_span (show wd w ∈ {x | ∃ w, IsLinExt α w ∧ x = wd w} from
      ⟨w, (mem_filter.1 hw).2, rfl⟩))

variable (α) in
/-- `pr_P` with codomain `W_P`. -/
noncomputable def prW : Alg α →ₗ[ℂ] W α := (pr α).codRestrict (W α) pr_mem_W

variable (α) in
/-- `R_P`, as a subspace of `W_P`. -/
noncomputable abbrev RinW : Submodule ℂ (W α) := (R α).comap (W α).subtype

variable (α) in
/-- `M_P = W_P / R_P = ℂ[Lin P]/R_P`. -/
noncomputable abbrev MP := W α ⧸ RinW α

variable (α) in
/-- `ψ_P : PLie(P) → M_P`, `y ↦ pr_P(y) mod R_P`. (The note writes the target as
`(W_P + Sh_n)/Sh_n`; it is identified with `W_P/R_P` through `W_P ∩ Sh_n = R_P`, Theorem S(b),
and under that identification the two maps agree.) -/
noncomputable def psi (ζ : ℂ) : PLie α ζ →ₗ[ℂ] MP α :=
  (RinW α).mkQ ∘ₗ prW α ∘ₗ (PLie α ζ).subtype

/-- `Aut(P)` acting on `PLie(P)` by left multiplication. -/
noncomputable def actPLie (ζ : ℂ) (g : α ≃o α) : PLie α ζ →ₗ[ℂ] PLie α ζ :=
  (relabel g.toEquiv).restrict fun _ hy => relabel_mem_PLie g ζ hy

/-- `Aut(P)` acting on `M_P = ℂ[Lin P]/R_P` by left multiplication. -/
noncomputable def actMP (g : α ≃o α) : MP α →ₗ[ℂ] MP α :=
  Submodule.mapQ _ _ ((relabel g.toEquiv).restrict fun _ hy => relabel_mem_W g hy)
    fun x hy => by exact relabel_mem_R g hy


open Classical in
lemma pr_eq (y : Alg α) : pr α y = ∑ w ∈ univ.filter (IsLinExt α), y w • wd w := by
  rw [pr, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  change Finsupp.single w (y w) = y w • Finsupp.single w (1 : ℂ)
  rw [Finsupp.smul_single_one]

open Classical in
lemma pr_apply (y : Alg α) (z : Word α) : pr α y z = if IsLinExt α z then y z else 0 := by
  rw [pr_eq, alg_sum_apply]
  simp only [alg_smul_apply, wd_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

open Classical in
lemma pr_wd (z : Word α) : pr α (wd z) = if IsLinExt α z then wd z else 0 := by
  apply alg_ext
  intro y
  rw [pr_apply]
  by_cases hz : IsLinExt α z
  · rw [if_pos hz]
    by_cases hy : IsLinExt α y
    · rw [if_pos hy]
    · rw [if_neg hy, wd_apply, if_neg (fun (h : z = y) => hy (h ▸ hz))]
  · rw [if_neg hz, alg_zero_apply]
    split_ifs with hy
    · rw [wd_apply, if_neg (fun (h : z = y) => hz (h ▸ hy))]
    · rfl

lemma relabel_apply (g : Equiv.Perm α) (y : Alg α) (z : Word α) :
    relabel g y z = y (z.trans g.symm) := by
  have := Finsupp.mapDomain_apply (f := fun w : Word α => w.trans g)
    (fun w w' h => Equiv.ext fun i => g.injective (congrArg (fun u : Word α => u i) h)) y
    (z.trans g.symm)
  rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl] at this
  exact this

lemma isLinExt_trans_symm_iff (g : α ≃o α) (z : Word α) :
    IsLinExt α (z.trans g.toEquiv.symm) ↔ IsLinExt α z := by
  have h : ∀ a b : α, g.toEquiv.symm a < g.toEquiv.symm b ↔ a < b :=
    fun a b => g.symm.lt_iff_lt
  simp only [IsLinExt, Equiv.trans_apply, h]

lemma pr_relabel (g : α ≃o α) (y : Alg α) :
    pr α (relabel g.toEquiv y) = relabel g.toEquiv (pr α y) := by
  classical
  apply alg_ext
  intro z
  rw [pr_apply, relabel_apply, relabel_apply, pr_apply, isLinExt_trans_symm_iff]

lemma isLinExt_rot_iff {w : Word α} (hw : IsLinExt α w) {j : ℕ}
    (hj : j < Fintype.card α) : IsLinExt α (rot w j) ↔ IsCut w j := by
  have hl := (isLinExt_iff w).1 hw
  have hsplit : toL w = (toL w).take j ++ (toL w).drop j := (List.take_append_drop _ _).symm
  rw [isLinExt_iff, toL_rot, List.rotate_eq_drop_append_take (by rw [length_toL]; omega), IsCut,
    isUnionOfComponents_iff, prefixSet_eq]
  constructor
  · intro h; exact ⟨hj, L.uoC_of_linL_rotate (hsplit ▸ hl) h⟩
  · rintro ⟨-, h⟩; exact L.linL_rotate (hsplit ▸ hl) h

lemma card_prefixSet (w : Word α) {k : ℕ} (hk : k ≤ Fintype.card α) :
    (prefixSet w k).card = k := by
  rw [prefixSet_eq, List.toFinset_card_of_nodup
    ((isWordOn_toL w).1.sublist (List.take_sublist _ _)), List.length_take, length_toL,
    min_eq_left hk]

/-- `pr_P(w e_ζ) = s_ζ(w)/n` for `w ∈ Lin(P)` (`notes/natural_isomorphism.md`, Cor. Ψ.1). -/
lemma pr_wEζ (ζ : ℂ) {w : Word α} (hw : IsLinExt α w) :
    pr α (wEζ ζ w) = ((Fintype.card α : ℂ))⁻¹ • sLam (fun _ => ζ) w := by
  classical
  rw [wEζ, map_sum, sLam, Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [map_smul, pr_wd]
  by_cases hc : IsCut w j
  · rw [if_pos ((isLinExt_rot_iff hw hj').2 hc), if_pos hc, Finset.prod_const,
      card_prefixSet w hj'.le, smul_smul]
  · rw [if_neg (fun h => hc ((isLinExt_rot_iff hw hj').1 h)), if_neg hc, smul_zero]

/-- Corollary Ψ.1, bijectivity: for every finite poset `P` and every primitive `n`-th root of
unity `ζ`, the truncation map `ψ_P` is a linear isomorphism `PLie(P) ≅ ℂ[Lin P]/R_P`. -/
theorem corPsi_bijective (h0 : 0 < Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    Function.Bijective (psi α ζ) := by
  classical
  obtain ⟨x₀⟩ : Nonempty α := Fintype.card_pos_iff.1 h0
  have hrepex : ∀ C : cyc α, ∃ w, w ∈ C.1 ∧ IsLinExt α w := fun C => by
    obtain ⟨w, hw, hC⟩ := Finset.mem_image.1 C.2
    exact ⟨w, hC ▸ self_mem_coset h0 w, (Finset.mem_filter.1 hw).2⟩
  choose rep hrep using hrepex
  set v : cyc α → Alg α := fun C => wEζ ζ (rep C) with hv
  have hadm : IsAdmissible (fun _ : α => ζ) := by
    refine ⟨by rw [Finset.prod_const, Finset.card_univ]; exact hζ.pow_eq_one,
      fun U hne hU _ => ?_⟩
    rw [Finset.prod_const]
    intro h
    have hdvd := (hζ.pow_eq_one_iff_dvd _).1 h
    have hlt : U.card < Fintype.card α := by
      rw [← Finset.card_univ]; exact Finset.card_lt_card (Finset.ssubset_univ_iff.2 hU)
    exact absurd (Nat.le_of_dvd (Finset.card_pos.2 hne) hdvd) (not_le.2 hlt)
  have hψ := thmPsi (fun _ => ζ) hadm rep hrep
  have hn : ((Fintype.card α : ℂ)) ≠ 0 := by exact_mod_cast h0.ne'
  have key : ∀ c : cyc α → ℂ, pr α (∑ C, c C • v C) ∈ Sh α → c = 0 := by
    intro c hc
    have hpr : pr α (∑ C, c C • v C) =
        ((Fintype.card α : ℂ))⁻¹ • ∑ C, c C • sLam (fun _ => ζ) (rep C) := by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [map_smul, hv, pr_wEζ ζ (hrep C).2, smul_comm]
    rw [hpr] at hc
    have hmem := Submodule.smul_mem _ (Fintype.card α : ℂ) hc
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul] at hmem
    have h0' : ∑ C, c C • (Sh α).mkQ (sLam (fun _ => ζ) (rep C)) = 0 := by
      simp only [← map_smul, ← map_sum]
      exact (Submodule.Quotient.mk_eq_zero (Sh α)).2 hmem
    funext C
    exact Fintype.linearIndependent_iff.1 hψ c h0' C
  have hli : LinearIndependent ℂ v := Fintype.linearIndependent_iff.2 fun c hc => by
    have := key c (by rw [hc, map_zero]; exact zero_mem _)
    intro C; simp [this]
  have hspan : PLie α ζ = Submodule.span ℂ (Set.range v) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rw [PLie, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      let C : cyc α := ⟨coset w, Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨mem_univ _, hw⟩,
        rfl⟩⟩
      obtain ⟨j, hj⟩ := ((mem_coset_iff h0).1 (hrep C).1).symm
      have hwr : w = rot (rep C) j := toL_injective (by rw [toL_rot, hj])
      rw [hwr, wEζ_rot hζ.pow_eq_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨C, rfl⟩)
    · rintro _ ⟨C, rfl⟩
      exact Submodule.subset_span ⟨rep C, (hrep C).2, rfl⟩
  have hdimL : Module.finrank ℂ (PLie α ζ) = eC α := by
    rw [hspan, finrank_span_eq_card hli, eC, Fintype.card_coe]
  have hdimM : Module.finrank ℂ (MP α) = eC α := by
    have h1 : Module.finrank ℂ (MP α) + Module.finrank ℂ (RinW α) = Module.finrank ℂ (W α) :=
      Submodule.finrank_quotient_add_finrank (RinW α)
    have h2 : Module.finrank ℂ (RinW α) = Module.finrank ℂ (R α) :=
      (Submodule.comapSubtypeEquivOfLe R_le_W).finrank_eq
    have h3 := (thmS_b x₀).2.2.2
    have h4 : Module.finrank ℂ (W α) = Nat.card {w : Word α // IsLinExt α w} := by
      rw [W, finrank_span_wd]
    have h5 : eC α ≤ Nat.card {w : Word α // IsLinExt α w} := by
      rw [eC, cyc, Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact Finset.card_image_le
    omega
  have hinj : Function.Injective (psi α ζ) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : (y : Alg α) ∈ Submodule.span ℂ (Set.range v) := hspan ▸ y.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy'
    have hR : pr α (y : Alg α) ∈ Sh α := by
      have : prW α y ∈ RinW α := by
        rw [psi, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hy
        exact hy
      exact R_le_Sh this
    rw [← hc] at hR
    have hc0 := key c hR
    apply Subtype.ext
    rw [← hc, hc0]
    simp
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdimL.trans hdimM.symm)).1 hinj⟩

/-- Corollary Ψ.1, equivariance: `ψ_P` commutes with the action of `Aut(P)` (no sign twist). -/
theorem corPsi_equivariant (ζ : ℂ) (g : α ≃o α) :
    psi α ζ ∘ₗ actPLie ζ g = actMP g ∘ₗ psi α ζ := by
  refine LinearMap.ext fun y => ?_
  simp only [psi, actPLie, actMP, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  simp only [prW, LinearMap.codRestrict_apply, LinearMap.restrict_apply, Submodule.subtype_apply]
  exact pr_relabel g y

/-- Corollary Ψ.1 in packaged form: an `Aut(P)`-equivariant linear isomorphism
`PLie(P) ≃ ℂ[Lin P]/R_P` (namely `ψ_P`). -/
theorem corPsi (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    ∃ e : PLie α ζ ≃ₗ[ℂ] MP α, (∀ y, e y = psi α ζ y) ∧
      ∀ (g : α ≃o α) (y : PLie α ζ), e (actPLie ζ g y) = actMP g (e y) := by
  refine ⟨LinearEquiv.ofBijective (psi α ζ) (corPsi_bijective h0 hζ), fun _ => rfl, fun g y => ?_⟩
  simp only [LinearEquiv.ofBijective_apply]
  exact LinearMap.congr_fun (corPsi_equivariant ζ g) y

end PosetJKS
