import PosetJKS.Bridge

/-!
# First milestone: the homology-free presentation `PLie(P) ≅ ℂ[Lin P]/R_P`

Statements of `notes/poset_jks_theorem.tex`:

* Theorem S (a), (b) (`thmS_a`, `thmS_b`): pure word combinatorics modulo shuffles;
* Theorem Ψ (`thmPsi`): admissible class sums are independent modulo `Sh_n`;
* Corollary Ψ.1 (`corPsi_bijective`, `corPsi_equivariant`): the truncation map
  `ψ_P : PLie(P) → ℂ[Lin P]/R_P` is an `Aut(P)`-isomorphism, for every finite poset `P`.

None of these uses homology, the Jenča–Sarkoci theorem, P. Hall, or the Hopf trace formula.
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
  have key := L.muL_lt_of_shuffle (r := (· < ·)) (mem_univ x₀) hlin (z := toL z)
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

/-- Theorem Ψ: for admissible `λ`, the class sums `s_λ(C)`, one for each cyclic class `C`
(computed from any representative `w ∈ C ∩ Lin(P)`), are linearly independent modulo `Sh_n`. -/
theorem thmPsi (lam : α → ℂ) (hlam : IsAdmissible lam) (rep : cyc α → Word α)
    (hrep : ∀ C, rep C ∈ C.1 ∧ IsLinExt α (rep C)) :
    LinearIndependent ℂ (fun C => (Sh α).mkQ (sLam lam (rep C))) := by
  sorry

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

/-- Corollary Ψ.1, bijectivity: for every finite poset `P` and every primitive `n`-th root of
unity `ζ`, the truncation map `ψ_P` is a linear isomorphism `PLie(P) ≅ ℂ[Lin P]/R_P`. -/
theorem corPsi_bijective (h0 : 0 < Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    Function.Bijective (psi α ζ) := by
  sorry

/-- Corollary Ψ.1, equivariance: `ψ_P` commutes with the action of `Aut(P)` (no sign twist). -/
theorem corPsi_equivariant (ζ : ℂ) (g : α ≃o α) :
    psi α ζ ∘ₗ actPLie ζ g = actMP g ∘ₗ psi α ζ := by
  sorry

/-- Corollary Ψ.1 in packaged form: an `Aut(P)`-equivariant linear isomorphism
`PLie(P) ≃ ℂ[Lin P]/R_P` (namely `ψ_P`). -/
theorem corPsi (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    ∃ e : PLie α ζ ≃ₗ[ℂ] MP α, (∀ y, e y = psi α ζ y) ∧
      ∀ (g : α ≃o α) (y : PLie α ζ), e (actPLie ζ g y) = actMP g (e y) := by
  refine ⟨LinearEquiv.ofBijective (psi α ζ) (corPsi_bijective h0 hζ), fun _ => rfl, fun g y => ?_⟩
  simp only [LinearEquiv.ofBijective_apply]
  exact LinearMap.congr_fun (corPsi_equivariant ζ g) y

end PosetJKS
