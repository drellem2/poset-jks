import PosetJKS.ConeRetract

/-!
# The decomposition of `\widehat{OP(P)}` at `π_a`, and Proposition C

Route C, slice S3 (`notes/lean_js_route.md` §3.2 and §6, as audited in
`notes/audit_lean_js_route.md` §§3–4).

**General part.** Let `L` be a poset and `A ⊆ L` a finite set of minimal elements, and put
`Q = L ∖ A`. For `x₀ ∈ A` let `Upper x₀ = (x₀, ·)` be its open upper set.

* `consMap x₀` prepends `x₀` to a chain of `Upper x₀`, and `strip x₀` is the coordinate
  projection back: `strip x₀ m w` is the coefficient function `e ↦ w (x₀ :: e)`.
* (iv) `strip_bd`: `strip x₀ ∘ ∂ = −∂ ∘ strip x₀`, for `x₀` minimal.
* (v) `mem_range_of_strip_eq_zero`: a chain killed by every `strip x₀`, `x₀ ∈ A`, is the
  pushforward of a chain of `Q`. (A chain meets `A` at most in its least element.)
* (vi) `strip_cons`, `strip_cons_of_ne`: `strip x₀ ∘ consMap x₀ = id`, and
  `strip x₁ ∘ consMap x₀ = 0` for `x₁ ≠ x₀`.
* **Proposition C** (`propC_core`, and its two forms `propC_succ`, `propC_zero`): if `Q` is
  acyclic in degree `d` and, for every `x₀ ∈ A`, `H̃_{d−1}(Upper x₀) = 0` (for `d ≥ 1`), resp.
  `Upper x₀ ≠ ∅` (for `d = 0`), then `H̃_d(Δ(L)) = 0`.

**At `π_a`.** Let `a` be minimal in `P` and `n ≥ 3`. In `L = \widehat{OP(P)}`, `A = Aset a` is the
set of the `π_ab`; they are minimal (`pab_minimal`, §3.2 (ii)). `Q a = L ∖ A` carries the cone
retraction `x ↦ x ∧ π_a` with apex `π_a` (`coneQ`, §3.2 (i)), so it is acyclic by Lemma K
(`Q_acyclic`). The upper interval `(π_ab, 1̂)` is `\widehat{OP(P/π_ab)}` (`upperIso`, Lemma U,
§3.2 (iii)). Hence `propC` (`d ≥ 1`) and `propC_zero` (`d = 0`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Prepending a minimal element: `consMap` and `strip` -/

section Strip

variable {L : Type*} [PartialOrder L]

/-- The open upper set `(x₀, ·) = {y : x₀ < y}`. -/
abbrev Upper (x₀ : L) := {y : L // x₀ < y}

theorem strictMono_cons (x₀ : L) {m : ℕ} (e : Fin m ↪o Upper x₀) :
    StrictMono (Fin.cons x₀ (fun i => (e i).1) : Fin (m + 1) → L) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j => simpa only [Fin.cons_zero, Fin.cons_succ] using (e j).2
  | succ i =>
    cases j using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ j =>
      simp only [Fin.cons_succ]
      exact e.strictMono (Fin.succ_lt_succ_iff.1 hij)

/-- The chain `x₀ :: e` of `L`, for a chain `e` of `(x₀, ·)`. -/
def consChain (x₀ : L) {m : ℕ} (e : Fin m ↪o Upper x₀) : Fin (m + 1) ↪o L :=
  OrderEmbedding.ofStrictMono _ (strictMono_cons x₀ e)

variable {x₀ : L}

@[simp] theorem consChain_zero {m : ℕ} (e : Fin m ↪o Upper x₀) : consChain x₀ e 0 = x₀ :=
  show (Fin.cons x₀ (fun i => (e i).1) : Fin (m + 1) → L) 0 = x₀ from Fin.cons_zero _ _

@[simp] theorem consChain_succ {m : ℕ} (e : Fin m ↪o Upper x₀) (i : Fin m) :
    consChain x₀ e i.succ = (e i).1 :=
  show (Fin.cons x₀ (fun i => (e i).1) : Fin (m + 1) → L) i.succ = (e i).1 from Fin.cons_succ _ _ _

theorem consChain_injective {m : ℕ} :
    Function.Injective (consChain x₀ : (Fin m ↪o Upper x₀) → Fin (m + 1) ↪o L) :=
  fun e e' h => DFunLike.ext _ _ fun i => Subtype.ext (by
    simpa only [consChain_succ] using DFunLike.congr_fun h i.succ)

theorem consChain_ne {x₁ : L} (hne : x₀ ≠ x₁) {m : ℕ} (e : Fin m ↪o Upper x₀)
    (e' : Fin m ↪o Upper x₁) : consChain x₀ e ≠ consChain x₁ e' := fun h => hne (by
  simpa only [consChain_zero] using DFunLike.congr_fun h 0)

/-- The tail of a chain whose least element is `x₀`, as a chain of `(x₀, ·)`. -/
def tailChain {m : ℕ} (c : Fin (m + 1) ↪o L) (h : c 0 = x₀) : Fin m ↪o Upper x₀ :=
  OrderEmbedding.ofStrictMono (fun i => ⟨c i.succ, h ▸ c.strictMono (Fin.succ_pos i)⟩)
    fun _ _ hij => c.strictMono (Fin.succ_lt_succ_iff.2 hij)

theorem consChain_tailChain {m : ℕ} (c : Fin (m + 1) ↪o L) (h : c 0 = x₀) :
    consChain x₀ (tailChain c h) = c :=
  DFunLike.ext _ _ fun i => by
    cases i using Fin.cases with
    | zero => rw [consChain_zero, h]
    | succ i => rw [consChain_succ]; rfl

/-- Deleting the least element `x₀` of `x₀ :: e` gives `e` back, as a chain of `L`. -/
theorem face_consChain_zero {m : ℕ} (e : Fin m ↪o Upper x₀) :
    face (consChain x₀ e) 0 = e.trans (OrderEmbedding.subtype _) :=
  DFunLike.ext _ _ fun i => by
    simp only [face, RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply,
      Fin.succAbove_zero, consChain_succ, OrderEmbedding.subtype_apply]

/-- Deleting any other element commutes with prepending `x₀`. -/
theorem face_consChain_succ {m : ℕ} (e : Fin (m + 1) ↪o Upper x₀) (i : Fin (m + 1)) :
    face (consChain x₀ e) i.succ = consChain x₀ (face e i) :=
  DFunLike.ext _ _ fun k => by
    cases k using Fin.cases with
    | zero =>
      simp only [face, RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply,
        Fin.succ_succAbove_zero, consChain_zero]
    | succ k =>
      simp only [face, RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply,
        Fin.succ_succAbove_succ, consChain_succ]

variable (x₀) in
/-- `cons_{x₀}`: prepend `x₀`, `C_m((x₀, ·)) → C_{m+1}(L)`. -/
noncomputable def consMap (m : ℕ) : Chains (Upper x₀) m →ₗ[ℂ] Chains L (m + 1) :=
  Finsupp.lmapDomain ℂ ℂ (consChain x₀)

variable (x₀) in
/-- `strip_{x₀}`: `C_{m+1}(L) → C_m((x₀, ·))`, sending a chain with least element `x₀` to its
tail and every other chain to `0`. As a map of coefficient functions it is
`w ↦ (e ↦ w (x₀ :: e))`. -/
noncomputable def strip (m : ℕ) : Chains L (m + 1) →ₗ[ℂ] Chains (Upper x₀) m :=
  Finsupp.lcomapDomain (consChain x₀) consChain_injective

theorem strip_apply {m : ℕ} (w : Chains L (m + 1)) (e : Fin m ↪o Upper x₀) :
    DFunLike.coe (F := (Fin m ↪o Upper x₀) →₀ ℂ) (strip x₀ m w) e =
      DFunLike.coe (F := (Fin (m + 1) ↪o L) →₀ ℂ) w (consChain x₀ e) :=
  rfl

theorem consMap_single {m : ℕ} (e : Fin m ↪o Upper x₀) :
    consMap x₀ m (Chains.single _ e) = Chains.single L (consChain x₀ e) :=
  Finsupp.mapDomain_single

/-- (vi) `strip_{x₀} ∘ cons_{x₀} = id`. -/
theorem strip_cons {m : ℕ} (x : Chains (Upper x₀) m) : strip x₀ m (consMap x₀ m x) = x := by
  refine Finsupp.ext fun e => ?_
  rw [strip_apply]
  exact Finsupp.mapDomain_apply consChain_injective _ _

/-- (vi) `strip_{x₁} ∘ cons_{x₀} = 0` for `x₁ ≠ x₀`. -/
theorem strip_cons_of_ne {x₁ : L} (hne : x₀ ≠ x₁) {m : ℕ} (x : Chains (Upper x₀) m) :
    strip x₁ m (consMap x₀ m x) = 0 := by
  refine Finsupp.ext fun e => ?_
  rw [strip_apply]
  exact Finsupp.mapDomain_notin_range _ _ fun ⟨e', he'⟩ => consChain_ne hne e' e he'

theorem strip_single_of_ne {m : ℕ} (c : Fin (m + 1) ↪o L) (h : c 0 ≠ x₀) :
    strip x₀ m (Chains.single L c) = 0 := by
  classical
  refine Finsupp.ext fun e => ?_
  rw [strip_apply]
  change Finsupp.single c (1 : ℂ) (consChain x₀ e) = 0
  rw [Finsupp.single_apply, if_neg fun he => h (by rw [he, consChain_zero])]

/-- The boundary of `x₀ :: e`: the face at `0` is `e`, and the others are `x₀ :: (faces of e)`
with the sign flipped. -/
theorem bd_single_consChain {m : ℕ} (e : Fin (m + 1) ↪o Upper x₀) :
    bd L (m + 1) (Chains.single L (consChain x₀ e)) =
      Chains.single L (e.trans (OrderEmbedding.subtype _)) -
        consMap x₀ m (bd (Upper x₀) m (Chains.single _ e)) := by
  rw [bd_single, Fin.sum_univ_succ, face_consChain_zero, bd_single, map_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  simp only [face_consChain_succ, Fin.val_zero, pow_zero, one_smul, map_smul, consMap_single,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul]

/-- (iv) `strip_{x₀} ∘ ∂ = −∂ ∘ strip_{x₀}`, for `x₀` minimal. -/
theorem strip_bd (hx₀ : IsMin x₀) (m : ℕ) (x : Chains L (m + 2)) :
    strip x₀ m (bd L (m + 1) x) = -bd (Upper x₀) m (strip x₀ (m + 1) x) := by
  have key : strip x₀ m ∘ₗ bd L (m + 1) = -(bd (Upper x₀) m ∘ₗ strip x₀ (m + 1)) := by
    refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
    change strip x₀ m (bd L (m + 1) (Chains.single L c)) =
      -bd (Upper x₀) m (strip x₀ (m + 1) (Chains.single L c))
    by_cases h : c 0 = x₀
    · obtain ⟨e, rfl⟩ : ∃ e, consChain x₀ e = c := ⟨_, consChain_tailChain c h⟩
      rw [bd_single_consChain, map_sub, strip_cons, ← consMap_single, strip_cons,
        strip_single_of_ne _ (ne_of_gt (e 0).2), zero_sub]
    · rw [strip_single_of_ne c h, map_zero, neg_zero, bd_single, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, strip_single_of_ne _ fun h' => h ?_, smul_zero]
      have hle : c 0 ≤ face c i 0 := c.monotone (Fin.zero_le _)
      exact le_antisymm (h' ▸ hle) (hx₀ (h' ▸ hle))
  exact LinearMap.congr_fun key x

/-- (v) A chain of `L` killed by every `strip_{x₀}`, `x₀ ∈ A`, is the pushforward of a chain of
`L ∖ A`: by minimality, an element of `A` can only be the least element of a chain. -/
theorem mem_range_of_strip_eq_zero (A : Set L) (hA : ∀ x ∈ A, IsMin x) (m : ℕ)
    (w : Chains L (m + 1)) (hw : ∀ x ∈ A, strip x m w = 0) :
    w ∈ LinearMap.range (chainMapEmb (OrderEmbedding.subtype fun x => x ∉ A) (m + 1)) := by
  have hsupp : ∀ c ∈ (w : (Fin (m + 1) ↪o L) →₀ ℂ).support, ∀ k, c k ∉ A := by
    intro c hc k hk
    have hle : c 0 ≤ c k := c.monotone (Fin.zero_le _)
    have h0 : c 0 = c k := le_antisymm hle (hA _ hk hle)
    have := congrArg (fun f : Chains (Upper (c 0)) m =>
      DFunLike.coe (F := (Fin m ↪o Upper (c 0)) →₀ ℂ) f (tailChain c rfl)) (hw (c 0) (h0 ▸ hk))
    simp only [strip_apply, consChain_tailChain] at this
    exact Finsupp.mem_support_iff.1 hc this
  let f : (Fin (m + 1) ↪o {x : L // x ∉ A}) → Fin (m + 1) ↪o L :=
    fun c => c.trans (OrderEmbedding.subtype _)
  have hf : Function.Injective f := trans_injective _
  refine ⟨Finsupp.comapDomain f w hf.injOn, ?_⟩
  refine Finsupp.mapDomain_comapDomain f hf w fun c hc => ?_
  exact ⟨OrderEmbedding.ofStrictMono (fun k => ⟨c k, hsupp c hc k⟩) fun _ _ h => c.strictMono h,
    rfl⟩

/-! ### Proposition C -/

/-- **Proposition C**, general form (`notes/lean_js_route.md` §3.2). Let `A` be a finite set of
minimal elements of `L`. If `L ∖ A` is acyclic in degree `d`, and for every `x₀ ∈ A` the strip
of every `d`-cycle of `L` is a boundary in `(x₀, ·)`, then `H̃_d(Δ(L)) = 0`. -/
theorem propC_core (A : Set L) (hAf : A.Finite) (hA : ∀ x ∈ A, IsMin x) (d : ℕ)
    (hQ : Subsingleton (redHom {x : L // x ∉ A} d))
    (hU : ∀ x ∈ A, ∀ z : Chains L (d + 1), bd L d z = 0 →
      strip x d z ∈ LinearMap.range (bd (Upper x) d)) :
    Subsingleton (redHom L d) := by
  classical
  have := hAf.fintype
  rw [subsingleton_redHom_iff]
  intro z hz
  choose e he using fun x : A => hU x.1 x.2 z hz
  -- `w = z + ∑_x ∂ cons_x e_x` has no chain meeting `A`
  set w := z + ∑ x : A, bd L (d + 1) (consMap x.1 (d + 1) (e x)) with hw
  have hstrip : ∀ y (hy : y ∈ A), strip y d w = 0 := by
    intro y hy
    rw [hw, map_add, map_sum, Finset.sum_eq_single ⟨y, hy⟩, strip_bd (hA y hy), strip_cons,
      add_neg_eq_zero]
    · exact (he ⟨y, hy⟩).symm
    · rintro x - hxy
      rw [strip_bd (hA y hy), strip_cons_of_ne (fun h => hxy (Subtype.ext h)), map_zero, neg_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hwc : bd L d w = 0 := by
    rw [hw, map_add, hz, zero_add, map_sum]
    exact Finset.sum_eq_zero fun x _ => by
      rw [← LinearMap.comp_apply, bd_comp_bd', LinearMap.zero_apply]
  obtain ⟨q, hq⟩ := mem_range_of_strip_eq_zero A hA d w hstrip
  have hqc : bd _ d q = 0 := chainMapEmb_injective (OrderEmbedding.subtype fun x => x ∉ A) d
    (by rw [← bd_chainMapEmb_apply, hq, hwc, map_zero])
  obtain ⟨r, hr⟩ := (subsingleton_redHom_iff d).1 hQ q hqc
  refine ⟨chainMapEmb (OrderEmbedding.subtype fun x => x ∉ A) (d + 2) r -
    ∑ x : A, consMap x.1 (d + 1) (e x), ?_⟩
  rw [map_sub, bd_chainMapEmb_apply, hr, hq, map_sum, hw, add_sub_cancel_right]

/-- **Proposition C**, `d ≥ 1`: if `L ∖ A` is acyclic in degree `m + 1` and
`H̃_m((x₀, ·)) = 0` for every `x₀ ∈ A`, then `H̃_{m+1}(Δ(L)) = 0`. -/
theorem propC_succ (A : Set L) (hAf : A.Finite) (hA : ∀ x ∈ A, IsMin x) (m : ℕ)
    (hQ : Subsingleton (redHom {x : L // x ∉ A} (m + 1)))
    (hU : ∀ x ∈ A, Subsingleton (redHom (Upper x) m)) :
    Subsingleton (redHom L (m + 1)) :=
  propC_core A hAf hA (m + 1) hQ fun x hx z hz =>
    (subsingleton_redHom_iff m).1 (hU x hx) _
      (by rw [← neg_eq_zero, ← strip_bd (hA x hx), hz, map_zero])

/-- **Proposition C**, `d = 0`: if `L ∖ A` is acyclic in degree `0` and every `(x₀, ·)`,
`x₀ ∈ A`, is nonempty, then `H̃_0(Δ(L)) = 0`. -/
theorem propC_zero (A : Set L) (hAf : A.Finite) (hA : ∀ x ∈ A, IsMin x)
    (hQ : Subsingleton (redHom {x : L // x ∉ A} 0)) (hU : ∀ x ∈ A, Nonempty (Upper x)) :
    Subsingleton (redHom L 0) :=
  propC_core A hAf hA 0 hQ fun x hx _ _ => by
    have := hU x hx
    rw [range_bd_zero]
    exact Submodule.mem_top

end Strip

/-! ### The decomposition at `π_a` -/

section AtPa

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] {a : α}

theorem pab_self (a : α) : pab a a = ⊥ := by
  ext u v
  rw [pab_apply, Setoid.bot_def]
  grind

/-- A partition below `π_a` is `π_ab` only if it is `0̂` (since `π_ab ∧ π_a = 0̂`). -/
theorem eq_bot_of_le_pa {s : Setoid α} {b : α} (hs : s ≤ pa a) (h : s = pab a b) : s = ⊥ :=
  calc s = s ⊓ pa a := (inf_eq_left.2 hs).symm
    _ = ⊥ := by rw [h, pab_inf_pa]

theorem pa_ne_bot (hn : 3 ≤ Fintype.card α) : pa a ≠ ⊥ := by
  have h2 : 2 ≤ (univ.erase a).card := by rw [card_erase_of_mem (mem_univ a), card_univ]; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h2
  rw [mem_erase] at hu hv
  intro h
  have : pa a u v := (pa_apply a u v).2 ⟨fun h' => absurd h' hu.1, fun h' => absurd h' hv.1⟩
  rw [h, Setoid.bot_def] at this
  exact huv this

theorem pa_ne_top (hn : 2 ≤ Fintype.card α) : pa a ≠ ⊤ := by
  obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card hn a
  intro h
  have : pa a a u := by rw [h, Setoid.top_def]; trivial
  exact hu (((pa_apply a a u).1 this).1 rfl)

/-- `π_a` as an element of the proper part (`n ≥ 3`, `a` minimal). -/
def paP (ha : ∀ u, u ≤ a → u = a) (hn : 3 ≤ Fintype.card α) : ProperOP α :=
  ⟨pa a, isOrderPreserving_pa ha, pa_ne_bot hn, pa_ne_top (by omega)⟩

variable (a) in
/-- `A = {π_ab}`: the elements of `\widehat{OP(P)}` of the form `π_ab`. (Only `b ≠ a` occurs,
since `π_aa = 0̂`.) -/
def Aset : Set (ProperOP α) := {x | ∃ b, x.1 = pab a b}

variable (a) in
/-- `Q = \widehat{OP(P)} ∖ A`: the proper order-preserving partitions other than the `π_ab`. -/
abbrev Q := {x : ProperOP α // x ∉ Aset a}

theorem not_mem_Aset_iff (x : ProperOP α) : x ∉ Aset a ↔ ∀ b, x.1 ≠ pab a b := by
  simp [Aset]

theorem finite_Aset : (Aset a).Finite :=
  (Set.finite_range fun b : {b : α // IsOrderPreserving (pab a b) ∧ pab a b ≠ ⊥ ∧ pab a b ≠ ⊤} =>
    (⟨pab a b.1, b.2⟩ : ProperOP α)).subset (by
      rintro ⟨s, hs⟩ ⟨b, hb⟩
      change s = pab a b at hb
      subst hb
      exact ⟨⟨b, hs⟩, rfl⟩)

/-- §3.2 (ii): each `π_ab` is minimal in `\widehat{OP(P)}`. -/
theorem pab_minimal {x : ProperOP α} (hx : x ∈ Aset a) : IsMin x := by
  obtain ⟨b, hb⟩ := hx
  intro y hy
  have hy' : y.1 ⊓ pa a = ⊥ := le_bot_iff.1 (calc
    y.1 ⊓ pa a ≤ x.1 ⊓ pa a := inf_le_inf_right _ hy
    _ = ⊥ := by rw [hb, pab_inf_pa])
  rcases inf_pa_eq_bot_iff'.1 hy' with h | ⟨b', hb', h⟩
  · exact absurd h y.2.2.1
  · have h1 : pab a b' a b' := by rw [pab_apply]; grind
    have h2 : x.1 a b' := hy (show y.1 a b' from h ▸ h1)
    rw [hb, pab_apply] at h2
    have hbb : b' = b := by grind
    exact le_of_eq (Subtype.ext (by rw [hb, h, hbb]))

theorem inf_pa_ne_bot (x : Q a) : x.1.1 ⊓ pa a ≠ ⊥ := by
  rw [Ne, inf_pa_eq_bot_iff']
  rintro (h | ⟨b, -, h⟩)
  · exact x.1.2.2.1 h
  · exact x.2 ⟨b, h⟩

/-- §3.2 (i): `x ↦ x ∧ π_a` is a cone retraction of `Q` with apex `π_a` (the hypotheses of
Lemma K). -/
def coneQ (ha : ∀ u, u ≤ a → u = a) (hn : 3 ≤ Fintype.card α) : ConeRetraction (Q a) where
  t := ⟨paP ha hn, fun ⟨_, hb⟩ => (paP ha hn).2.2.1 (eq_bot_of_le_pa le_rfl hb)⟩
  p x := ⟨⟨x.1.1 ⊓ pa a, isOrderPreserving_inf x.1.2.1 (isOrderPreserving_pa ha),
      inf_pa_ne_bot x, fun h => (paP ha hn).2.2.2
        (top_le_iff.1 (h ▸ inf_le_right : (⊤ : Setoid α) ≤ pa a))⟩,
    fun ⟨_, hb⟩ => inf_pa_ne_bot x (eq_bot_of_le_pa inf_le_right hb)⟩
  monotone x y h := show x.1.1 ⊓ pa a ≤ y.1.1 ⊓ pa a from inf_le_inf_right (pa a) h
  le_self x := show x.1.1 ⊓ pa a ≤ x.1.1 from inf_le_left
  le_t x := show x.1.1 ⊓ pa a ≤ pa a from inf_le_right
  eq_of_le _ h := Subtype.ext (Subtype.ext (inf_eq_left.2 h))

/-- `Q` is acyclic, by Lemma K. -/
theorem Q_acyclic (ha : ∀ u, u ≤ a → u = a) (hn : 3 ≤ Fintype.card α) (d : ℕ) :
    Subsingleton (redHom (Q a) d) :=
  (coneQ ha hn).exact_of_retract d

/-! ### Lemma U on the open interval: `(π_ab, 1̂) ≅ \widehat{OP(P/π_ab)}` -/

section LemmaU

variable {b : α} (hab : a ≠ b) (h : IsOrderPreserving (pab a b))

theorem comap_val_comap_proj (τ : Setoid (Contr a b h)) :
    (τ.comap (Contr.proj hab)).comap (Contr.val (h := h)) = τ := by
  ext u v
  change τ (Contr.proj hab u.val) (Contr.proj hab v.val) ↔ τ u v
  rw [Contr.proj_val, Contr.proj_val]

theorem comap_proj_comap_val {σ : Setoid α} (hσ : pab a b ≤ σ) :
    (σ.comap (Contr.val (h := h))).comap (Contr.proj hab) = σ := by
  ext x y
  change σ (Contr.proj (h := h) hab x).val (Contr.proj (h := h) hab y).val ↔ σ x y
  have hx := hσ (Contr.pab_proj (h := h) hab x)
  have hy := hσ (Contr.pab_proj (h := h) hab y)
  exact ⟨fun hxy => σ.trans (σ.symm hx) (σ.trans hxy hy),
    fun hxy => σ.trans hx (σ.trans hxy (σ.symm hy))⟩

theorem comap_proj_bot : (⊥ : Setoid (Contr a b h)).comap (Contr.proj hab) = pab a b := by
  ext x y
  change (⊥ : Setoid (Contr a b h)) (Contr.proj hab x) (Contr.proj hab y) ↔ pab a b x y
  rw [Setoid.bot_def]
  exact Contr.proj_eq_iff hab x y

theorem comap_val_bot : (⊥ : Setoid α).comap (Contr.val (h := h)) = ⊥ := by
  ext u v
  change (⊥ : Setoid α) u.val v.val ↔ (⊥ : Setoid (Contr a b h)) u v
  rw [Setoid.bot_def, Setoid.bot_def]
  exact Contr.val_injective.eq_iff

theorem comap_top' {β γ : Type*} (f : β → γ) : (⊤ : Setoid γ).comap f = ⊤ := by
  ext x y
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- **Lemma U** on the open interval (§3.2 (iii)): `σ ↦ σ/π_ab` is an order isomorphism from
`(π_ab, 1̂)` onto the proper part of `OP(P/π_ab)`, with inverse the pullback along
`P → P/π_ab`. -/
def upperIso : {y : ProperOP α // pab a b < y.1} ≃o ProperOP (Contr a b h) where
  toFun y := ⟨y.1.1.comap (Contr.val (h := h)),
    fun _ _ huv hvu => y.1.2.1 _ _ (reach_val_contr h y.2.le huv) (reach_val_contr h y.2.le hvu),
    fun he => y.2.ne (calc
      pab a b = (⊥ : Setoid (Contr a b h)).comap (Contr.proj hab) := (comap_proj_bot hab h).symm
      _ = (y.1.1.comap (Contr.val (h := h))).comap (Contr.proj hab) :=
        congrArg (Setoid.comap (Contr.proj hab)) he.symm
      _ = y.1.1 := comap_proj_comap_val hab h y.2.le),
    fun he => y.1.2.2.2 (calc
      y.1.1 = (y.1.1.comap (Contr.val (h := h))).comap (Contr.proj hab) :=
        (comap_proj_comap_val hab h y.2.le).symm
      _ = (⊤ : Setoid (Contr a b h)).comap (Contr.proj hab) := congrArg _ he
      _ = ⊤ := comap_top' _)⟩
  invFun τ := ⟨⟨τ.1.comap (Contr.proj hab), isOrderPreserving_comap_proj hab h τ.2.1,
      fun he => τ.2.2.1 (calc
        τ.1 = (τ.1.comap (Contr.proj hab)).comap (Contr.val (h := h)) :=
          (comap_val_comap_proj hab h τ.1).symm
        _ = (⊥ : Setoid α).comap (Contr.val (h := h)) := congrArg _ he
        _ = ⊥ := comap_val_bot h),
      fun he => τ.2.2.2 (calc
        τ.1 = (τ.1.comap (Contr.proj hab)).comap (Contr.val (h := h)) :=
          (comap_val_comap_proj hab h τ.1).symm
        _ = (⊤ : Setoid α).comap (Contr.val (h := h)) := congrArg _ he
        _ = ⊤ := comap_top' _)⟩,
    lt_of_le_of_ne
      (fun u v huv => by
        have : Contr.proj (h := h) hab u = Contr.proj hab v := (Contr.proj_eq_iff hab u v).2 huv
        change τ.1 (Contr.proj hab u) (Contr.proj hab v)
        rw [this])
      fun he => τ.2.2.1 (calc
        τ.1 = (τ.1.comap (Contr.proj hab)).comap (Contr.val (h := h)) :=
          (comap_val_comap_proj hab h τ.1).symm
        _ = ((⊥ : Setoid (Contr a b h)).comap (Contr.proj hab)).comap (Contr.val (h := h)) := by
          rw [comap_proj_bot hab h, he]
        _ = ⊥ := comap_val_comap_proj hab h ⊥)⟩
  left_inv y := Subtype.ext (Subtype.ext (comap_proj_comap_val hab h y.2.le))
  right_inv τ := Subtype.ext (comap_val_comap_proj hab h τ.1)
  map_rel_iff' {y y'} := by
    constructor
    · intro hle
      have : (y.1.1.comap (Contr.val (h := h))).comap (Contr.proj hab) ≤
          (y'.1.1.comap (Contr.val (h := h))).comap (Contr.proj hab) := fun _ _ huv => hle huv
      rwa [comap_proj_comap_val hab h y.2.le, comap_proj_comap_val hab h y'.2.le] at this
    · intro hle _ _ huv
      exact hle huv

end LemmaU

/-- The upper set of an element of `A` is the proper part of `OP(P/π_ab)`. -/
theorem exists_upperIso {x : ProperOP α} (hx : x ∈ Aset a) :
    ∃ b, ∃ (_ : a ≠ b) (h : IsOrderPreserving (pab a b)),
      Nonempty (Upper x ≃o ProperOP (Contr a b h)) := by
  obtain ⟨s, hs⟩ := x
  obtain ⟨b, hb⟩ := hx
  change s = pab a b at hb
  subst hb
  have hab : a ≠ b := fun e => hs.2.1 (by rw [← e, pab_self])
  exact ⟨b, hab, hs.1, ⟨upperIso hab hs.1⟩⟩

/-- **Proposition C** at `π_a`, `d ≥ 1` (`notes/lean_js_route.md` §3.2). Let `a` be minimal and
`n ≥ 3`. If `H̃_m(Δ(\widehat{OP(P/π_ab)})) = 0` for every `b ≠ a` with `π_ab ∈ OP(P)`, then
`H̃_{m+1}(Δ(\widehat{OP(P)})) = 0`. -/
theorem propC (ha : ∀ u, u ≤ a → u = a) (hn : 3 ≤ Fintype.card α) (m : ℕ)
    (hU : ∀ b (_ : a ≠ b) (h : IsOrderPreserving (pab a b)),
      Subsingleton (redHom (ProperOP (Contr a b h)) m)) :
    Subsingleton (redHom (ProperOP α) (m + 1)) :=
  propC_succ (Aset a) finite_Aset (fun _ hx => pab_minimal hx) m (Q_acyclic ha hn _)
    fun _ hx => by
      obtain ⟨b, hab, h, ⟨e⟩⟩ := exists_upperIso hx
      have := hU b hab h
      exact subsingleton_redHom_of_orderIso e.symm m

/-- **Proposition C** at `π_a`, `d = 0`: if every `(π_ab, 1̂)` is nonempty, then
`H̃_0(Δ(\widehat{OP(P)})) = 0`. -/
theorem propC_zero_pa (ha : ∀ u, u ≤ a → u = a) (hn : 3 ≤ Fintype.card α)
    (hU : ∀ b (_ : a ≠ b) (h : IsOrderPreserving (pab a b)), Nonempty (ProperOP (Contr a b h))) :
    Subsingleton (redHom (ProperOP α) 0) :=
  propC_zero (Aset a) finite_Aset (fun _ hx => pab_minimal hx) (Q_acyclic ha hn _)
    fun _ hx => by
      obtain ⟨b, hab, h, ⟨e⟩⟩ := exists_upperIso hx
      exact (hU b hab h).map e.symm

/-- The case `d = 0` for `n ≥ 4`: each `P/π_ab` has `n − 1 ≥ 3` points, so its proper part is
nonempty. -/
theorem redHom_zero_subsingleton (ha : ∀ u, u ≤ a → u = a) (hn : 4 ≤ Fintype.card α) :
    Subsingleton (redHom (ProperOP α) 0) :=
  propC_zero_pa ha (by omega) fun _ _ _ => properOP_nonempty (by rw [Contr.card_eq]; omega)

end AtPa

end PosetJKS
