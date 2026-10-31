import PosetJKS.OrderComplex
import PosetJKS.MuOP
import PosetJKS.Hall
import PosetJKS.Hopf

/-!
# `tr(g | H_P) = (-1)^{n-3} μ(OP(P)^g)` from the vanishing of `H̃_d`, `d ≠ n - 3`

Lemma `lem:homchar` of `notes/poset_jks_theorem.tex`, by the note's route:

* the hand-rolled augmented chain complex of `OrderComplex.lean` is a complex
  (`bd_comp_bd'`), of finite-dimensional spaces for a finite poset, and `chainMap φ` is a chain
  map (`bd_chainMap`); the Hopf trace formula (`IsChainMap.hopf_trace`) applies to it;
* `tr(φ | C_m)` is the number of `φ`-fixed `m`-element chains (`trace_chainMap`), since
  `chainMap φ` permutes the basis of chains;
* a chain of the proper part of `OP(P)` is fixed by `g` iff each of its elements is, so the fixed
  `m`-element chains are the `m`-element chains of the proper part of `OP(P)^g`
  (`card_fixedChains`);
* P. Hall on `OP(P)^g` (`mu_bot_top_eq_chainSum`) turns the alternating fixed-chain count into
  `-μ(OP(P)^g)`;
* the lowest homology `C_0/∂C_1` vanishes because the proper part of `OP(P)` is nonempty for
  `n ≥ 3` (`π_a` for a minimal `a`, `properOP_nonempty`), and the vanishing of `H̃_d` for
  `d ≠ n - 3` is a hypothesis (`trace_HP_of_vanishing`); in `MainTheorem.lean` it is supplied by
  `jencaSarkoci_homology`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### The chain complex of a finite poset -/

section Complex

variable (L : Type*) [PartialOrder L]

instance [Finite L] (m : ℕ) : Finite (Fin m ↪o L) :=
  Finite.of_injective (fun c : Fin m ↪o L => (c : Fin m → L)) DFunLike.coe_injective

instance [Finite L] (m : ℕ) : FiniteDimensional ℂ (Chains L m) :=
  inferInstanceAs (Module.Finite ℂ ((Fin m ↪o L) →₀ ℂ))

theorem face_face' {m : ℕ} (c : Fin (m + 2) ↪o L) (i : Fin (m + 2)) (j : Fin (m + 1)) :
    face (face c i) j = face (face c (i.succAbove j)) (j.predAbove i) := by
  ext k
  simp only [face, RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  rw [Fin.succAbove_succAbove_succAbove_predAbove]

/-- `∂_m ∘ ∂_{m+1} = 0` (the same proof as `Test.bd_comp_bd`, which lives in the test file). -/
theorem bd_comp_bd' (m : ℕ) : bd L m ∘ₗ bd L (m + 1) = 0 := by
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
    rw [← face_face']
    simp only [one_mul, ← pow_add]
    rw [Fin.neg_one_pow_succAbove_add_predAbove, neg_smul, add_neg_cancel]
  · rintro ⟨i, j⟩ - -
    exact fun h => Fin.succAbove_ne i j (congrArg Prod.fst h)
  · rintro ⟨i, j⟩ -
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

variable {L}

theorem isChainMap_chainMap [Finite L] (φ : L ≃o L) : IsChainMap (bd L) (chainMap φ) :=
  bd_chainMap φ

/-- The induced map on `H̃_j` is the Hopf-formula homology map of the chain map `chainMap φ`. -/
theorem homMap_eq [Finite L] (φ : L ≃o L) (j : ℕ) :
    homMap φ j = (isChainMap_chainMap φ).homol j := rfl

open Classical in
/-- `tr(φ | C_m)` is the number of `φ`-fixed `m`-element chains. -/
theorem trace_chainMap [Finite L] (φ : L ≃o L) (m : ℕ) [Fintype (Fin m ↪o L)] :
    LinearMap.trace ℂ (Chains L m) (chainMap φ m) =
      ((univ.filter fun c : Fin m ↪o L => c.trans φ.toOrderEmbedding = c).card : ℂ) := by
  let b : Module.Basis (Fin m ↪o L) ℂ (Chains L m) := Finsupp.basisSingleOne
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Finset.card_filter]
  push_cast
  refine sum_congr rfl fun c _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [b, Finsupp.basisSingleOne_repr]
  erw [chainMap_single, Finsupp.single_apply]

theorem bd_zero_single' (c : Fin 1 ↪o L) (e : Fin 0 ↪o L) :
    bd L 0 (Chains.single L c) = Chains.single L e := by
  unfold bd Chains.single
  erw [Finsupp.linearCombination_single]
  rw [one_smul, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  congr 1
  ext i
  exact i.elim0

/-- For a nonempty poset, `∂_0` (the augmentation) is onto, so `C_0 / ∂C_1 = 0`. -/
theorem range_bd_zero [Nonempty L] : LinearMap.range (bd L 0) = ⊤ := by
  let x : L := Classical.arbitrary L
  let c : Fin 1 ↪o L := OrderEmbedding.ofStrictMono (fun _ => x) fun i j h => absurd h (by omega)
  let e : Fin 0 ↪o L := OrderEmbedding.ofStrictMono Fin.elim0 fun i => i.elim0
  have he : ∀ e' : Fin 0 ↪o L, e' = e := fun e' => by ext i; exact i.elim0
  rw [eq_top_iff]
  intro v _
  let v' : (Fin 0 ↪o L) →₀ ℂ := v
  refine ⟨(v' e) • Chains.single L c, ?_⟩
  rw [map_smul, bd_zero_single' c e]
  change (v' e) • Finsupp.single e (1 : ℂ) = v'
  ext e'
  rw [he e']
  simp

end Complex

/-! ### `OP(P)^g`: bounded, and its proper part is the fixed part of `\widehat{OP(P)}` -/

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- `OP(P)^g` is bounded by `0̂` and `1̂`. -/
@[reducible] def OPFixed.boundedOrder (g : α ≃o α) : BoundedOrder (OPFixed α g) where
  top := OPFixed.top g
  le_top s := le_top (a := s.1)
  bot := OPFixed.bot g
  bot_le s := bot_le (a := s.1)

variable (α) in
/-- The proper part of `OP(P)^g`. -/
abbrev ProperFixed (g : α ≃o α) := {x : OPFixed α g // x ≠ OPFixed.bot g ∧ x ≠ OPFixed.top g}

theorem fixedChains_equiv (g : α ≃o α) (m : ℕ) :
    Nonempty ({c : Fin m ↪o ProperOP α // c.trans (actProper g).toOrderEmbedding = c} ≃
      (Fin m ↪o ProperFixed α g)) := by
  have hfix : ∀ c : Fin m ↪o ProperOP α, c.trans (actProper g).toOrderEmbedding = c ↔
      ∀ i, actSetoid g (c i).1 = (c i).1 := by
    intro c
    constructor
    · intro h i
      exact congrArg Subtype.val (DFunLike.congr_fun h i)
    · intro h
      ext i : 1
      exact Subtype.ext (h i)
  refine ⟨
    { toFun := fun c => OrderEmbedding.ofStrictMono
        (fun i => ⟨⟨(c.1 i).1, (c.1 i).2.1, (hfix c.1).1 c.2 i⟩,
          fun h => (c.1 i).2.2.1 (congrArg Subtype.val h),
          fun h => (c.1 i).2.2.2 (congrArg Subtype.val h)⟩)
        fun i j hij => c.1.strictMono hij
      invFun := fun e => ⟨OrderEmbedding.ofStrictMono
        (fun i => ⟨(e i).1.1, (e i).1.2.1,
          fun h => (e i).2.1 (Subtype.ext h), fun h => (e i).2.2 (Subtype.ext h)⟩)
        (fun i j hij => e.strictMono hij), (hfix _).2 fun i => (e i).1.2.2⟩
      left_inv := fun c => by ext; rfl
      right_inv := fun e => by ext; rfl }⟩

open Classical in
/-- The `g`-fixed `m`-element chains of `\widehat{OP(P)}` are the `m`-element chains of the
proper part of `OP(P)^g`. -/
theorem card_fixedChains (g : α ≃o α) (m : ℕ) [Fintype (Fin m ↪o ProperOP α)] :
    (univ.filter fun c : Fin m ↪o ProperOP α => c.trans (actProper g).toOrderEmbedding = c).card =
      Nat.card (Fin m ↪o ProperFixed α g) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (fixedChains_equiv g m).some

/-- For `n ≥ 3` the proper part of `OP(P)` is nonempty: `π_a` for a minimal `a`. -/
theorem properOP_nonempty (hn : 3 ≤ Fintype.card α) : Nonempty (ProperOP α) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨a, -, ha'⟩ :=
    exists_minimal_of_wellFoundedLT (fun _ : α => True) ⟨Classical.arbitrary α, trivial⟩
  have ha : ∀ u, u ≤ a → u = a := fun u hu => le_antisymm hu (ha' trivial hu)
  -- two points other than `a`
  have h2 : 2 ≤ (univ.erase a).card := by rw [card_erase_of_mem (mem_univ a), card_univ]; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h2
  rw [mem_erase] at hu hv
  refine ⟨⟨pa a, isOrderPreserving_pa ha, fun h => huv ?_, fun h => ?_⟩⟩
  · have : pa a u v := (pa_apply a u v).2 ⟨fun h' => absurd h' hu.1, fun h' => absurd h' hv.1⟩
    rw [h, Setoid.bot_def] at this
    exact this
  · have : pa a a u := by rw [h, Setoid.top_def]; trivial
    exact hu.1 (((pa_apply a a u).1 this).1 rfl)

/-! ### Lemma `lem:homchar` -/

/-- `tr(g | H_P) = (-1)^{n-3} μ(OP(P)^g)`, given that `H̃_d(Δ(\widehat{OP(P)})) = 0` for
`d ≠ n - 3`. Hopf trace formula + P. Hall on `OP(P)^g`. -/
theorem trace_HP_of_vanishing (hn : 3 ≤ Fintype.card α)
    (hvan : ∀ d, d ≠ Fintype.card α - 3 → Subsingleton (redHom (ProperOP α) d)) (g : α ≃o α) :
    LinearMap.trace ℂ (HP α) (actHP g) = (-1 : ℂ) ^ (Fintype.card α - 3) * (muFixed g : ℂ) := by
  classical
  set n := Fintype.card α with hn_def
  have : Finite (Setoid α) :=
    Finite.of_injective (fun s : Setoid α => fun x y => s x y) fun s t h => by
      ext x y; exact iff_of_eq (congrFun (congrFun h x) y)
  have : Fintype (ProperOP α) := Fintype.ofFinite _
  have : Fintype (OPFixed α g) := Fintype.ofFinite _
  have : Nonempty (ProperOP α) := properOP_nonempty hn
  have hf := isChainMap_chainMap (actProper g)
  -- fixed-chain counts
  let N : ℕ → ℕ := fun m => Nat.card (Fin m ↪o ProperFixed α g)
  have htr : ∀ m,
      LinearMap.trace ℂ (Chains (ProperOP α) m) (chainMap (actProper g) m) = (N m : ℂ) := by
    intro m
    have : Fintype (Fin m ↪o ProperOP α) := Fintype.ofFinite _
    rw [trace_chainMap]
    norm_cast
    convert card_fixedChains g m
  have hN0 : ∀ m, Fintype.card (OPFixed α g) < m → N m = 0 := by
    intro m hm
    refine Nat.card_eq_zero.2 (Or.inl ⟨fun c => ?_⟩)
    have h1 := Fintype.card_le_of_injective _ c.injective
    have h2 : Fintype.card (ProperFixed α g) ≤ Fintype.card (OPFixed α g) :=
      Fintype.card_subtype_le _
    rw [Fintype.card_fin] at h1
    omega
  -- the length bound
  set K := Fintype.card (ProperOP α) + Fintype.card (OPFixed α g) + n + 1 with hK
  have : Subsingleton (Chains (ProperOP α) K) := by
    have : IsEmpty (Fin K ↪o ProperOP α) := ⟨fun c => by
      have := Fintype.card_le_of_injective _ c.injective
      rw [Fintype.card_fin] at this
      omega⟩
    exact inferInstanceAs (Subsingleton ((Fin K ↪o ProperOP α) →₀ ℂ))
  have hopf := hf.hopf_trace (bd_comp_bd' (ProperOP α)) K
  simp_rw [htr] at hopf
  -- the lowest homology vanishes
  have hbot : LinearMap.trace ℂ _ hf.homolBot = 0 := by
    have : Subsingleton (Chains (ProperOP α) 0 ⧸ LinearMap.range (bd (ProperOP α) 0)) := by
      rw [range_bd_zero]
      exact Submodule.Quotient.subsingleton_iff.2 rfl
    exact trace_eq_zero_of_subsingleton _
  -- only degree `n - 3` survives
  have hsum : ∑ j ∈ range K, (-1 : ℂ) ^ (j + 1) * LinearMap.trace ℂ _ (hf.homol j) =
      (-1 : ℂ) ^ (n - 3 + 1) * LinearMap.trace ℂ (HP α) (actHP g) := by
    rw [sum_eq_single (n - 3)]
    · rfl
    · intro j _ hj
      have := hvan j hj
      rw [trace_eq_zero_of_subsingleton, mul_zero]
    · intro h
      exact absurd (mem_range.2 (by omega)) h
  rw [hbot, zero_add, hsum] at hopf
  -- P. Hall on `OP(P)^g`
  letI := OPFixed.boundedOrder g
  have hall : muFixed g = ∑ m ∈ range (Fintype.card (OPFixed α g) + 1),
      (-1 : ℤ) ^ (m + 1) * (N m : ℤ) := by
    have := mu_bot_top_eq_chainSum (OPFixed α g) (OPFixed.bot_ne_top g (by omega))
    convert this using 1
  have hall' : (muFixed g : ℂ) = -∑ m ∈ range (K + 1), (-1 : ℂ) ^ m * (N m : ℂ) := by
    rw [hall, sum_subset (range_subset_range.2 (by omega : Fintype.card (OPFixed α g) + 1 ≤ K + 1))
      (fun m _ hm => by rw [hN0 m (by simpa using hm)]; simp)]
    push_cast
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun m _ => ?_
    ring
  rw [hall', hopf, pow_succ]
  have hs : ((-1 : ℂ) ^ (n - 3)) * (-1) ^ (n - 3) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-LinearMap.trace ℂ (HP α) (actHP g)) * hs

end PosetJKS
