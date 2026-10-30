import PosetJKS.Basic

/-!
# `OP(P)`, the order complex of its proper part, and `H_P`

* A set partition of `α` is a `Setoid α`; Mathlib orders `Setoid α` by refinement
  (`r ≤ s` iff every `r`-related pair is `s`-related), so `⊥` is the discrete partition and `⊤`
  the one-block partition.
* `π` is *order-preserving* iff the quotient digraph `P/π` is acyclic. We state acyclicity as:
  if `x` and `y` reach each other along steps `a ≤ b` or `a ~_π b`, then `x ~_π y`. (A directed
  cycle through two distinct blocks gives such `x, y` in different blocks; conversely a mutual
  reachability between different blocks yields a closed walk through two distinct blocks, hence a
  directed cycle.)
* The order complex `Δ(L)` of a finite poset `L` has the chains of `L` as simplices. A chain
  with `m` elements is the same as an order embedding `Fin m ↪o L` (its increasing
  enumeration), so the oriented simplicial chain group in dimension `m - 1` is
  `(Fin m ↪o L) →₀ ℂ`, with boundary `∂c = ∑_i (-1)^i (c with its i-th element deleted)`.
  Taking `m = 0` (the empty chain) as degree `-1` gives the augmented complex, whose homology is
  reduced homology: `H̃_d = ker ∂_{d} / im ∂_{d+1}` where `∂_d` goes from `d+1`-element chains to
  `d`-element chains.
* `H_P = H̃_{n-3}(Δ(proper part of OP(P)); ℂ)`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Reduced simplicial homology of the order complex of a poset -/

section OrderComplex

variable (L : Type*) [PartialOrder L]

/-- Oriented chains of the order complex: formal `ℂ`-combinations of `m`-element chains
(simplices of dimension `m - 1`; `m = 0` is the empty simplex of the augmented complex). -/
def Chains (m : ℕ) := (Fin m ↪o L) →₀ ℂ

-- `Chains` is a `def` (not an `abbrev`) carrying the `Finsupp` group and module structures
-- directly; with an `abbrev`, instance synthesis for quotients of submodules of `Finsupp` fails
-- (the two `AddCommMonoid` paths are not unified at instance transparency).
noncomputable instance (m : ℕ) : AddCommGroup (Chains L m) := Finsupp.instAddCommGroup
noncomputable instance (m : ℕ) : Module ℂ (Chains L m) := Finsupp.module _ _

/-- The basis chain `[c]`. -/
noncomputable def Chains.single {m : ℕ} (c : Fin m ↪o L) : Chains L m := Finsupp.single c 1

variable {L} in
/-- The `i`-th face of an `(m+1)`-element chain: delete its `i`-th element. -/
def face {m : ℕ} (c : Fin (m + 1) ↪o L) (i : Fin (m + 1)) : Fin m ↪o L :=
  (Fin.succAboveOrderEmb i).trans c

/-- The boundary map `∂_m : C_m → C_{m-1}` of the augmented chain complex, from `(m+1)`-element
chains to `m`-element chains. -/
noncomputable def bd (m : ℕ) : Chains L (m + 1) →ₗ[ℂ] Chains L m :=
  Finsupp.linearCombination ℂ fun c => ∑ i : Fin (m + 1), ((-1 : ℂ) ^ (i : ℕ)) • Chains.single L (face c i)

/-- `d`-cycles: `ker ∂_d` (chains with `d+1` elements). -/
noncomputable abbrev cycles (d : ℕ) : Submodule ℂ (Chains L (d + 1)) := LinearMap.ker (bd L d)

/-- `d`-boundaries, as a submodule of the `d`-cycles. -/
noncomputable abbrev boundaries (d : ℕ) : Submodule ℂ (cycles L d) :=
  (LinearMap.range (bd L (d + 1))).comap (cycles L d).subtype

/-- Reduced homology `H̃_d(Δ(L); ℂ) = ker ∂_d / im ∂_{d+1}`. -/
noncomputable abbrev redHom (d : ℕ) := cycles L d ⧸ boundaries L d

/-! Functoriality in order isomorphisms (used for the `Aut(P)` action). -/

variable {L}

/-- An order isomorphism `φ : L ≃o L` acts on chains by pushing forward. -/
noncomputable def chainMap (φ : L ≃o L) (m : ℕ) : Chains L m →ₗ[ℂ] Chains L m :=
  Finsupp.lmapDomain ℂ ℂ fun c => c.trans φ.toOrderEmbedding

theorem chainMap_single (φ : L ≃o L) (m : ℕ) (c : Fin m ↪o L) (a : ℂ) :
    chainMap φ m (Finsupp.single c a) = Finsupp.single (c.trans φ.toOrderEmbedding) a := by
  exact Finsupp.mapDomain_single

theorem bd_chainMap (φ : L ≃o L) (m : ℕ) :
    bd L m ∘ₗ chainMap φ (m + 1) = chainMap φ m ∘ₗ bd L m := by
  refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
  change bd L m (chainMap φ (m + 1) (Finsupp.single c 1)) =
    chainMap φ m (bd L m (Finsupp.single c 1))
  rw [chainMap_single]
  unfold bd
  erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  rw [one_smul, one_smul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Chains.single, Chains.single, chainMap_single]
  rfl

theorem chainMap_mem_cycles (φ : L ≃o L) (d : ℕ) {z : Chains L (d + 1)} (hz : z ∈ cycles L d) :
    chainMap φ (d + 1) z ∈ cycles L d := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [← LinearMap.comp_apply, bd_chainMap, LinearMap.comp_apply, hz, map_zero]

/-- The action of `φ` on `d`-cycles. -/
noncomputable def cycleMap (φ : L ≃o L) (d : ℕ) : cycles L d →ₗ[ℂ] cycles L d :=
  (chainMap φ (d + 1)).restrict fun _ hz => chainMap_mem_cycles φ d hz

theorem boundaries_le_comap (φ : L ≃o L) (d : ℕ) :
    boundaries L d ≤ (boundaries L d).comap (cycleMap φ d) := by
  rintro z ⟨b, hb⟩
  refine ⟨chainMap φ (d + 2) b, ?_⟩
  change bd L (d + 1) (chainMap φ (d + 2) b) = chainMap φ (d + 1) z
  rw [← LinearMap.comp_apply, bd_chainMap, LinearMap.comp_apply, hb]
  rfl

/-- The action of `φ` on `H̃_d(Δ(L))`. -/
noncomputable def homMap (φ : L ≃o L) (d : ℕ) : redHom L d →ₗ[ℂ] redHom L d :=
  Submodule.mapQ _ _ (cycleMap φ d) (boundaries_le_comap φ d)

end OrderComplex

/-! ### Order-preserving partitions -/

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- One step of the quotient digraph `P/π`, viewed on elements: `a ≤ b` or `a ~_π b`. -/
def opStep (s : Setoid α) (a b : α) : Prop := a ≤ b ∨ s a b

/-- `π` is order-preserving: the quotient digraph `P/π` is acyclic. -/
def IsOrderPreserving (s : Setoid α) : Prop :=
  ∀ x y, Relation.ReflTransGen (opStep s) x y → Relation.ReflTransGen (opStep s) y x → s x y

variable (α) in
/-- The lattice `OP(P)` of order-preserving partitions, ordered by refinement. -/
abbrev OP := {s : Setoid α // IsOrderPreserving s}

variable (α) in
/-- The proper part of `OP(P)`: order-preserving partitions other than the discrete partition
`0̂ = ⊥` and the one-block partition `1̂ = ⊤`. -/
abbrev ProperOP := {s : Setoid α // IsOrderPreserving s ∧ s ≠ ⊥ ∧ s ≠ ⊤}

variable (α) in
/-- `H_P = H̃_{n-3}(Δ(\widehat{OP(P)}); ℂ)`. -/
noncomputable abbrev HP := redHom (ProperOP α) (Fintype.card α - 3)

/-! ### The action of `Aut(P)` -/

/-- `g ∈ Aut(P)` acts on partitions by `x ~_{gπ} y ↔ g⁻¹x ~_π g⁻¹y`. -/
def actSetoid (g : α ≃o α) (s : Setoid α) : Setoid α := Setoid.comap g.symm s

theorem actSetoid_apply (g : α ≃o α) (s : Setoid α) (x y : α) :
    actSetoid g s x y ↔ s (g.symm x) (g.symm y) := Iff.rfl

theorem actSetoid_mono (g : α ≃o α) {s t : Setoid α} (h : s ≤ t) :
    actSetoid g s ≤ actSetoid g t := fun _ _ hxy => h hxy

theorem actSetoid_actSetoid_symm (g : α ≃o α) (s : Setoid α) :
    actSetoid g (actSetoid g.symm s) = s := by
  ext x y; simp [actSetoid_apply]

theorem actSetoid_symm_actSetoid (g : α ≃o α) (s : Setoid α) :
    actSetoid g.symm (actSetoid g s) = s := by
  ext x y; simp [actSetoid_apply]

theorem actSetoid_bot (g : α ≃o α) : actSetoid g ⊥ = ⊥ := by
  ext x y; simp [actSetoid_apply]

theorem actSetoid_top (g : α ≃o α) : actSetoid g ⊤ = ⊤ := by
  ext x y; simp [actSetoid_apply, Setoid.top_def]

theorem reflTransGen_opStep_act (g : α ≃o α) (s : Setoid α) {x y : α}
    (h : Relation.ReflTransGen (opStep (actSetoid g s)) x y) :
    Relation.ReflTransGen (opStep s) (g.symm x) (g.symm y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ?_
    rcases hbc with hbc | hbc
    · exact Or.inl (g.symm.monotone hbc)
    · exact Or.inr hbc

theorem isOrderPreserving_act (g : α ≃o α) {s : Setoid α} (hs : IsOrderPreserving s) :
    IsOrderPreserving (actSetoid g s) := fun x y hxy hyx =>
  hs _ _ (reflTransGen_opStep_act g s hxy) (reflTransGen_opStep_act g s hyx)

/-- `Aut(P)` acts on the proper part of `OP(P)` by order automorphisms. -/
def actProper (g : α ≃o α) : ProperOP α ≃o ProperOP α where
  toFun s := ⟨actSetoid g s.1, isOrderPreserving_act g s.2.1,
    fun h => s.2.2.1 (by rw [← actSetoid_symm_actSetoid g s.1, h, actSetoid_bot]),
    fun h => s.2.2.2 (by rw [← actSetoid_symm_actSetoid g s.1, h, actSetoid_top])⟩
  invFun s := ⟨actSetoid g.symm s.1, isOrderPreserving_act g.symm s.2.1,
    fun h => s.2.2.1 (by rw [← actSetoid_actSetoid_symm g s.1, h, actSetoid_bot]),
    fun h => s.2.2.2 (by rw [← actSetoid_actSetoid_symm g s.1, h, actSetoid_top])⟩
  left_inv s := Subtype.ext (actSetoid_symm_actSetoid g s.1)
  right_inv s := Subtype.ext (actSetoid_actSetoid_symm g s.1)
  map_rel_iff' {s t} := by
    constructor
    · intro h
      have := actSetoid_mono g.symm (show actSetoid g s.1 ≤ actSetoid g t.1 from h)
      rwa [actSetoid_symm_actSetoid, actSetoid_symm_actSetoid] at this
    · intro h
      exact actSetoid_mono g (show s.1 ≤ t.1 from h)

/-- The action of `g ∈ Aut(P)` on `H_P`. -/
noncomputable def actHP (g : α ≃o α) : HP α →ₗ[ℂ] HP α :=
  homMap (actProper g) _

/-! ### The fixed-point lattice `OP(P)^g` and its Möbius invariant -/

theorem isOrderPreserving_bot : IsOrderPreserving (⊥ : Setoid α) := by
  intro x y hxy hyx
  have key : ∀ {a b}, Relation.ReflTransGen (opStep (⊥ : Setoid α)) a b → a ≤ b := by
    intro a b h
    induction h with
    | refl => exact le_rfl
    | tail _ hbc ih =>
      rcases hbc with hbc | hbc
      · exact ih.trans hbc
      · rw [Setoid.bot_def] at hbc; exact hbc ▸ ih
  rw [Setoid.bot_def]
  exact le_antisymm (key hxy) (key hyx)

theorem isOrderPreserving_top : IsOrderPreserving (⊤ : Setoid α) := by
  intro _ _ _ _
  rw [Setoid.top_def]; trivial

variable (α) in
/-- The fixed-point lattice `OP(P)^g`: order-preserving partitions fixed by `g`. -/
abbrev OPFixed (g : α ≃o α) := {s : Setoid α // IsOrderPreserving s ∧ actSetoid g s = s}

/-- `0̂ ∈ OP(P)^g`. -/
def OPFixed.bot (g : α ≃o α) : OPFixed α g := ⟨⊥, isOrderPreserving_bot, actSetoid_bot g⟩

/-- `1̂ ∈ OP(P)^g`. -/
def OPFixed.top (g : α ≃o α) : OPFixed α g := ⟨⊤, isOrderPreserving_top, actSetoid_top g⟩

/-- Non-degeneracy check: for `n ≥ 2`, `0̂ ≠ 1̂` in `OP(P)^g`, so `μ(OP(P)^g)` is a Möbius value
on a nontrivial interval. -/
theorem OPFixed.bot_ne_top (g : α ≃o α) (h : 2 ≤ Fintype.card α) :
    OPFixed.bot g ≠ OPFixed.top g := by
  intro he
  have hst : (⊥ : Setoid α) = ⊤ := congrArg Subtype.val he
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h
  have hr : (⊥ : Setoid α) a b := by rw [hst, Setoid.top_def]; trivial
  rw [Setoid.bot_def] at hr
  exact hab hr

instance (g : α ≃o α) : Finite (OPFixed α g) := by
  have : Finite (Setoid α) :=
    Finite.of_injective (fun s : Setoid α => fun x y => s x y) fun s t h => by
      ext x y; exact iff_of_eq (congrFun (congrFun h x) y)
  infer_instance

open Classical in
noncomputable instance (g : α ≃o α) : LocallyFiniteOrder (OPFixed α g) :=
  have := Fintype.ofFinite (OPFixed α g)
  Fintype.toLocallyFiniteOrder

open Classical in
/-- `μ(OP(P)^g) = μ_{OP(P)^g}(0̂, 1̂)`, computed by Mathlib's Möbius function of a locally finite
order. -/
noncomputable def muFixed (g : α ≃o α) : ℤ :=
  IncidenceAlgebra.mu ℤ (OPFixed.bot g) (OPFixed.top g)

end PosetJKS
