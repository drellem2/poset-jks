import PosetJKS.OrderComplex

/-!
# Lattice structure of `OP(P)` and `OP(P)^g`; Weisner's theorem

Homology-free infrastructure for the Möbius side of the character identity
(`notes/poset_jks_theorem.tex`, Lemmas `lem:orbitquot`, `lem:lattice`, `lem:weisner`).

* `weisner`: Weisner's theorem `∑_{x ∨ a = 1̂} μ(0̂, x) = 0` for `a ≠ 0̂`, in a finite poset with
  `0̂`, `1̂` in which `x` and `a` have a least upper bound `j x` for every `x`. This avoids
  building a `Lattice` instance on `OP(P)^g`: only joins with the fixed element `a` are used.
* `isOrderPreserving_inf`: `OP(P)` is closed under the partition meet (Lemma `lem:lattice`(i)).
* `orbitSetoid g`: the partition `O_g` into `⟨g⟩`-orbits; it is order-preserving
  (Lemma `lem:orbitquot` for `K = ⟨g⟩` acting on `P`) and `g`-fixed (Lemma `lem:lattice`(ii)).
* `joinOrbit g s`: for `g`-fixed `s`, the partition join `s ∨ O_g`, whose blocks are the
  `⟨g⟩`-orbits of blocks of `s`. It is order-preserving and `g`-fixed when `s` is, so it is the
  join of `s` and `O_g` in `OP(P)^g` (Lemma `lem:lattice`(iii)).
* `joinOrbit_eq_top_iff`, `le_rel_of_joinOrbit_eq_top`: `s ∨ O_g = 1̂` iff `g` permutes the
  blocks of `s` transitively, and then every block is a union of components
  (Lemma `lem:lattice`(iv)).
* `sum_mu_joinOrbit_eq_top`: Weisner in `OP(P)^g` with `a = O_g`, for `g ≠ 1`:
  `∑_{x ∈ OP(P)^g, x ∨ O_g = 1̂} μ(0̂, x) = 0` (the first step of the recursion (W)).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Weisner's theorem -/

section Weisner

variable {L : Type*} [PartialOrder L] [Fintype L] [DecidableEq L] [LocallyFiniteOrder L]

/-- **Weisner's theorem** (Lemma `lem:weisner`). Let `L` be a finite poset with least element
`bot` and greatest element `top`, let `a ≠ bot`, and suppose every `x` has a least upper bound
`j x` with `a`. Then `∑_{x : j x = top} μ(bot, x) = 0`. -/
theorem weisner (bot top a : L) (hbot : ∀ x, bot ≤ x) (htop : ∀ x, x ≤ top) (ha : a ≠ bot)
    (j : L → L) (hj : ∀ x y, (x ≤ y ∧ a ≤ y) ↔ j x ≤ y) :
    ∑ x ∈ univ.filter (fun x => j x = top), IncidenceAlgebra.mu ℤ bot x = 0 := by
  classical
  set μ := IncidenceAlgebra.mu ℤ (α := L)
  -- `[j x = top] = ∑_{y ≥ x, y ≥ a} μ(y, top)`
  have h1 : ∀ x, (if j x = top then (1 : ℤ) else 0) =
      ∑ y, if x ≤ y ∧ a ≤ y then μ y top else 0 := by
    intro x
    rw [← IncidenceAlgebra.sum_Icc_mu_left, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y; simp [hj, htop]
  -- `∑_{x ≤ y} μ(bot, x) = [bot = y]`
  have h2 : ∀ y, (∑ x, if x ≤ y then μ bot x else 0) = if bot = y then 1 else 0 := by
    intro y
    rw [← IncidenceAlgebra.sum_Icc_mu_right, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x; simp [hbot]
  calc ∑ x ∈ univ.filter (fun x => j x = top), μ bot x
      = ∑ x, μ bot x * (if j x = top then 1 else 0) := by
        rw [Finset.sum_filter]; simp [mul_ite]
    _ = ∑ x, ∑ y, if x ≤ y ∧ a ≤ y then μ bot x * μ y top else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [h1, Finset.mul_sum]
        simp [mul_ite]
    _ = ∑ y, ∑ x, if x ≤ y ∧ a ≤ y then μ bot x * μ y top else 0 := Finset.sum_comm
    _ = ∑ y, if a ≤ y then (∑ x, if x ≤ y then μ bot x else 0) * μ y top else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hay : a ≤ y
        · rw [if_pos hay, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hxy : x ≤ y <;> simp [hxy, hay]
        · rw [if_neg hay]
          exact Finset.sum_eq_zero fun x _ => by simp [hay]
    _ = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [h2]
        by_cases hay : a ≤ y
        · rw [if_pos hay, if_neg, zero_mul]
          rintro rfl
          exact ha (le_antisymm hay (hbot a))
        · rw [if_neg hay]

end Weisner

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-! ### Reachability in the quotient digraph -/

/-- `b` is reachable from `a` in `P/π`, on elements: a path of steps `u ≤ v` or `u ~_π v`. -/
abbrev Reach (s : Setoid α) : α → α → Prop := Relation.ReflTransGen (opStep s)

theorem reach_mono {s t : Setoid α} (h : s ≤ t) {a b : α} (hab : Reach s a b) : Reach t a b :=
  hab.mono fun _ _ hu => hu.imp id fun hst => h hst

/-- `OP(P)` is closed under the partition meet (Lemma `lem:lattice`(i)). -/
theorem isOrderPreserving_inf {s t : Setoid α} (hs : IsOrderPreserving s)
    (ht : IsOrderPreserving t) : IsOrderPreserving (s ⊓ t) := fun x y hxy hyx =>
  ⟨hs x y (reach_mono inf_le_left hxy) (reach_mono inf_le_left hyx),
    ht x y (reach_mono inf_le_right hxy) (reach_mono inf_le_right hyx)⟩

/-! ### Powers of an automorphism -/

section Powers

variable (g : α ≃o α)

local notation "σ" => g.toEquiv

theorem orderOf_toEquiv_pos : 0 < orderOf σ := orderOf_pos σ

theorem monotone_pow (k : ℕ) : Monotone ⇑(σ ^ k) := by
  rw [Equiv.Perm.coe_pow]; exact g.monotone.iterate k

theorem pow_apply_add (k m : ℕ) (a : α) : (σ ^ k) ((σ ^ m) a) = (σ ^ (k + m)) a := by
  rw [pow_add, Equiv.Perm.mul_apply]

/-- `σ^k` is inverted by `σ^(o k - k)`, `o` the order of `σ`. -/
theorem pow_inv_apply (k : ℕ) (a : α) :
    (σ ^ (orderOf σ * k - k)) ((σ ^ k) a) = a := by
  rw [pow_apply_add, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k (orderOf_toEquiv_pos g)),
    pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]

theorem pow_inv_apply' (k : ℕ) (a : α) :
    (σ ^ k) ((σ ^ (orderOf σ * k - k)) a) = a := by
  rw [pow_apply_add, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left k (orderOf_toEquiv_pos g)),
    pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]

/-- If a reflexive, transitive, `σ`-invariant relation relates `a` to `σ^h a`, it also relates
`σ^h a` to `a` (iterate `o - 1` more times, `σ^{ho} = 1`). -/
theorem rel_back {R : α → α → Prop} (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hinv : ∀ k a b, R a b → R ((σ ^ k) a) ((σ ^ k) b)) {h : ℕ} {a : α}
    (hR : R a ((σ ^ h) a)) : R ((σ ^ h) a) a := by
  have hall : ∀ i, R a ((σ ^ (h * i)) a) := by
    intro i
    induction i with
    | zero => simpa using hrefl a
    | succ i ih =>
      refine htrans _ _ _ ih ?_
      have := hinv (h * i) _ _ hR
      rwa [pow_apply_add, ← mul_add_one] at this
  have := hinv h _ _ (hall (orderOf σ - 1))
  have e : 1 + (orderOf σ - 1) = orderOf σ := by have := orderOf_toEquiv_pos g; omega
  rwa [pow_apply_add, ← mul_one_add, e, pow_mul',
    pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply] at this

variable {g}

theorem rel_pow_of_fixed {s : Setoid α} (hs : actSetoid g s = s) (k : ℕ) (a b : α) :
    s ((σ ^ k) a) ((σ ^ k) b) ↔ s a b := by
  have h1 : ∀ a b, s (σ a) (σ b) ↔ s a b := by
    intro a b
    conv_lhs => rw [← hs]
    rw [actSetoid_apply]
    simp
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact (h1 _ _).trans (ih _ _)

theorem reach_pow {s : Setoid α} (hs : actSetoid g s = s) (k : ℕ) {a b : α} (h : Reach s a b) :
    Reach s ((σ ^ k) a) ((σ ^ k) b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ?_
    rcases hbc with hbc | hbc
    · exact Or.inl (monotone_pow g k hbc)
    · exact Or.inr ((rel_pow_of_fixed hs k _ _).2 hbc)

theorem reach_back {s : Setoid α} (hs : actSetoid g s = s) {h : ℕ} {a : α}
    (hR : Reach s a ((σ ^ h) a)) : Reach s ((σ ^ h) a) a :=
  rel_back g (fun _ => Relation.ReflTransGen.refl) (fun _ _ _ => Relation.ReflTransGen.trans)
    (fun k _ _ => reach_pow hs k) hR

end Powers

/-! ### The orbit partition `O_g` -/

section Orbit

variable (g : α ≃o α)

local notation "σ" => g.toEquiv

/-- The partition `O_g` of `α` into `⟨g⟩`-orbits. -/
def orbitSetoid : Setoid α where
  r a b := ∃ k : ℕ, (σ ^ k) a = b
  iseqv :=
    ⟨fun _ => ⟨0, rfl⟩,
     fun ⟨k, hk⟩ => ⟨orderOf σ * k - k, by rw [← hk, pow_inv_apply]⟩,
     fun ⟨k, hk⟩ ⟨m, hm⟩ => ⟨m + k, by rw [← hm, ← hk, pow_apply_add]⟩⟩

theorem orbitSetoid_apply (a b : α) : orbitSetoid g a b ↔ ∃ k : ℕ, (σ ^ k) a = b := Iff.rfl

theorem le_of_reach_orbit {a b : α} (h : Reach (orbitSetoid g) a b) : ∃ k : ℕ, a ≤ (σ ^ k) b := by
  induction h with
  | refl => exact ⟨0, le_rfl⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    rcases hbc with hbc | ⟨m, rfl⟩
    · exact ⟨k, hk.trans (monotone_pow g k hbc)⟩
    · refine ⟨k + (orderOf σ * m - m), ?_⟩
      rw [← pow_apply_add, pow_inv_apply]
      exact hk

/-- `O_g` is order-preserving (Lemma `lem:orbitquot`, `K = ⟨g⟩` acting on `P`). -/
theorem isOrderPreserving_orbitSetoid : IsOrderPreserving (orbitSetoid g) := by
  intro a b hab hba
  obtain ⟨k, hk⟩ := le_of_reach_orbit g hab
  obtain ⟨l, hl⟩ := le_of_reach_orbit g hba
  have h1 : a ≤ (σ ^ (k + l)) a := by
    rw [← pow_apply_add]; exact hk.trans (monotone_pow g k hl)
  have h2 : (σ ^ (k + l)) a ≤ a :=
    rel_back g (fun _ => le_rfl) (fun _ _ _ => le_trans) (fun k _ _ h => monotone_pow g k h) h1
  have heq : a = (σ ^ k) b := le_antisymm hk (by
    calc (σ ^ k) b ≤ (σ ^ k) ((σ ^ l) a) := monotone_pow g k hl
      _ = (σ ^ (k + l)) a := pow_apply_add g k l a
      _ ≤ a := h2)
  exact (orbitSetoid g).symm ⟨k, heq.symm⟩

/-- `O_g` is `g`-fixed. -/
theorem actSetoid_orbitSetoid : actSetoid g (orbitSetoid g) = orbitSetoid g := by
  ext a b
  rw [actSetoid_apply, orbitSetoid_apply, orbitSetoid_apply]
  have hcomm : ∀ (k : ℕ) (x : α), σ ((σ ^ k) x) = (σ ^ k) (σ x) := fun k x => by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_succ', pow_succ]
  have hs : ∀ x, g.symm x = g.toEquiv.symm x := fun _ => rfl
  simp only [hs]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := congrArg σ hk
    rwa [hcomm, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  · rintro ⟨k, rfl⟩
    refine ⟨k, g.toEquiv.injective ?_⟩
    rw [hcomm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- `O_g ≠ 0̂` for `g ≠ 1`. -/
theorem orbitSetoid_ne_bot (hg : g ≠ 1) : orbitSetoid g ≠ ⊥ := by
  intro h
  apply hg
  ext a
  have : orbitSetoid g a (σ a) := ⟨1, by simp⟩
  rw [h, Setoid.bot_def] at this
  exact this.symm

end Orbit

/-! ### The join `s ∨ O_g` of a `g`-fixed partition with the orbit partition -/

section Join

variable (g : α ≃o α) {s : Setoid α}

local notation "σ" => g.toEquiv

/-- For `g`-fixed `s`, the partition join `s ∨ O_g`: `a ~ b` iff `σ^k a ~_s b` for some `k`.
Its blocks are the unions of the `⟨g⟩`-orbits of blocks of `s`. -/
def joinOrbit (hs : actSetoid g s = s) : Setoid α where
  r a b := ∃ k : ℕ, s ((σ ^ k) a) b
  iseqv :=
    ⟨fun a => ⟨0, s.refl _⟩,
     fun {a b} ⟨k, hk⟩ => ⟨orderOf σ * k - k, by
       rw [← rel_pow_of_fixed hs (orderOf σ * k - k), pow_inv_apply] at hk
       exact s.symm hk⟩,
     fun {a b c} ⟨k, hk⟩ ⟨m, hm⟩ => ⟨m + k, by
       rw [← rel_pow_of_fixed hs m, pow_apply_add] at hk
       exact s.trans hk hm⟩⟩

variable {g}

theorem joinOrbit_apply (hs : actSetoid g s = s) (a b : α) :
    joinOrbit g hs a b ↔ ∃ k : ℕ, s ((σ ^ k) a) b := Iff.rfl

theorem le_joinOrbit (hs : actSetoid g s = s) : s ≤ joinOrbit g hs :=
  fun _ _ h => ⟨0, h⟩

theorem orbit_le_joinOrbit (hs : actSetoid g s = s) : orbitSetoid g ≤ joinOrbit g hs :=
  fun _ _ ⟨k, hk⟩ => ⟨k, hk ▸ s.refl _⟩

theorem joinOrbit_le (hs : actSetoid g s = s) {t : Setoid α} (hst : s ≤ t)
    (hot : orbitSetoid g ≤ t) : joinOrbit g hs ≤ t :=
  fun _ _ ⟨k, hk⟩ => t.trans (hot ⟨k, rfl⟩) (hst hk)

theorem actSetoid_joinOrbit (hs : actSetoid g s = s) :
    actSetoid g (joinOrbit g hs) = joinOrbit g hs := by
  have h1 : ∀ x, g.symm x = (σ ^ (orderOf σ * 1 - 1)) x := fun x => by
    apply g.toEquiv.injective
    have := pow_inv_apply' g 1 x
    rw [pow_one] at this
    rw [this]; exact g.apply_symm_apply x
  ext a b
  rw [actSetoid_apply, h1, h1, joinOrbit_apply, joinOrbit_apply]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← rel_pow_of_fixed hs (orderOf σ * 1 - 1), pow_apply_add, add_comm, ← pow_apply_add]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [pow_apply_add, add_comm, ← pow_apply_add, rel_pow_of_fixed hs]
    exact hk

/-- A path in `P/(s ∨ O_g)` lifts to a path in `P/s` ending in the `⟨g⟩`-orbit of the end. -/
theorem reach_of_reach_joinOrbit (hs : actSetoid g s = s) {a b : α}
    (h : Reach (joinOrbit g hs) a b) : ∃ k : ℕ, Reach s a ((σ ^ k) b) := by
  induction h with
  | refl => exact ⟨0, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    rcases hbc with hbc | ⟨m, hm⟩
    · exact ⟨k, hk.tail (Or.inl (monotone_pow g k hbc))⟩
    · -- `σ^m b ~_s c`, so `σ^k b ~_s σ^(k + o m - m) c`
      refine ⟨k + (orderOf σ * m - m), hk.tail (Or.inr ?_)⟩
      rw [← rel_pow_of_fixed hs (k + (orderOf σ * m - m)), ← pow_apply_add g k,
        ← pow_apply_add g k, pow_inv_apply, pow_apply_add] at hm
      exact hm

/-- `s ∨ O_g` is order-preserving if `s` is (Lemma `lem:lattice`(iii)). -/
theorem isOrderPreserving_joinOrbit (hs : actSetoid g s = s) (hop : IsOrderPreserving s) :
    IsOrderPreserving (joinOrbit g hs) := by
  intro a b hab hba
  obtain ⟨k, hk⟩ := reach_of_reach_joinOrbit hs hab
  obtain ⟨l, hl⟩ := reach_of_reach_joinOrbit hs hba
  have h1 : Reach s ((σ ^ k) b) ((σ ^ (k + l)) a) := by
    rw [← pow_apply_add]; exact reach_pow hs k hl
  have hloop : Reach s a ((σ ^ (k + l)) a) := hk.trans h1
  have hback := reach_back hs hloop
  have : s a ((σ ^ k) b) := hop _ _ hk (h1.trans hback)
  exact (joinOrbit g hs).symm ⟨k, s.symm this⟩

/-- `s ∨ O_g = 1̂` iff `⟨g⟩` is transitive on the blocks of `s`. -/
theorem joinOrbit_eq_top_iff (hs : actSetoid g s = s) :
    joinOrbit g hs = ⊤ ↔ ∀ a b, ∃ k : ℕ, s ((σ ^ k) a) b := by
  constructor
  · intro h a b
    have : joinOrbit g hs a b := by rw [h, Setoid.top_def]; trivial
    exact this
  · intro h
    ext a b
    rw [Setoid.top_def]
    exact ⟨fun _ => trivial, fun _ => h a b⟩

/-- If `s ∨ O_g = 1̂` and `s` is `g`-fixed, the blocks of `s` are unions of components:
`a ≤ b` implies `a ~_s b`. (The quotient `P/s` has a transitive group of automorphisms, so it
is an antichain; Lemma `lem:lattice`(iv).) -/
theorem rel_of_le_of_joinOrbit_eq_top (hs : actSetoid g s = s) (hop : IsOrderPreserving s)
    (htop : joinOrbit g hs = ⊤) {a b : α} (hab : a ≤ b) : s a b := by
  obtain ⟨k, hk⟩ := (joinOrbit_eq_top_iff hs).1 htop b a
  -- `σ^k b ~ a ≤ b`, so `b` reaches `σ^k b` and hence `a`
  have h1 : Reach s ((σ ^ k) b) b :=
    Relation.ReflTransGen.tail (b := a)
      (Relation.ReflTransGen.single (show opStep s _ a from Or.inr hk))
      (show opStep s a b from Or.inl hab)
  -- `b = σ^{o k - k} (σ^k b)`, so `rel_back` at `σ^k b` reverses `h1`
  have h1' : Reach s ((σ ^ k) b) ((σ ^ (orderOf σ * k - k)) ((σ ^ k) b)) := by
    rw [pow_inv_apply]; exact h1
  have h2 : Reach s b ((σ ^ k) b) := by
    have := rel_back g (fun _ => Relation.ReflTransGen.refl)
      (fun _ _ _ => Relation.ReflTransGen.trans) (fun k _ _ => reach_pow hs k) h1'
    rwa [pow_inv_apply] at this
  exact hop a b (Relation.ReflTransGen.single (Or.inl hab))
    (h2.trans (Relation.ReflTransGen.single (Or.inr hk)))

/-- Conversely, a `g`-fixed partition whose blocks are unions of components is
order-preserving: its quotient has no relations. -/
theorem isOrderPreserving_of_rel_of_le {t : Setoid α} (h : ∀ a b : α, a ≤ b → t a b) :
    IsOrderPreserving t := by
  intro a b hab hba
  clear hba
  induction hab with
  | refl => exact t.refl _
  | tail _ hbc ih =>
    rcases hbc with hbc | hbc
    · exact t.trans ih (h _ _ hbc)
    · exact t.trans ih hbc

end Join

/-! ### Weisner in `OP(P)^g` with `a = O_g` -/

section WeisnerFixed

variable (g : α ≃o α)

/-- `O_g ∈ OP(P)^g`. -/
def OPFixed.orbit : OPFixed α g :=
  ⟨orbitSetoid g, isOrderPreserving_orbitSetoid g, actSetoid_orbitSetoid g⟩

/-- The join `x ∨ O_g` in `OP(P)^g`. -/
def OPFixed.join (x : OPFixed α g) : OPFixed α g :=
  ⟨joinOrbit g x.2.2, isOrderPreserving_joinOrbit x.2.2 x.2.1, actSetoid_joinOrbit x.2.2⟩

theorem OPFixed.join_le_iff (x y : OPFixed α g) :
    (x ≤ y ∧ OPFixed.orbit g ≤ y) ↔ OPFixed.join g x ≤ y := by
  constructor
  · rintro ⟨h1, h2⟩
    exact joinOrbit_le x.2.2 h1 h2
  · intro h
    exact ⟨(le_joinOrbit x.2.2).trans h, (orbit_le_joinOrbit x.2.2).trans h⟩

open Classical in
/-- **Weisner's theorem in `OP(P)^g` with `a = O_g`** (first step of the recursion (W) in the
proof of Proposition `prop:Mside`): for `g ≠ 1`,
`∑_{x ∈ OP(P)^g, x ∨ O_g = 1̂} μ(0̂, x) = 0`. -/
theorem sum_mu_join_eq_top (hg : g ≠ 1) :
    have := Fintype.ofFinite (OPFixed α g)
    ∑ x ∈ univ.filter (fun x => OPFixed.join g x = OPFixed.top g),
      IncidenceAlgebra.mu ℤ (OPFixed.bot g) x = 0 := by
  intro _
  refine weisner (OPFixed.bot g) (OPFixed.top g) (OPFixed.orbit g) ?_ ?_ ?_ (OPFixed.join g)
    (OPFixed.join_le_iff g)
  · intro x a b hab
    rw [OPFixed.bot, Setoid.bot_def] at hab
    exact hab ▸ x.1.refl a
  · intro x a b _
    change (⊤ : Setoid α) a b
    rw [Setoid.top_def]; trivial
  · intro h
    exact orbitSetoid_ne_bot g hg (congrArg Subtype.val h)

end WeisnerFixed

end PosetJKS
