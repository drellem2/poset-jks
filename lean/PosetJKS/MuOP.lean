import PosetJKS.Interval
import PosetJKS.Milestone

/-!
# `μ(OP(P)) = (-1)^{n-1} e_C(P)` without homology (Lemma `lem:small`)

Proof W of `notes/mu_op_elementary.md` (audited in `notes/audit_mu_op_elementary.md`), for every
finite poset `P` on `n ≥ 1` points, by induction on `n`. Fix a minimal element `a`.

* `weisner_dual`: the dual form of Weisner's theorem, `∑_{x ∧ c = 0̂} μ(x, 1̂) = 0` for `c ≠ 1̂`.
* `pa a` is `π_a = {{a}, P ∖ a}` and `pab a b` is `π_ab`, whose only non-singleton block is
  `{a, b}`. For `a` minimal, `π_a ∈ OP(P)`, and `x ∧ π_a = 0̂` iff `x = 0̂` or `x = π_ab`
  (Lemma M).
* `Contr a b h` is the quotient poset `P/π_ab`, realised on `P ∖ {b}` (the merged block is
  represented by `a`) with `u ≤ v` iff `v` is reachable from `u` in the quotient digraph.
* `mu_pab_top` (Lemma U at `π_ab`): `μ_{OP(P)}(π_ab, 1̂) = μ(OP(P/π_ab))`.
* `mu_op_rec` (Lemma D): `μ(OP(P)) = -∑_b μ(OP(P/π_ab))`, over `b ≠ a` with `π_ab ∈ OP(P)`.
* `eC_rec` (Lemma C, Jenča–Sarkoci's recursion): `e_C(P) = ∑_b e_C(P/π_ab)` over the same `b`.
  It is proved on the words of `B_P(a)`, one per cyclic class (`card_inB`): the letter after `a`
  is `b`, and deleting it is a bijection onto `∐_b B_{P/π_ab}(a)`.
* `mu_OP_eq` (Theorem A): `μ(OP(P)) = (-1)^{n-1} e_C(P)`.

No topology or homology is used: only finite sums, Möbius functions and words.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Weisner's theorem, dual form -/

section WeisnerDual

variable {L : Type*} [PartialOrder L] [Fintype L] [DecidableEq L] [LocallyFiniteOrder L]

/-- **Weisner's theorem, dual form.** Let `L` be a finite poset with least element `bot` and
greatest element `top`, let `c ≠ top`, and suppose every `x` has a greatest lower bound `m x`
with `c`. Then `∑_{x : m x = bot} μ(x, top) = 0`. -/
theorem weisner_dual (bot top c : L) (hbot : ∀ x, bot ≤ x) (htop : ∀ x, x ≤ top) (hc : c ≠ top)
    (m : L → L) (hm : ∀ x y, (y ≤ x ∧ y ≤ c) ↔ y ≤ m x) :
    ∑ x ∈ univ.filter (fun x => m x = bot), IncidenceAlgebra.mu ℤ x top = 0 := by
  classical
  set μ := IncidenceAlgebra.mu ℤ (α := L)
  -- `[m x = bot] = ∑_{y ≤ x, y ≤ c} μ(bot, y)`
  have h1 : ∀ x, (if m x = bot then (1 : ℤ) else 0) =
      ∑ y, if y ≤ x ∧ y ≤ c then μ bot y else 0 := by
    intro x
    have e : (if m x = bot then (1 : ℤ) else 0) = if bot = m x then 1 else 0 := by
      by_cases h : m x = bot
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [e, ← IncidenceAlgebra.sum_Icc_mu_right, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y; simp [hm, hbot]
  -- `∑_{x ≥ y} μ(x, top) = [y = top]`
  have h2 : ∀ y, (∑ x, if y ≤ x then μ x top else 0) = if y = top then 1 else 0 := by
    intro y
    rw [← IncidenceAlgebra.sum_Icc_mu_left, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x; simp [htop]
  calc ∑ x ∈ univ.filter (fun x => m x = bot), μ x top
      = ∑ x, μ x top * (if m x = bot then 1 else 0) := by
        rw [Finset.sum_filter]; simp [mul_ite]
    _ = ∑ x, ∑ y, if y ≤ x ∧ y ≤ c then μ bot y * μ x top else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
    _ = ∑ y, ∑ x, if y ≤ x ∧ y ≤ c then μ bot y * μ x top else 0 := Finset.sum_comm
    _ = ∑ y, if y ≤ c then μ bot y * (∑ x, if y ≤ x then μ x top else 0) else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hyc : y ≤ c
        · rw [if_pos hyc, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hyx : y ≤ x <;> simp [hyx, hyc]
        · rw [if_neg hyc]
          exact Finset.sum_eq_zero fun x _ => by simp [hyc]
    _ = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [h2]
        by_cases hyc : y ≤ c
        · rw [if_pos hyc, if_neg, mul_zero]
          rintro rfl
          exact hc (le_antisymm (htop c) hyc)
        · rw [if_neg hyc]

end WeisnerDual

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-! ### `OP(P)` as `OP(P)^1` -/

theorem actSetoid_one (s : Setoid α) : actSetoid (1 : α ≃o α) s = s := by
  ext x y; rfl

/-- An order-preserving partition, as an element of `OP(P) = OP(P)^1`. -/
def op1 (s : Setoid α) (hs : IsOrderPreserving s) : OPFixed α 1 := ⟨s, hs, actSetoid_one s⟩

/-! ### The partitions `π_a` and `π_ab` -/

/-- `π_a = {{a}, P ∖ a}`. -/
def pa (a : α) : Setoid α where
  r u v := (u = a ↔ v = a)
  iseqv := ⟨fun _ => Iff.rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

theorem pa_apply (a u v : α) : pa a u v ↔ (u = a ↔ v = a) := Iff.rfl

/-- `π_ab`: the only block that may have two elements is `{a, b}`. -/
def pab (a b : α) : Setoid α where
  r u v := u = v ∨ ((u = a ∨ u = b) ∧ (v = a ∨ v = b))
  iseqv := ⟨fun _ => Or.inl rfl, fun h => by grind, fun h1 h2 => by grind⟩

theorem pab_apply (a b u v : α) :
    pab a b u v ↔ u = v ∨ ((u = a ∨ u = b) ∧ (v = a ∨ v = b)) := Iff.rfl

variable {a : α}

/-- Nothing reaches a minimal element `a` in `P/π_a` except `a` itself. -/
theorem eq_of_reach_pa (ha : ∀ u, u ≤ a → u = a) {u v : α} (h : Reach (pa a) u v) (hv : v = a) :
    u = a := by
  induction h with
  | refl => exact hv
  | tail _ hbc ih =>
    rcases hbc with hbc | hbc
    · exact ih (ha _ (hv ▸ hbc))
    · exact ih ((pa_apply _ _ _).1 hbc |>.2 hv)

/-- For `a` minimal, `π_a ∈ OP(P)` (Lemma M(b)). -/
theorem isOrderPreserving_pa (ha : ∀ u, u ≤ a → u = a) : IsOrderPreserving (pa a) := by
  intro x y hxy hyx
  rw [pa_apply]
  exact ⟨fun hx => eq_of_reach_pa ha hyx hx, fun hy => eq_of_reach_pa ha hxy hy⟩

theorem inf_pa_eq_bot_iff {s : Setoid α} :
    s ⊓ pa a = ⊥ ↔ ∀ u v, s u v → u ≠ a → v ≠ a → u = v := by
  constructor
  · intro h u v huv hu hv
    have : (s ⊓ pa a) u v :=
      ⟨huv, by rw [pa_apply]; exact ⟨fun h => absurd h hu, fun h => absurd h hv⟩⟩
    rw [h, Setoid.bot_def] at this
    exact this
  · intro h
    ext u v
    rw [Setoid.bot_def]
    constructor
    · rintro ⟨huv, hp⟩
      rw [pa_apply] at hp
      by_cases hu : u = a
      · exact hu.trans (hp.1 hu).symm
      · exact h u v huv hu fun hv => hu (hp.2 hv)
    · rintro rfl; exact (s ⊓ pa a).refl u

theorem pab_inf_pa (b : α) : pab a b ⊓ pa a = ⊥ := by
  rw [inf_pa_eq_bot_iff]
  intro u v huv hu hv
  rw [pab_apply] at huv
  grind

theorem pab_ne_bot {b : α} (hab : a ≠ b) : pab a b ≠ ⊥ := by
  intro h
  have : pab a b a b := by rw [pab_apply]; grind
  rw [h, Setoid.bot_def] at this
  exact hab this

theorem pab_injective {b b' : α} (hb : b ≠ a) (h : pab a b = pab a b') : b = b' := by
  have : pab a b' a b := by rw [← h, pab_apply]; grind
  rw [pab_apply] at this
  grind

/-- Lemma M(b): `x ∧ π_a = 0̂` iff `x = 0̂` or `x = π_ab` for some `b ≠ a`. -/
theorem inf_pa_eq_bot_iff' {s : Setoid α} :
    s ⊓ pa a = ⊥ ↔ s = ⊥ ∨ ∃ b, b ≠ a ∧ s = pab a b := by
  constructor
  · intro h
    rw [inf_pa_eq_bot_iff] at h
    by_cases hs : s = ⊥
    · exact Or.inl hs
    right
    obtain ⟨u, v, huv, hne⟩ : ∃ u v, s u v ∧ u ≠ v := by
      by_contra hc
      push Not at hc
      exact hs (by ext u v; rw [Setoid.bot_def]; exact ⟨hc u v, fun h => h ▸ s.refl u⟩)
    -- one of `u, v` is `a`; the other is `b`
    obtain ⟨b, hb, hab⟩ : ∃ b, b ≠ a ∧ s a b := by
      by_cases hu : u = a
      · exact ⟨v, fun hv => hne (hu.trans hv.symm), hu ▸ huv⟩
      · by_cases hv : v = a
        · exact ⟨u, hu, hv ▸ s.symm huv⟩
        · exact absurd (h u v huv hu hv) hne
    refine ⟨b, hb, ?_⟩
    ext x y
    rw [pab_apply]
    constructor
    · intro hxy
      by_cases hxy' : x = y
      · exact Or.inl hxy'
      right
      have key : ∀ z, s a z → z = a ∨ z = b := fun z hz => by
        by_cases hza : z = a
        · exact Or.inl hza
        · exact Or.inr (h z b (s.trans (s.symm hz) hab) hza hb)
      by_cases hx : x = a
      · subst hx; exact ⟨Or.inl rfl, key y hxy⟩
      · by_cases hy : y = a
        · subst hy; exact ⟨key x (s.symm hxy), Or.inl rfl⟩
        · exact absurd (h x y hxy hx hy) hxy'
    · rintro (rfl | ⟨hx, hy⟩)
      · exact s.refl x
      · have hza : ∀ z, z = a ∨ z = b → s a z := fun z hz => by
          rcases hz with rfl | rfl
          · exact s.refl _
          · exact hab
        exact s.trans (s.symm (hza x hx)) (hza y hy)
  · rintro (rfl | ⟨b, _, rfl⟩)
    · exact bot_inf_eq _
    · exact pab_inf_pa b

/-! ### The quotient poset `P/π_ab` -/

/-- The quotient poset `P/π_ab` (for `π_ab ∈ OP(P)`), on the points other than `b`; `a` stands
for the block `{a, b}`. `u ≤ v` iff `v` is reachable from `u` in the quotient digraph. -/
def Contr (a b : α) (_h : IsOrderPreserving (pab a b)) : Type _ := {u : α // u ≠ b}

namespace Contr

variable {b : α} {h : IsOrderPreserving (pab a b)}

instance : Fintype (Contr a b h) := inferInstanceAs (Fintype {u : α // u ≠ b})
instance : DecidableEq (Contr a b h) := inferInstanceAs (DecidableEq {u : α // u ≠ b})

/-- The underlying point. -/
def val (u : Contr a b h) : α := Subtype.val (p := fun u : α => u ≠ b) u

theorem val_ne (u : Contr a b h) : u.val ≠ b := Subtype.property (p := fun u : α => u ≠ b) u

theorem val_injective : Function.Injective (val (h := h)) :=
  Subtype.val_injective (p := fun u : α => u ≠ b)

/-- A point other than `b`, as a point of `P/π_ab`. -/
def mk' (u : α) (hu : u ≠ b) : Contr a b h := (⟨u, hu⟩ : {u : α // u ≠ b})

@[simp] theorem val_mk' (u : α) (hu : u ≠ b) : (mk' (h := h) u hu).val = u := rfl

@[simp] theorem mk'_val (u : Contr a b h) : mk' u.val u.val_ne = u := rfl

instance : PartialOrder (Contr a b h) where
  le u v := Reach (pab a b) u.val v.val
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm u v h1 h2 := by
    apply val_injective
    have := h _ _ h1 h2
    rw [pab_apply] at this
    have := u.val_ne
    have := v.val_ne
    grind

theorem le_iff (u v : Contr a b h) : u ≤ v ↔ Reach (pab a b) u.val v.val := Iff.rfl

theorem card_eq : Fintype.card (Contr a b h) = Fintype.card α - 1 := by
  change Fintype.card {u : α // u ≠ b} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- The quotient map `P → P/π_ab` (`b ↦ a`). -/
def proj (hab : a ≠ b) (u : α) : Contr a b h := if hu : u = b then mk' a hab else mk' u hu

theorem proj_val (hab : a ≠ b) (u : Contr a b h) : proj hab u.val = u := by
  rw [proj, dif_neg u.val_ne]; rfl

theorem pab_proj (hab : a ≠ b) (u : α) : pab a b (proj (h := h) hab u).val u := by
  rw [proj]
  split_ifs with hu
  · rw [pab_apply, val_mk']; grind
  · exact (pab a b).refl u

theorem proj_eq_iff (hab : a ≠ b) (u v : α) :
    proj (h := h) hab u = proj hab v ↔ pab a b u v := by
  constructor
  · intro e
    have := congrArg val e
    exact (pab a b).trans ((pab a b).symm (pab_proj hab u)) (this ▸ pab_proj hab v)
  · intro huv
    rw [pab_apply] at huv
    unfold proj
    split_ifs with hu hv hv <;> grind

end Contr

/-! ### Lemma U at `π_ab`: `[π_ab, 1̂] ≅ OP(P/π_ab)` -/

section LemmaU

variable {b : α} (hab : a ≠ b) (h : IsOrderPreserving (pab a b))

theorem reach_proj {s : Setoid (Contr a b h)} {x y : α}
    (hxy : Reach (s.comap (Contr.proj hab)) x y) :
    Reach s (Contr.proj hab x) (Contr.proj hab y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    refine ih.tail ?_
    rcases hyz with hyz | hyz
    · left
      rw [Contr.le_iff]
      have h1 : opStep (pab a b) (Contr.proj (h := h) hab y).val y := Or.inr (Contr.pab_proj hab y)
      have h2 : opStep (pab a b) y z := Or.inl hyz
      have h3 : opStep (pab a b) z (Contr.proj (h := h) hab z).val :=
        Or.inr ((pab a b).symm (Contr.pab_proj hab z))
      exact ((Relation.ReflTransGen.single h1).tail h2).tail h3
    · exact Or.inr hyz

theorem isOrderPreserving_comap_proj {s : Setoid (Contr a b h)} (hs : IsOrderPreserving s) :
    IsOrderPreserving (s.comap (Contr.proj hab)) := fun _ _ hxy hyx =>
  hs _ _ (reach_proj hab h hxy) (reach_proj hab h hyx)

/-- Pull back along `P → P/π_ab`: `OP(P/π_ab) → [π_ab, 1̂]`. -/
def pullOP (τ : OPFixed (Contr a b h) 1) : OPFixed α 1 :=
  op1 (τ.1.comap (Contr.proj hab)) (isOrderPreserving_comap_proj hab h τ.2.1)

theorem reach_val_contr {σ : Setoid α} (hσ : pab a b ≤ σ) {u v : Contr a b h}
    (huv : Reach (σ.comap Contr.val) u v) : Reach σ u.val v.val := by
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hyz ih =>
    rcases hyz with hyz | hyz
    · exact ih.trans (reach_mono hσ hyz)
    · exact ih.tail (Or.inr hyz)

theorem pullOP_bot : pullOP hab h (OPFixed.bot 1) = op1 (pab a b) h := by
  apply Subtype.ext
  ext x y
  change (⊥ : Setoid (Contr a b h)) (Contr.proj hab x) (Contr.proj hab y) ↔ pab a b x y
  rw [Setoid.bot_def]
  exact Contr.proj_eq_iff hab x y

theorem pullOP_top : pullOP hab h (OPFixed.top 1) = OPFixed.top 1 := by
  apply Subtype.ext
  ext x y
  change (⊤ : Setoid (Contr a b h)) (Contr.proj hab x) (Contr.proj hab y) ↔ (⊤ : Setoid α) x y
  exact ⟨fun _ => trivial, fun _ => trivial⟩

include hab in
open Classical in
/-- **Lemma U** at `π_ab`: `μ_{OP(P)}(π_ab, 1̂) = μ(OP(P/π_ab))`. -/
theorem mu_pab_top :
    IncidenceAlgebra.mu ℤ (op1 (pab a b) h) (OPFixed.top 1) =
      muFixed (1 : Contr a b h ≃o Contr a b h) := by
  have hle : ∀ x y : OPFixed (Contr a b h) 1, pullOP hab h x ≤ pullOP hab h y ↔ x ≤ y := by
    intro x y
    constructor
    · intro hxy u v huv
      have := @hxy u.val v.val
      change x.1 (Contr.proj hab u.val) (Contr.proj hab v.val) →
        y.1 (Contr.proj hab u.val) (Contr.proj hab v.val) at this
      rw [Contr.proj_val, Contr.proj_val] at this
      exact this huv
    · intro hxy u v huv
      exact hxy huv
  have key := mu_eq_of_interval (pullOP hab h) (OPFixed.bot 1) (OPFixed.top 1)
    (fun x y _ _ _ _ => hle x y)
    (fun σ hσ _ => by
      rw [pullOP_bot] at hσ
      refine ⟨op1 (σ.1.comap Contr.val) (fun u v huv hvu =>
          σ.2.1 _ _ (reach_val_contr h hσ huv) (reach_val_contr h hσ hvu)),
        fun u v huv => by rw [OPFixed.bot, Setoid.bot_def] at huv; exact huv ▸ σ.1.refl _,
        fun u v _ => by change (⊤ : Setoid (Contr a b h)) u v; rw [Setoid.top_def]; trivial,
        ?_⟩
      apply Subtype.ext
      ext x y
      change σ.1 (Contr.proj hab x).val (Contr.proj hab y).val ↔ σ.1 x y
      have hx := hσ (Contr.pab_proj (h := h) hab x)
      have hy := hσ (Contr.pab_proj (h := h) hab y)
      exact ⟨fun hxy => σ.1.trans (σ.1.symm hx) (σ.1.trans hxy hy),
        fun hxy => σ.1.trans hx (σ.1.trans hxy (σ.1.symm hy))⟩)
    (OPFixed.top 1) (fun u v huv => by
      rw [OPFixed.bot, Setoid.bot_def] at huv; exact huv ▸ (OPFixed.top 1).1.refl _) le_rfl
  rw [pullOP_bot, pullOP_top] at key
  rw [key]
  rfl

end LemmaU

/-! ### Lemma D -/

variable (a) in
/-- The index set of Lemmas C and D: the `b ≠ a` with `π_ab ∈ OP(P)`. -/
abbrev Bset := {b : α // b ≠ a ∧ IsOrderPreserving (pab a b)}

open Classical in
/-- **Lemma D**: for `n ≥ 2` and `a` minimal, `μ(OP(P)) = -∑_b μ(OP(P/π_ab))`, the sum over
`b ≠ a` with `π_ab ∈ OP(P)`. Dual Weisner at the coatom `π_a`, then Lemma U. -/
theorem mu_op_rec (ha : ∀ u, u ≤ a → u = a) (h2 : 2 ≤ Fintype.card α) :
    muFixed (1 : α ≃o α) =
      -∑ b : Bset a, muFixed (1 : Contr a b.1 b.2.2 ≃o Contr a b.1 b.2.2) := by
  have := Fintype.ofFinite (OPFixed α 1)
  have hpa := isOrderPreserving_pa ha
  set c : OPFixed α 1 := op1 (pa a) hpa
  set m : OPFixed α 1 → OPFixed α 1 := fun x =>
    op1 (x.1 ⊓ pa a) (isOrderPreserving_inf x.2.1 hpa)
  have hbot : ∀ x : OPFixed α 1, OPFixed.bot 1 ≤ x := fun x u v huv => by
    rw [OPFixed.bot, Setoid.bot_def] at huv; exact huv ▸ x.1.refl u
  have htop : ∀ x : OPFixed α 1, x ≤ OPFixed.top 1 := fun x u v _ => by
    change (⊤ : Setoid α) u v; trivial
  have hc : c ≠ OPFixed.top 1 := by
    intro hct
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h2 a
    have : (pa a) b a := by
      have e : pa a = ⊤ := congrArg Subtype.val hct
      rw [e]; trivial
    rw [pa_apply] at this
    exact hb (this.2 rfl)
  have hm : ∀ x y : OPFixed α 1, (y ≤ x ∧ y ≤ c) ↔ y ≤ m x := fun x y => by
    change (y.1 ≤ x.1 ∧ y.1 ≤ pa a) ↔ y.1 ≤ x.1 ⊓ pa a
    exact le_inf_iff.symm
  have hW := weisner_dual (OPFixed.bot 1) (OPFixed.top 1) c hbot htop hc m hm
  -- the `x` with `x ∧ π_a = 0̂` are `0̂` and the `π_ab` (Lemma M(b))
  set F : Bset a → OPFixed α 1 := fun b => op1 (pab a b.1) b.2.2
  have hfilter : univ.filter (fun x => m x = OPFixed.bot 1) =
      insert (OPFixed.bot 1) (univ.image F) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
    have e : m x = OPFixed.bot 1 ↔ x.1 ⊓ pa a = ⊥ :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e, inf_pa_eq_bot_iff']
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · left; exact Subtype.ext h
      · right; exact ⟨⟨b, hb, h ▸ x.2.1⟩, Subtype.ext h.symm⟩
    · rintro (rfl | ⟨b, rfl⟩)
      · left; rfl
      · right; exact ⟨b.1, b.2.1, rfl⟩
  have hnot : OPFixed.bot 1 ∉ univ.image F := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    intro b hb
    exact pab_ne_bot (Ne.symm b.2.1) (congrArg Subtype.val hb)
  rw [hfilter, sum_insert hnot, sum_image (fun b _ b' _ hbb' =>
    Subtype.ext (pab_injective b.2.1 (congrArg Subtype.val hbb')))] at hW
  have hU : ∀ b : Bset a, IncidenceAlgebra.mu ℤ (F b) (OPFixed.top 1) =
      muFixed (1 : Contr a b.1 b.2.2 ≃o Contr a b.1 b.2.2) := fun b =>
    mu_pab_top (Ne.symm b.2.1) b.2.2
  rw [Finset.sum_congr rfl fun b _ => hU b] at hW
  change IncidenceAlgebra.mu ℤ (OPFixed.bot 1) (OPFixed.top 1) = _
  linarith

/-! ### Lemma C: Jenča–Sarkoci's recursion for `e_C` -/

section LemmaC

/-- `|B_P(x₀)| = e_C(P)`, with `B_P(x₀)` on lists (`card_inB`). -/
theorem card_inBL {β : Type*} [Fintype β] [DecidableEq β] [PartialOrder β] (x₀ : β) :
    Nat.card {l : List β // L.InBL (· < ·) univ x₀ l} = eC β := by
  rw [← card_inB x₀]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨toL w.1, (inB_iff x₀ w.1).1 w.2⟩) ⟨?_, ?_⟩)
  · intro w w' e
    exact Subtype.ext (toL_injective (congrArg Subtype.val e))
  · rintro ⟨l, hl⟩
    obtain ⟨w, rfl⟩ := exists_toL hl.1.1
    exact ⟨⟨w, (inB_iff x₀ w).2 hl⟩, rfl⟩

theorem toFinset_map' {β : Type*} [DecidableEq β] (f : β → α) (l : List β) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext; simp

/-- `B` on lists is transported by an injective map that transports the relation. -/
theorem inBL_map {β : Type*} [Fintype β] [DecidableEq β] {f : β → α}
    (hf : Function.Injective f) {rβ : β → β → Prop} {rα : α → α → Prop}
    (hr : ∀ x y, rα (f x) (f y) ↔ rβ x y) (A : Finset β) (x₀ : β) (l : List β) :
    L.InBL rα (A.image f) (f x₀) (l.map f) ↔ L.InBL rβ A x₀ l := by
  have hword : ∀ (S : Finset β) (u : List β),
      IsWordOn (S.image f) (u.map f) ↔ IsWordOn S u := by
    intro S u
    unfold IsWordOn
    rw [List.nodup_map_iff hf, toFinset_map', (Finset.image_injective hf).eq_iff]
  have huoc : ∀ U : Finset β, L.UoC rα (A.image f) (U.image f) ↔ L.UoC rβ A U := by
    intro U
    constructor
    · intro h p hp q hq hpq
      have := h (f p) (mem_image_of_mem f hp) (f q) (mem_image_of_mem f hq) ((hr p q).2 hpq)
      rwa [hf.mem_finset_image, hf.mem_finset_image] at this
    · intro h p hp q hq hpq
      obtain ⟨p', hp', rfl⟩ := mem_image.1 hp
      obtain ⟨q', hq', rfl⟩ := mem_image.1 hq
      rw [hf.mem_finset_image, hf.mem_finset_image]
      exact h p' hp' q' hq' ((hr _ _).1 hpq)
  have hlin : ∀ u : List β, L.LinL rα (A.image f) (u.map f) ↔ L.LinL rβ A u := by
    intro u
    unfold L.LinL
    rw [hword, List.pairwise_map]
    simp only [hr]
  unfold L.InBL
  rw [hlin]
  refine and_congr_right fun _ => ⟨fun h s t hst hs hU => ?_, fun h s t hst hs hU => ?_⟩
  · have := h (s.map f) (t.map f) (by rw [hst, List.map_append]) (by simpa using hs)
      (by rw [toFinset_map', huoc]; exact hU)
    obtain ⟨y, hy, e⟩ := List.mem_map.1 this
    exact hf e ▸ hy
  · obtain ⟨s', t', rfl, rfl, rfl⟩ := List.map_eq_append_iff.1 hst
    rw [toFinset_map', huoc] at hU
    exact List.mem_map_of_mem (h s' t' rfl (by simpa using hs) hU)

/-- The strict order of `P/π_ab`, on points of `P`. -/
def Rab (a b : α) (p q : α) : Prop := p ≠ q ∧ Reach (pab a b) p q

theorem Contr.exists_map_val {b : α} {h : IsOrderPreserving (pab a b)} {l : List α}
    (hl : ∀ u ∈ l, u ≠ b) : ∃ l' : List (Contr a b h), l'.map Contr.val = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons u l ih =>
    obtain ⟨l', hl'⟩ := ih fun v hv => hl v (List.mem_cons_of_mem _ hv)
    exact ⟨Contr.mk' u (hl u List.mem_cons_self) :: l', by simp [hl']⟩

theorem finite_inBL (r : α → α → Prop) (A : Finset α) (x₀ : α) :
    Finite {l : List α // L.InBL r A x₀ l} :=
  ((List.finite_length_le α (Fintype.card α)).subset
    fun _ hl => List.Nodup.length_le_card hl.1.1.1).to_subtype

/-- `|B_{P/π_ab}(a)| = e_C(P/π_ab)`, on lists of points of `P`. -/
theorem card_TL {b : α} (hab : a ≠ b) (h : IsOrderPreserving (pab a b)) :
    Nat.card {l : List α // L.InBL (Rab a b) (univ.erase b) a l} = eC (Contr a b h) := by
  rw [← card_inBL (Contr.mk' (h := h) a hab)]
  symm
  have himg : (univ : Finset (Contr a b h)).image Contr.val = univ.erase b := by
    ext u
    simp only [mem_image, mem_univ, true_and, mem_erase, and_true]
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.val_ne, fun hu => ⟨Contr.mk' u hu, rfl⟩⟩
  have hr : ∀ x y : Contr a b h, Rab a b x.val y.val ↔ x < y := fun x y => by
    rw [lt_iff_le_and_ne, Rab, Contr.le_iff, and_comm, Contr.val_injective.ne_iff]
  have key := fun l => inBL_map (Contr.val_injective (h := h)) hr univ (Contr.mk' a hab) l
  simp only [himg, Contr.val_mk'] at key
  refine Nat.card_congr (Equiv.ofBijective (fun l => ⟨l.1.map Contr.val, (key l.1).2 l.2⟩)
    ⟨?_, ?_⟩)
  · intro l l' e
    exact Subtype.ext ((List.map_injective_iff.2 Contr.val_injective) (congrArg Subtype.val e))
  · rintro ⟨l, hl⟩
    obtain ⟨l', rfl⟩ : ∃ l' : List (Contr a b h), l'.map Contr.val = l :=
      Contr.exists_map_val fun u hu => by
        have := (L.mem_of_isWordOn hl.1.1).1 hu
        exact (mem_erase.1 this).1
    exact ⟨⟨l', (key l').1 hl⟩, rfl⟩

/-- In `P/π_ab` (`a` minimal), `v` is reachable from `u` only if `u ≤ v`, or `u` lies below
the block `{a, b}` and `v` above it. -/
theorem reach_pab_cases (ha : ∀ u, u ≤ a → u = a) {b u v : α} (h : Reach (pab a b) u v) :
    u ≤ v ∨ ((u = a ∨ u ≤ b) ∧ (a ≤ v ∨ b ≤ v)) := by
  induction h with
  | refl => exact Or.inl le_rfl
  | @tail v w _ hvw ih =>
    rcases hvw with hvw | hvw
    · rcases ih with ih | ⟨h1, h2⟩
      · exact Or.inl (ih.trans hvw)
      · exact Or.inr ⟨h1, h2.imp (·.trans hvw) (·.trans hvw)⟩
    · rw [pab_apply] at hvw
      rcases hvw with rfl | ⟨hv, hw⟩
      · exact ih
      · have hw' : a ≤ w ∨ b ≤ w := hw.imp (fun e => le_of_eq e.symm) (fun e => le_of_eq e.symm)
        rcases ih with ih | ⟨h1, _⟩
        · refine Or.inr ⟨?_, hw'⟩
          rcases hv with rfl | rfl
          · exact Or.inl (ha _ ih)
          · exact Or.inr ih
        · exact Or.inr ⟨h1, hw'⟩

/-- A `π_ab`-path between points outside a union of components `S` that misses `a` and `b`
stays outside `S`. -/
theorem reach_mem_iff {b : α} {S : Finset α} (hS : L.UoC (· < ·) univ S) (haS : a ∉ S)
    (hbS : b ∉ S) {p q : α} (h : Reach (pab a b) p q) : p ∈ S ↔ q ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | @tail v w _ hvw ih =>
    refine ih.trans ?_
    rcases hvw with hvw | hvw
    · rcases hvw.lt_or_eq with hlt | rfl
      · exact hS v (mem_univ _) w (mem_univ _) hlt
      · exact Iff.rfl
    · rw [pab_apply] at hvw
      rcases hvw with rfl | ⟨hv, hw⟩
      · exact Iff.rfl
      · have h1 : v ∉ S := by rcases hv with rfl | rfl <;> assumption
        have h2 : w ∉ S := by rcases hw with rfl | rfl <;> assumption
        exact iff_of_false h1 h2

/-- Positional facts about `pre ++ a :: b :: post ∈ Lin(P)`. -/
theorem lin_facts {pre post : List α} {b : α}
    (hl : L.LinL (· < ·) univ (pre ++ a :: b :: post)) :
    a ∉ pre ∧ b ∉ pre ∧ a ∉ post ∧ b ∉ post ∧ a ≠ b ∧
    (∀ u ∈ pre, ¬ a < u ∧ ¬ b < u) ∧ (∀ u ∈ post, ¬ u < b) ∧
    (∀ u, u ∈ pre ∨ u = a ∨ u = b ∨ u ∈ post) := by
  obtain ⟨⟨hnd, hset⟩, hpw⟩ := hl
  have hall : ∀ u, u ∈ pre ++ a :: b :: post := fun u =>
    (L.mem_of_isWordOn ⟨hnd, hset⟩).2 (mem_univ u)
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hnd
  simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at hpw
  simp only [List.mem_append, List.mem_cons] at hall
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind
  · grind
  · grind
  · intro u hu
    exact ⟨hpw.2.2 u hu a (Or.inl rfl), hpw.2.2 u hu b (Or.inr (Or.inl rfl))⟩
  · intro u hu
    exact hpw.2.1.2.1 u hu
  · grind

theorem between {pre post : List α} {b x : α}
    (hl : L.LinL (· < ·) univ (pre ++ a :: b :: post)) (h1 : a ≤ x) (h2 : x ≤ b) :
    x = a ∨ x = b := by
  obtain ⟨hapre, -, -, hbpost, -, hpre, hpost, hall⟩ := lin_facts hl
  rcases hall x with hx | hx | hx | hx
  · exact absurd (lt_of_le_of_ne h1 fun e => hapre (e ▸ hx)) (hpre x hx).1
  · exact Or.inl hx
  · exact Or.inr hx
  · exact absurd (lt_of_le_of_ne h2 fun e => hbpost (e ▸ hx)) (hpost x hx)

/-- If `a` is immediately followed by `b` in a linear extension, then `π_ab ∈ OP(P)`. -/
theorem isOrderPreserving_pab_of_lin (ha : ∀ u, u ≤ a → u = a) {pre post : List α} {b : α}
    (hl : L.LinL (· < ·) univ (pre ++ a :: b :: post)) : IsOrderPreserving (pab a b) := by
  have inAB : ∀ z, (z = a ∨ z ≤ b) → (a ≤ z ∨ b ≤ z) → z = a ∨ z = b := by
    intro z h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · rcases h2 with h2 | h2
      · exact between hl h2 h1
      · exact Or.inr (le_antisymm h1 h2)
  -- `x ≤ y` with `y` below the block and `x` above it
  have mixed : ∀ x y, x ≤ y → (y = a ∨ y ≤ b) → (a ≤ x ∨ b ≤ x) →
      (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
    intro x y hxy h1 h2
    refine ⟨inAB x ?_ h2, inAB y h1 (h2.imp (·.trans hxy) (·.trans hxy))⟩
    rcases h1 with rfl | h1
    · exact Or.inl (ha x hxy)
    · exact Or.inr (hxy.trans h1)
  intro x y hxy hyx
  rw [pab_apply]
  rcases reach_pab_cases ha hxy with h1 | ⟨h1, h2⟩ <;>
    rcases reach_pab_cases ha hyx with h3 | ⟨h3, h4⟩
  · exact Or.inl (le_antisymm h1 h3)
  · exact Or.inr (mixed x y h1 h3 h4)
  · exact Or.inr (mixed y x h3 h1 h2).symm
  · exact Or.inr ⟨inAB x h1 h4, inAB y h3 h2⟩

/-- Deleting `b`, the letter after `a`, maps `B_P(a)` to `B_{P/π_ab}(a)`. -/
theorem inBL_erase (ha : ∀ u, u ≤ a → u = a) {pre post : List α} {b : α}
    (hl : L.InBL (· < ·) univ a (pre ++ a :: b :: post)) :
    L.InBL (Rab a b) (univ.erase b) a (pre ++ a :: post) := by
  obtain ⟨hapre, hbpre, hapost, hbpost, hab, hpre, hpost, hall⟩ := lin_facts hl.1
  have hsub : (pre ++ a :: post).Sublist (pre ++ a :: b :: post) :=
    List.Sublist.append_left (List.Sublist.cons₂ a (List.sublist_cons_self b post)) pre
  have hmem : ∀ u, u ∈ pre ++ a :: post ↔ u ≠ b := by
    intro u
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (hu | rfl | hu)
      · exact fun e => hbpre (e ▸ hu)
      · exact hab
      · exact fun e => hbpost (e ▸ hu)
    · intro hu
      rcases hall u with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd h hu
      · exact Or.inr (Or.inr h)
  refine ⟨⟨⟨hl.1.1.1.sublist hsub, ?_⟩, ?_⟩, ?_⟩
  · ext u; rw [List.mem_toFinset, hmem, mem_erase]; simp
  · have hpos : (pre ++ a :: post).Pairwise (fun p q => p ∈ pre ∨ q ∈ post) := by
      rw [List.pairwise_append, List.pairwise_cons]
      have hpw := hl.1.2
      simp only [List.pairwise_append, List.pairwise_cons] at hpw
      exact ⟨hpw.1.imp_of_mem fun hp _ _ => Or.inl hp,
        ⟨fun _ hq => Or.inr hq, hpw.2.1.2.2.imp_of_mem fun _ hq _ => Or.inr hq⟩,
        fun p hp _ _ => Or.inl hp⟩
    refine ((hl.1.2.sublist hsub).and hpos).imp_of_mem fun {p q} _ _ ⟨h1, h2⟩ hR => ?_
    obtain ⟨hne, hreach⟩ := hR
    rcases reach_pab_cases ha hreach with h | ⟨h3, h4⟩
    · exact h1 (lt_of_le_of_ne h hne)
    · rcases h2 with hp | hq
      · rcases h4 with h4 | h4
        · exact (hpre p hp).1 (lt_of_le_of_ne h4 fun e => hapre (e ▸ hp))
        · exact (hpre p hp).2 (lt_of_le_of_ne h4 fun e => hbpre (e ▸ hp))
      · rcases h3 with rfl | h3
        · exact hapost hq
        · exact hpost q hq (lt_of_le_of_ne h3 fun e => hbpost (e ▸ hq))
  · intro s' t' hst hs' hU
    obtain ⟨s, t, hz, hs, hne⟩ := L.split_pullback (x := b) (c := [a, b]) (Or.inr rfl) hapre hst
    have hbs' : b ∉ s'.toFinset := by
      intro hb
      have : b ∈ pre ++ a :: post := hst ▸ List.mem_append_left _ (List.mem_toFinset.1 hb)
      exact (hmem b).1 this rfl
    have hUs : L.UoC (· < ·) univ s.toFinset := by
      rw [hs]
      intro p _ q _ hpq
      -- `f`: the quotient map, `b ↦ a`
      set f : α → α := fun u => if u = b then a else u
      have hf : ∀ u, u ∈ L.pb a b s'.toFinset ↔ f u ∈ s'.toFinset := by
        intro u
        rw [L.mem_pb hbs']
        by_cases hu : u = b
        · simp [f, hu]
        · simp [f, hu]
      have hfb : ∀ u, f u ≠ b := by
        intro u; by_cases hu : u = b
        · simp [f, hu, hab]
        · simp [f, hu]
      have hfp : ∀ u, pab a b (f u) u := by
        intro u; by_cases hu : u = b
        · simp only [f, hu, if_true]; rw [pab_apply]; grind
        · simp only [f, hu, if_false]; exact (pab a b).refl u
      have s1 : opStep (pab a b) (f p) p := Or.inr (hfp p)
      have s2 : opStep (pab a b) p q := Or.inl hpq.le
      have s3 : opStep (pab a b) q (f q) := Or.inr ((pab a b).symm (hfp q))
      have hreach : Reach (pab a b) (f p) (f q) :=
        ((Relation.ReflTransGen.single s1).tail s2).tail s3
      rw [hf, hf]
      by_cases e : f p = f q
      · rw [e]
      · exact hU (f p) (mem_erase.2 ⟨hfb p, mem_univ _⟩) (f q) (mem_erase.2 ⟨hfb q, mem_univ _⟩)
          ⟨e, hreach⟩
    have has := hl.2 s t (by simpa using hz) (hne hs') hUs
    have : a ∈ L.pb a b s'.toFinset := hs ▸ List.mem_toFinset.2 has
    rw [L.mem_pb hbs'] at this
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · exact List.mem_toFinset.1 h
    · exact absurd h hab

/-- Inserting `b` after `a` maps `B_{P/π_ab}(a)` to `B_P(a)`. -/
theorem inBL_insert {pre post : List α} {b : α} (ha : ∀ u, u ≤ a → u = a)
    (hl : L.InBL (Rab a b) (univ.erase b) a (pre ++ a :: post)) :
    L.InBL (· < ·) univ a (pre ++ a :: b :: post) := by
  obtain ⟨⟨hnd, hset⟩, hpw⟩ := hl.1
  have hmem : ∀ u, u ∈ pre ++ a :: post ↔ u ≠ b := fun u => by
    rw [← List.mem_toFinset, hset, mem_erase]; simp
  have hab : a ≠ b := (hmem a).1 (by simp)
  have hbpre : b ∉ pre := fun h => (hmem b).1 (List.mem_append_left _ h) rfl
  have hbpost : b ∉ post := fun h => (hmem b).1 (by simp [h]) rfl
  have hnd' := hnd
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hnd'
  have hapre : a ∉ pre := by grind
  have hapost : a ∉ post := by grind
  have hlt : ∀ {p q}, q < p → Rab a b q p := fun hqp =>
    ⟨ne_of_lt hqp, Relation.ReflTransGen.single (Or.inl hqp.le)⟩
  have hab' : pab a b a b := by rw [pab_apply]; grind
  simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at hpw
  obtain ⟨hpw1, ⟨hpwa, hpw2⟩, hpw3⟩ := hpw
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hnd ⊢
    grind
  · ext u
    simp only [List.mem_toFinset, mem_univ, iff_true, List.mem_append, List.mem_cons]
    by_cases hu : u = b
    · exact Or.inr (Or.inr (Or.inl hu))
    · have := (hmem u).2 hu
      simp only [List.mem_append, List.mem_cons] at this
      grind
  · rw [List.pairwise_append, List.pairwise_cons, List.pairwise_cons]
    refine ⟨hpw1.imp fun h h' => h (hlt h'), ⟨?_, ?_, hpw2.imp fun h h' => h (hlt h')⟩, ?_⟩
    · intro q _ hq
      exact (ne_of_lt hq) (ha q hq.le)
    · -- `q ∈ post`, `q < b` would give `q < a` in `P/π_ab`
      intro q hq hqb
      have s1 : opStep (pab a b) q b := Or.inl hqb.le
      have s2 : opStep (pab a b) b a := Or.inr ((pab a b).symm hab')
      exact hpwa q hq ⟨fun e => hapost (e ▸ hq),
        (Relation.ReflTransGen.single s1).tail s2⟩
    · intro p hp q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq | hq
      · rw [hq]; exact fun h => hpw3 p hp a (Or.inl rfl) (hlt h)
      · -- `b < p` would give `a < p` in `P/π_ab`
        rw [hq]
        intro hbp
        have s1 : opStep (pab a b) a b := Or.inr hab'
        have s2 : opStep (pab a b) b p := Or.inl hbp.le
        exact hpw3 p hp a (Or.inl rfl) ⟨fun e => hapre (e ▸ hp),
          (Relation.ReflTransGen.single s1).tail s2⟩
      · exact fun h => hpw3 p hp q (Or.inr hq) (hlt h)
  · intro s t hst hs hU
    by_contra has
    have hbs : b ∉ s := fun h => by
      rcases List.append_eq_append_iff.1 hst with ⟨a', rfl, h2⟩ | ⟨c', h1, h2⟩
      · rcases a' with _ | ⟨x, a'⟩
        · simp at h; exact hbpre h
        · simp only [List.cons_append, List.cons.injEq] at h2
          exact has (by simp [← h2.1])
      · exact hbpre (h1 ▸ List.mem_append_left _ h)
    -- `s` is a prefix of `pre`
    obtain ⟨c', hc'⟩ : ∃ c', pre = s ++ c' := by
      rcases List.append_eq_append_iff.1 hst with ⟨a', rfl, h2⟩ | ⟨c', h1, h2⟩
      · rcases a' with _ | ⟨x, a'⟩
        · exact ⟨[], by simp⟩
        · simp only [List.cons_append, List.cons.injEq] at h2
          exact absurd (by simp [← h2.1]) has
      · exact ⟨c', h1⟩
    refine has (hl.2 s (c' ++ a :: post) (by rw [hc', List.append_assoc]) hs ?_)
    intro p _ q _ hpq
    exact reach_mem_iff hU (by simpa using has) (by simpa using hbs) hpq.2

/-- The letter after `a` in `l`. -/
def nxt (a : α) (l : List α) : α := l.getD (l.idxOf a + 1) a

theorem nxt_eq {pre post : List α} {b : α} (h : a ∉ pre) : nxt a (pre ++ a :: b :: post) = b := by
  unfold nxt
  rw [List.idxOf_append_of_notMem h, List.idxOf_cons_self,
    List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem exists_split (ha : ∀ u, u ≤ a → u = a) (h2 : 2 ≤ Fintype.card α) {l : List α}
    (hl : L.InBL (· < ·) univ a l) : ∃ pre b post, l = pre ++ a :: b :: post := by
  have hmem : a ∈ l := (L.mem_of_isWordOn hl.1.1).2 (mem_univ a)
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  rcases post with _ | ⟨b, post⟩
  · exfalso
    obtain ⟨⟨hnd, hset⟩, hpw⟩ := hl.1
    have hapre : a ∉ pre := by
      simp only [List.nodup_append, List.nodup_cons] at hnd; grind
    have hall : ∀ u, u ∈ pre ∨ u = a := fun u => by
      have := (L.mem_of_isWordOn ⟨hnd, hset⟩).2 (mem_univ u)
      simpa using this
    have hpre : pre ≠ [] := by
      rintro rfl
      obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h2 a
      exact hb ((hall b).resolve_left (by simp))
    have hpwa : ∀ u ∈ pre, ¬ a < u := by
      intro u hu
      rw [List.pairwise_append] at hpw
      exact hpw.2.2 u hu a (by simp)
    have hU : L.UoC (· < ·) univ pre.toFinset := by
      intro p _ q _ hpq
      rcases hall p with hp | rfl
      · rcases hall q with hq | rfl
        · simp [hp, hq]
        · exact absurd (ha p hpq.le) (ne_of_lt hpq)
      · rcases hall q with hq | rfl
        · exact absurd hpq (hpwa q hq)
        · exact Iff.rfl
    exact hapre (hl.2 pre [a] rfl hpre hU)
  · exact ⟨pre, b, post, rfl⟩

theorem insA_split {pre post : List α} {b : α} (hpre : a ∉ pre) (hpost : a ∉ post) :
    L.insA b a (pre ++ a :: post) = pre ++ a :: b :: post := by
  rw [L.insA_append, L.insA_cons, L.insA_of_not_mem hpre, L.insA_of_not_mem hpost, if_pos rfl]
  simp

theorem erase_split {pre post : List α} {b : α} (hb : b ∉ pre) (hab : a ≠ b) :
    (pre ++ a :: b :: post).erase b = pre ++ a :: post := by
  rw [List.erase_append_right _ hb, List.erase_cons_tail (by simpa using hab),
    List.erase_cons_head]

variable (a) in
/-- `B_P(a)` on lists. -/
abbrev BLmin := {l : List α // L.InBL (· < ·) univ a l}

variable (a) in
/-- `B_{P/π_ab}(a)` on lists of points of `P`. -/
abbrev TLmin (b : α) := {l : List α // L.InBL (Rab a b) (univ.erase b) a l}

theorem fwd_spec (ha : ∀ u, u ≤ a → u = a) (h2 : 2 ≤ Fintype.card α) {l : List α}
    (hl : L.InBL (· < ·) univ a l) :
    (nxt a l ≠ a ∧ IsOrderPreserving (pab a (nxt a l))) ∧
      L.InBL (Rab a (nxt a l)) (univ.erase (nxt a l)) a (l.erase (nxt a l)) := by
  obtain ⟨pre, b, post, rfl⟩ := exists_split ha h2 hl
  obtain ⟨hapre, hbpre, -, -, hab, -⟩ := lin_facts hl.1
  rw [nxt_eq hapre, erase_split hbpre hab]
  exact ⟨⟨Ne.symm hab, isOrderPreserving_pab_of_lin ha hl.1⟩, inBL_erase ha hl⟩

theorem split_of_TL {b : α} (hab : a ≠ b) {l : List α}
    (hl : L.InBL (Rab a b) (univ.erase b) a l) :
    ∃ pre post, l = pre ++ a :: post ∧ a ∉ pre ∧ a ∉ post ∧ b ∉ pre := by
  have hmem : a ∈ l := (L.mem_of_isWordOn hl.1.1).2 (mem_erase.2 ⟨hab, mem_univ a⟩)
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  have hnd := hl.1.1.1
  have hb : b ∉ pre ++ a :: post := fun h => by
    have := (L.mem_of_isWordOn hl.1.1).1 h
    simp at this
  simp only [List.nodup_append, List.nodup_cons] at hnd
  refine ⟨pre, post, rfl, ?_, ?_, fun h => hb (List.mem_append_left _ h)⟩ <;> grind

/-- **Lemma C**, the bijection: `B_P(a) ≅ ∐_b B_{P/π_ab}(a)`, `w ↦ (b, w ∖ b)` with `b` the
letter after `a`; the inverse inserts `b` after `a`. -/
noncomputable def lemmaC_equiv (ha : ∀ u, u ≤ a → u = a) (h2 : 2 ≤ Fintype.card α) :
    BLmin a ≃ Σ b : Bset a, TLmin a b.1 where
  toFun l := ⟨⟨nxt a l.1, (fwd_spec ha h2 l.2).1⟩,
    ⟨l.1.erase (nxt a l.1), (fwd_spec ha h2 l.2).2⟩⟩
  invFun x := ⟨L.insA x.1.1 a x.2.1, by
    obtain ⟨pre, post, e, hapre, hapost, -⟩ := split_of_TL (Ne.symm x.1.2.1) x.2.2
    have := x.2.2
    rw [e] at this ⊢
    rw [insA_split hapre hapost]
    exact inBL_insert ha this⟩
  left_inv l := by
    obtain ⟨l, hl⟩ := l
    apply Subtype.ext
    obtain ⟨pre, b, post, rfl⟩ := exists_split ha h2 hl
    obtain ⟨hapre, hbpre, hapost, -, hab, -⟩ := lin_facts hl.1
    change L.insA (nxt a _) a ((pre ++ a :: b :: post).erase (nxt a _)) = _
    rw [nxt_eq hapre, erase_split hbpre hab, insA_split hapre hapost]
  right_inv x := by
    obtain ⟨⟨b, hb⟩, ⟨l, hl⟩⟩ := x
    obtain ⟨pre, post, rfl, hapre, hapost, hbpre⟩ := split_of_TL (Ne.symm hb.1) hl
    refine Sigma.subtype_ext ?_ ?_
    · apply Subtype.ext
      change nxt a (L.insA b a _) = b
      rw [insA_split hapre hapost, nxt_eq hapre]
    · change (L.insA b a _).erase (nxt a (L.insA b a _)) = _
      rw [insA_split hapre hapost, nxt_eq hapre, erase_split hbpre (Ne.symm hb.1)]

open Classical in
/-- **Lemma C** (Jenča–Sarkoci's recursion): for `n ≥ 2` and `a` minimal,
`e_C(P) = ∑_b e_C(P/π_ab)`, the sum over `b ≠ a` with `π_ab ∈ OP(P)`. -/
theorem eC_rec (ha : ∀ u, u ≤ a → u = a) (h2 : 2 ≤ Fintype.card α) :
    eC α = ∑ b : Bset a, eC (Contr a b.1 b.2.2) := by
  have := fun b : Bset a => finite_inBL (Rab a b.1) (univ.erase b.1) a
  rw [← card_inBL a, Nat.card_congr (lemmaC_equiv ha h2), Nat.card_sigma]
  exact Finset.sum_congr rfl fun b _ => card_TL (Ne.symm b.2.1) b.2.2

end LemmaC

/-! ### Theorem A -/

open Classical in
theorem mu_OP_eq_aux : ∀ (n : ℕ) (β : Type*) [Fintype β] [DecidableEq β] [PartialOrder β],
    Fintype.card β = n + 1 → muFixed (1 : β ≃o β) = (-1) ^ n * (eC β : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro β _ _ _ hcard
  have : Nonempty β := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨a, -, ha'⟩ :=
    exists_minimal_of_wellFoundedLT (fun _ : β => True) ⟨Classical.arbitrary β, trivial⟩
  have ha : ∀ u, u ≤ a → u = a := fun u hu => le_antisymm hu (ha' trivial hu)
  rcases n with _ | n
  · -- one point: `OP(P)` is a point and there is one cyclic class
    have hsub : Subsingleton β := Fintype.card_le_one_iff_subsingleton.1 hcard.le
    have hbt : OPFixed.bot (1 : β ≃o β) = OPFixed.top 1 := by
      apply Subtype.ext
      ext u v
      change (⊥ : Setoid β) u v ↔ (⊤ : Setoid β) u v
      rw [Setoid.bot_def]
      exact ⟨fun _ => trivial, fun _ => Subsingleton.elim u v⟩
    have he : eC β = 1 := by
      rw [← card_inB a, Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun w w' => Subtype.ext (Equiv.ext fun i => Subsingleton.elim _ _)⟩,
        ⟨⟨(Fintype.equivFin β).symm, ?_, ?_⟩⟩⟩
      · intro i j hij
        rw [Subsingleton.elim ((Fintype.equivFin β).symm i) ((Fintype.equivFin β).symm j)] at hij
        exact absurd hij (lt_irrefl _)
      · intro k hk hkn _
        rw [prefixSet, mem_image]
        exact ⟨⟨0, by omega⟩, by simp [hk], Subsingleton.elim _ _⟩
    rw [muFixed, hbt, IncidenceAlgebra.mu_self, he]
    simp
  · have h2 : 2 ≤ Fintype.card β := by omega
    rw [mu_op_rec ha h2, eC_rec ha h2]
    have hb : ∀ b : Bset a, muFixed (1 : Contr a b.1 b.2.2 ≃o Contr a b.1 b.2.2) =
        (-1) ^ n * (eC (Contr a b.1 b.2.2) : ℤ) := fun b =>
      ih n (by omega) _ (by rw [Contr.card_eq, hcard]; omega)
    rw [Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum]
    push_cast
    ring

/-- **Theorem A** (Lemma `lem:small`, homology-free; Proof W of `notes/mu_op_elementary.md`):
for every finite poset `P` on `n ≥ 1` points, `μ(OP(P)) = (-1)^{n-1} e_C(P)`. -/
theorem mu_OP_eq (h0 : 0 < Fintype.card α) :
    muFixed (1 : α ≃o α) = (-1) ^ (Fintype.card α - 1) * (eC α : ℤ) :=
  mu_OP_eq_aux _ α (by omega)

end PosetJKS
