import Mathlib

/-!
# P. Hall's theorem: `μ(x, y)` as a signed count of chains

For `x < y` in a finite poset, `μ(x, y) = ∑_{m ≥ 0} (-1)^{m+1} #{m-element chains of (x, y)}`
(Stanley EC1, Prop. 3.8.5). An `m`-element chain of the open interval `(x, y)` is recorded by
its increasing enumeration, a strictly monotone `f : Fin m → L` with values in `(x, y)`
(`chainsIn x y m`).

The proof is the recursion behind the `(ζ - 1)` expansion: deleting the top element `z` of an
`(m+1)`-element chain of `(x, y)` leaves an `m`-element chain of `(x, z)`
(`card_chainsIn_succ`), so the signed chain count satisfies Mathlib's defining recursion
`μ(x, y) = -∑_{x ≤ z < y} μ(x, z)` (`mu_eq_chainEuler`, by well-founded induction on `y`).
The form used in `MainTheorem.lean`, with order embeddings of `Fin m` into the proper part of a
bounded poset, is `mu_bot_top_eq_chainSum`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

section Hall

variable {L : Type*} [PartialOrder L] [Fintype L] [DecidableEq L]

open Classical in
/-- The `m`-element chains of the open interval `(x, y)`, as strictly increasing tuples. -/
noncomputable def chainsIn (x y : L) (m : ℕ) : Finset (Fin m → L) :=
  univ.filter fun f => StrictMono f ∧ ∀ i, x < f i ∧ f i < y

theorem mem_chainsIn {x y : L} {m : ℕ} {f : Fin m → L} :
    f ∈ chainsIn x y m ↔ StrictMono f ∧ ∀ i, x < f i ∧ f i < y := by
  simp [chainsIn]

theorem card_chainsIn_zero (x y : L) : (chainsIn x y 0).card = 1 := by
  have : chainsIn x y 0 = univ := by
    ext f
    simp only [mem_chainsIn, mem_univ, iff_true]
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  rw [this, card_univ, Fintype.card_unique]

theorem chainsIn_eq_empty {x y : L} {m : ℕ} (hm : Fintype.card L < m) : chainsIn x y m = ∅ := by
  ext f
  simp only [mem_chainsIn, Finset.notMem_empty, iff_false, not_and]
  intro hf _
  have := Fintype.card_le_of_injective f hf.injective
  rw [Fintype.card_fin] at this
  omega

/-- An `(m+1)`-element chain of `(x, y)` is its top element `z ∈ (x, y)` and an `m`-element
chain of `(x, z)`. -/
theorem mem_chainsIn_succ {x y : L} {m : ℕ} {f : Fin (m + 1) → L} :
    f ∈ chainsIn x y (m + 1) ↔
      (x < f (Fin.last m) ∧ f (Fin.last m) < y) ∧ Fin.init f ∈ chainsIn x (f (Fin.last m)) m := by
  simp only [mem_chainsIn]
  constructor
  · rintro ⟨hf, hb⟩
    exact ⟨hb _, fun i j hij => hf (Fin.castSucc_lt_castSucc_iff.2 hij),
      fun i => ⟨(hb _).1, hf (Fin.castSucc_lt_last i)⟩⟩
  · rintro ⟨hz, hg, hb⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction j using Fin.lastCases with
      | last =>
        induction i using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast i => exact (hb i).2
      | cast j =>
        induction i using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast i => exact hg (Fin.castSucc_lt_castSucc_iff.1 hij)
    · induction i using Fin.lastCases with
      | last => exact hz
      | cast i => exact ⟨(hb i).1, (hb i).2.trans hz.2⟩

variable [LocallyFiniteOrder L]

theorem card_chainsIn_succ (x y : L) (m : ℕ) :
    (chainsIn x y (m + 1)).card = ∑ z ∈ Ioo x y, (chainsIn x z m).card := by
  rw [card_eq_sum_card_fiberwise (f := fun f => f (Fin.last m)) (t := Ioo x y)
    (fun f hf => mem_Ioo.2 (mem_chainsIn_succ.1 hf).1)]
  refine sum_congr rfl fun z _ => ?_
  refine card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g z) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter] at hf
    obtain ⟨hf, rfl⟩ := hf
    exact (mem_chainsIn_succ.1 hf).2
  · intro g hg
    simp only [coe_filter, Set.mem_setOf_eq, Fin.snoc_last, and_true]
    rw [mem_chainsIn_succ, Fin.snoc_last, Fin.init_snoc]
    exact ⟨mem_Ioo.1 ‹z ∈ Ioo x y›, hg⟩
  · intro f hf
    simp only [coe_filter] at hf
    obtain ⟨-, rfl⟩ := hf
    exact Fin.snoc_init_self f
  · intro g _
    exact Fin.init_snoc ..

/-- The reduced Euler characteristic of the order complex of the open interval `(x, y)`. -/
noncomputable def chainEuler (x y : L) : ℤ :=
  ∑ m ∈ range (Fintype.card L + 1), (-1 : ℤ) ^ (m + 1) * ((chainsIn x y m).card : ℤ)

/-- **P. Hall's theorem**: for `x < y`, `μ(x, y) = ∑_m (-1)^{m+1} #{m-element chains of (x,y)}`. -/
theorem mu_eq_chainEuler {x y : L} (hxy : x < y) : IncidenceAlgebra.mu ℤ x y = chainEuler x y := by
  induction y using WellFoundedLT.induction with
  | _ y ih =>
  have hN : ∀ m, ∑ z ∈ Ioo x y, ((chainsIn x z m).card : ℤ) = (chainsIn x y (m + 1)).card := by
    intro m
    rw [card_chainsIn_succ]
    push_cast
    rfl
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hxy.ne, ← Finset.Ioo_insert_left hxy,
    sum_insert left_notMem_Ioo, IncidenceAlgebra.mu_self,
    sum_congr rfl fun z hz => ih z (mem_Ioo.1 hz).2 (mem_Ioo.1 hz).1]
  unfold chainEuler
  rw [sum_comm]
  simp_rw [← mul_sum, hN]
  rw [sum_range_succ, sum_range_succ' _ (Fintype.card L),
    chainsIn_eq_empty (by omega : Fintype.card L < Fintype.card L + 1), card_chainsIn_zero]
  simp only [card_empty, Nat.cast_zero, mul_zero, add_zero, zero_add, pow_one, Nat.cast_one,
    mul_one]
  rw [neg_add, ← sum_neg_distrib, add_comm]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  ring

/-- `m`-element chains of the proper part of a bounded poset, as order embeddings, are the
`m`-element chains of the open interval `(⊥, ⊤)`. -/
theorem natCard_embedding_eq_card_chainsIn [BoundedOrder L] (m : ℕ) :
    Nat.card (Fin m ↪o {x : L // x ≠ ⊥ ∧ x ≠ ⊤}) = (chainsIn (⊥ : L) ⊤ m).card := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun c => ⟨fun i => (c i).1, mem_chainsIn.2 ⟨fun i j hij => c.strictMono hij,
        fun i => ⟨bot_lt_iff_ne_bot.2 (c i).2.1, lt_top_iff_ne_top.2 (c i).2.2⟩⟩⟩
      invFun := fun f => OrderEmbedding.ofStrictMono
        (fun i => ⟨f.1 i, ((mem_chainsIn.1 f.2).2 i).1.ne', ((mem_chainsIn.1 f.2).2 i).2.ne⟩)
        fun i j hij => (mem_chainsIn.1 f.2).1 hij
      left_inv := fun c => by ext; rfl
      right_inv := fun f => rfl }

/-- **P. Hall's theorem** in the form of `hall_mu_eq_reducedEuler`. -/
theorem mu_bot_top_eq_chainSum (L : Type*) [PartialOrder L] [BoundedOrder L] [Fintype L]
    [DecidableEq L] [LocallyFiniteOrder L] (h : (⊥ : L) ≠ ⊤) :
    IncidenceAlgebra.mu ℤ (⊥ : L) ⊤ =
      ∑ m ∈ range (Fintype.card L + 1),
        (-1 : ℤ) ^ (m + 1) * (Nat.card (Fin m ↪o {x : L // x ≠ ⊥ ∧ x ≠ ⊤}) : ℤ) := by
  rw [mu_eq_chainEuler (bot_lt_iff_ne_bot.2 h.symm), chainEuler]
  simp_rw [natCard_embedding_eq_card_chainsIn]

end Hall

end PosetJKS
