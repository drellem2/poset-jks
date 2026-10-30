import PosetJKS.Basic

/-!
# Word combinatorics on lists: the contraction operator `E_{a,x}`

This file is the list-level core of the first milestone (Theorem S(a),(b) and Theorem Ψ of
`notes/poset_jks_theorem.tex`, proved in `notes/conjecture_s_splitting_cycles_span.md` and
`notes/natural_isomorphism.md`).

The induction of those proofs passes from a poset `P` on a letter set `A` to the contraction
`P/{a,x}` on `A ∖ {x}`. To keep the ambient type fixed along the induction, words are lists over
a fixed type `α`, a letter set is a `Finset α`, and the poset is replaced by an arbitrary
relation `r` on `α`. A list `l` is a linear extension of `r` on `A` (`LinL r A l`) if it is a
word on `A` and never puts `q` before `p` when `r p q`. For a partial order `r = (· < ·)` these
are the linear extensions; the contraction is the relation `rc r a x`, whose linear extensions
are those of the quotient poset (the note takes the transitive closure; that does not change the
linear extensions or the unions of components).

* `ins x a l` / `insA x a l`: insert `x` just before / just after `a`.
* `shq q u v`: the sum of the lists whose subwords on `q` and on `¬q` are `u` and `v`.
* `ShL A`: the span of the proper shuffles of words on complementary subsets of `A`.
* `E a x`: the contraction operator, `E(X)(y) = X(y[a→xa]) - X(y[a→ax])` for `x ∉ y`.
* `map_E_ShL` (Lemma 1 of the note): `E_{a,x}(Sh_A) ⊆ Sh_{A∖x}`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

namespace L

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Inserting `x` next to `a` -/

/-- Insert `x` immediately before every occurrence of `a`. -/
def ins (x a : α) (l : List α) : List α := l.flatMap fun b => if b = a then [x, a] else [b]

/-- Insert `x` immediately after every occurrence of `a`. -/
def insA (x a : α) (l : List α) : List α := l.flatMap fun b => if b = a then [a, x] else [b]

variable {x a : α}

@[simp] lemma ins_nil : ins x a [] = [] := rfl
@[simp] lemma insA_nil : insA x a [] = [] := rfl

@[simp] lemma ins_cons (b : α) (l : List α) :
    ins x a (b :: l) = (if b = a then [x, a] else [b]) ++ ins x a l := by
  simp [ins, List.flatMap_cons]

@[simp] lemma insA_cons (b : α) (l : List α) :
    insA x a (b :: l) = (if b = a then [a, x] else [b]) ++ insA x a l := by
  simp [insA, List.flatMap_cons]

@[simp] lemma ins_append (l₁ l₂ : List α) : ins x a (l₁ ++ l₂) = ins x a l₁ ++ ins x a l₂ := by
  simp [ins, List.flatMap_append]

@[simp] lemma insA_append (l₁ l₂ : List α) :
    insA x a (l₁ ++ l₂) = insA x a l₁ ++ insA x a l₂ := by
  simp [insA, List.flatMap_append]

lemma ins_of_not_mem {l : List α} (h : a ∉ l) : ins x a l = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b ≠ a := fun hb => h (hb ▸ List.mem_cons_self)
    simp [hb, ih (fun h' => h (List.mem_cons_of_mem _ h'))]

lemma insA_of_not_mem {l : List α} (h : a ∉ l) : insA x a l = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b ≠ a := fun hb => h (hb ▸ List.mem_cons_self)
    simp [hb, ih (fun h' => h (List.mem_cons_of_mem _ h'))]

lemma filter_ins {l : List α} (h : x ∉ l) : (ins x a l).filter (· ≠ x) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b ≠ x := fun hb => h (hb ▸ List.mem_cons_self)
    have ih := ih (fun h' => h (List.mem_cons_of_mem _ h'))
    by_cases hba : b = a
    · subst hba; simp [hb]; simpa using ih
    · simp [hba, hb]; simpa using ih

lemma filter_insA {l : List α} (h : x ∉ l) : (insA x a l).filter (· ≠ x) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b ≠ x := fun hb => h (hb ▸ List.mem_cons_self)
    have ih := ih (fun h' => h (List.mem_cons_of_mem _ h'))
    by_cases hba : b = a
    · subst hba; simp [hb]; simpa using ih
    · simp [hba, hb]; simpa using ih

lemma mem_ins {l : List α} {b : α} : b ∈ ins x a l ↔ b ∈ l ∨ (b = x ∧ a ∈ l) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases hca : c = a
    · subst hca; simp [ih]; tauto
    · simp [hca, ih]
      constructor
      · rintro (h | h | h) <;> [tauto; tauto; (rcases h with ⟨h1, h2⟩; tauto)]
      · rintro ((h | h) | ⟨h1, h2 | h2⟩) <;> [tauto; tauto; exact absurd h2.symm hca; tauto]

lemma mem_insA {l : List α} {b : α} : b ∈ insA x a l ↔ b ∈ l ∨ (b = x ∧ a ∈ l) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases hca : c = a
    · subst hca; simp [ih]; tauto
    · simp [hca, ih]
      constructor
      · rintro (h | h | h) <;> [tauto; tauto; (rcases h with ⟨h1, h2⟩; tauto)]
      · rintro ((h | h) | ⟨h1, h2 | h2⟩) <;> [tauto; tauto; exact absurd h2.symm hca; tauto]

lemma ins_ne_insA (hxa : x ≠ a) {l : List α} (h : a ∈ l) : ins x a l ≠ insA x a l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba; simp [hxa]
    · have : a ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hba
        · exact h
      simpa [hba] using ih this

/-! ### Filtering through an insertion -/

variable {q : α → Bool}

lemma filter_ins_tt (hx : q x = true) (ha : q a = true) (l : List α) :
    (ins x a l).filter q = ins x a (l.filter q) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba; simp [List.filter_cons, hx, ha, ih]
    · by_cases hb : q b = true <;> simp [List.filter_cons, hba, hb, ih]

lemma filter_insA_tt (hx : q x = true) (ha : q a = true) (l : List α) :
    (insA x a l).filter q = insA x a (l.filter q) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba; simp [List.filter_cons, hx, ha, ih]
    · by_cases hb : q b = true <;> simp [List.filter_cons, hba, hb, ih]

lemma filter_ins_ff (hx : q x = false) (ha : q a = false) (l : List α) :
    (ins x a l).filter q = l.filter q := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba; simp [List.filter_cons, hx, ha, ih]
    · by_cases hb : q b = true <;> simp [List.filter_cons, hba, hb, ih]

lemma filter_insA_ff (hx : q x = false) (ha : q a = false) (l : List α) :
    (insA x a l).filter q = l.filter q := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba; simp [List.filter_cons, hx, ha, ih]
    · by_cases hb : q b = true <;> simp [List.filter_cons, hba, hb, ih]

lemma filter_ins_eq_insA (h : q x ≠ q a) (l : List α) :
    (ins x a l).filter q = (insA x a l).filter q := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hba : b = a
    · subst hba
      cases hx : q x <;> cases hb : q b <;> simp_all [List.filter_cons]
    · simp [hba, List.filter_cons, ih]

/-- An `x`-free list `m` is recovered from `ins x a m`. -/
lemma ins_eq_iff {m u : List α} (hm : x ∉ m) :
    ins x a m = u ↔ u = ins x a (u.filter (· ≠ x)) ∧ m = u.filter (· ≠ x) := by
  constructor
  · rintro rfl; rw [filter_ins hm]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [h2, ← h1]

lemma insA_eq_iff {m u : List α} (hm : x ∉ m) :
    insA x a m = u ↔ u = insA x a (u.filter (· ≠ x)) ∧ m = u.filter (· ≠ x) := by
  constructor
  · rintro rfl; rw [filter_insA hm]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [h2, ← h1]

/-! ### Shuffles -/

/-- `shq q u v`: the sum of the lists `z` with `z|_q = u` and `z|_{¬q} = v`. When `u`, `v` are
words on complementary letter sets these are the interleavings of `u` and `v`. -/
noncomputable def shq (q : α → Bool) (u v : List α) : List α →₀ ℂ :=
  Finsupp.onFinset (u ++ v).permutations.toFinset
    (fun z => if z.filter q = u ∧ z.filter (fun b => !q b) = v then 1 else 0) (by
      intro z hz
      rw [List.mem_toFinset, List.mem_permutations]
      dsimp only at hz
      split_ifs at hz with h
      · rw [← h.1, ← h.2]; exact (List.filter_append_perm q z).symm
      · exact absurd rfl hz)

lemma shq_apply (q : α → Bool) (u v z : List α) :
    shq q u v z = if z.filter q = u ∧ z.filter (fun b => !q b) = v then 1 else 0 :=
  Finsupp.onFinset_apply

lemma shq_swap (q : α → Bool) (u v : List α) : shq q u v = shq (fun b => !q b) v u := by
  ext z
  simp only [shq_apply, Bool.not_not]
  congr 1
  exact propext and_comm

/-- Changing the predicate at the single letter `x` does not change a shuffle of `x`-free
words. -/
lemma shq_congr {q q' : α → Bool} (h : ∀ b, b ≠ x → q b = q' b) {u v : List α} (hu : x ∉ u)
    (hv : x ∉ v) : shq q u v = shq q' u v := by
  ext z
  simp only [shq_apply]
  by_cases hz : x ∈ z
  · have key : ∀ p : α → Bool, ¬ (z.filter p = u ∧ z.filter (fun b => !p b) = v) := by
      rintro p ⟨h1, h2⟩
      cases hp : p x
      · exact hv (h2 ▸ List.mem_filter.2 ⟨hz, by simp [hp]⟩)
      · exact hu (h1 ▸ List.mem_filter.2 ⟨hz, hp⟩)
    rw [if_neg (key q), if_neg (key q')]
  · have h1 : z.filter q = z.filter q' :=
      List.filter_congr fun b hb => h b (fun hbx => hz (hbx ▸ hb))
    have h2 : z.filter (fun b => !q b) = z.filter (fun b => !q' b) :=
      List.filter_congr fun b hb => by rw [h b (fun hbx => hz (hbx ▸ hb))]
    rw [h1, h2]

/-- `Sh_A` on lists: the span of the proper shuffles `u ⧢ v`, `u` a word on `S`, `v` a word on
`A ∖ S`, `∅ ≠ S ⊊ A`. -/
noncomputable def ShL (A : Finset α) : Submodule ℂ (List α →₀ ℂ) :=
  Submodule.span ℂ
    {X | ∃ (S : Finset α) (u v : List α), S ⊆ A ∧ S.Nonempty ∧ S ≠ A ∧ IsWordOn S u ∧
      IsWordOn (A \ S) v ∧ X = shq (fun b => decide (b ∈ S)) u v}

/-! ### The contraction operator `E_{a,x}` -/

/-- `E_{a,x}`: `E(X)(y) = X(y[a→xa]) - X(y[a→ax])` for `x ∉ y`, and `0` if `x ∈ y`. On a word
`w` it is `+(w∖x)` if `x` immediately precedes `a`, `-(w∖x)` if it immediately follows `a`, and
`0` otherwise. -/
noncomputable def E (a x : α) : (List α →₀ ℂ) →ₗ[ℂ] (List α →₀ ℂ) where
  toFun X := Finsupp.onFinset (X.support.image (List.filter (· ≠ x)))
    (fun y => if x ∈ y then 0 else X (ins x a y) - X (insA x a y)) (by
      intro y hy
      dsimp only at hy
      split_ifs at hy with hxy
      · exact absurd rfl hy
      · rw [Finset.mem_image]
        by_cases h1 : X (ins x a y) = 0
        · refine ⟨insA x a y, ?_, filter_insA hxy⟩
          rw [Finsupp.mem_support_iff]
          intro h2; rw [h1, h2, sub_zero] at hy; exact hy rfl
        · exact ⟨ins x a y, Finsupp.mem_support_iff.2 h1, filter_ins hxy⟩)
  map_add' X Y := by
    ext y
    simp only [Finsupp.onFinset_apply, Finsupp.add_apply]
    split_ifs <;> ring
  map_smul' c X := by
    ext y
    simp only [Finsupp.onFinset_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma E_apply (X : List α →₀ ℂ) (y : List α) :
    E a x X y = if x ∈ y then 0 else X (ins x a y) - X (insA x a y) :=
  rfl

/-- The coefficient `c ∈ {1, -1, 0}` of Lemma 1: `+1` if `xa` is a factor of `u`, `-1` if `ax`
is. -/
noncomputable def sgnE (x a : α) (u : List α) : ℂ :=
  if u = ins x a (u.filter (· ≠ x)) then 1
  else if u = insA x a (u.filter (· ≠ x)) then -1 else 0

/-- Lemma 1, case `x, a` on the `q`-side. -/
lemma E_shq_tt (hxa : x ≠ a) (hqx : q x = true) (hqa : q a = true) {u v : List α}
    (hxu : x ∈ u) (hxv : x ∉ v) :
    E a x (shq q u v) = sgnE x a u • shq q (u.filter (· ≠ x)) v := by
  set u' := u.filter (· ≠ x) with hu'
  have hxu' : x ∉ u' := by simp [hu']
  have hnot : ¬ (u = ins x a u' ∧ u = insA x a u') := by
    rintro ⟨h1, h2⟩
    have ha : a ∈ u' := by
      have := h1 ▸ hxu
      rcases mem_ins.1 this with h | h
      · exact absurd h hxu'
      · exact h.2
    exact ins_ne_insA hxa ha (h1.symm.trans h2)
  ext y
  rw [E_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hy : x ∈ y
  · rw [if_pos hy, shq_apply, if_neg, mul_zero]
    rintro ⟨h1, -⟩
    exact hxu' (h1 ▸ List.mem_filter.2 ⟨hy, hqx⟩)
  · rw [if_neg hy]
    have hqnx : (fun b => !q b) x = false := by simp [hqx]
    have hqna : (fun b => !q b) a = false := by simp [hqa]
    have hm : x ∉ y.filter q := fun h => hy (List.mem_of_mem_filter h)
    have hm' : x ∉ u' := hxu'
    have inj : ∀ {m m' : List α}, x ∉ m → x ∉ m' → (ins x a m = ins x a m' ↔ m = m') :=
      fun hm hm' => ⟨fun h => by rw [← filter_ins hm, h, filter_ins hm'], fun h => h ▸ rfl⟩
    have injA : ∀ {m m' : List α}, x ∉ m → x ∉ m' → (insA x a m = insA x a m' ↔ m = m') :=
      fun hm hm' => ⟨fun h => by rw [← filter_insA hm, h, filter_insA hm'], fun h => h ▸ rfl⟩
    rw [shq_apply, shq_apply, shq_apply, filter_ins_tt hqx hqa, filter_insA_tt hqx hqa,
      filter_ins_ff (q := fun b => !q b) (x := x) (a := a) hqnx hqna,
      filter_insA_ff (q := fun b => !q b) (x := x) (a := a) hqnx hqna, sgnE, ← hu']
    by_cases h1 : u = ins x a u'
    · have e1 : ins x a (y.filter q) = u ↔ y.filter q = u' := by rw [h1]; exact inj hm hm'
      have e2 : ¬ insA x a (y.filter q) = u := fun h => hnot ⟨h1, ((insA_eq_iff hm).1 h).1⟩
      simp only [e1, e2, if_pos h1, false_and, if_false, sub_zero, one_mul]
    · have e1 : ¬ ins x a (y.filter q) = u := fun h => h1 ((ins_eq_iff hm).1 h).1
      by_cases h2 : u = insA x a u'
      · have e2 : insA x a (y.filter q) = u ↔ y.filter q = u' := by
          rw [h2]; exact injA hm hm'
        simp only [e1, e2, if_neg h1, if_pos h2, false_and, if_false, zero_sub, neg_one_mul]
      · have e2 : ¬ insA x a (y.filter q) = u := fun h => h2 ((insA_eq_iff hm).1 h).1
        simp only [e1, e2, if_neg h1, if_neg h2, false_and, if_false, sub_zero, zero_mul]

/-- Lemma 1, case `x, a` both off the `q`-side. -/
lemma E_shq_ff (hxa : x ≠ a) (hqx : q x = false) (hqa : q a = false) {u v : List α}
    (hxu : x ∉ u) (hxv : x ∈ v) :
    E a x (shq q u v) = sgnE x a v • shq q u (v.filter (· ≠ x)) := by
  rw [shq_swap, E_shq_tt hxa (by simp [hqx]) (by simp [hqa]) hxv hxu, shq_swap]
  simp only [Bool.not_not]

/-- Lemma 1, case `x`, `a` on different sides: the image vanishes. -/
lemma E_shq_mixed (h : q x ≠ q a) (u v : List α) : E a x (shq q u v) = 0 := by
  ext y
  rw [E_apply, Finsupp.zero_apply]
  split_ifs
  · rfl
  · have h' : (fun b => !q b) x ≠ (fun b => !q b) a := by simpa using h
    rw [shq_apply, shq_apply, filter_ins_eq_insA h y,
      filter_ins_eq_insA (q := fun b => !q b) (x := x) (a := a) h' y, sub_self]

lemma isWordOn_filter_ne {S : Finset α} {u : List α} (hu : IsWordOn S u) (x : α) :
    IsWordOn (S.erase x) (u.filter (· ≠ x)) := by
  refine ⟨hu.1.filter _, ?_⟩
  rw [List.toFinset_filter, hu.2]
  ext b; simp [and_comm]

/-- **Lemma 1** (`notes/conjecture_s_splitting_cycles_span.md` §2): `E_{a,x}(Sh_A) ⊆ Sh_{A∖x}`
for distinct letters `a, x ∈ A`. -/
theorem map_E_ShL {A : Finset α} (hxa : x ≠ a) (hx : x ∈ A) (ha : a ∈ A) :
    (ShL A).map (E a x) ≤ ShL (A.erase x) := by
  rw [ShL, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨S, u, v, hSA, hne, hSne, hu, hv, rfl⟩, rfl⟩
  obtain ⟨b, hbA, hbS⟩ : ∃ b ∈ A, b ∉ S := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hSne (Finset.Subset.antisymm hSA h)
  have gen : ∀ (S' : Finset α) (u' v' : List α), S' ⊆ A.erase x → S'.Nonempty →
      S' ≠ A.erase x → IsWordOn S' u' → IsWordOn (A.erase x \ S') v' →
      shq (fun b => decide (b ∈ S')) u' v' ∈ ShL (A.erase x) := fun S' u' v' h1 h2 h3 h4 h5 =>
    Submodule.subset_span ⟨S', u', v', h1, h2, h3, h4, h5, rfl⟩
  by_cases hxS : x ∈ S <;> by_cases haS : a ∈ S
  · -- both in `S`
    have hxv : x ∉ v := fun h => by
      have := hv.2 ▸ List.mem_toFinset.2 h; simp [hxS] at this
    rw [E_shq_tt hxa (by simpa using hxS) (by simpa using haS)
      (List.mem_toFinset.1 (hu.2 ▸ hxS)) hxv]
    refine Submodule.smul_mem _ _ ?_
    rw [shq_congr (q' := fun b => decide (b ∈ S.erase x)) (fun b hb => by simp [hb])
      (by simp) hxv]
    refine gen _ _ _ (Finset.erase_subset_erase _ hSA) ⟨a, by simp [haS, hxa.symm]⟩ ?_
      (isWordOn_filter_ne hu x) ?_
    · intro h
      have : b ∈ S.erase x := h ▸ Finset.mem_erase.2 ⟨fun hbx => hbS (hbx ▸ hxS), hbA⟩
      exact hbS (Finset.mem_of_mem_erase this)
    · have : A.erase x \ S.erase x = A \ S := by
        ext c; by_cases hc : c = x <;> simp [hc, hxS]
      rw [this]; exact hv
  · rw [E_shq_mixed (by simp [hxS, haS])]; exact zero_mem _
  · rw [E_shq_mixed (by simp [hxS, haS])]; exact zero_mem _
  · -- both off `S`
    have hxu : x ∉ u := fun h => hxS (hu.2 ▸ List.mem_toFinset.2 h)
    have hxv : x ∈ v := List.mem_toFinset.1 (hv.2 ▸ Finset.mem_sdiff.2 ⟨hx, hxS⟩)
    rw [E_shq_ff hxa (by simpa using hxS) (by simpa using haS) hxu hxv]
    refine Submodule.smul_mem _ _ (gen _ _ _ ?_ hne ?_ hu ?_)
    · intro c hc; exact Finset.mem_erase.2 ⟨fun hcx => hxS (hcx ▸ hc), hSA hc⟩
    · intro h
      exact haS (h ▸ Finset.mem_erase.2 ⟨hxa.symm, ha⟩)
    · have := isWordOn_filter_ne hv x
      have e : (A \ S).erase x = A.erase x \ S := by
        ext c; by_cases hc : c = x <;> simp [hc]
      rwa [e] at this

/-! ### Linear extensions of a relation, unions of components, contraction -/

variable (r : α → α → Prop)

/-- `l` is a linear extension of `r` on `A`: a word on `A` that never puts `q` before `p` when
`r p q`. -/
def LinL (A : Finset α) (l : List α) : Prop := IsWordOn A l ∧ l.Pairwise fun p q => ¬ r q p

/-- `U` is a union of components of `r` on `A`: closed under `r`-related pairs inside `A`. -/
def UoC (A U : Finset α) : Prop := ∀ p ∈ A, ∀ q ∈ A, r p q → (p ∈ U ↔ q ∈ U)

/-- `B_P` on lists: linear extensions whose nonempty union-prefixes all contain `x₀`. -/
def InBL (A : Finset α) (x₀ : α) (l : List α) : Prop :=
  LinL r A l ∧ ∀ s t, l = s ++ t → s ≠ [] → UoC r A s.toFinset → x₀ ∈ s

/-- The relation of the contraction `P/{a,x}`: relations through `x` are moved to `a`. -/
def rc (a x : α) : α → α → Prop := fun p q => r p q ∨ (p = a ∧ r x q) ∨ (q = a ∧ r p x)

/-- Pull back a subset of `A ∖ x` along the contraction: add `x` if `a` is present. -/
def pb (a x : α) (U : Finset α) : Finset α := if a ∈ U then insert x U else U

variable {r}

lemma isWordOn_perm {A : Finset α} {l l' : List α} (h : l.Perm l') (hl : IsWordOn A l) :
    IsWordOn A l' := ⟨h.nodup_iff.1 hl.1, by rw [← List.toFinset_eq_of_perm _ _ h]; exact hl.2⟩

lemma mem_of_isWordOn {A : Finset α} {l : List α} (hl : IsWordOn A l) {b : α} :
    b ∈ l ↔ b ∈ A := by rw [← hl.2, List.mem_toFinset]

lemma mem_pb {a x : α} {U : Finset α} (hx : x ∉ U) {b : α} :
    b ∈ pb a x U ↔ (b ≠ x ∧ b ∈ U) ∨ (b = x ∧ a ∈ U) := by
  unfold pb
  split_ifs with ha
  · rw [Finset.mem_insert]
    by_cases hb : b = x
    · subst hb; simp [ha]
    · simp [hb]
  · by_cases hb : b = x
    · subst hb; simp [hx, ha]
    · simp [hb]

lemma uoC_pb {A U : Finset α} {a x : α} (hxa : x ≠ a) (ha : a ∈ A) (hx : x ∉ U)
    (h : UoC (rc r a x) (A.erase x) U) : UoC r A (pb a x U) := by
  intro p hp q hq hpq
  rw [mem_pb hx, mem_pb hx]
  have haA : a ∈ A.erase x := Finset.mem_erase.2 ⟨hxa.symm, ha⟩
  by_cases hpx : p = x <;> by_cases hqx : q = x
  · subst hpx; subst hqx; exact Iff.rfl
  · subst hpx
    have := h a haA q (Finset.mem_erase.2 ⟨hqx, hq⟩) (Or.inr (Or.inl ⟨rfl, hpq⟩))
    simp [hqx, this]
  · subst hqx
    have := h p (Finset.mem_erase.2 ⟨hpx, hp⟩) a haA (Or.inr (Or.inr ⟨rfl, hpq⟩))
    simp [hpx, this]
  · have := h p (Finset.mem_erase.2 ⟨hpx, hp⟩) q (Finset.mem_erase.2 ⟨hqx, hq⟩) (Or.inl hpq)
    simp [hpx, hqx, this]

/-- The base point of the contraction. -/
def bp (a x x₀ : α) : α := if x₀ = x then a else x₀

lemma bp_mem {a x x₀ : α} {U : Finset α} (hx : x ∉ U) (h : x₀ ∈ pb a x U) : bp a x x₀ ∈ U := by
  rw [mem_pb hx] at h
  unfold bp
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_neg h1]; exact h2
  · rw [if_pos h1]; exact h2

/-- **Lemma 2(a), 5** (`notes/conjecture_s_splitting_cycles_span.md` §3), linear-extension
part: deleting `x` from a linear extension in which `x`, `a` are adjacent gives a linear
extension of the contraction. -/
lemma linL_contract {A : Finset α} {a x : α} (hxa : x ≠ a) {pre post c : List α}
    (hc : c = [x, a] ∨ c = [a, x]) (h : LinL r A (pre ++ c ++ post)) :
    LinL (rc r a x) (A.erase x) (pre ++ a :: post) := by
  obtain ⟨⟨hnd, hset⟩, hpw⟩ := h
  have hpre := hpw.sublist ((List.sublist_append_left pre c).trans (List.sublist_append_left _ post))
  have hpost := hpw.sublist (List.sublist_append_right (pre ++ c) post)
  rcases hc with rfl | rfl <;>
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd ⊢
      grind
    · rw [← hset]; ext b
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
        List.mem_toFinset, Finset.mem_erase]
      simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd
      grind
    · simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd
      simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons, List.mem_append,
        List.mem_singleton] at hpw
      rw [List.pairwise_append, List.pairwise_cons]
      refine ⟨hpre.imp_of_mem fun {p q} hp hq h => ?_, ⟨fun q hq => ?_,
        hpost.imp_of_mem fun {p q} hp hq h => ?_⟩, fun p hp q hq => ?_⟩ <;> simp only [rc] <;>
        grind

/-- A split of `pre ++ a :: post` pulls back to a split of `pre ++ c ++ post` (`c = xa` or
`ax`) whose first part has letter set `pb a x` of the first part. -/
lemma split_pullback {a x : α} {pre post c s' t' : List α} (hc : c = [x, a] ∨ c = [a, x])
    (hpre : a ∉ pre) (h : pre ++ a :: post = s' ++ t') :
    ∃ s t, pre ++ c ++ post = s ++ t ∧ s.toFinset = pb a x s'.toFinset ∧ (s' ≠ [] → s ≠ []) := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · rcases List.cons_eq_append_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨as', rfl, rfl⟩
    · refine ⟨pre, c ++ post, by simp, ?_, fun hs => ?_⟩
      · rw [pb, if_neg (by simpa [h1] using hpre), h1, List.append_nil]
      · rw [h1, List.append_nil] at hs; exact hs
    · refine ⟨pre ++ c ++ as', t', by simp, ?_, fun _ => by rcases hc with rfl | rfl <;> simp⟩
      rw [h1, pb, if_pos (by simp)]
      rcases hc with rfl | rfl <;> ext b <;> simp <;> tauto
  · refine ⟨s', bs ++ c ++ post, by simp [h1], ?_, id⟩
    rw [pb, if_neg (by intro ha; exact hpre (h1 ▸ List.mem_append_left _ (List.mem_toFinset.1 ha)))]

/-- **Lemma 5** (`notes/conjecture_s_splitting_cycles_span.md` §3): if `x`, `a` are adjacent
in `w ∈ B_P`, then `w ∖ x ∈ B_Q` for the contraction `Q = P/{a,x}` with base point `bp`. -/
lemma inBL_contract {A : Finset α} {a x x₀ : α} (hxa : x ≠ a) {pre post c : List α}
    (hc : c = [x, a] ∨ c = [a, x]) (h : InBL r A x₀ (pre ++ c ++ post)) :
    InBL (rc r a x) (A.erase x) (bp a x x₀) (pre ++ a :: post) := by
  have hlin := linL_contract hxa hc h.1
  refine ⟨hlin, fun s' t' hst hs' hU => ?_⟩
  have hnd := h.1.1.1
  have hpre : a ∉ pre := by
    rcases hc with rfl | rfl <;>
    · simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd
      grind
  have hxs' : x ∉ s'.toFinset := by
    intro hx
    have : x ∈ pre ++ a :: post := hst ▸ List.mem_append_left _ (List.mem_toFinset.1 hx)
    have := (mem_of_isWordOn hlin.1).1 this
    simp at this
  obtain ⟨s, t, hz, hs, hne⟩ := split_pullback hc hpre hst
  have hA : a ∈ A := (mem_of_isWordOn h.1.1).1 (by rcases hc with rfl | rfl <;> simp)
  have hx0 := h.2 s t hz (hne hs') (hs ▸ uoC_pb hxa hA hxs' hU)
  exact List.mem_toFinset.1 (bp_mem hxs' (hs ▸ List.mem_toFinset.2 hx0))

/-! ### From swaps to permutations -/

/-- A function on lists invariant under adjacent transpositions is invariant under
permutations. -/
lemma perm_invariant (f : List α → ℂ)
    (h : ∀ pre post (p q : α), f (pre ++ p :: q :: post) = f (pre ++ q :: p :: post))
    {l l' : List α} (hl : l.Perm l') : f l = f l' := by
  suffices ∀ pre, f (pre ++ l) = f (pre ++ l') by simpa using this []
  induction hl with
  | nil => intro; rfl
  | cons b _ ih => intro pre; simpa using ih (pre ++ [b])
  | swap b c l => intro pre; exact h pre l c b
  | trans _ _ ih1 ih2 => intro pre; exact (ih1 pre).trans (ih2 pre)

lemma word_cons (A : Finset α) {y : α} (hy : y ∈ A) : IsWordOn A (y :: (A.erase y).toList) := by
  refine ⟨List.nodup_cons.2 ⟨by simp, Finset.nodup_toList _⟩, ?_⟩
  ext b; by_cases hb : b = y <;> simp [hb, hy]

/-- If every word on `A` is a linear extension, `r` relates no two distinct letters of `A`. -/
lemma discrete_of_all_lin {A : Finset α} (h : ∀ l, IsWordOn A l → LinL r A l) {p q : α}
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) : ¬ r p q := by
  have hw : IsWordOn A (q :: p :: ((A.erase q).erase p).toList) := by
    have := word_cons A hq
    refine ⟨?_, ?_⟩
    · refine List.nodup_cons.2 ⟨by simp [hpq.symm], List.nodup_cons.2 ⟨by simp, ?_⟩⟩
      exact Finset.nodup_toList _
    · ext b; by_cases hb : b = q <;> by_cases hb' : b = p <;> simp [hb, hb', hp, hq]
  have := (h _ hw).2
  simp only [List.pairwise_cons, List.mem_cons] at this
  exact this.1 p (Or.inl rfl)

lemma ShL_eq_bot {A : Finset α} (hA : A.card ≤ 1) : ShL A = ⊥ := by
  rw [ShL, Submodule.span_eq_bot]
  rintro _ ⟨S, u, v, hSA, hne, hSne, -, -, -, rfl⟩
  exact absurd (Finset.eq_of_subset_of_card_le hSA
    (hA.trans (Finset.one_le_card.2 hne))) hSne

/-- If `E_{a,x}(X) = 0` for all distinct `a, x ∈ A` and `X` lives on words on `A`, then `X` is
invariant under adjacent transpositions, hence under all permutations of positions. -/
lemma perm_invariant_of_E {A : Finset α} {X : List α →₀ ℂ}
    (hX : ∀ l, X l ≠ 0 → IsWordOn A l)
    (hE : ∀ x ∈ A, ∀ a ∈ A, x ≠ a → E a x X = 0) {l l' : List α} (hl : l.Perm l') :
    X l = X l' := by
  refine perm_invariant X (fun pre post p q => ?_) hl
  by_cases hpq : p = q
  · rw [hpq]
  have hperm : (pre ++ p :: q :: post).Perm (pre ++ q :: p :: post) :=
    List.Perm.append_left _ (List.Perm.swap q p post)
  by_cases hw : IsWordOn A (pre ++ p :: q :: post)
  · have hnd := hw.1
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd
    have hpA : p ∈ A := (mem_of_isWordOn hw).1 (by simp)
    have hqA : q ∈ A := (mem_of_isWordOn hw).1 (by simp)
    have hq1 : q ∉ pre := by grind
    have hq2 : q ∉ post := by grind
    have hp : p ∉ pre ++ q :: post := by simp; grind
    have := congrArg (fun F => F (pre ++ q :: post)) (hE p hpA q hqA hpq)
    simp only [E_apply, if_neg hp, Finsupp.zero_apply, ins_append, insA_append, ins_cons,
      insA_cons, if_true, ins_of_not_mem hq1, ins_of_not_mem hq2, insA_of_not_mem hq1,
      insA_of_not_mem hq2, sub_eq_zero] at this
    simpa using this
  · have h1 : X (pre ++ p :: q :: post) = 0 := by
      by_contra h; exact hw (hX _ h)
    have h2 : X (pre ++ q :: p :: post) = 0 := by
      by_contra h; exact hw (isWordOn_perm hperm.symm (hX _ h))
    rw [h1, h2]

/-- A permutation-invariant `X` on words on `A` that vanishes at one word vanishes. -/
lemma eq_zero_of_perm_invariant {A : Finset α} {X : List α →₀ ℂ}
    (hX : ∀ l, X l ≠ 0 → IsWordOn A l) (hperm : ∀ l l', l.Perm l' → X l = X l')
    {l₀ : List α} (hl₀ : IsWordOn A l₀) (h0 : X l₀ = 0) : X = 0 := by
  ext l
  by_contra h
  have hl := hX l h
  have : l.Perm l₀ := List.perm_of_nodup_nodup_toFinset_eq hl.1 hl₀.1 (hl.2.trans hl₀.2.symm)
  exact h ((hperm _ _ this).trans h0)

/-- Supports of `E_{a,x} X` come from words with `x`, `a` adjacent. -/
lemma E_support {A : Finset α} {X : List α →₀ ℂ} (hX : ∀ l, X l ≠ 0 → IsWordOn A l)
    {a x : α} (hxa : x ≠ a) (ha : a ∈ A) {y : List α} (hy : E a x X y ≠ 0) :
    ∃ pre post c, (c = [x, a] ∨ c = [a, x]) ∧ y = pre ++ a :: post ∧ X (pre ++ c ++ post) ≠ 0 := by
  rw [E_apply] at hy
  split_ifs at hy with hxy
  · exact absurd rfl hy
  have key : ∀ z, (z = ins x a y ∨ z = insA x a y) → X z ≠ 0 → ∃ pre post c,
      (c = [x, a] ∨ c = [a, x]) ∧ y = pre ++ a :: post ∧ X (pre ++ c ++ post) ≠ 0 := by
    intro z hz hXz
    have hw := hX z hXz
    have haz : a ∈ z := (mem_of_isWordOn hw).2 ha
    have hay : a ∈ y := by
      rcases hz with rfl | rfl
      · rcases mem_ins.1 haz with h | h
        · exact h
        · exact absurd h.1.symm hxa
      · rcases mem_insA.1 haz with h | h
        · exact h
        · exact absurd h.1.symm hxa
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hay
    have hndy : (pre ++ a :: post).Nodup := by
      have := hw.1.filter (fun b => decide (b ≠ x))
      rcases hz with rfl | rfl
      · rwa [filter_ins hxy] at this
      · rwa [filter_insA hxy] at this
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hndy
    have h1 : a ∉ pre := by grind
    have h2 : a ∉ post := by grind
    rcases hz with rfl | rfl
    · refine ⟨pre, post, [x, a], Or.inl rfl, rfl, ?_⟩
      simpa [ins_of_not_mem h1, ins_of_not_mem h2] using hXz
    · refine ⟨pre, post, [a, x], Or.inr rfl, rfl, ?_⟩
      simpa [insA_of_not_mem h1, insA_of_not_mem h2] using hXz
  by_cases h1 : X (ins x a y) = 0
  · refine key _ (Or.inr rfl) ?_
    intro h2; rw [h1, h2, sub_zero] at hy; exact hy rfl
  · exact key _ (Or.inl rfl) h1

/-! ### Theorem A: `B_P` is independent modulo shuffles -/

/-- **Theorem A** (`notes/conjecture_s_splitting_cycles_span.md` §4), on lists: a combination
of words of `B_P` that is a sum of proper shuffles vanishes. The relation `r` is arbitrary. -/
theorem eq_zero_of_inBL (A : Finset α) (r : α → α → Prop) (x₀ : α) (X : List α →₀ ℂ)
    (hSh : X ∈ ShL A) (hB : ∀ l, X l ≠ 0 → InBL r A x₀ l) : X = 0 := by
  induction hn : A.card using Nat.strong_induction_on generalizing A r x₀ X with
  | _ n ih =>
  by_cases hA : A.card ≤ 1
  · rw [ShL_eq_bot hA] at hSh; exact (Submodule.mem_bot ℂ).1 hSh
  have hW : ∀ l, X l ≠ 0 → IsWordOn A l := fun l h => (hB l h).1.1
  have hE : ∀ x ∈ A, ∀ a ∈ A, x ≠ a → E a x X = 0 := by
    intro x hx a ha hxa
    refine ih (A.erase x).card (by rw [Finset.card_erase_of_mem hx]; omega) (A.erase x)
      (rc r a x) (bp a x x₀) _ (map_E_ShL hxa hx ha (Submodule.mem_map_of_mem hSh))
      (fun y hy => ?_) rfl
    obtain ⟨pre, post, c, hc, rfl, hXz⟩ := E_support hW hxa ha hy
    exact inBL_contract hxa hc (hB _ hXz)
  have hperm := fun l l' (h : List.Perm l l') => perm_invariant_of_E hW hE h
  obtain ⟨y, hyA, hyx⟩ : ∃ y ∈ A, y ≠ x₀ := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hA (Finset.card_le_one.2 fun b hb c hc => (h b hb).trans (h c hc).symm)
  by_cases hall : ∀ l, IsWordOn A l → LinL r A l
  · refine eq_zero_of_perm_invariant hW hperm (word_cons A hyA) ?_
    by_contra h
    have := (hB _ h).2 [y] _ rfl (by simp) (fun p hp q hq hpq => ?_)
    · simp at this; exact hyx this.symm
    · by_cases hpq' : p = q
      · rw [hpq']
      · exact absurd hpq (discrete_of_all_lin hall hp hq hpq')
  · simp only [not_forall] at hall
    obtain ⟨l₀, hl₀, hlin⟩ := hall
    refine eq_zero_of_perm_invariant hW hperm hl₀ ?_
    by_contra h; exact hlin (hB _ h).1

/-! ### Unions of components, rotations at cuts -/

lemma uoC_union {A U V : Finset α} (hU : UoC r A U) (hV : UoC r A V) : UoC r A (U ∪ V) :=
  fun p hp q hq h => by simp only [Finset.mem_union, hU p hp q hq h, hV p hp q hq h]

lemma uoC_inter {A U V : Finset α} (hU : UoC r A U) (hV : UoC r A V) : UoC r A (U ∩ V) :=
  fun p hp q hq h => by simp only [Finset.mem_inter, hU p hp q hq h, hV p hp q hq h]

lemma uoC_sdiff {A U : Finset α} (hU : UoC r A U) : UoC r A (A \ U) :=
  fun p hp q hq h => by simp only [Finset.mem_sdiff, hp, hq, true_and, hU p hp q hq h]

lemma toFinset_right {A : Finset α} {s t : List α} (h : IsWordOn A (s ++ t)) :
    t.toFinset = A \ s.toFinset := by
  rw [← h.2]
  have hd := (List.nodup_append.1 h.1).2.2
  ext b
  simp only [List.mem_toFinset, Finset.mem_sdiff, List.toFinset_append, Finset.mem_union]
  constructor
  · intro hb; exact ⟨Or.inr hb, fun hs => hd b hs b hb rfl⟩
  · rintro ⟨hb | hb, hs⟩
    · exact absurd hb hs
    · exact hb

/-- Rotating a linear extension at a union-prefix gives a linear extension. -/
lemma linL_rotate {A : Finset α} {s t : List α} (h : LinL r A (s ++ t))
    (hs : UoC r A s.toFinset) : LinL r A (t ++ s) := by
  refine ⟨isWordOn_perm List.perm_append_comm h.1, ?_⟩
  have hpw := List.pairwise_append.1 h.2
  have hd := (List.nodup_append.1 h.1.1).2.2
  refine List.pairwise_append.2 ⟨hpw.2.1, hpw.1, fun p hp q hq hqp => ?_⟩
  have hpA : p ∈ A := (mem_of_isWordOn h.1).1 (List.mem_append_right _ hp)
  have hqA : q ∈ A := (mem_of_isWordOn h.1).1 (List.mem_append_left _ hq)
  have := (hs q hqA p hpA hqp).1 (List.mem_toFinset.2 hq)
  exact hd p (List.mem_toFinset.1 this) p hp rfl

/-- Conversely, if both `s ++ t` and `t ++ s` are linear extensions, `s` is a union of
components. -/
lemma uoC_of_linL_rotate {A : Finset α} {s t : List α} (h : LinL r A (s ++ t))
    (h' : LinL r A (t ++ s)) : UoC r A s.toFinset := by
  intro p hp q hq hpq
  have hw := h.1
  have hpt : p ∈ s ∨ p ∈ t := List.mem_append.1 ((mem_of_isWordOn hw).2 hp)
  have hqt : q ∈ s ∨ q ∈ t := List.mem_append.1 ((mem_of_isWordOn hw).2 hq)
  have hd := (List.nodup_append.1 hw.1).2.2
  have c1 := (List.pairwise_append.1 h.2).2.2
  have c2 := (List.pairwise_append.1 h'.2).2.2
  simp only [List.mem_toFinset]
  rcases hpt with hp' | hp' <;> rcases hqt with hq' | hq'
  · exact iff_of_true hp' hq'
  · exact absurd hpq (c2 q hq' p hp')
  · exact absurd hpq (c1 q hq' p hp')
  · exact iff_of_false (fun h => hd p h p hp' rfl) (fun h => hd q h q hq' rfl)

/-! ### Weights -/

/-- `λ(l) = ∏_{b ∈ l} λ(b)`. -/
def lamL (lam : α → ℂ) (l : List α) : ℂ := (l.map lam).prod

/-- The weights of the contraction: `λ'(a) = λ(a) λ(x)`. -/
def lamc (lam : α → ℂ) (a x : α) : α → ℂ := fun b => if b = a then lam a * lam x else lam b

@[simp] lemma lamL_nil (lam : α → ℂ) : lamL lam [] = 1 := rfl

lemma lamL_append (lam : α → ℂ) (l₁ l₂ : List α) :
    lamL lam (l₁ ++ l₂) = lamL lam l₁ * lamL lam l₂ := by simp [lamL]

lemma lamL_perm (lam : α → ℂ) {l₁ l₂ : List α} (h : l₁.Perm l₂) : lamL lam l₁ = lamL lam l₂ :=
  (h.map lam).prod_eq

lemma lamL_eq_prod (lam : α → ℂ) {l : List α} (h : l.Nodup) :
    lamL lam l = ∏ b ∈ l.toFinset, lam b := (List.prod_toFinset lam h).symm

lemma lamL_ins (lam : α → ℂ) (a x : α) (l : List α) :
    lamL lam (ins x a l) = lamL (lamc lam a x) l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [ins_cons, lamL_append, ih]
    by_cases hb : b = a
    · subst hb
      simp only [lamL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, lamc,
        if_pos rfl, if_true]
      ring
    · simp [lamL, lamc, hb]

lemma lamL_insA (lam : α → ℂ) (a x : α) (l : List α) :
    lamL lam (insA x a l) = lamL (lamc lam a x) l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [insA_cons, lamL_append, ih]
    by_cases hb : b = a
    · subst hb
      simp only [lamL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, lamc,
        if_pos rfl, if_true]
      ring
    · simp [lamL, lamc, hb]

lemma toFinset_ins {a x : α} {l : List α} (hx : x ∉ l) :
    (ins x a l).toFinset = pb a x l.toFinset := by
  ext b
  rw [List.mem_toFinset, mem_ins, mem_pb (by simpa using hx), List.mem_toFinset,
    List.mem_toFinset]
  by_cases hb : b = x
  · subst hb; simp [hx]
  · simp [hb]

lemma toFinset_insA {a x : α} {l : List α} (hx : x ∉ l) :
    (insA x a l).toFinset = pb a x l.toFinset := by
  ext b
  rw [List.mem_toFinset, mem_insA, mem_pb (by simpa using hx), List.mem_toFinset,
    List.mem_toFinset]
  by_cases hb : b = x
  · subst hb; simp [hx]
  · simp [hb]

lemma isWordOn_ins {A : Finset α} {a x : α} (hxa : x ≠ a) (hx : x ∈ A) {y : List α}
    (hy : IsWordOn (A.erase x) y) (ha : a ∈ y) :
    IsWordOn A (ins x a y) ∧ IsWordOn A (insA x a y) := by
  have hxy : x ∉ y := fun h => by simpa using (mem_of_isWordOn hy).1 h
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  have hnd := hy.1
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hnd
  have h1 : a ∉ pre := by grind
  have h2 : a ∉ post := by grind
  have hset : ∀ l, l.toFinset = pb a x (pre ++ a :: post).toFinset → IsWordOn A l →
      IsWordOn A l := fun _ _ h => h
  have hpb : pb a x (pre ++ a :: post).toFinset = A := by
    rw [hy.2, pb, if_pos (Finset.mem_erase.2 ⟨hxa.symm, ?_⟩), Finset.insert_erase hx]
    exact (mem_of_isWordOn hy).1 ha |> Finset.mem_of_mem_erase
  have hxy' : x ∉ pre ∧ x ∉ post := ⟨fun h => hxy (by simp [h]), fun h => hxy (by simp [h])⟩
  constructor
  · refine ⟨?_, by rw [toFinset_ins hxy, hpb]⟩
    rw [ins_append, ins_cons, if_pos rfl, ins_of_not_mem h1, ins_of_not_mem h2]
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd ⊢
    grind
  · refine ⟨?_, by rw [toFinset_insA hxy, hpb]⟩
    rw [insA_append, insA_cons, if_pos rfl, insA_of_not_mem h1, insA_of_not_mem h2]
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd ⊢
    grind

lemma prod_pb (lam : α → ℂ) {a x : α} (hxa : x ≠ a) {U : Finset α} (hx : x ∉ U) :
    ∏ b ∈ pb a x U, lam b = ∏ b ∈ U, lamc lam a x b := by
  unfold pb
  split_ifs with ha
  · rw [Finset.prod_insert hx, ← Finset.mul_prod_erase U _ ha,
      ← Finset.mul_prod_erase U (lamc lam a x) ha]
    have : ∏ b ∈ U.erase a, lamc lam a x b = ∏ b ∈ U.erase a, lam b :=
      Finset.prod_congr rfl fun b hb => if_neg (Finset.ne_of_mem_erase hb)
    rw [this, lamc, if_pos rfl]; ring
  · exact Finset.prod_congr rfl fun b hb => (if_neg (fun h : b = a => ha (h ▸ hb))).symm

/-! ### Theorem Ψ: weighted class sums are independent modulo shuffles -/

/-- The cyclic relation (Ψ.1) of the note: `X(t s) λ(s) = X(s t)` whenever `s` is a
union-prefix of the word `s t`. -/
def EqL (r : α → α → Prop) (A : Finset α) (lam : α → ℂ) (X : List α →₀ ℂ) : Prop :=
  ∀ s t, IsWordOn A (s ++ t) → UoC r A s.toFinset → X (t ++ s) * lamL lam s = X (s ++ t)

/-- Admissibility, the part used by the induction: `λ(U) ≠ 1` for nonempty proper unions of
components. -/
def AdmL (r : α → α → Prop) (A : Finset α) (lam : α → ℂ) : Prop :=
  ∀ U ⊆ A, U.Nonempty → U ≠ A → UoC r A U → ∏ b ∈ U, lam b ≠ 1

/-- **Theorem Ψ** (`notes/natural_isomorphism.md` §3.1), on lists: a combination of linear
extensions satisfying the cyclic relation (Ψ.1) for admissible weights, which is a sum of proper
shuffles, vanishes. -/
theorem eq_zero_of_eqL (A : Finset α) (r : α → α → Prop) (lam : α → ℂ) (X : List α →₀ ℂ)
    (hSh : X ∈ ShL A) (hlin : ∀ l, X l ≠ 0 → LinL r A l) (hEq : EqL r A lam X)
    (hadm : AdmL r A lam) : X = 0 := by
  induction hn : A.card using Nat.strong_induction_on generalizing A r lam X with
  | _ n ih =>
  by_cases hA : A.card ≤ 1
  · rw [ShL_eq_bot hA] at hSh; exact (Submodule.mem_bot ℂ).1 hSh
  have hW : ∀ l, X l ≠ 0 → IsWordOn A l := fun l h => (hlin l h).1
  have hE : ∀ x ∈ A, ∀ a ∈ A, x ≠ a → E a x X = 0 := by
    intro x hx a ha hxa
    have haA' : a ∈ A.erase x := Finset.mem_erase.2 ⟨hxa.symm, ha⟩
    refine ih (A.erase x).card (by rw [Finset.card_erase_of_mem hx]; omega) (A.erase x)
      (rc r a x) (lamc lam a x) _ (map_E_ShL hxa hx ha (Submodule.mem_map_of_mem hSh))
      (fun y hy => ?_) (fun s t hst hs => ?_) (fun U hU hne hUA hUoC => ?_) rfl
    · obtain ⟨pre, post, c, hc, rfl, hXz⟩ := E_support hW hxa ha hy
      exact linL_contract hxa hc (hlin _ hXz)
    · have hxst : x ∉ s ++ t := fun h => by simpa using (mem_of_isWordOn hst).1 h
      have hxs : x ∉ s := fun h => hxst (List.mem_append_left _ h)
      have hxt : x ∉ t := fun h => hxst (List.mem_append_right _ h)
      have hxts : x ∉ t ++ s := fun h => hxst (List.perm_append_comm.mem_iff.1 h)
      have haw : a ∈ s ++ t := (mem_of_isWordOn hst).2 haA'
      obtain ⟨hw1, hw2⟩ := isWordOn_ins hxa hx hst haw
      have hU : ∀ l : List α, x ∉ l → UoC (rc r a x) (A.erase x) l.toFinset →
          UoC r A (pb a x l.toFinset) := fun l hl h => uoC_pb hxa ha (by simpa using hl) h
      rw [E_apply, E_apply, if_neg hxts, if_neg hxst, ins_append, ins_append, insA_append,
        insA_append, sub_mul]
      rw [ins_append] at hw1
      rw [insA_append] at hw2
      rw [← hEq _ _ hw1 (by rw [toFinset_ins hxs]; exact hU s hxs hs),
        ← hEq _ _ hw2 (by rw [toFinset_insA hxs]; exact hU s hxs hs), lamL_ins, lamL_insA]
    · have hxU : x ∉ U := fun h => by simpa using hU h
      rw [← prod_pb lam hxa hxU]
      refine hadm _ ?_ ?_ ?_ (uoC_pb hxa ha hxU hUoC)
      · intro b hb
        rw [mem_pb hxU] at hb
        rcases hb with ⟨-, hb⟩ | ⟨rfl, -⟩
        · exact Finset.mem_of_mem_erase (hU hb)
        · exact hx
      · obtain ⟨b, hb⟩ := hne
        exact ⟨b, (mem_pb hxU).2 (Or.inl ⟨fun h => hxU (h ▸ hb), hb⟩)⟩
      · intro h
        apply hUA
        rw [← h]
        ext b
        by_cases hbx : b = x
        · subst hbx; simp [hxU]
        · simp [Finset.mem_erase, mem_pb hxU, hbx]
  have hperm := fun l l' (h : List.Perm l l') => perm_invariant_of_E hW hE h
  by_cases hall : ∀ l, IsWordOn A l → LinL r A l
  · obtain ⟨y, hyA⟩ : A.Nonempty := Finset.card_pos.1 (by omega)
    have hw := word_cons A hyA
    refine eq_zero_of_perm_invariant hW hperm hw ?_
    have hdisc : ∀ p ∈ A, ∀ q ∈ A, r p q → p = q := fun p hp q hq h => by
      by_contra hpq; exact discrete_of_all_lin hall hp hq hpq h
    have hUy : UoC r A ({y} : Finset α) := fun p hp q hq h => by rw [hdisc p hp q hq h]
    have key := hEq [y] (A.erase y).toList hw (by simpa using hUy)
    rw [hperm _ _ (List.perm_append_comm (l₁ := (A.erase y).toList) (l₂ := [y])),
      List.singleton_append] at key
    have hne : lam y ≠ 1 := by
      have := hadm {y} (by simpa using hyA) (by simp) (fun h => hA (by rw [← h]; simp)) hUy
      simpa using this
    have : X (y :: (A.erase y).toList) * (lam y - 1) = 0 := by
      simp only [lamL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one] at key
      rw [mul_sub, key, mul_one, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  · simp only [not_forall] at hall
    obtain ⟨l₀, hl₀, hlin₀⟩ := hall
    refine eq_zero_of_perm_invariant hW hperm hl₀ ?_
    by_contra h; exact hlin₀ (hlin _ h)

/-! ### Lemma Ψ.0: the class sums satisfy the cyclic relation -/

lemma rotate_of_append {w p q : List α} (h : w = p ++ q) (hq : q ≠ []) :
    w.rotate p.length = q ++ p ∧ p.length < w.length ∧ w.take p.length = p := by
  subst h
  refine ⟨List.rotate_append_length_eq p q, ?_, by simp⟩
  simp only [List.length_append]
  have := List.length_pos_iff.2 hq
  omega

lemma lamL_ne_zero_of_word {lam : α → ℂ} {A : Finset α} {w : List α} (hw : IsWordOn A w)
    (hlam : lamL lam w = 1) {s t : List α} (hst : IsWordOn A (s ++ t)) : lamL lam s ≠ 0 := by
  have hp : (s ++ t).Perm w :=
    List.perm_of_nodup_nodup_toFinset_eq hst.1 hw.1 (hst.2.trans hw.2.symm)
  intro h
  have := lamL_perm lam hp
  rw [lamL_append, h, zero_mul, hlam] at this
  exact zero_ne_one this

/-- The key step of Lemma Ψ.0: rotating a rotation `s t` of `w` at a union-prefix `s` gives a
rotation of `w` at a union-prefix, with the weight multiplied by `λ(s)`. -/
lemma rotate_rotate {A : Finset α} {lam : α → ℂ} {w s₁ t₁ s t : List α} (hw : w = s₁ ++ t₁)
    (hnd : w.Nodup) (hlam : lamL lam w = 1) (h₁ : UoC r A s₁.toFinset) (hs : UoC r A s.toFinset)
    (ht : t ≠ []) (h : t₁ ++ s₁ = s ++ t) :
    ∃ p q, w = p ++ q ∧ q ≠ [] ∧ t ++ s = q ++ p ∧ UoC r A p.toFinset ∧
      lamL lam p = lamL lam s₁ * lamL lam s := by
  rcases List.append_eq_append_iff.1 h with ⟨m, h1, h2⟩ | ⟨m, h1, h2⟩
  · -- `s = t₁ ++ m`, `s₁ = m ++ t`
    subst h1 h2
    refine ⟨m, t ++ t₁, by simp [hw], by simp [ht], by simp, ?_, ?_⟩
    · have : m.toFinset = (t₁ ++ m).toFinset ∩ (m ++ t).toFinset := by
        rw [hw] at hnd
        have hd := (List.nodup_append.1 hnd).2.2
        ext b
        simp only [List.mem_toFinset, Finset.mem_inter, List.mem_append]
        constructor
        · intro hb; exact ⟨Or.inr hb, Or.inl hb⟩
        · rintro ⟨hb | hb, hb'⟩
          · exact absurd rfl (hd b (List.mem_append.2 hb') b hb)
          · exact hb
      rw [this]; exact uoC_inter hs h₁
    · rw [hw] at hlam
      simp only [lamL_append] at hlam ⊢
      linear_combination (-lamL lam m) * hlam
  · -- `t₁ = s ++ m`, `t = m ++ s₁`
    subst h1 h2
    by_cases hm : m = []
    · subst hm
      simp only [List.nil_append] at ht
      refine ⟨[], w, by simp, ?_, by simp [hw], by simp [UoC], ?_⟩
      · intro hw0; rw [hw0] at hw; exact ht (List.append_eq_nil_iff.1 hw.symm).1
      · rw [hw] at hlam; simp only [lamL_append, List.append_nil] at hlam
        rw [lamL_nil, hlam]
    · refine ⟨s₁ ++ s, m, by simp [hw], hm, by simp, ?_, lamL_append _ _ _⟩
      rw [List.toFinset_append]; exact uoC_union h₁ hs

/-- **Lemma Ψ.0** (`notes/natural_isomorphism.md` §3.1): for a linear extension `w` and weights
with `λ(w) = 1`, the class sum `s_λ(w) = ∑_{k cut} λ(w_1⋯w_k)⁻¹ w γ^k` satisfies the cyclic
relation (Ψ.1). `K` is the set of cuts. -/
theorem eqL_classSum {A : Finset α} {lam : α → ℂ} {w : List α} (hw : IsWordOn A w)
    (hlam : lamL lam w = 1) (K : Finset ℕ)
    (hK : ∀ k, k ∈ K ↔ k < w.length ∧ UoC r A (w.take k).toFinset) :
    EqL r A lam (∑ k ∈ K, (lamL lam (w.take k))⁻¹ • Finsupp.single (w.rotate k) (1 : ℂ)) := by
  set Y := ∑ k ∈ K, (lamL lam (w.take k))⁻¹ • Finsupp.single (w.rotate k) (1 : ℂ) with hY
  have hval : ∀ z k₀, k₀ ∈ K → w.rotate k₀ = z → Y z = (lamL lam (w.take k₀))⁻¹ := by
    intro z k₀ hk₀ hz
    rw [hY, Finsupp.finset_sum_apply, Finset.sum_eq_single k₀]
    · simp [hz]
    · intro k hk hne
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      rw [if_neg, mul_zero]
      intro h
      have hwne : w ≠ [] := by
        rintro rfl; have := (hK k₀).1 hk₀; simp at this
      have := List.Nodup.rotate_congr hw.1 hwne k k₀ (h.trans hz.symm)
      rw [Nat.mod_eq_of_lt ((hK k).1 hk).1, Nat.mod_eq_of_lt ((hK k₀).1 hk₀).1] at this
      exact hne this
    · intro h; exact absurd hk₀ h
  have hzero : ∀ z, (¬ ∃ k ∈ K, w.rotate k = z) → Y z = 0 := by
    intro z hz
    rw [hY, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    rw [if_neg (fun h => hz ⟨k, hk, h⟩), mul_zero]
  -- one direction of the class correspondence
  have step : ∀ s t, IsWordOn A (s ++ t) → UoC r A s.toFinset → t ≠ [] → ∀ k ∈ K,
      w.rotate k = s ++ t → ∃ k' ∈ K, w.rotate k' = t ++ s ∧
        lamL lam (w.take k') = lamL lam (w.take k) * lamL lam s := by
    intro s t hst hs ht k hk hrot
    obtain ⟨hkw, hUk⟩ := (hK k).1 hk
    rw [List.rotate_eq_drop_append_take hkw.le] at hrot
    obtain ⟨p, q, hpq, hq, htq, hUp, hlp⟩ := rotate_rotate (List.take_append_drop k w).symm
      hw.1 hlam hUk hs ht hrot
    obtain ⟨h1, h2, h3⟩ := rotate_of_append hpq hq
    refine ⟨p.length, (hK _).2 ⟨h2, by rw [h3]; exact hUp⟩, by rw [h1, htq], by rw [h3, hlp]⟩
  intro s t hst hs
  by_cases ht : t = []
  · subst ht
    have : lamL lam s = 1 := by
      rw [← hlam]
      exact lamL_perm lam (List.perm_of_nodup_nodup_toFinset_eq (by simpa using hst.1) hw.1
        (by simpa using hst.2.trans hw.2.symm))
    simp [this]
  by_cases hs0 : s = []
  · subst hs0; simp
  by_cases h : ∃ k ∈ K, w.rotate k = s ++ t
  · obtain ⟨k, hk, hrot⟩ := h
    obtain ⟨k', hk', hrot', hl⟩ := step s t hst hs ht k hk hrot
    rw [hval _ k' hk' hrot', hval _ k hk hrot, hl, mul_inv, mul_assoc,
      inv_mul_cancel₀ (lamL_ne_zero_of_word hw hlam hst), mul_one]
  · rw [hzero _ h, hzero, zero_mul]
    rintro ⟨k', hk', hrot'⟩
    have hts : IsWordOn A (t ++ s) := isWordOn_perm List.perm_append_comm hst
    have hUt : UoC r A t.toFinset := by rw [toFinset_right hst]; exact uoC_sdiff hs
    obtain ⟨k, hk, hrot, -⟩ := step t s hts hUt hs0 k' hk' hrot'
    exact h ⟨k, hk, hrot⟩

/-! ### The measure `μ`, Lemma 6 and Lemma 4 on lists -/

open Classical in
/-- `μ(l)`: the length of the longest union-prefix of `l` not containing `x₀`. -/
noncomputable def muL (r : α → α → Prop) (A : Finset α) (x₀ : α) (l : List α) : ℕ :=
  Nat.findGreatest (fun k => UoC r A (l.take k).toFinset ∧ x₀ ∉ l.take k) l.length

lemma muL_spec {A : Finset α} {x₀ : α} {l : List α} :
    muL r A x₀ l ≤ l.length ∧ UoC r A (l.take (muL r A x₀ l)).toFinset ∧
      x₀ ∉ l.take (muL r A x₀ l) ∧
      ∀ k, muL r A x₀ l < k → k ≤ l.length → UoC r A (l.take k).toFinset → x₀ ∈ l.take k := by
  classical
  have hdef : Nat.findGreatest (fun k => UoC r A (l.take k).toFinset ∧ x₀ ∉ l.take k)
      l.length = muL r A x₀ l := rfl
  obtain ⟨h1, h2, h3⟩ := Nat.findGreatest_eq_iff.1 hdef
  by_cases h0 : muL r A x₀ l = 0
  · refine ⟨h1, by rw [h0]; simp [UoC], by rw [h0]; simp, fun k hk hkl hU => ?_⟩
    by_contra hx; exact h3 hk hkl ⟨hU, hx⟩
  · exact ⟨h1, (h2 h0).1, (h2 h0).2, fun k hk hkl hU => by_contra fun hx => h3 hk hkl ⟨hU, hx⟩⟩

lemma inBL_iff_muL {A : Finset α} {x₀ : α} {l : List α} :
    InBL r A x₀ l ↔ LinL r A l ∧ muL r A x₀ l = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := muL_spec (r := r) (A := A) (x₀ := x₀) (l := l)
  constructor
  · rintro ⟨hl, hB⟩
    refine ⟨hl, by_contra fun h0 => h3 (hB _ _ (List.take_append_drop _ l).symm ?_ h2)⟩
    intro h
    rcases List.take_eq_nil_iff.1 h with h | h
    · exact h0 h
    · have := List.length_eq_zero_iff.2 h; omega
  · rintro ⟨hl, h0⟩
    refine ⟨hl, fun s t hst hs hU => ?_⟩
    have hk : l.take s.length = s := by rw [hst]; simp
    have := h4 s.length (by rw [h0]; exact List.length_pos_iff.2 hs)
      (by rw [hst]; simp) (by rw [hk]; exact hU)
    rwa [hk] at this

/-- The step of **Lemma 6** (`notes/conjecture_s_splitting_cycles_span.md` §5): if `w ∉ B_P`
splits as `s t` at its longest union-prefix `s` avoiding `x₀`, every other word `z` of `s ⧢ t`
is a linear extension with `μ(z) < μ(w)`. -/
lemma muL_lt_of_shuffle {A : Finset α} {x₀ : α} (hx₀ : x₀ ∈ A) {l z : List α}
    (hl : LinL r A l)
    (hz1 : z.filter (fun b => decide (b ∈ (l.take (muL r A x₀ l)).toFinset)) =
      l.take (muL r A x₀ l))
    (hz2 : z.filter (fun b => !decide (b ∈ (l.take (muL r A x₀ l)).toFinset)) =
      l.drop (muL r A x₀ l))
    (hzl : z ≠ l) : LinL r A z ∧ muL r A x₀ z < muL r A x₀ l := by
  obtain ⟨hk1, hkU, hkx, hkmax⟩ := muL_spec (r := r) (A := A) (x₀ := x₀) (l := l)
  set k := muL r A x₀ l
  set s := l.take k
  set t := l.drop k
  set S := s.toFinset
  have hl' : l = s ++ t := (List.take_append_drop k l).symm
  have hzperm : z.Perm (s ++ t) := by
    rw [← hz1, ← hz2]; exact (List.filter_append_perm _ z).symm
  have hzw : IsWordOn A z := isWordOn_perm hzperm.symm (hl' ▸ hl.1)
  have hpwl := hl'.symm ▸ hl.2
  -- `z` is a linear extension
  have hzlin : LinL r A z := by
    refine ⟨hzw, List.pairwise_iff_forall_sublist.2 fun {p q} hpq => ?_⟩
    have hp : p ∈ A := (mem_of_isWordOn hzw).1 (hpq.subset (by simp))
    have hq : q ∈ A := (mem_of_isWordOn hzw).1 (hpq.subset (by simp))
    by_cases hpS : p ∈ S <;> by_cases hqS : q ∈ S
    · have := hpq.filter (fun b => decide (b ∈ S))
      rw [hz1] at this
      simp only [List.filter_cons, hpS, hqS, decide_true, if_true, List.filter_nil] at this
      exact List.pairwise_iff_forall_sublist.1 (List.pairwise_append.1 hpwl).1 this
    · intro hqp; exact hqS ((hkU q hq p hp hqp).2 hpS)
    · intro hqp; exact hpS ((hkU q hq p hp hqp).1 hqS)
    · have := hpq.filter (fun b => !decide (b ∈ S))
      rw [hz2] at this
      simp only [List.filter_cons, hpS, hqS, decide_false, Bool.not_false, if_true,
        List.filter_nil] at this
      exact List.pairwise_iff_forall_sublist.1 (List.pairwise_append.1 hpwl).2.1 this
  refine ⟨hzlin, ?_⟩
  obtain ⟨hm1, hmU, hmx, -⟩ := muL_spec (r := r) (A := A) (x₀ := x₀) (l := z)
  by_contra hge
  push Not at hge
  have hm0 : 0 < muL r A x₀ z := by
    have : 0 < k := by
      by_contra h0
      push Not at h0
      have hk0 : k = 0 := by omega
      apply hzl
      rw [hl']
      have hs : s = [] := by simp [s, hk0]
      have hS : S = ∅ := by simp [S, hs]
      rw [hs, List.nil_append, ← hz2]
      simp [hS]
    omega
  set j := muL r A x₀ z
  set π := z.take j
  set ρ := z.drop j
  have hz' : z = π ++ ρ := (List.take_append_drop j z).symm
  have hπt : π.filter (fun b => !decide (b ∈ S)) = [] := by
    by_contra hne
    set πt := π.filter (fun b => !decide (b ∈ S))
    have ht' : t = πt ++ ρ.filter (fun b => !decide (b ∈ S)) := by
      rw [← hz2, hz', List.filter_append]
    have htake : l.take (k + πt.length) = s ++ πt := by
      rw [hl', ht', ← List.append_assoc, List.take_left' (by simp [s, List.length_take,
        min_eq_left hk1])]
    have hset : (s ++ πt).toFinset = S ∪ π.toFinset := by
      ext b
      simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, πt,
        List.mem_filter, S]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · by_cases hb : b ∈ s
          · exact Or.inl hb
          · exact Or.inr ⟨h, by simp [hb]⟩
    have hlen : k + πt.length ≤ l.length := by
      have : t.length = l.length - k := by simp [t]
      have h2 : πt.length ≤ t.length := by rw [ht']; simp
      omega
    have := hkmax (k + πt.length) (by have := List.length_pos_iff.2 hne; omega) hlen
      (by rw [htake, hset]; exact uoC_union hkU hmU)
    rw [htake] at this
    rcases List.mem_append.1 this with h | h
    · exact hkx h
    · exact hmx (List.mem_of_mem_filter h)
  -- so `π` lies in `S`, hence is a prefix of `s`
  have hπS : π.filter (fun b => decide (b ∈ S)) = π := by
    rw [List.filter_eq_self]
    intro b hb
    by_contra h
    have : b ∈ π.filter (fun b => !decide (b ∈ S)) := List.mem_filter.2 ⟨hb, by simpa using h⟩
    rw [hπt] at this; simp at this
  have hs' : s = π ++ ρ.filter (fun b => decide (b ∈ S)) := by
    rw [← hz1, hz', List.filter_append, hπS]
  have hπlen : π.length = j := by simp [π, List.length_take, min_eq_left hm1]
  have hslen : s.length = k := by simp [s, List.length_take, min_eq_left hk1]
  have hρ : ρ.filter (fun b => decide (b ∈ S)) = [] := by
    have := congrArg List.length hs'
    rw [List.length_append, hπlen, hslen] at this
    exact List.length_eq_zero_iff.1 (by omega)
  apply hzl
  have hρt : ρ.filter (fun b => !decide (b ∈ S)) = ρ := by
    rw [List.filter_eq_self]
    intro b hb
    by_contra h
    have : b ∈ ρ.filter (fun b => decide (b ∈ S)) := List.mem_filter.2 ⟨hb, by simpa using h⟩
    rw [hρ] at this; simp at this
  rw [hl', hz', hs', hρ, List.append_nil, ← hρt, ← hz2, hz', List.filter_append, hπt,
    List.nil_append]

/-- **Lemma 4**, existence: rotating a linear extension at `μ` gives a word of `B_P`. -/
lemma inBL_rotate_muL {A : Finset α} {x₀ : α} (hx₀ : x₀ ∈ A) {l : List α} (hl : LinL r A l) :
    InBL r A x₀ (l.drop (muL r A x₀ l) ++ l.take (muL r A x₀ l)) := by
  obtain ⟨hk1, hkU, hkx, hkmax⟩ := muL_spec (r := r) (A := A) (x₀ := x₀) (l := l)
  set k := muL r A x₀ l
  have hl' : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  refine ⟨linL_rotate (hl' ▸ hl) hkU, fun π ρ h hπ hU => ?_⟩
  by_contra hx
  have hxd : x₀ ∈ l.drop k := by
    have : x₀ ∈ l := (mem_of_isWordOn hl.1).2 hx₀
    rw [hl'] at this
    rcases List.mem_append.1 this with h | h
    · exact absurd h hkx
    · exact h
  rcases List.append_eq_append_iff.1 h with ⟨m, h1, h2⟩ | ⟨m, h1, h2⟩
  · exact hx (h1 ▸ List.mem_append_left _ hxd)
  · have htake : l.take (k + π.length) = l.take k ++ π := by
      conv_lhs => rw [hl', h1, ← List.append_assoc]
      rw [List.take_left' (by simp [List.length_take, min_eq_left hk1])]
    have hlen : k + π.length ≤ l.length := by
      have := congrArg List.length h1
      simp only [List.length_append, List.length_drop] at this
      omega
    have := hkmax (k + π.length) (by have := List.length_pos_iff.2 hπ; omega) hlen
      (by rw [htake, List.toFinset_append]; exact uoC_union hkU hU)
    rw [htake] at this
    rcases List.mem_append.1 this with h | h
    · exact hkx h
    · exact hx h

/-- **Lemma 4**, uniqueness: a nontrivial rotation of a word of `B_P` is not in `B_P`. -/
lemma rotate_eq_zero_of_inBL {A : Finset α} {x₀ : α} {l : List α} {j : ℕ}
    (hl : InBL r A x₀ l) (hj : j < l.length) (hl' : InBL r A x₀ (l.drop j ++ l.take j)) :
    j = 0 := by
  by_contra h0
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  have hU : UoC r A (l.take j).toFinset := uoC_of_linL_rotate (hsplit ▸ hl.1) hl'.1
  have h1 := hl.2 _ _ hsplit (by
    intro h; rcases List.take_eq_nil_iff.1 h with h | h
    · exact h0 h
    · simp [h] at hj) hU
  have hw : IsWordOn A (l.take j ++ l.drop j) := hsplit ▸ hl.1.1
  have h2 := hl'.2 _ _ rfl (by intro h; rw [List.drop_eq_nil_iff] at h; omega)
    (by rw [toFinset_right hw]; exact uoC_sdiff hU)
  exact (List.nodup_append.1 hw.1).2.2 x₀ h1 x₀ h2 rfl

/-! ### Closure properties used by the transfer to words `Fin n ≃ α` -/

/-- A word whose subwords on `S` and off `S` are linear extensions, for a union of components
`S`, is a linear extension. -/
lemma linL_of_filter {A S : Finset α} {z : List α} (hz : IsWordOn A z) (hS : UoC r A S)
    (h1 : (z.filter (fun b => decide (b ∈ S))).Pairwise (fun p q => ¬ r q p))
    (h2 : (z.filter (fun b => !decide (b ∈ S))).Pairwise (fun p q => ¬ r q p)) :
    LinL r A z := by
  refine ⟨hz, List.pairwise_iff_forall_sublist.2 fun {p q} hpq => ?_⟩
  have hp : p ∈ A := (mem_of_isWordOn hz).1 (hpq.subset (by simp))
  have hq : q ∈ A := (mem_of_isWordOn hz).1 (hpq.subset (by simp))
  by_cases hpS : p ∈ S <;> by_cases hqS : q ∈ S
  · have := hpq.filter (fun b => decide (b ∈ S))
    simp only [List.filter_cons, hpS, hqS, decide_true, if_true, List.filter_nil] at this
    exact List.pairwise_iff_forall_sublist.1 h1 this
  · intro hqp; exact hqS ((hS q hq p hp hqp).2 hpS)
  · intro hqp; exact hpS ((hS q hq p hp hqp).1 hqS)
  · have := hpq.filter (fun b => !decide (b ∈ S))
    simp only [List.filter_cons, hpS, hqS, decide_false, Bool.not_false, if_true,
      List.filter_nil] at this
    exact List.pairwise_iff_forall_sublist.1 h2 this

lemma eqL_zero {A : Finset α} {lam : α → ℂ} : EqL r A lam 0 := fun _ _ _ _ => by simp

lemma eqL_add {A : Finset α} {lam : α → ℂ} {X Y : List α →₀ ℂ} (hX : EqL r A lam X)
    (hY : EqL r A lam Y) : EqL r A lam (X + Y) := fun s t h hs => by
  simp only [Finsupp.add_apply, add_mul, hX s t h hs, hY s t h hs]

lemma eqL_smul {A : Finset α} {lam : α → ℂ} {X : List α →₀ ℂ} (c : ℂ) (hX : EqL r A lam X) :
    EqL r A lam (c • X) := fun s t h hs => by
  simp only [Finsupp.smul_apply, smul_eq_mul, mul_assoc, hX s t h hs]

lemma eqL_sum {ι : Type*} {A : Finset α} {lam : α → ℂ} (I : Finset ι) (X : ι → List α →₀ ℂ)
    (h : ∀ i ∈ I, EqL r A lam (X i)) : EqL r A lam (∑ i ∈ I, X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using eqL_zero
  | insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact eqL_add (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The class sum of a linear extension is supported on linear extensions. -/
lemma linL_of_classSum {A : Finset α} {lam : α → ℂ} {w : List α} (hw : LinL r A w)
    (K : Finset ℕ) (hK : ∀ k, k ∈ K ↔ k < w.length ∧ UoC r A (w.take k).toFinset) {z : List α}
    (hz : (∑ k ∈ K, (lamL lam (w.take k))⁻¹ • Finsupp.single (w.rotate k) (1 : ℂ)) z ≠ 0) :
    LinL r A z := by
  rw [Finsupp.finset_sum_apply] at hz
  obtain ⟨k, hk, hkz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hkz
  split_ifs at hkz with h
  · obtain ⟨hkl, hU⟩ := (hK k).1 hk
    rw [← h, List.rotate_eq_drop_append_take hkl.le]
    exact linL_rotate ((List.take_append_drop k w).symm ▸ hw) hU
  · simp at hkz

end L

end PosetJKS
