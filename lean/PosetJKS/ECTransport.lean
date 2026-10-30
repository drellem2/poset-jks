import PosetJKS.Milestone

/-!
# `e_C` is invariant under order isomorphisms; `e_C` of an induced subposet

* `L.inBL_map`: the list form `B_P` of Lemma 4 is transported along an injective map that
  preserves and reflects the relation.
* `BL A x₀`: the words of `B_{P|_A}(x₀)`, as a finite set of lists on the letter set `A`;
  `card_BL`: `|B_{P|_A}(x₀)| = e_C(P|_A)` for `x₀ ∈ A` (Lemma 4 for the induced subposet).
* `eC_congr`: `e_C(P) = e_C(Q)` for an order isomorphism `P ≃o Q`;
  `eC_image`: `e_C(P|_B) = e_C(P|_{φ B})` for an automorphism `φ` of `P`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

namespace L

variable {β α : Type*} [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]

lemma toFinset_map (f : β → α) (l : List β) : (l.map f).toFinset = l.toFinset.image f := by
  ext; simp

lemma exists_map_eq {f : β → α} {l : List α} (h : ∀ a ∈ l, ∃ b, f b = a) :
    ∃ l' : List β, l'.map f = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨b, rfl⟩ := h a (List.mem_cons_self ..)
    obtain ⟨l', rfl⟩ := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    exact ⟨b :: l', rfl⟩

lemma isWordOn_map {f : β → α} (hf : Function.Injective f) {A : Finset β} {l : List β} :
    IsWordOn (A.image f) (l.map f) ↔ IsWordOn A l := by
  unfold IsWordOn
  rw [List.nodup_map_iff hf, toFinset_map, (Finset.image_injective hf).eq_iff]

lemma uoC_map {r : β → β → Prop} {r' : α → α → Prop} {f : β → α} (hf : Function.Injective f)
    (hr : ∀ a b, r' (f a) (f b) ↔ r a b) {A : Finset β} {U : Finset β} :
    UoC r' (A.image f) (U.image f) ↔ UoC r A U := by
  constructor
  · intro h p hp q hq hpq
    have := h (f p) (mem_image_of_mem f hp) (f q) (mem_image_of_mem f hq) ((hr p q).2 hpq)
    rwa [hf.mem_finset_image, hf.mem_finset_image] at this
  · intro h p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hq
    rw [hf.mem_finset_image, hf.mem_finset_image]
    exact h a ha b hb ((hr a b).1 hpq)

/-- `B_P` on lists is transported along an injective map `f` with `r' (f a) (f b) ↔ r a b`. -/
theorem inBL_map {r : β → β → Prop} {r' : α → α → Prop} {f : β → α} (hf : Function.Injective f)
    (hr : ∀ a b, r' (f a) (f b) ↔ r a b) {A : Finset β} {x₀ : β} {l : List β} :
    InBL r' (A.image f) (f x₀) (l.map f) ↔ InBL r A x₀ l := by
  have hlin : LinL r' (A.image f) (l.map f) ↔ LinL r A l := by
    unfold LinL
    rw [isWordOn_map hf, List.pairwise_map]
    simp only [hr]
  have huoc : ∀ s : List β, UoC r' (A.image f) (s.map f).toFinset ↔ UoC r A s.toFinset := by
    intro s; rw [toFinset_map]; exact uoC_map hf hr
  unfold InBL
  rw [hlin]
  refine and_congr_right fun _ => ⟨fun h s t hst hs hU => ?_, fun h s' t' hst hs hU => ?_⟩
  · have := h (s.map f) (t.map f) (by rw [hst, List.map_append]) (by simpa using hs)
      ((huoc s).2 hU)
    rwa [List.mem_map_of_injective hf] at this
  · obtain ⟨s, t, rfl, rfl, rfl⟩ := List.map_eq_append_iff.1 hst
    rw [List.mem_map_of_injective hf]
    exact h s t rfl (by simpa using hs) ((huoc s).1 hU)

end L

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

open Classical in
/-- `B_{P|_A}(x₀)` as a finite set of lists: the linear extensions of `P|_A`, written as lists on
`A`, whose nonempty union-prefixes all contain `x₀`. -/
noncomputable def BL (A : Finset α) (x₀ : α) : Finset (List α) :=
  (A.toList.permutations.toFinset).filter (L.InBL (· < ·) A x₀)

lemma mem_BL {A : Finset α} {x₀ : α} {l : List α} : l ∈ BL A x₀ ↔ L.InBL (· < ·) A x₀ l := by
  classical
  unfold BL
  rw [mem_filter, List.mem_toFinset, List.mem_permutations]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨hnd, hset⟩ := h.1.1
  exact List.perm_of_nodup_nodup_toFinset_eq hnd (Finset.nodup_toList A)
    (by rw [hset, Finset.toList_toFinset])

/-- Lemma 4 in list form: `|B_P(x₀)| = e_C(P)`. -/
lemma card_BL_univ (x₀ : α) : (BL (univ : Finset α) x₀).card = eC α := by
  classical
  rw [← card_inB x₀, Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun w _ => toL w) ?_ ?_ ?_
  · intro w hw
    exact mem_BL.2 ((inB_iff x₀ w).1 (mem_filter.1 hw).2)
  · intro w _ w' _ h
    exact toL_injective h
  · intro l hl
    have hl := mem_BL.1 hl
    obtain ⟨w, rfl⟩ := exists_toL hl.1.1
    exact ⟨w, mem_filter.2 ⟨mem_univ _, (inB_iff x₀ w).2 hl⟩, rfl⟩

/-- Transport of `B_{P|_A}` along an injective map that preserves and reflects `<`. -/
lemma card_BL_map {β : Type*} [Fintype β] [DecidableEq β] [PartialOrder β] {f : β → α}
    (hf : Function.Injective f) (hlt : ∀ a b, f a < f b ↔ a < b) (A : Finset β) (x₀ : β) :
    (BL (A.image f) (f x₀)).card = (BL A x₀).card := by
  symm
  refine Finset.card_bij (fun l _ => l.map f) ?_ ?_ ?_
  · intro l hl
    exact mem_BL.2 ((L.inBL_map hf hlt).2 (mem_BL.1 hl))
  · intro l _ l' _ h
    exact List.map_injective_iff.2 hf h
  · intro l hl
    have hl' := mem_BL.1 hl
    have hall : ∀ a ∈ l, ∃ b, f b = a := by
      intro a ha
      have := (L.mem_of_isWordOn hl'.1.1).1 ha
      obtain ⟨b, -, rfl⟩ := mem_image.1 this
      exact ⟨b, rfl⟩
    obtain ⟨l, rfl⟩ := L.exists_map_eq hall
    exact ⟨l, mem_BL.2 ((L.inBL_map hf hlt).1 hl'), rfl⟩

/-- Lemma 4 for an induced subposet: `|B_{P|_A}(x₀)| = e_C(P|_A)` for `x₀ ∈ A`. -/
theorem card_BL {A : Finset α} {x₀ : α} (hx₀ : x₀ ∈ A) : (BL A x₀).card = eC A := by
  rw [← card_BL_univ (⟨x₀, hx₀⟩ : A), ← card_BL_map Subtype.val_injective (fun _ _ => Iff.rfl)]
  congr 1
  ext a
  simp

lemma eC_of_isEmpty (β : Type*) [Fintype β] [DecidableEq β] [PartialOrder β] [IsEmpty β] :
    eC β = 1 := by
  classical
  let u : Unique (Word β) :=
    { default := (Fintype.equivFin β).symm
      uniq := fun w => Equiv.ext fun i => (IsEmpty.false (w i)).elim }
  have hlin : ∀ w : Word β, IsLinExt β w := fun w i => (IsEmpty.false (w i)).elim
  rw [eC, cyc, Finset.filter_true_of_mem fun w _ => hlin w, Finset.univ_unique,
    Finset.image_singleton, Finset.card_singleton]

/-- **`e_C` is invariant under order isomorphisms.** -/
theorem eC_congr {β γ : Type*} [Fintype β] [DecidableEq β] [PartialOrder β]
    [Fintype γ] [DecidableEq γ] [PartialOrder γ] (e : β ≃o γ) : eC β = eC γ := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · have : IsEmpty γ := e.symm.toEquiv.isEmpty
    rw [eC_of_isEmpty, eC_of_isEmpty]
  · rw [← card_BL_univ b, ← card_BL_univ (e b), ← card_BL_map e.injective (fun _ _ => e.lt_iff_lt)]
    congr 2
    ext c
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨e.symm c, e.apply_symm_apply c⟩

/-- An automorphism `φ` of `P` restricts to an order isomorphism `P|_B ≃o P|_{φ B}`. -/
def imageOrderIso (φ : α ≃o α) (B : Finset α) : B ≃o (B.image φ) where
  toFun a := ⟨φ a, mem_image_of_mem _ a.2⟩
  invFun b := ⟨φ.symm b, by
    obtain ⟨a, ha, h⟩ := mem_image.1 b.2
    rw [← h, φ.symm_apply_apply]; exact ha⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp
  map_rel_iff' := by intro a b; simp

/-- `e_C(P|_B) = e_C(P|_{φ B})` for `φ ∈ Aut(P)`. -/
theorem eC_image (φ : α ≃o α) (B : Finset α) : eC (B.image φ) = eC B :=
  (eC_congr (imageOrderIso φ B)).symm

end PosetJKS
