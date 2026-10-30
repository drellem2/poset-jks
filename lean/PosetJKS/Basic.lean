import Mathlib

/-!
# Words, linear extensions, cyclic classes, shuffles, `PLie(P)`

Conventions follow `notes/poset_jks_theorem.tex`, Section "Objects and conventions".

* The poset `P` is a finite type `α` with a `PartialOrder`; `n = Fintype.card α`.
  The note labels the ground set `[n]`; here the ground set is an arbitrary finite type, and a
  *word* is a bijection `Fin n ≃ α` (`w i` is the letter in position `i`). The group algebra
  `ℂ[S_n]` of the note is the free vector space `Word α →₀ ℂ` on words: `S_α` acts on the left by
  relabelling letters and `S_n = Perm (Fin n)` on the right by permuting positions.
* `γ = (1 2 ⋯ n)` acts on the right by rotation of positions: `(w γ^j)_i = w_{i+j}`; this is
  `rot w j`.
* `e_ζ = (1/n) ∑_j ζ^{-j} γ^j`, so `w e_ζ = (1/n) ∑_j ζ^{-j} (w γ^j)`; this is `wEζ ζ w`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

section Words

variable (α : Type*) [Fintype α]

/-- A word: a bijection from positions `Fin n` to letters `α`, `n = |α|`. -/
abbrev Word := Fin (Fintype.card α) ≃ α

/-- The ambient space `ℂ[S_n]`, realised as the free `ℂ`-vector space on words. -/
def Alg := Word α →₀ ℂ

-- `Alg` is a `def` (not an `abbrev`) carrying the `Finsupp` group and module structures
-- directly; with an `abbrev`, instance synthesis for quotients of submodules of `Finsupp` fails
-- (the two `AddCommMonoid` paths are not unified at instance transparency).
noncomputable instance : AddCommGroup (Alg α) := Finsupp.instAddCommGroup
noncomputable instance : Module ℂ (Alg α) := Finsupp.module _ _
/-- Coefficient of a word. -/
noncomputable instance : FunLike (Alg α) (Word α) ℂ := Finsupp.instFunLike

end Words

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Right multiplication by `γ^j`: `(rot w j)_i = w_{i+j}` (indices mod `n`). -/
def rot (w : Word α) (j : ℕ) : Word α := (finRotate _ ^ j).trans w

/-- The positions `0, …, k-1` of `w`, as a set of letters: the letter set of the length-`k`
prefix `w_1 ⋯ w_k`. -/
def prefixSet (w : Word α) (k : ℕ) : Finset α :=
  (univ.filter fun i : Fin (Fintype.card α) => (i : ℕ) < k).image w

/-- The subword of `w` on the letters of `S` (letters of `S` in the order they occur in `w`). -/
def restrict (w : Word α) (S : Finset α) : List α :=
  (List.ofFn w).filter (· ∈ S)

/-- Left multiplication by a permutation `g` of the letters: `(g w)_i = g (w_i)`, extended
linearly to `ℂ[S_n]`. -/
noncomputable def relabel (g : Equiv.Perm α) : Alg α →ₗ[ℂ] Alg α :=
  Finsupp.lmapDomain ℂ ℂ fun w : Word α => w.trans g

/-- The basis vector of `ℂ[S_n]` attached to a word. -/
noncomputable def wd (w : Word α) : Alg α := Finsupp.single w 1

/-- `w e_ζ = (1/n) ∑_{j<n} ζ^{-j} w γ^j`. -/
noncomputable def wEζ (ζ : ℂ) (w : Word α) : Alg α :=
  ∑ j ∈ range (Fintype.card α), (((Fintype.card α : ℂ))⁻¹ * (ζ ^ j)⁻¹) • wd (rot w j)

/-- The cyclic class (right `C_n`-coset) `w C_n` of a word, as a finite set of words. -/
def coset (w : Word α) : Finset (Word α) :=
  (range (Fintype.card α)).image (rot w)

/-- A shuffle generator `u ⧢ v` attached to a letter set `S` and words `u` on `S`, `v` on `Sᶜ`:
the sum of all words whose subword on `S` is `u` and whose subword on `Sᶜ` is `v`.
(When `u` and `v` enumerate `S` and `Sᶜ` these words are exactly the interleavings of `u`
and `v`.) -/
noncomputable def shuffle (S : Finset α) (u v : List α) : Alg α :=
  ∑ w ∈ univ.filter (fun w : Word α => restrict w S = u ∧ restrict w Sᶜ = v), wd w

/-- `u` is a word on the letter set `S`: each letter of `S` exactly once. -/
def IsWordOn (S : Finset α) (u : List α) : Prop :=
  u.Nodup ∧ u.toFinset = S

/-- `Sh_n`: the span of the proper shuffles `u ⧢ v` (`u`, `v` nonempty, complementary letter
sets). -/
noncomputable def Sh (α : Type*) [Fintype α] [DecidableEq α] : Submodule ℂ (Alg α) :=
  Submodule.span ℂ
    {x | ∃ (S : Finset α) (u v : List α), S.Nonempty ∧ S ≠ univ ∧
      IsWordOn S u ∧ IsWordOn Sᶜ v ∧ x = shuffle S u v}

section Poset

variable [PartialOrder α]

variable (α) in
/-- `Lin(P)`: `w` is a linear extension iff `w_i <_P w_j` implies `i < j`. -/
def IsLinExt (w : Word α) : Prop := ∀ i j, w i < w j → i < j

/-- `S` is a union of connected components of the comparability graph of `P`. -/
def IsUnionOfComponents (S : Finset α) : Prop := ∀ x y : α, x ≤ y → (x ∈ S ↔ y ∈ S)

variable (α) in
/-- `P` is connected: nonempty, and its only unions of components are `∅` and the whole set. -/
def IsConnectedPoset : Prop :=
  Nonempty α ∧ ∀ S : Finset α, IsUnionOfComponents S → S = ∅ ∨ S = univ

/-- `u` is a linear extension of the induced subposet `P|_S`, written as a list. -/
def IsLinExtOn (S : Finset α) (u : List α) : Prop :=
  IsWordOn S u ∧ u.Pairwise fun a b => ¬ b < a

/-- `k ∈ {0, …, n-1}` is a cut of `w`: the prefix `w_1 ⋯ w_k` is a union of components. -/
def IsCut (w : Word α) (k : ℕ) : Prop :=
  k < Fintype.card α ∧ IsUnionOfComponents (prefixSet w k)

variable (α) in
/-- `W_P = ℂ{Lin(P)}`. -/
noncomputable def W : Submodule ℂ (Alg α) :=
  Submodule.span ℂ {x | ∃ w, IsLinExt α w ∧ x = wd w}

variable (α) in
/-- `R_P`: the span of `s ⧢ t` with `s ∈ Lin(P|_S)`, `t ∈ Lin(P|_{Sᶜ})`, `S` a nonempty proper
union of components. -/
noncomputable def R : Submodule ℂ (Alg α) :=
  Submodule.span ℂ
    {x | ∃ (S : Finset α) (u v : List α), S.Nonempty ∧ S ≠ univ ∧ IsUnionOfComponents S ∧
      IsLinExtOn S u ∧ IsLinExtOn Sᶜ v ∧ x = shuffle S u v}

variable (α) in
/-- `PLie(P) = span{w e_ζ : w ∈ Lin(P)}`. -/
noncomputable def PLie (ζ : ℂ) : Submodule ℂ (Alg α) :=
  Submodule.span ℂ {x | ∃ w, IsLinExt α w ∧ x = wEζ ζ w}

variable (α) in
open Classical in
/-- `Cyc(P)`: the cyclic classes, i.e. the cosets `w C_n` that meet `Lin(P)`. -/
noncomputable def cyc : Finset (Finset (Word α)) :=
  (univ.filter (IsLinExt α)).image coset

variable (α) in
/-- `e_C(P) = |Cyc(P)|`. -/
noncomputable def eC : ℕ := (cyc α).card

open Classical in
/-- For `g ∈ Aut(P)` and a class `C` with `gC = C`, the rotation `r_g(C) ∈ {0, …, n-1}`:
the `r` with `g w = w γ^r` for `w ∈ C` (it does not depend on `w`). Junk value `0` if `C` is
not `g`-stable. -/
noncomputable def classRot (g : α ≃o α) (C : Finset (Word α)) : ℕ :=
  if h : ∃ r, r < Fintype.card α ∧ ∃ w ∈ C, w.trans g.toEquiv = rot w r then Nat.find h else 0

open Classical in
/-- `∑_{C ∈ Cyc(P), gC = C} ζ^{r_g(C)}`, the character of `PLie(P)` at `g`. -/
noncomputable def fixedClassSum (ζ : ℂ) (g : α ≃o α) : ℂ :=
  ∑ C ∈ (cyc α).filter (fun C => C.image (fun w => w.trans g.toEquiv) = C), ζ ^ classRot g C

/-! ### Aut(P) acts on Lin(P), `W_P`, `R_P`, `PLie(P)` -/

theorem isLinExt_trans (g : α ≃o α) {w : Word α} (hw : IsLinExt α w) :
    IsLinExt α (w.trans g.toEquiv) := fun i j h => hw i j (by simpa using h)

theorem relabel_wd (g : Equiv.Perm α) (w : Word α) : relabel g (wd w) = wd (w.trans g) :=
  Finsupp.mapDomain_single

theorem rot_trans (g : Equiv.Perm α) (w : Word α) (j : ℕ) :
    rot (w.trans g) j = (rot w j).trans g := rfl

theorem relabel_wEζ (g : Equiv.Perm α) (ζ : ℂ) (w : Word α) :
    relabel g (wEζ ζ w) = wEζ ζ (w.trans g) := by
  simp only [wEζ, map_sum, map_smul, relabel_wd, rot_trans]

theorem relabel_mem_PLie (g : α ≃o α) (ζ : ℂ) {y : Alg α} (hy : y ∈ PLie α ζ) :
    relabel g.toEquiv y ∈ PLie α ζ := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [relabel_wEζ]
    exact Submodule.subset_span ⟨_, isLinExt_trans g hw, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem relabel_mem_W (g : α ≃o α) {y : Alg α} (hy : y ∈ W α) : relabel g.toEquiv y ∈ W α := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [relabel_wd]
    exact Submodule.subset_span ⟨_, isLinExt_trans g hw, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem mem_image_perm_iff (g : Equiv.Perm α) (S : Finset α) (x : α) :
    g x ∈ S.image g ↔ x ∈ S :=
  g.injective.mem_finset_image

theorem compl_image_perm (g : Equiv.Perm α) (S : Finset α) :
    (S.image g)ᶜ = Sᶜ.image g := by
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  simp only [mem_compl, mem_image_perm_iff]

theorem restrict_trans (g : Equiv.Perm α) (w : Word α) (S : Finset α) :
    restrict (w.trans g) (S.image g) = (restrict w S).map g := by
  unfold restrict
  have : List.ofFn (w.trans g) = (List.ofFn w).map g := by
    rw [List.map_ofFn]; rfl
  rw [this, List.filter_map]
  congr 2
  funext x
  simp only [Function.comp_apply, mem_image_perm_iff]

theorem relabel_shuffle (g : Equiv.Perm α) (S : Finset α) (u v : List α) :
    relabel g (shuffle S u v) = shuffle (S.image g) (u.map g) (v.map g) := by
  unfold shuffle
  rw [map_sum]
  simp only [relabel_wd]
  refine Finset.sum_bij' (fun w _ => w.trans g) (fun w _ => w.trans g.symm) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨h1, h2⟩ := (mem_filter.1 hw).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [compl_image_perm, restrict_trans, restrict_trans, h1, h2]
    exact ⟨rfl, rfl⟩
  · intro w hw
    obtain ⟨h1, h2⟩ := (mem_filter.1 hw).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have hw' : w = (w.trans g.symm).trans g := by ext; simp
    rw [hw'] at h1 h2
    rw [compl_image_perm] at h2
    rw [restrict_trans] at h1 h2
    exact ⟨List.map_injective_iff.2 g.injective h1, List.map_injective_iff.2 g.injective h2⟩
  · intro w _; ext; simp
  · intro w _; ext; simp
  · intro w _; rfl

/-- `Aut(P)` preserves `R_P`. (Needed to define the action on `ℂ[Lin P]/R_P`.) -/
theorem relabel_mem_R (g : α ≃o α) {y : Alg α} (hy : y ∈ R α) : relabel g.toEquiv y ∈ R α := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, u, v, hne, huniv, hS, hu, hv, rfl⟩ := hx
    rw [relabel_shuffle]
    have hlin : ∀ (T : Finset α) (t : List α), IsLinExtOn T t →
        IsLinExtOn (T.image g.toEquiv) (t.map g.toEquiv) := by
      rintro T t ⟨⟨hnd, hset⟩, hpw⟩
      refine ⟨⟨hnd.map g.injective, ?_⟩, ?_⟩
      · rw [← hset]; ext; simp
      · rw [List.pairwise_map]
        refine hpw.imp fun {a b} h hlt => h ?_
        simpa using hlt
    refine Submodule.subset_span ⟨S.image g.toEquiv, u.map g.toEquiv, v.map g.toEquiv,
      hne.image _, ?_, ?_, hlin S u hu, ?_, rfl⟩
    · intro h
      apply huniv
      have := congrArg Finset.card h
      rw [Finset.card_image_of_injective _ g.toEquiv.injective, Finset.card_univ] at this
      exact Finset.eq_univ_of_card _ this
    · intro x y hxy
      obtain ⟨a, rfl⟩ := g.toEquiv.surjective x
      obtain ⟨b, rfl⟩ := g.toEquiv.surjective y
      rw [mem_image_perm_iff, mem_image_perm_iff]
      exact hS a b (by simpa using hxy)
    · rw [compl_image_perm]; exact hlin _ _ hv
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end Poset

end PosetJKS
