import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining

/-!
# Representations with equal characters are isomorphic

Let `G` be a finite group and `k` a field of characteristic zero. Two finite-dimensional
representations of `G` over `k` with the same character are isomorphic
(`Representation.nonempty_equiv_of_character_eq`). Mathlib has the converse,
`Representation.char_iso`. Together: `Representation.nonempty_equiv_iff_character_eq`.

No algebraic closedness is needed. The proof is by induction on `dim V`. Pick a nonzero
subrepresentation `S ⊆ V` of least dimension. The character inner product computes
`dim Hom_G(S, -)` (`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`), so
`dim Hom_G(S, W) = dim Hom_G(S, V) ≥ 1`. A nonzero `G`-map `f : S → W` is injective by the
minimality of `S`, so `S ≅ f(S)`. By Maschke, `V = S ⊕ S'` and `W = f(S) ⊕ T'`; the characters
of `S'` and `T'` agree, and the induction hypothesis gives `S' ≅ T'`.
-/

open Module

namespace Representation

section Prod

variable {k G V₁ V₂ W₁ W₂ : Type*} [Field k] [Monoid G]
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]

/-- The character of `V₁ × V₂` is the sum of the characters. -/
theorem char_prod [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂) :
    (prod ρ₁ ρ₂).character = ρ₁.character + ρ₂.character := by
  ext g
  exact LinearMap.trace_prodMap' (ρ₁ g) (ρ₂ g)

/-- Products of equivalences of representations. -/
noncomputable def Equiv.prodCongr {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {σ₁ : Representation k G W₁} {σ₂ : Representation k G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) : (prod ρ₁ ρ₂).Equiv (prod σ₁ σ₂) :=
  Equiv.mk (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) fun g => LinearMap.ext fun x =>
    Prod.ext (IntertwiningMap.isIntertwining _ _ e₁.toIntertwiningMap g x.1)
      (IntertwiningMap.isIntertwining _ _ e₂.toIntertwiningMap g x.2)

end Prod

section Subrep

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

theorem Subrepresentation.isCompl_toSubmodule {S T : Subrepresentation ρ} (h : IsCompl S T) :
    IsCompl S.toSubmodule T.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule (disjoint_iff.1 h.1)
  · rw [codisjoint_iff]
    exact congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 h.2)

/-- An internal direct sum `V = S ⊕ T` of subrepresentations. -/
noncomputable def Subrepresentation.prodEquivOfIsCompl {S T : Subrepresentation ρ}
    (h : IsCompl S T) : (prod S.toRepresentation T.toRepresentation).Equiv ρ :=
  Equiv.mk (Submodule.prodEquivOfIsCompl _ _ (isCompl_toSubmodule h)) fun g => by
    refine LinearMap.ext fun x => ?_
    simp [Subrepresentation.toRepresentation]

end Subrep

variable {k G : Type*} [Field k] [CharZero k] [Group G] [Finite G]

/-- `dim Hom_G(V, W)` depends only on the characters. -/
private theorem finrank_intertwiningMap_eq {U V W : Type*} [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (τ : Representation k G U) (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) :
    finrank k (IntertwiningMap τ ρ) = finrank k (IntertwiningMap τ σ) := by
  letI := Fintype.ofFinite G
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank τ ρ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  rw [h, h2] at h1
  exact_mod_cast h1.symm

private theorem nonempty_equiv_aux (n : ℕ) {V W : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (hn : finrank k V = n)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  induction n using Nat.strong_induction_on generalizing V W with
  | _ n ih =>
  have hdim : finrank k V = finrank k W := by
    have := congrFun h 1
    simp only [char_one] at this
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- both are zero
    haveI : Subsingleton V := Module.finrank_zero_iff.1 hn
    haveI : Subsingleton W := Module.finrank_zero_iff.1 (hdim.symm.trans hn)
    exact ⟨Equiv.mk (LinearEquiv.ofFinrankEq V W hdim) fun g =>
      LinearMap.ext fun x => Subsingleton.elim _ _⟩
  -- a nonzero subrepresentation `S` of least dimension
  have hex : ∃ m, ∃ S : Subrepresentation ρ, 0 < finrank k S.toSubmodule ∧
      finrank k S.toSubmodule = m :=
    ⟨n, ⊤, by
      change 0 < finrank k (⊤ : Submodule k V); rwa [finrank_top, hn], by
      change finrank k (⊤ : Submodule k V) = n; rw [finrank_top, hn]⟩
  classical
  obtain ⟨S, hSpos, hSm⟩ := Nat.find_spec hex
  have hSmin : ∀ T : Subrepresentation ρ, 0 < finrank k T.toSubmodule →
      finrank k S.toSubmodule ≤ finrank k T.toSubmodule := fun T hT => by
    rw [hSm]; exact Nat.find_min' hex ⟨T, hT, rfl⟩
  -- `Hom_G(S, W) ≠ 0`, because `Hom_G(S, V) ≠ 0`
  let ι : IntertwiningMap S.toRepresentation ρ :=
    S.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap _ _ fun g v => rfl
  have hι : ι ≠ 0 := by
    obtain ⟨v, hvS, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.1 hSpos)
    intro h0
    have h1 : ι ⟨v, hvS⟩ = 0 := by rw [h0]; rfl
    exact hv h1
  have hpos' : 0 < finrank k (IntertwiningMap S.toRepresentation σ) := by
    rw [← finrank_intertwiningMap_eq S.toRepresentation ρ σ h]
    exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι⟩
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos'
  -- `f` is injective, by the minimality of `S`
  have hker : LinearMap.ker f.toLinearMap = ⊥ := by
    let K : Subrepresentation ρ :=
      ⟨(LinearMap.ker f.toLinearMap).map S.toSubmodule.subtype, by
        rintro g _ ⟨x, hx, rfl⟩
        exact ⟨S.toRepresentation g x, f.ker.apply_mem_toSubmodule g hx, rfl⟩⟩
    have hK : finrank k K.toSubmodule = finrank k (LinearMap.ker f.toLinearMap) :=
      (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective _ Subtype.val_injective _)).symm
    have hlt : finrank k (LinearMap.ker f.toLinearMap) < finrank k S.toSubmodule := by
      refine Submodule.finrank_lt fun htop => hf ?_
      exact IntertwiningMap.ext (LinearMap.ker_eq_top.1 htop)
    by_contra hne
    have := hSmin K (hK ▸ Submodule.one_le_finrank_iff.2 hne)
    omega
  -- `S ≅ f(S)`
  let T : Subrepresentation σ := f.range
  let eST : S.toRepresentation.Equiv T.toRepresentation :=
    Equiv.mk (LinearEquiv.ofInjective f.toLinearMap (LinearMap.ker_eq_bot.1 hker)) fun g =>
      LinearMap.ext fun x => Subtype.ext (IntertwiningMap.isIntertwining _ _ f g x)
  -- Maschke: complements `S'` of `S` and `T'` of `T`
  haveI : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨S', hS'⟩ := exists_isCompl S
  obtain ⟨T', hT'⟩ := exists_isCompl T
  let eV := Subrepresentation.prodEquivOfIsCompl hS'
  let eW := Subrepresentation.prodEquivOfIsCompl hT'
  have hchar : S'.toRepresentation.character = T'.toRepresentation.character := by
    have h1 := char_iso eV
    have h2 := char_iso eW
    rw [char_prod] at h1 h2
    rw [← h1, ← h2, char_iso eST] at h
    exact add_left_cancel h
  have hfin : finrank k S'.toSubmodule < n := by
    have := Submodule.finrank_add_eq_of_isCompl (Subrepresentation.isCompl_toSubmodule hS')
    omega
  obtain ⟨e'⟩ := ih _ hfin S'.toRepresentation T'.toRepresentation rfl hchar
  exact ⟨(eV.symm.trans (Equiv.prodCongr eST e')).trans eW⟩

variable {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Two finite-dimensional representations of a finite group over a field of characteristic
zero with the same character are isomorphic. -/
theorem nonempty_equiv_of_character_eq (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_aux _ ρ σ rfl h

/-- Finite-dimensional representations of a finite group over a field of characteristic zero
are isomorphic iff their characters are equal. -/
theorem nonempty_equiv_iff_character_eq (ρ : Representation k G V) (σ : Representation k G W) :
    Nonempty (ρ.Equiv σ) ↔ ρ.character = σ.character :=
  ⟨fun ⟨e⟩ => char_iso e, nonempty_equiv_of_character_eq ρ σ⟩

/-- Unbundled form: if `tr ρ(g) = tr σ(g)` for all `g`, there is a linear isomorphism
`e : V ≃ W` with `e (ρ g x) = σ g (e x)`. -/
theorem exists_linearEquiv_of_trace_eq (ρ : Representation k G V) (σ : Representation k G W)
    (h : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    ∃ e : V ≃ₗ[k] W, ∀ g x, e (ρ g x) = σ g (e x) := by
  obtain ⟨φ⟩ := nonempty_equiv_of_character_eq ρ σ (funext h)
  exact ⟨φ.toLinearEquiv, fun g x => IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x⟩

end Representation
