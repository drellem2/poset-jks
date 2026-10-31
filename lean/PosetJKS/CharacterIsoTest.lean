import PosetJKS.CharacterIso
import Mathlib.Analysis.Complex.Basic

/-!
# Controls for `Representation.nonempty_equiv_of_character_eq`

`G = S_2 = Perm (Fin 2)` over `ℂ`, with three 2-dimensional representations:

* `permRep`: the permutation representation on `Fin 2 → ℂ`, character `(2, 0)`;
* `trivSgn`: trivial ⊕ sign on `ℂ × ℂ`, character `(1 + 1, 1 - 1) = (2, 0)`;
* `triv2`: the trivial representation on `Fin 2 → ℂ`, character `(2, 2)`.

The lemma gives `trivSgn ≅ permRep` (equal characters, different underlying modules, and no
identity map between them), while `triv2 ≇ permRep` (different characters, same module, same
dimension). Likewise `trivial ≇ sign` on `ℂ`.
-/

open Module Equiv

namespace PosetJKS.CharacterIsoTest

/-- The sign representation of `S_2` on `ℂ`. -/
noncomputable def sgnRep : Representation ℂ (Perm (Fin 2)) ℂ where
  toFun g := (((Perm.sign g : ℤˣ) : ℤ) : ℂ) • LinearMap.id
  map_one' := by simp; rfl
  map_mul' g h := by
    ext
    simp [Perm.sign_mul, mul_comm]

/-- The permutation representation of `S_2` on `Fin 2 → ℂ`: `(g x)(i) = x(g⁻¹ i)`. -/
noncomputable def permRep : Representation ℂ (Perm (Fin 2)) (Fin 2 → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ g.symm
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [LinearMap.funLeft, Perm.mul_def, Equiv.symm_trans_apply]

/-- trivial ⊕ sign on `ℂ × ℂ`. -/
noncomputable def trivSgn : Representation ℂ (Perm (Fin 2)) (ℂ × ℂ) :=
  Representation.prod (Representation.trivial ℂ (Perm (Fin 2)) ℂ) sgnRep

/-- The trivial representation on `Fin 2 → ℂ`. -/
noncomputable def triv2 : Representation ℂ (Perm (Fin 2)) (Fin 2 → ℂ) :=
  Representation.trivial ℂ _ _

theorem perm_fin_two (g : Perm (Fin 2)) : g = 1 ∨ g = swap 0 1 := by
  revert g; decide

theorem char_permRep (g : Perm (Fin 2)) :
    permRep.character g = if g = 1 then 2 else 0 := by
  rcases perm_fin_two g with rfl | rfl
  · simp
  · rw [if_neg (by decide), Representation.character,
      LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2)), Matrix.trace_fin_two]
    simp [permRep, LinearMap.funLeft]

theorem char_trivSgn (g : Perm (Fin 2)) :
    trivSgn.character g = if g = 1 then 2 else 0 := by
  rw [trivSgn, Representation.char_prod]
  rcases perm_fin_two g with rfl | rfl
  · simp; norm_num
  · rw [if_neg (by decide)]
    simp [Representation.character, sgnRep]

theorem char_triv2 (g : Perm (Fin 2)) : triv2.character g = 2 := by
  simp [Representation.character, triv2]

/-- Equal characters: the lemma produces an isomorphism `ℂ × ℂ ≅ Fin 2 → ℂ`. -/
theorem trivSgn_equiv_permRep : Nonempty (trivSgn.Equiv permRep) :=
  Representation.nonempty_equiv_of_character_eq _ _ (funext fun g => by
    rw [char_trivSgn, char_permRep])

/-- Different characters: same module and dimension, not isomorphic. -/
theorem not_triv2_equiv_permRep : IsEmpty (triv2.Equiv permRep) := by
  refine ⟨fun e => ?_⟩
  have := congrFun (Representation.char_iso e) (swap 0 1)
  rw [char_triv2, char_permRep, if_neg (by decide)] at this
  norm_num at this

/-- `trivial ≇ sign` on `ℂ`. -/
theorem not_triv_equiv_sgn :
    IsEmpty ((Representation.trivial ℂ (Perm (Fin 2)) ℂ).Equiv sgnRep) := by
  refine ⟨fun e => ?_⟩
  have := congrFun (Representation.char_iso e) (swap 0 1)
  simp [Representation.character, sgnRep] at this
  norm_num at this

/-- The iff form, on both pairs. -/
example : Nonempty (trivSgn.Equiv permRep) ∧ ¬ Nonempty (triv2.Equiv permRep) := by
  rw [Representation.nonempty_equiv_iff_character_eq,
    Representation.nonempty_equiv_iff_character_eq]
  refine ⟨funext fun g => by rw [char_trivSgn, char_permRep], fun h => ?_⟩
  have := congrFun h (swap 0 1)
  rw [char_triv2, char_permRep, if_neg (by decide)] at this
  norm_num at this

end PosetJKS.CharacterIsoTest
