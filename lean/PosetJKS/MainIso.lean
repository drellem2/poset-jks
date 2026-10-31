import PosetJKS.OrderComplex
import PosetJKS.Milestone
import PosetJKS.LieTrace
import PosetJKS.CharacterIso

/-!
# (mainiso) from the two characters

`H_P` with `g ↦ actHP g` and `sgn ⊗ PLie(P)` with `g ↦ sgn(g) · actPLie g` are representations
of the finite group `Aut(P)` (`repHP`, `repSgnPLie`). If their characters agree, they are
isomorphic (`Representation.exists_linearEquiv_of_trace_eq`). The character of `sgn ⊗ PLie(P)`
is `sgn(g) ∑_{gC=C} ζ^{r_g(C)}` by Lemma `lem:liechar` (`trace_actPLie`). So
`exists_iso_HP_PLie_of_trace` reduces (mainiso) to `tr(g | H_P) = sgn(g) ∑_{gC=C} ζ^{r_g(C)}`,
which is (homchar) followed by (characterconj).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Functoriality of the action on homology -/

section OrderComplex

variable {L : Type*} [PartialOrder L]

theorem chainMap_refl (m : ℕ) (z : Chains L m) : chainMap (OrderIso.refl L) m z = z := by
  change Finsupp.mapDomain _ z = z
  convert Finsupp.mapDomain_id

theorem chainMap_trans (φ ψ : L ≃o L) (m : ℕ) (z : Chains L m) :
    chainMap (φ.trans ψ) m z = chainMap ψ m (chainMap φ m z) := by
  change Finsupp.mapDomain _ z = Finsupp.mapDomain _ (Finsupp.mapDomain _ z)
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem homMap_refl (d : ℕ) (x : redHom L d) : homMap (OrderIso.refl L) d x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    unfold homMap
    rw [Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (chainMap_refl _ _)

theorem homMap_trans (φ ψ : L ≃o L) (d : ℕ) (x : redHom L d) :
    homMap (φ.trans ψ) d x = homMap ψ d (homMap φ d x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    unfold homMap
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (chainMap_trans _ _ _ _)

/-- `H̃_d(Δ(L))` is finite-dimensional for a finite poset `L`. -/
theorem finiteDimensional_redHom [Finite L] (d : ℕ) : FiniteDimensional ℂ (redHom L d) := by
  haveI : Finite (Fin (d + 1) ↪o L) :=
    Finite.of_injective (fun f : Fin (d + 1) ↪o L => (f : Fin (d + 1) → L))
      DFunLike.coe_injective
  haveI : FiniteDimensional ℂ (Chains L (d + 1)) :=
    (inferInstance : FiniteDimensional ℂ ((Fin (d + 1) ↪o L) →₀ ℂ))
  infer_instance

end OrderComplex

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

theorem actProper_one : actProper (1 : α ≃o α) = OrderIso.refl _ := by
  refine OrderIso.ext (funext fun s => Subtype.ext ?_)
  ext x y
  exact Iff.rfl

theorem actProper_mul (g h : α ≃o α) :
    actProper (g * h) = (actProper h).trans (actProper g) := by
  refine OrderIso.ext (funext fun s => Subtype.ext ?_)
  ext x y
  exact Iff.rfl

omit [DecidableEq α] in
theorem finiteDimensional_HP : FiniteDimensional ℂ (HP α) := by
  haveI : Finite (Setoid α) :=
    Finite.of_injective (fun s : Setoid α => fun x y => s x y) fun s t h => by
      ext x y; exact iff_of_eq (congrFun (congrFun h x) y)
  exact finiteDimensional_redHom _

variable (α) in
/-- `H_P` as a representation of `Aut(P)`. -/
noncomputable def repHP : Representation ℂ (α ≃o α) (HP α) where
  toFun := actHP
  map_one' := LinearMap.ext fun x => by
    simp only [actHP, actProper_one, homMap_refl]; rfl
  map_mul' g h := LinearMap.ext fun x => by
    simp only [actHP, actProper_mul, homMap_trans]; rfl

theorem repHP_apply (g : α ≃o α) : repHP α g = actHP g := rfl

/-! ### `sgn ⊗ PLie(P)` -/

omit [DecidableEq α] in
theorem relabel_mul (g h : Equiv.Perm α) (y : Alg α) :
    relabel (g * h) y = relabel g (relabel h y) := by
  change Finsupp.mapDomain _ y = Finsupp.mapDomain _ (Finsupp.mapDomain _ y)
  rw [← Finsupp.mapDomain_comp]
  rfl

omit [DecidableEq α] in
theorem relabel_one (y : Alg α) : relabel (1 : Equiv.Perm α) y = y := by
  change Finsupp.mapDomain _ y = y
  convert Finsupp.mapDomain_id

/-- `sgn(g)` as a complex number. -/
noncomputable abbrev sgnAut (g : α ≃o α) : ℂ := ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ)

theorem sgnAut_mul (g h : α ≃o α) : sgnAut (g * h) = sgnAut g * sgnAut h := by
  simp only [sgnAut]
  rw [show (g * h).toEquiv = g.toEquiv * h.toEquiv from rfl, Equiv.Perm.sign_mul]
  push_cast; ring

theorem sgnAut_one : sgnAut (1 : α ≃o α) = 1 := by
  simp only [sgnAut]
  rw [show (1 : α ≃o α).toEquiv = 1 from rfl, Equiv.Perm.sign_one]
  simp

variable (α) in
/-- `sgn ⊗ PLie(P)` as a representation of `Aut(P)`: `g ↦ sgn(g) · (left multiplication)`. -/
noncomputable def repSgnPLie (ζ : ℂ) : Representation ℂ (α ≃o α) (PLie α ζ) where
  toFun g := sgnAut g • actPLie ζ g
  map_one' := LinearMap.ext fun y => Subtype.ext <| by
    change sgnAut 1 • relabel (1 : α ≃o α).toEquiv (y : Alg α) = y
    rw [sgnAut_one, one_smul]
    exact relabel_one _
  map_mul' g h := LinearMap.ext fun y => Subtype.ext <| by
    simp only [sgnAut_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
      Submodule.coe_smul, actPLie, LinearMap.restrict_coe_apply, smul_smul]
    rw [show (g * h).toEquiv = g.toEquiv * h.toEquiv from rfl, relabel_mul, mul_comm]

theorem trace_repSgnPLie (h0 : 0 < Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :
    LinearMap.trace ℂ (PLie α ζ) (repSgnPLie α ζ g) = sgnAut g * fixedClassSum ζ g := by
  change LinearMap.trace ℂ (PLie α ζ) (sgnAut g • actPLie ζ g) = _
  rw [map_smul, trace_actPLie h0 hζ.pow_eq_one g, smul_eq_mul]

/-- (mainiso) from the characters: if `tr(g | H_P) = sgn(g) ∑_{gC=C} ζ^{r_g(C)}` for every
`g ∈ Aut(P)`, then `H_P ≅ sgn ⊗ PLie(P)` as `Aut(P)`-modules, in the form of `main_iso`. -/
theorem exists_iso_HP_PLie_of_trace (h0 : 0 < Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α))
    (htr : ∀ g : α ≃o α, LinearMap.trace ℂ (HP α) (actHP g) = sgnAut g * fixedClassSum ζ g) :
    ∃ e : HP α ≃ₗ[ℂ] PLie α ζ, ∀ (g : α ≃o α) (x : HP α),
      (e (actHP g x) : Alg α) = sgnAut g • relabel g.toEquiv (e x) := by
  haveI : Finite (α ≃o α) :=
    Finite.of_injective (fun g : α ≃o α => g.toEquiv) fun _ _ h => OrderIso.ext (by
      simpa using congrArg DFunLike.coe h)
  haveI := finiteDimensional_HP (α := α)
  obtain ⟨e, he⟩ := Representation.exists_linearEquiv_of_trace_eq (repHP α) (repSgnPLie α ζ)
    fun g => by rw [repHP_apply, htr, trace_repSgnPLie h0 hζ]
  refine ⟨e, fun g x => ?_⟩
  rw [← repHP_apply, he]
  rfl

end PosetJKS
