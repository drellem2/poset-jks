import PosetJKS.Basic

/-!
# First milestone: the homology-free presentation `PLie(P) ≅ ℂ[Lin P]/R_P`

Statements of `notes/poset_jks_theorem.tex`:

* Theorem S (a), (b) (`thmS_a`, `thmS_b`): pure word combinatorics modulo shuffles;
* Theorem Ψ (`thmPsi`): admissible class sums are independent modulo `Sh_n`;
* Corollary Ψ.1 (`corPsi_bijective`, `corPsi_equivariant`): the truncation map
  `ψ_P : PLie(P) → ℂ[Lin P]/R_P` is an `Aut(P)`-isomorphism, for every finite poset `P`.

None of these uses homology, the Jenča–Sarkoci theorem, P. Hall, or the Hopf trace formula.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-! ### Theorem S -/

/-- `w ∈ B_P` for the base component containing `x₀`: `w ∈ Lin(P)` and the first block of `w`
(the shortest nonempty prefix whose letter set is a union of components) contains `x₀`.
Equivalently, `x₀` lies in every nonempty union-prefix, since union-prefixes are nested. -/
def InB (x₀ : α) (w : Word α) : Prop :=
  IsLinExt α w ∧ ∀ k, 0 < k → k ≤ Fintype.card α →
    IsUnionOfComponents (prefixSet w k) → x₀ ∈ prefixSet w k

/-- Theorem S(a). -/
theorem thmS_a (x₀ : α) :
    LinearIndependent ℂ (fun w : {w : Word α // InB x₀ w} => (Sh α).mkQ (wd w.1)) ∧
    Nat.card {w : Word α // InB x₀ w} = eC α ∧
    (IsConnectedPoset α → W α ⊓ Sh α = ⊥) := by
  sorry

/-- Theorem S(b): `W_P = span(B_P) ⊕ R_P`, `W_P ∩ Sh_n = R_P`, `dim R_P = |Lin P| - e_C(P)`. -/
theorem thmS_b (x₀ : α) :
    Submodule.span ℂ {x | ∃ w, InB x₀ w ∧ x = wd w} ⊔ R α = W α ∧
    Disjoint (Submodule.span ℂ {x | ∃ w, InB x₀ w ∧ x = wd w}) (R α) ∧
    W α ⊓ Sh α = R α ∧
    Module.finrank ℂ (R α) = Nat.card {w : Word α // IsLinExt α w} - eC α := by
  sorry

/-! ### Theorem Ψ -/

/-- `λ : α → ℂ` is admissible: `λ([n]) = 1` and `λ(U) ≠ 1` for every nonempty proper union of
components `U`, where `λ(U) = ∏_{x ∈ U} λ(x)`. (`λ([n]) = 1` forces `λ` to take values in
`ℂˣ`, as in the note.) -/
def IsAdmissible (lam : α → ℂ) : Prop :=
  ∏ a, lam a = 1 ∧
    ∀ U : Finset α, U.Nonempty → U ≠ univ → IsUnionOfComponents U → ∏ a ∈ U, lam a ≠ 1

open Classical in
/-- `s_λ(w) = ∑_{k a cut of w} λ(w_1 ⋯ w_k)⁻¹ w γ^k`. -/
noncomputable def sLam (lam : α → ℂ) (w : Word α) : Alg α :=
  ∑ k ∈ (range (Fintype.card α)).filter (IsCut w), (∏ a ∈ prefixSet w k, lam a)⁻¹ • wd (rot w k)

/-- Theorem Ψ: for admissible `λ`, the class sums `s_λ(C)`, one for each cyclic class `C`
(computed from any representative `w ∈ C ∩ Lin(P)`), are linearly independent modulo `Sh_n`. -/
theorem thmPsi (lam : α → ℂ) (hlam : IsAdmissible lam) (rep : cyc α → Word α)
    (hrep : ∀ C, rep C ∈ C.1 ∧ IsLinExt α (rep C)) :
    LinearIndependent ℂ (fun C => (Sh α).mkQ (sLam lam (rep C))) := by
  sorry

/-! ### Corollary Ψ.1: the truncation isomorphism `ψ_P : PLie(P) ≅ ℂ[Lin P]/R_P` -/

open Classical in
variable (α) in
/-- The coordinate truncation `pr_P : ℂ[S_n] → W_P` to `Lin(P)`. -/
noncomputable def pr : Alg α →ₗ[ℂ] Alg α :=
  ∑ w ∈ univ.filter (IsLinExt α), Finsupp.lsingle w ∘ₗ Finsupp.lapply w

theorem pr_mem_W (y : Alg α) : pr α y ∈ W α := by
  classical
  rw [pr, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun w hw => ?_
  have : (Finsupp.lsingle w ∘ₗ Finsupp.lapply w : Alg α →ₗ[ℂ] Alg α) y = y w • wd w := by
    change Finsupp.single w (y w) = y w • Finsupp.single w (1 : ℂ)
    rw [Finsupp.smul_single_one]
  rw [this]
  exact Submodule.smul_mem _ (y w)
    (Submodule.subset_span (show wd w ∈ {x | ∃ w, IsLinExt α w ∧ x = wd w} from
      ⟨w, (mem_filter.1 hw).2, rfl⟩))

variable (α) in
/-- `pr_P` with codomain `W_P`. -/
noncomputable def prW : Alg α →ₗ[ℂ] W α := (pr α).codRestrict (W α) pr_mem_W

variable (α) in
/-- `R_P`, as a subspace of `W_P`. -/
noncomputable abbrev RinW : Submodule ℂ (W α) := (R α).comap (W α).subtype

variable (α) in
/-- `M_P = W_P / R_P = ℂ[Lin P]/R_P`. -/
noncomputable abbrev MP := W α ⧸ RinW α

variable (α) in
/-- `ψ_P : PLie(P) → M_P`, `y ↦ pr_P(y) mod R_P`. (The note writes the target as
`(W_P + Sh_n)/Sh_n`; it is identified with `W_P/R_P` through `W_P ∩ Sh_n = R_P`, Theorem S(b),
and under that identification the two maps agree.) -/
noncomputable def psi (ζ : ℂ) : PLie α ζ →ₗ[ℂ] MP α :=
  (RinW α).mkQ ∘ₗ prW α ∘ₗ (PLie α ζ).subtype

/-- `Aut(P)` acting on `PLie(P)` by left multiplication. -/
noncomputable def actPLie (ζ : ℂ) (g : α ≃o α) : PLie α ζ →ₗ[ℂ] PLie α ζ :=
  (relabel g.toEquiv).restrict fun _ hy => relabel_mem_PLie g ζ hy

/-- `Aut(P)` acting on `M_P = ℂ[Lin P]/R_P` by left multiplication. -/
noncomputable def actMP (g : α ≃o α) : MP α →ₗ[ℂ] MP α :=
  Submodule.mapQ _ _ ((relabel g.toEquiv).restrict fun _ hy => relabel_mem_W g hy)
    fun x hy => by exact relabel_mem_R g hy

/-- Corollary Ψ.1, bijectivity: for every finite poset `P` and every primitive `n`-th root of
unity `ζ`, the truncation map `ψ_P` is a linear isomorphism `PLie(P) ≅ ℂ[Lin P]/R_P`. -/
theorem corPsi_bijective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    Function.Bijective (psi α ζ) := by
  sorry

/-- Corollary Ψ.1, equivariance: `ψ_P` commutes with the action of `Aut(P)` (no sign twist). -/
theorem corPsi_equivariant (ζ : ℂ) (g : α ≃o α) :
    psi α ζ ∘ₗ actPLie ζ g = actMP g ∘ₗ psi α ζ := by
  sorry

/-- Corollary Ψ.1 in packaged form: an `Aut(P)`-equivariant linear isomorphism
`PLie(P) ≃ ℂ[Lin P]/R_P` (namely `ψ_P`). -/
theorem corPsi {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    ∃ e : PLie α ζ ≃ₗ[ℂ] MP α, (∀ y, e y = psi α ζ y) ∧
      ∀ (g : α ≃o α) (y : PLie α ζ), e (actPLie ζ g y) = actMP g (e y) := by
  refine ⟨LinearEquiv.ofBijective (psi α ζ) (corPsi_bijective hζ), fun _ => rfl, fun g y => ?_⟩
  simp only [LinearEquiv.ofBijective_apply]
  exact LinearMap.congr_fun (corPsi_equivariant ζ g) y

end PosetJKS
