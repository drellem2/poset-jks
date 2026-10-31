import Mathlib

/-!
# The Hopf trace formula

Linear algebra over `ℂ`.

* `trace_eq_trace_restrict_add_trace_mapQ`: additivity of the trace on
  `0 → W → V → V/W → 0` for an endomorphism `f` of a finite-dimensional `V` with `f W ⊆ W`.
  Proof: split `V = W ⊕ W'` and `f = ι_W p f + ι_{W'} q f` with the two projections; cycle the
  traces (`trace_comp_comm'`); `p f ι_W` is `f|_W`, and `q f ι_{W'}` is conjugate to `f` on
  `V/W` under `V/W ≅ W'`.
* `hopf_trace`: for a chain complex `⋯ → C_{m+1} → C_m → ⋯ → C_0` of finite-dimensional spaces
  (`d m : C (m+1) → C m`, `d ∘ d = 0`) with a chain endomorphism `f` and `C_K = 0`,
  `∑_{m ≤ K} (-1)^m tr(f | C_m) = tr(f | C_0/∂C_1) - ∑_{j < K} (-1)^j tr(f | H_j)`, where
  `H_j = ker(d j)/im(d (j+1))` is the homology at `C_{j+1}`. With `C_m` in degree `m - 1` (as
  for the augmented complex of `OrderComplex.lean`, where `H_j = H̃_j`) this is
  `∑_m (-1)^{m-1} tr(f | C_m) = ∑_{j ≥ -1} (-1)^j tr(f | H_j)`.

The proof of `hopf_trace` is the telescoping of `tr(f|C_0) = R_0 + tr(f|C_0/∂C_1)` and
`tr(f|C_{m+1}) = R_{m+1} + tr(f|H_m) + R_m`, with `R_m = tr(f | ∂C_{m+1})`, from the exact
sequences `0 → ker d_m → C_{m+1} → im d_m → 0` and `0 → im d_{m+1} → ker d_m → H_m → 0`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

section TraceAdd

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Additivity of the trace: `tr f = tr(f|_W) + tr(f on V/W)` for `f W ⊆ W`. -/
theorem trace_eq_trace_restrict_add_trace_mapQ (f : V →ₗ[ℂ] V) (W : Submodule ℂ V)
    (hW : ∀ x ∈ W, f x ∈ W) :
    LinearMap.trace ℂ V f =
      LinearMap.trace ℂ W (f.restrict hW) + LinearMap.trace ℂ (V ⧸ W) (W.mapQ W f hW) := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  set p := W.linearProjOfIsCompl W' hc
  set q := W'.linearProjOfIsCompl W hc.symm
  have hpq : ∀ v, (p v : V) + q v = v := fun v => by
    rw [Submodule.coe_linearProjOfIsCompl_apply, Submodule.coe_linearProjOfIsCompl_apply,
      Submodule.IsCompl.projection_add_projection_eq_self]
  have hf : f = W.subtype ∘ₗ (p ∘ₗ f) + W'.subtype ∘ₗ (q ∘ₗ f) := by
    ext v; simp [hpq]
  have h1 : (p ∘ₗ f) ∘ₗ W.subtype = f.restrict hW := by
    ext w
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.restrict_coe_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨f w, hW w w.2⟩)
  have hmk : ∀ v : V, W.quotientEquivOfIsCompl W' hc (Submodule.Quotient.mk v) = q v := by
    intro v
    have : (Submodule.Quotient.mk v : V ⧸ W) = Submodule.Quotient.mk ((q v : W') : V) := by
      rw [Submodule.Quotient.eq, ← eq_sub_of_add_eq (hpq v)]
      exact (p v).2
    rw [this, Submodule.quotientEquivOfIsCompl_apply_mk_coe]
  have h2 : (q ∘ₗ f) ∘ₗ W'.subtype = (W.quotientEquivOfIsCompl W' hc).conj (W.mapQ W f hW) := by
    ext w'
    change (q (f w') : V) = ((W.quotientEquivOfIsCompl W' hc)
      (W.mapQ W f hW ((W.quotientEquivOfIsCompl W' hc).symm w')) : V)
    rw [Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply, hmk]
  calc LinearMap.trace ℂ V f
      = LinearMap.trace ℂ V (W.subtype ∘ₗ (p ∘ₗ f) + W'.subtype ∘ₗ (q ∘ₗ f)) :=
        congrArg _ hf
    _ = _ := by
      rw [map_add, LinearMap.trace_comp_comm' (p ∘ₗ f) W.subtype,
        LinearMap.trace_comp_comm' (q ∘ₗ f) W'.subtype, h1, h2,
        LinearMap.trace_conj']

theorem trace_eq_zero_of_subsingleton [Subsingleton V] (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V f = 0 := by
  rw [Subsingleton.elim f 0, map_zero]

end TraceAdd

section Hopf

variable {C : ℕ → Type*} [∀ m, AddCommGroup (C m)] [∀ m, Module ℂ (C m)]
  [∀ m, FiniteDimensional ℂ (C m)]
  (d : ∀ m, C (m + 1) →ₗ[ℂ] C m) (f : ∀ m, C m →ₗ[ℂ] C m)

/-- `f` is a chain map. -/
def IsChainMap : Prop := ∀ m, d m ∘ₗ f (m + 1) = f m ∘ₗ d m

variable {d f}

theorem IsChainMap.apply (hf : IsChainMap d f) (m : ℕ) (x : C (m + 1)) :
    d m (f (m + 1) x) = f m (d m x) := LinearMap.congr_fun (hf m) x

theorem IsChainMap.range_mem (hf : IsChainMap d f) (m : ℕ) :
    ∀ x ∈ LinearMap.range (d m), f m x ∈ LinearMap.range (d m) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨f (m + 1) y, hf.apply m y⟩

theorem IsChainMap.ker_mem (hf : IsChainMap d f) (m : ℕ) :
    ∀ x ∈ LinearMap.ker (d m), f (m + 1) x ∈ LinearMap.ker (d m) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [hf.apply, hx, map_zero]

/-- `f` on the cycles `ker d_m ⊆ C_{m+1}`. -/
noncomputable def IsChainMap.cyc (hf : IsChainMap d f) (m : ℕ) :
    LinearMap.ker (d m) →ₗ[ℂ] LinearMap.ker (d m) :=
  (f (m + 1)).restrict (hf.ker_mem m)

theorem IsChainMap.bdry_le (hf : IsChainMap d f) (m : ℕ) :
    (LinearMap.range (d (m + 1))).comap (LinearMap.ker (d m)).subtype ≤
      ((LinearMap.range (d (m + 1))).comap (LinearMap.ker (d m)).subtype).comap (hf.cyc m) := by
  rintro z ⟨b, hb⟩
  exact ⟨f (m + 2) b, by rw [hf.apply, hb]; rfl⟩

/-- `f` on the homology `H_m = ker d_m / im d_{m+1}` (at `C_{m+1}`). -/
noncomputable def IsChainMap.homol (hf : IsChainMap d f) (m : ℕ) :
    (LinearMap.ker (d m) ⧸ (LinearMap.range (d (m + 1))).comap (LinearMap.ker (d m)).subtype) →ₗ[ℂ]
      (LinearMap.ker (d m) ⧸ (LinearMap.range (d (m + 1))).comap (LinearMap.ker (d m)).subtype) :=
  Submodule.mapQ _ _ (hf.cyc m) (hf.bdry_le m)

/-- `f` on `C_0 / im d_0` (the homology in the lowest degree). -/
noncomputable def IsChainMap.homolBot (hf : IsChainMap d f) :
    (C 0 ⧸ LinearMap.range (d 0)) →ₗ[ℂ] (C 0 ⧸ LinearMap.range (d 0)) :=
  Submodule.mapQ _ _ (f 0) (hf.range_mem 0)

/-- `R_m = tr(f | im d_m)`. -/
noncomputable def IsChainMap.trRange (hf : IsChainMap d f) (m : ℕ) : ℂ :=
  LinearMap.trace ℂ (LinearMap.range (d m)) ((f m).restrict (hf.range_mem m))

theorem IsChainMap.trace_zero (hf : IsChainMap d f) :
    LinearMap.trace ℂ (C 0) (f 0) = hf.trRange 0 + LinearMap.trace ℂ _ hf.homolBot :=
  trace_eq_trace_restrict_add_trace_mapQ _ _ _

/-- `tr(f | C_{m+1}) = tr(f | ker d_m) + tr(f | im d_m)`. -/
theorem IsChainMap.trace_succ (hf : IsChainMap d f) (m : ℕ) :
    LinearMap.trace ℂ (C (m + 1)) (f (m + 1)) =
      LinearMap.trace ℂ _ (hf.cyc m) + hf.trRange m := by
  rw [trace_eq_trace_restrict_add_trace_mapQ _ _ (hf.ker_mem m)]
  congr 1
  rw [IsChainMap.trRange, ← LinearMap.trace_conj' _ (d m).quotKerEquivRange]
  congr 1
  ext y
  obtain ⟨x, rfl⟩ := (d m).quotKerEquivRange.surjective y
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
  rw [Submodule.mapQ_apply, LinearMap.quotKerEquivRange_apply_mk, LinearMap.restrict_coe_apply,
    LinearMap.quotKerEquivRange_apply_mk]
  exact hf.apply m x

/-- `tr(f | ker d_m) = tr(f | im d_{m+1}) + tr(f | H_m)`. -/
theorem IsChainMap.trace_cyc (hf : IsChainMap d f) (hd : ∀ m, d m ∘ₗ d (m + 1) = 0) (m : ℕ) :
    LinearMap.trace ℂ _ (hf.cyc m) = hf.trRange (m + 1) + LinearMap.trace ℂ _ (hf.homol m) := by
  rw [trace_eq_trace_restrict_add_trace_mapQ _ _ (hf.bdry_le m)]
  congr 1
  have hle : LinearMap.range (d (m + 1)) ≤ LinearMap.ker (d m) := by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (hd m) y
  rw [IsChainMap.trRange, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hle)]
  congr 1

/-- Telescoped form, with the boundary term `(-1)^K R_K`. -/
theorem IsChainMap.hopf_aux (hf : IsChainMap d f) (hd : ∀ m, d m ∘ₗ d (m + 1) = 0) (K : ℕ) :
    ∑ m ∈ range (K + 1), (-1 : ℂ) ^ m * LinearMap.trace ℂ (C m) (f m) =
      LinearMap.trace ℂ _ hf.homolBot +
        ∑ j ∈ range K, (-1 : ℂ) ^ (j + 1) * LinearMap.trace ℂ _ (hf.homol j) +
        (-1 : ℂ) ^ K * hf.trRange K := by
  induction K with
  | zero => simp [hf.trace_zero, add_comm]
  | succ K ih =>
    rw [sum_range_succ, ih, sum_range_succ, hf.trace_succ, hf.trace_cyc hd, pow_succ]
    ring

/-- **The Hopf trace formula** for a complex with `C_K = 0`:
`∑_{m ≤ K} (-1)^m tr(f | C_m) = tr(f | C_0/∂C_1) + ∑_{j < K} (-1)^{j+1} tr(f | H_j)`. -/
theorem IsChainMap.hopf_trace (hf : IsChainMap d f) (hd : ∀ m, d m ∘ₗ d (m + 1) = 0) (K : ℕ)
    [Subsingleton (C K)] :
    ∑ m ∈ range (K + 1), (-1 : ℂ) ^ m * LinearMap.trace ℂ (C m) (f m) =
      LinearMap.trace ℂ _ hf.homolBot +
        ∑ j ∈ range K, (-1 : ℂ) ^ (j + 1) * LinearMap.trace ℂ _ (hf.homol j) := by
  rw [hf.hopf_aux hd K, IsChainMap.trRange,
    trace_eq_zero_of_subsingleton ((f K).restrict (hf.range_mem K)), mul_zero, add_zero]

end Hopf

end PosetJKS
