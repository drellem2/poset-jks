import PosetJKS.OrderComplex
import PosetJKS.Milestone

/-!
# The poset JKS theorem (Theorem `thm:main` of `notes/poset_jks_theorem.tex`)

For a finite poset `P` on `n ≥ 3` points, a primitive `n`-th root of unity `ζ`, and
`g ∈ Aut(P)`:

* (characterconj) `(-1)^{n-3} μ(OP(P)^g) = sgn(g) ∑_{C ∈ Cyc(P), gC = C} ζ^{r_g(C)}`;
* (mainiso) `H_P ≅ sgn ⊗ PLie(P)` as `Aut(P)`-modules;
* (closed) `sgn(g)(-1)^{n-3} μ(OP(P)^g) = ∑_{gC=C} ζ^{r_g(C)} = μ(o) ∑_{x ∈ F(P,g)} e_C(P|_{B_0(x)})`.

The note proves these assuming three cited inputs (Jenča–Sarkoci, P. Hall, Hopf trace
formula). Here the cited inputs are *not* assumed: the main theorem is stated outright, with
`sorry` proofs, and the two cited inputs that are expressible without topology are recorded as
separate `sorry`'d theorems (`jencaSarkoci_homology`, `hall_mu_eq_reducedEuler`) so that a later
proof can be assembled from them. No `axiom` is declared anywhere.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- `sgn(g)` as a complex number. -/
noncomputable def sgnC (g : α ≃o α) : ℂ := ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ)

/-! ### Main theorem -/

/-- (characterconj). -/
theorem character_identity (hn : 3 ≤ Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :
    (-1 : ℂ) ^ (Fintype.card α - 3) * (muFixed g : ℂ) = sgnC g * fixedClassSum ζ g := by
  sorry

/-- (mainiso): `H_P ≅ sgn ⊗ PLie(P)` as `Aut(P)`-modules. A linear isomorphism
`e : H_P ≃ PLie(P)` intertwines the `Aut(P)`-action on `H_P` with `sgn ⊗` (left multiplication
on `PLie(P)`): `e (g · x) = sgn(g) · g · e(x)`. -/
theorem main_iso (hn : 3 ≤ Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    ∃ e : HP α ≃ₗ[ℂ] PLie α ζ, ∀ (g : α ≃o α) (x : HP α),
      (e (actHP g x) : Alg α) = sgnC g • relabel g.toEquiv (e x) := by
  sorry

/-- `x ∈ F(P,g)` (with `o` the order of `g`): `x` is a partition of the ground set into exactly
`o` blocks, each block a union of components, and `g` permutes the blocks cyclically (maps
blocks to blocks, transitively). A partition is given by its set of blocks. -/
def InF (g : α ≃o α) (x : Finset (Finset α)) : Prop :=
  x.card = orderOf g ∧
  (∀ B ∈ x, B.Nonempty ∧ IsUnionOfComponents B) ∧
  (∀ B ∈ x, ∀ B' ∈ x, B ≠ B' → Disjoint B B') ∧
  (∀ a : α, ∃ B ∈ x, a ∈ B) ∧
  (∀ B ∈ x, B.image g ∈ x) ∧
  (∀ B ∈ x, ∀ B' ∈ x, ∃ k : ℕ, B' = B.image (g ^ k))

open Classical in
/-- (closed). `B₀` is any choice of one block of each `x ∈ F(P,g)`; `e_C(P|_B)` is `e_C` of the
induced subposet on `B`. -/
theorem closed_formula (hn : 3 ≤ Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α)
    (B₀ : Finset (Finset α) → Finset α) (hB₀ : ∀ x, InF g x → B₀ x ∈ x) :
    sgnC g * (-1 : ℂ) ^ (Fintype.card α - 3) * (muFixed g : ℂ) = fixedClassSum ζ g ∧
    fixedClassSum ζ g =
      (ArithmeticFunction.moebius (orderOf g) : ℂ) *
        ∑ x ∈ (univ : Finset (Finset (Finset α))).filter (InF g), (eC (B₀ x) : ℂ) := by
  sorry

/-! ### The two characters (intermediate statements of Proof I) -/

/-- (homchar): `tr(g | H_P) = (-1)^{n-3} μ(OP(P)^g)`. The note derives it from Jenča–Sarkoci,
P. Hall and the Hopf trace formula. -/
theorem trace_HP (hn : 3 ≤ Fintype.card α) (g : α ≃o α) :
    LinearMap.trace ℂ (HP α) (actHP g) = (-1 : ℂ) ^ (Fintype.card α - 3) * (muFixed g : ℂ) := by
  sorry

/-- (liechar): `tr(g | PLie(P)) = ∑_{gC=C} ζ^{r_g(C)}`. Elementary. -/
theorem trace_PLie {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :
    LinearMap.trace ℂ (PLie α ζ) (actPLie ζ g) = fixedClassSum ζ g := by
  sorry

/-! ### Cited inputs, in the form the proofs use them (not assumed; `sorry`'d) -/

/-- Homological content of Jenča–Sarkoci, Thm 4.5 (`Δ(\widehat{OP(P)}) ≃ ⋁^{e_C(P)} S^{n-3}`
for `n ≥ 3`): the reduced homology of the order complex vanishes outside degree `n - 3`, and
`dim H_P = e_C(P)`. Only this consequence is used by Proofs I and II. -/
theorem jencaSarkoci_homology (hn : 3 ≤ Fintype.card α) :
    (∀ d, d ≠ Fintype.card α - 3 → Subsingleton (redHom (ProperOP α) d)) ∧
    Module.finrank ℂ (HP α) = eC α := by
  sorry

/-- P. Hall's theorem (Stanley EC1, Prop. 3.8.5/3.8.6): for a finite bounded poset `L` with
`0̂ ≠ 1̂`, `μ_L(0̂, 1̂)` is the reduced Euler characteristic of the order complex of the proper
part, `∑_{m ≥ 0} (-1)^{m-1} #{m-element chains of L ∖ {0̂, 1̂}}` (the empty chain is the
`(-1)`-dimensional face). -/
theorem hall_mu_eq_reducedEuler (L : Type*) [PartialOrder L] [BoundedOrder L] [Fintype L]
    [DecidableEq L] [LocallyFiniteOrder L] (h : (⊥ : L) ≠ ⊤) :
    IncidenceAlgebra.mu ℤ (⊥ : L) ⊤ =
      ∑ m ∈ range (Fintype.card L + 1),
        (-1 : ℤ) ^ (m + 1) * (Nat.card (Fin m ↪o {x : L // x ≠ ⊥ ∧ x ≠ ⊤}) : ℤ) := by
  sorry

end PosetJKS
