import PosetJKS.OrderComplex
import PosetJKS.Milestone
import PosetJKS.LieTrace
import PosetJKS.OPLattice
import PosetJKS.Mside
import PosetJKS.LieSide
import PosetJKS.MainIso
import PosetJKS.TraceHP

/-!
# The poset JKS theorem (Theorem `thm:main` of `notes/poset_jks_theorem.tex`)

For a finite poset `P` on `n ≥ 3` points, a primitive `n`-th root of unity `ζ`, and
`g ∈ Aut(P)`:

* (characterconj) `(-1)^{n-3} μ(OP(P)^g) = sgn(g) ∑_{C ∈ Cyc(P), gC = C} ζ^{r_g(C)}`;
* (mainiso) `H_P ≅ sgn ⊗ PLie(P)` as `Aut(P)`-modules;
* (closed) `sgn(g)(-1)^{n-3} μ(OP(P)^g) = ∑_{gC=C} ζ^{r_g(C)} = μ(o) ∑_{x ∈ F(P,g)} e_C(P|_{B_0(x)})`.

The note proves these assuming three cited inputs (Jenča–Sarkoci, P. Hall, Hopf trace
formula). Here the cited inputs are *not* assumed. (characterconj) and (closed) are proved
without any of them: from Proposition `prop:Mside` (`prop_Mside`, which uses the homology-free
proof of Lemma `lem:small`, `mu_OP_eq`) and Proposition `prop:Lside` (`prop_Lside`). (mainiso)
is stated outright with a `sorry` proof, and the two cited inputs that are expressible without topology are recorded as
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

/-- (characterconj). Proved from `prop_Mside` and `prop_Lside`; no topology or homology. -/
theorem character_identity (hn : 3 ≤ Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :
    (-1 : ℂ) ^ (Fintype.card α - 3) * (muFixed g : ℂ) = sgnC g * fixedClassSum ζ g := by
  classical
  have h0 : 0 < Fintype.card α := by omega
  -- any choice of one block of each `x ∈ F(P,g)`
  let B₀ : Finset (Finset α) → Finset α := fun x => if h : x.Nonempty then h.choose else ∅
  have hB₀ : ∀ x, InF g x → B₀ x ∈ x := by
    intro x hx
    have hne : x.Nonempty := Finset.card_pos.1 (hx.1 ▸ orderOf_pos_aut g)
    simp only [B₀, dif_pos hne]
    exact hne.choose_spec
  -- Möbius side = Lie side
  have hML : (Mt g : ℂ) = fixedClassSum ζ g := by
    rw [prop_Lside h0 hζ g B₀ hB₀, prop_Mside h0 g B₀ hB₀]
    push_cast
    rfl
  have hs : sgnC g * sgnC g = 1 := by
    unfold sgnC
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card α = m + 3 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
  rw [← hML, Mt]
  push_cast
  change _ = sgnC g * ((-1 : ℂ) ^ (Fintype.card α + 1) * sgnC g * (muFixed g : ℂ))
  rw [hm, Nat.add_sub_cancel]
  calc (-1 : ℂ) ^ m * (muFixed g : ℂ)
      = (sgnC g * sgnC g) * ((-1) ^ m * (muFixed g : ℂ)) * ((-1) ^ 2) ^ 2 := by
        rw [hs]; ring
    _ = sgnC g * ((-1 : ℂ) ^ (m + 3 + 1) * sgnC g * (muFixed g : ℂ)) := by ring

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
  refine ⟨?_, prop_Lside (by omega) hζ g B₀ hB₀⟩
  have hs : sgnC g * sgnC g = 1 := by
    unfold sgnC
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [mul_assoc, character_identity hn hζ g, ← mul_assoc, hs, one_mul]

/-! ### Cited inputs, in the form the proofs use them (not assumed; Jenča–Sarkoci is `sorry`'d,
P. Hall is proved in `Hall.lean`) -/

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
        (-1 : ℤ) ^ (m + 1) * (Nat.card (Fin m ↪o {x : L // x ≠ ⊥ ∧ x ≠ ⊤}) : ℤ) :=
  mu_bot_top_eq_chainSum L h

/-! ### The two characters (intermediate statements of Proof I) -/

/-- (homchar): `tr(g | H_P) = (-1)^{n-3} μ(OP(P)^g)`. The note derives it from Jenča–Sarkoci,
P. Hall and the Hopf trace formula. -/
theorem trace_HP (hn : 3 ≤ Fintype.card α) (g : α ≃o α) :
    LinearMap.trace ℂ (HP α) (actHP g) = (-1 : ℂ) ^ (Fintype.card α - 3) * (muFixed g : ℂ) :=
  trace_HP_of_vanishing hn (jencaSarkoci_homology hn).1 g

/-- (liechar): `tr(g | PLie(P)) = ∑_{gC=C} ζ^{r_g(C)}`. Elementary. -/
theorem trace_PLie (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α))
    (g : α ≃o α) :
    LinearMap.trace ℂ (PLie α ζ) (actPLie ζ g) = fixedClassSum ζ g :=
  trace_actPLie h0 hζ.pow_eq_one g

/-- (mainiso): `H_P ≅ sgn ⊗ PLie(P)` as `Aut(P)`-modules. A linear isomorphism
`e : H_P ≃ PLie(P)` intertwines the `Aut(P)`-action on `H_P` with `sgn ⊗` (left multiplication
on `PLie(P)`): `e (g · x) = sgn(g) · g · e(x)`. -/
theorem main_iso (hn : 3 ≤ Fintype.card α) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
    ∃ e : HP α ≃ₗ[ℂ] PLie α ζ, ∀ (g : α ≃o α) (x : HP α),
      (e (actHP g x) : Alg α) = sgnC g • relabel g.toEquiv (e x) := by
  exact exists_iso_HP_PLie_of_trace (by omega) hζ fun g =>
    (trace_HP hn g).trans (character_identity hn hζ g)

end PosetJKS
