import PosetJKS.Complement
import PosetJKS.TraceHP
import PosetJKS.MainIso

/-!
# The homological content of Jenča–Sarkoci

Route C, slice S4 (`notes/lean_js_route.md` §1, §3.2 Theorem V, §6). For a finite poset `P` on
`n ≥ 3` points:

* **Theorem V** (`vanish_aux`, `redHom_properOP_subsingleton`): `H̃_d(Δ(\widehat{OP(P)})) = 0`
  for every `d ∈ ℕ` with `d + 3 ≠ n`. By strong induction on `n`: for `n ≤ 2` the proper part is
  empty (`isEmpty_properOP`); for `n ≥ 3` pick a minimal `a` and apply Proposition C at `π_a`
  (`propC` for `d ≥ 1`, with the induction hypothesis for the `(n − 1)`-point posets `P/π_ab`;
  `redHom_zero_subsingleton` for `d = 0`, where `d + 3 ≠ n` forces `n ≥ 4`).
* `actHP_one`: the identity of `Aut(P)` acts trivially on `H_P`.
* `finrank_HP` (§1): `dim H_P = e_C(P)`, from `trace_HP_of_vanishing` at `g = 1` and
  `mu_OP_eq`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

omit [DecidableEq α] in
/-- On at most two points every partition is `0̂` or `1̂`, so the proper part of `OP(P)` is
empty. -/
theorem isEmpty_properOP (hn : Fintype.card α ≤ 2) : IsEmpty (ProperOP α) := by
  classical
  refine ⟨fun s => ?_⟩
  obtain ⟨s, -, hbot, htop⟩ := s
  apply htop
  -- `s ≠ 0̂` gives two distinct related points `x, y`; every point is one of them
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, s x y ∧ x ≠ y := by
    by_contra hc
    push Not at hc
    exact hbot (Setoid.ext fun u v => ⟨fun h => hc u v h, fun h => h ▸ s.refl u⟩)
  have hxy' : ∀ z, z = x ∨ z = y := by
    intro z
    by_contra hz
    push Not at hz
    have : ({x, y, z} : Finset α).card = 3 := by
      rw [card_insert_of_notMem (by simp [hne, hz.1.symm]),
        card_pair (Ne.symm hz.2)]
    have := card_le_univ ({x, y, z} : Finset α)
    omega
  refine Setoid.ext fun u v => ⟨fun _ => trivial, fun _ => ?_⟩
  rcases hxy' u with rfl | rfl <;> rcases hxy' v with rfl | rfl
  · exact s.refl _
  · exact hxy
  · exact s.symm hxy
  · exact s.refl _

/-- **Theorem V** (`notes/lean_js_route.md` §3.2), in the form of `mu_OP_eq_aux`: for every
finite poset on `n` points and every `d` with `d + 3 ≠ n`, `H̃_d(Δ(\widehat{OP(P)})) = 0`. -/
theorem vanish_aux : ∀ (n : ℕ) (β : Type*) [Fintype β] [PartialOrder β],
    Fintype.card β = n → ∀ d, d + 3 ≠ n → Subsingleton (redHom (ProperOP β) d) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro β _ _ hcard d hd
  rcases Nat.lt_or_ge n 3 with hn | hn
  · have := isEmpty_properOP (α := β) (by omega)
    exact subsingleton_redHom_of_isEmpty d
  have : Nonempty β := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨a, -, ha'⟩ :=
    exists_minimal_of_wellFoundedLT (fun _ : β => True) ⟨Classical.arbitrary β, trivial⟩
  have ha : ∀ u, u ≤ a → u = a := fun u hu => le_antisymm hu (ha' trivial hu)
  rcases d with _ | m
  · exact redHom_zero_subsingleton ha (by omega)
  · exact propC ha (by omega) m fun b _ h =>
      ih (n - 1) (by omega) _ (by rw [Contr.card_eq, hcard]) m (by omega)

omit [DecidableEq α] in
/-- (V): `H̃_d(Δ(\widehat{OP(P)})) = 0` for `d + 3 ≠ n`. -/
theorem redHom_properOP_subsingleton {d : ℕ} (hd : d + 3 ≠ Fintype.card α) :
    Subsingleton (redHom (ProperOP α) d) :=
  vanish_aux _ α rfl d hd

theorem actProper_one_apply (s : ProperOP α) : actProper (1 : α ≃o α) s = s :=
  Subtype.ext (actSetoid_one s.1)

theorem chainMap_actProper_one (m : ℕ) :
    chainMap (actProper (1 : α ≃o α)) m = LinearMap.id := by
  have : (fun c : Fin m ↪o ProperOP α => c.trans (actProper (1 : α ≃o α)).toOrderEmbedding) =
      id := by
    funext c
    exact RelEmbedding.ext fun i => actProper_one_apply (c i)
  unfold chainMap
  rw [this]
  exact Finsupp.lmapDomain_id ℂ ℂ

/-- The identity of `Aut(P)` acts on `H_P` as the identity. -/
theorem actHP_one : actHP (1 : α ≃o α) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
  unfold actHP homMap
  rw [Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change chainMap _ _ z.1 = z.1
  rw [chainMap_actProper_one]
  rfl

/-- (D) (`notes/lean_js_route.md` §1): given (V), `dim H_P = e_C(P)`. At `g = 1` the trace
of `actHP 1 = id` is `dim H_P`, and `(-1)^{n-3} μ(OP(P)) = (-1)^{n-3} (-1)^{n-1} e_C(P) = e_C(P)`
by `mu_OP_eq`. -/
theorem finrank_HP (hn : 3 ≤ Fintype.card α)
    (hvan : ∀ d, d ≠ Fintype.card α - 3 → Subsingleton (redHom (ProperOP α) d)) :
    Module.finrank ℂ (HP α) = eC α := by
  haveI := finiteDimensional_HP (α := α)
  have htr := trace_HP_of_vanishing hn hvan 1
  rw [actHP_one, LinearMap.trace_id, mu_OP_eq (by omega)] at htr
  rw [show Fintype.card α - 1 = (Fintype.card α - 3) + 2 by omega] at htr
  have : ((Module.finrank ℂ (HP α) : ℕ) : ℂ) = (eC α : ℂ) := by
    rw [htr]
    push_cast
    rw [← mul_assoc, ← pow_add, ← add_assoc, ← two_mul, ← mul_add_one, pow_mul]
    norm_num
  exact_mod_cast this

/-- The homological content of Jenča–Sarkoci, in the form of
`MainTheorem.jencaSarkoci_homology`. -/
theorem jencaSarkoci_homology_aux (hn : 3 ≤ Fintype.card α) :
    (∀ d, d ≠ Fintype.card α - 3 → Subsingleton (redHom (ProperOP α) d)) ∧
    Module.finrank ℂ (HP α) = eC α :=
  have hvan : ∀ d, d ≠ Fintype.card α - 3 → Subsingleton (redHom (ProperOP α) d) :=
    fun _ hd => redHom_properOP_subsingleton (by omega)
  ⟨hvan, finrank_HP hn hvan⟩

end PosetJKS
