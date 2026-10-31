import PosetJKS

/-!
Run from `lean/`:  lake env lean scripts/CheckDeps.lean

Prints, for each listed theorem, whether the cited inputs `jencaSarkoci_homology` and
`hall_mu_eq_reducedEuler` occur in the transitive closure of the constants its proof uses.
-/

open Lean

/-- Positive controls: declarations that do use the cited inputs. -/
theorem PosetJKS.checkDepsControlJS {α : Type} [Fintype α] [DecidableEq α] [PartialOrder α]
    (hn : 3 ≤ Fintype.card α) : Module.finrank ℂ (PosetJKS.HP α) = PosetJKS.eC α :=
  (PosetJKS.jencaSarkoci_homology hn).2

theorem PosetJKS.checkDepsControlHall :
    IncidenceAlgebra.mu ℤ (⊥ : Fin 2) ⊤ = IncidenceAlgebra.mu ℤ (⊥ : Fin 2) ⊤ :=
  (PosetJKS.hall_mu_eq_reducedEuler (Fin 2) (by decide)).trans
    (PosetJKS.hall_mu_eq_reducedEuler (Fin 2) (by decide)).symm

/-- All constants reachable from `n` through types and values of declarations. -/
partial def depClosure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      for d in ci.type.getUsedConstants do todo := todo.push d
      if let some v := ci.value? (allowOpaque := true) then
        for d in v.getUsedConstants do todo := todo.push d
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let cited := [``PosetJKS.jencaSarkoci_homology, ``PosetJKS.hall_mu_eq_reducedEuler]
  for t in [``PosetJKS.checkDepsControlJS, ``PosetJKS.checkDepsControlHall, ``PosetJKS.mu_OP_eq, ``PosetJKS.prop_Mside, ``PosetJKS.character_identity,
      ``PosetJKS.closed_formula, ``PosetJKS.main_iso] do
    let s := depClosure env t
    let hits := cited.filter s.contains
    IO.println s!"{t}: {s.size} constants; cited inputs used: {hits}"
