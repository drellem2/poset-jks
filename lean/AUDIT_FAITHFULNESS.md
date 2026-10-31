# Faithfulness audit of the Lean statements and definitions

**Verdict: two statements are UNFAITHFUL and the rest are faithful.** `trace_PLie` and
`corPsi_bijective` (and with it the packaged `corPsi`) are false at the empty poset `n = 0`.
Both counterexamples are proved in Lean (`Test.lean`, sorry-free). All other stated results say
what `notes/poset_jks_theorem.tex` says, three of them with a note. Every definition passed its
positive controls on small posets, so no definition was changed. The model `HP` of `H_P` is the
reduced homology the note means. It has no degree or augmentation off-by-one, and `∂ ∘ ∂ = 0`
is now proved.

Scope: `lean/PosetJKS/{Basic,OrderComplex,Milestone,MainTheorem}.lean` at `59391ac`, compared
with `notes/poset_jks_theorem.tex` (§2 conventions, Theorem `thm:main`, Lemmas `lem:homchar`,
`lem:liechar`, cited inputs (A)–(C), Theorem `thm:S`, §`sec:natural`), not with
`lean/PLAN.md`'s description of it. Positive controls are in `lean/PosetJKS/Test.lean`, which
`lake build` builds. Reference values come from `compute/output/character_table.tsv`. Labels
`1, …, n` there are `0, …, n-1` in Lean.

## 1. Statement by statement

| Lean (file:line) | Note | Verdict |
|---|---|---|
| `character_identity` (`MainTheorem.lean:35`) | (characterconj) | **FAITHFUL** |
| `main_iso` (`MainTheorem.lean:43`) | (mainiso) | **FAITHFUL** |
| `closed_formula` (`MainTheorem.lean:63`) | (closed) | **FAITHFUL WITH NOTE** (a) |
| `trace_HP` (`MainTheorem.lean:76`) | Lemma `lem:homchar` | **FAITHFUL WITH NOTE** (b) |
| `trace_PLie` (`MainTheorem.lean:81`) | Lemma `lem:liechar` | **UNFAITHFUL**: false at `n = 0` (§1.1) |
| `jencaSarkoci_homology` (`MainTheorem.lean:90`) | input (A) | **FAITHFUL WITH NOTE** (c) |
| `hall_mu_eq_reducedEuler` (`MainTheorem.lean:99`) | input (B) | **FAITHFUL WITH NOTE** (d) |
| `thmS_a` (`Milestone.lean:34`) | Theorem `thm:S`(a) | **FAITHFUL** |
| `thmS_b` (`Milestone.lean:41`) | Theorem `thm:S`(b) | **FAITHFUL** |
| `thmPsi` (`Milestone.lean:64`) | Theorem `thm:Psi` | **FAITHFUL** |
| `corPsi_bijective` (`Milestone.lean:119`) | Corollary `cor:psi` | **UNFAITHFUL**: false at `n = 0` (§1.1) |
| `corPsi_equivariant` (`Milestone.lean:124`) | Corollary `cor:psi` | **FAITHFUL** |
| `corPsi` (`Milestone.lean:130`) | Corollary `cor:psi` | **UNFAITHFUL**: inherits `corPsi_bijective` |

**Status (2026-10-31): the three UNFAITHFUL rows are resolved by §1.1's suggested fix.** The
verdicts above are the audit's, for the statements at `59391ac`, and are left as they were.
Commit `ab4b48a` added `(h0 : 0 < Fintype.card α)` to `trace_PLie`, `corPsi_bijective` and
`corPsi`, which is exactly the fix §1.1 proposes, and changed nothing else in these statements.
`main_iso` and `closed_formula` discharge `h0` from `3 ≤ n`. The clean-checkout verification
(`notes/lean_verification.md` §4) compared every audited statement and definition at `59391ac`
with `origin/main` at `b7df20e`. This was the only change.

### 1.1 The defect: `n = 0`

The note's Lemma `lem:liechar` and Corollary `cor:psi` say "every finite poset". At `n = 0` the
note's objects are undefined (`e_ζ = (1/n)∑_j …`), so the note does not cover that case. The
Lean statements do: `IsPrimitiveRoot ζ 0` is satisfiable (Mathlib's `IsPrimitiveRoot.zero`: `ζ = 0`,
and also any `ζ` that is not a root of unity), and `(0 : ℂ)⁻¹ = 0`. So:

* `PLie(∅) = 0`, since `wEζ` is an empty sum (`PLie_fin0`).
* `M_∅ = W_∅/R_∅ = ℂ`. The empty word is a linear extension, and `R_∅ = 0` because no
  `S ⊆ ∅` is nonempty (`R_fin0`, `MP_fin0_ne`).
* So `ψ_∅ : 0 → ℂ` is not bijective. `Test.corPsi_bijective_false` proves
  `IsPrimitiveRoot (0:ℂ) (card (Fin 0)) ∧ ¬ Bijective (psi (Fin 0) 0)`.
* `coset w = (range 0).image _ = ∅`, so `Cyc(∅) = {∅}`, the empty class is fixed, and
  `fixedClassSum ζ 1 = ζ^0 = 1`. But the trace on `PLie(∅) = 0` is `0`.
  `Test.trace_PLie_false` proves the inequality for every `ζ`, including `ζ = 0`, which
  satisfies `trace_PLie`'s hypothesis.

Combined with the sorry'd statements, these lemmas derive `False`. A proof of
`corPsi_bijective` or `trace_PLie` as stated is therefore impossible.

**Suggested fix (for the PM to file; statements not changed here):** add `(h0 : 0 < Fintype.card α)`
(or `[Nonempty α]`) to `trace_PLie`, `corPsi_bijective` and `corPsi`. The note's statement has
no such hypothesis, but its objects need it (`1/n`). So this is the note's implicit `n ≥ 1`,
not a new mathematical restriction. `corPsi_equivariant` holds at `n = 0` and needs nothing.
`thmPsi` at `n = 0` is vacuously true (`hrep` asks for `rep C ∈ C = ∅`). `thmS_a` and `thmS_b`
carry `x₀ : α`, so they are safe. The main theorem carries `3 ≤ n`. Changing `coset` to contain
`w` at `n = 0` would not repair `trace_PLie`, because `PLie(∅) = 0` regardless.

### 1.2 Checks behind the FAITHFUL verdicts

Each check is against the note's §`sec:setup` conventions.

* **Rotation and `ζ` conventions.** `rot w j = (finRotate n ^ j).trans w`, so
  `rot w j i = w (i + j)`. This is the note's `(wγ^j)_i = w_{i+j}` (`finRotate_succ_apply`:
  `i ↦ i + 1`). `wEζ` uses the coefficients `n⁻¹ (ζ^j)⁻¹ = ζ^{-j}/n`, as in `e_ζ`.
  `classRot g C` takes the least `r < n` with `g ∘ w = rot w r` for some `w ∈ C`. That is the
  note's `g w = w γ^r`, i.e. `g(w_i) = w_{i+r}`, and `r` is unique because the `n` rotations
  of a word are distinct. Proved in Lean: `relabel g (w e_ζ) = ζ^r (w e_ζ)` whenever
  `g ∘ w = rot w r` and `ζ^n = 1` (`relabel_wEζ_of_rot`). So the per-class trace contribution is
  `ζ^{classRot}`, matching `fixedClassSum`, and not `ζ^{-r}`. The note's remark that the class
  *sum* is invariant under `r ↦ -r` makes the direction invisible in rotation multisets, so the
  per-class control `classRot_g3_012 = 1` (with the mismatch `≠ 2`) is the one that pins it.
* **Left vs right actions.** `relabel g` is `w ↦ g ∘ w` (left, relabel letters). `rot` is right
  multiplication. `actSetoid g s = comap g⁻¹ s` has blocks `g(B)`, a left action.
  `chainMap` pushes chains forward. An order isomorphism keeps a chain's increasing enumeration
  increasing, so `g` acts on oriented simplices with no sign, as in the proof of `lem:homchar`.
* **`sgnC`** is `sign(g)` as a permutation of the ground set, which is labelling-independent.
  Controls: `sgnC (0 1 2) = 1` and `sgnC (1 2) = -1`.
* **`(-1)^{n-3}` with `n - 3 : ℕ`.** Every statement that uses it, and `HP`, carries
  `3 ≤ n`, so truncated subtraction never occurs.
* **"Union of components".** `IsUnionOfComponents S := ∀ x y, x ≤ y → (x ∈ S ↔ y ∈ S)`.
  This says closed under comparability, i.e. a union of connected components of the
  comparability graph. Exercised through `B_P` and the cut set (controls below).
* **"Order-preserving"** (`IsOrderPreserving`): mutual reachability along `≤`-or-same-block
  steps forces the same block. This is acyclicity of `P/π` (a directed cycle through two blocks
  ⇔ two points in different blocks that reach each other). Jenča–Sarkoci's order congruences
  are the same partitions. Controls below, including one that must be rejected.
* **`InB`** ("first block contains `P_1`"). Union-prefixes of a linear extension are nested
  unions of components, and the first block is the shortest nonempty one. So "first block ⊇
  component of `x₀`" ⇔ "`x₀` lies in every nonempty union-prefix". Checked on the 2+1 poset for
  both base points: `|B_P| = 2 = e_C`.
* **`Sh`, `R`, `W`, `PLie`** match the note's spans. `shuffle S u v` is the sum of the words
  whose subwords on `S`, `Sᶜ` are `u`, `v`, i.e. the interleavings (letters are distinct, so
  there are no multiplicities).
* **`IsAdmissible`, `sLam`** match: `λ([n]) = 1`, `λ(U) ≠ 1` on nonempty proper unions, and
  `s_λ(w) = ∑_{k cut} λ(w_1⋯w_k)^{-1} wγ^k` with `k < n` (`IsCut`).
* **`main_iso`** states `e(g·x) = sgn(g)·g·e(x)` in the ambient `ℂ[S_n]`, which is
  `H_P ≅ sgn ⊗ PLie(P)`.

Notes on the FAITHFUL WITH NOTE rows:

* (a) `closed_formula`: `InF g x` encodes `x ∈ F(P,g)` as a set of blocks: exactly
  `orderOf g` nonempty blocks, each a union of components, pairwise disjoint, covering, `g`
  maps blocks to blocks, transitively. The note's "`B_0(x)` is any one block" is read
  universally (`∀ B₀, (∀ x, InF g x → B₀ x ∈ x) → …`). That is the stronger of the two
  readings, and it is what the note asserts (its proof shows that different blocks give
  isomorphic pairs). `μ(o)` is `ArithmeticFunction.moebius (orderOf g)`. `e_C(P|_B)` is
  `eC ↥B` with the induced order. Not evaluated in Lean (`orderOf` is not computable). Hand
  check on the 3-antichain with `g = (0 1 2)`: `F = {{0}|{1}|{2}}`, so the right side is
  `μ(3)·1 = -1`. This equals the proved `fixedClassSum = ζ + ζ² = -1`.
* (b) `trace_HP` is stated outright. The note derives it from (A)–(C), and that is not a
  faithfulness issue.
* (c) `jencaSarkoci_homology` keeps only the homological consequence of (A), which is all the
  proofs use. `H̃_{-1}` is not modelled (`d : ℕ`). That is harmless: for `n ≥ 3` the proper part
  is nonempty (merge a covering pair, or any two points of an antichain, into one block), so
  `H̃_{-1} = 0` holds anyway.
* (d) `hall_mu_eq_reducedEuler` adds `⊥ ≠ ⊤`. The note's statement of (B) is silent on it,
  but it is needed (one point: `μ = 1`, `χ̃(∅) = -1`). Stanley's Prop. 3.8.6 is stated for
  `0̂ ≠ 1̂`. The sign `(-1)^{m+1}` on `m`-element chains is `(-1)^{dim}` with `dim = m - 1`, and
  the empty chain counts `-1`. Hand checks: 2-element lattice `μ = -1 = -1 + 0`; 3-chain
  `μ = 0 = -1 + 1`; Boolean `B_2` `μ = 1 = -1 + 2`. Not evaluated in Lean.

**Hypotheses audit.** Apart from `⊥ ≠ ⊤` in the cited Hall theorem (d), no stated theorem has a
hypothesis absent from the note. The defect in §1.1 is the opposite: a hypothesis implicit in
the note (`n ≥ 1`) is missing.

## 2. Positive controls (`lean/PosetJKS/Test.lean`)

Posets: 3-antichain `anti3`, 3-chain `chain3`, 2+1 `p21` (`0<1`), 4-antichain `anti4`,
4-chain `chain4`, N `pN` (`0<2, 0<3, 1<2`), two 2-chains `twoChains` (`0<3, 1<2`), and the
2-chain `chain2`. "kernel" means `decide +kernel` or a proof, checked by the kernel. "guard" means
`#guard` (compiled evaluation; a false `#guard` fails the build, which was checked).

**Computability.** `cyc`, `eC`, `fixedClassSum` and `classRot` are written with
`open Classical`, so `#eval` cannot run them. The proved bridge lemmas `natCard_linExt`,
`eC_eq`, `cyc_eq`, `fixedClassSum_eq` and `classRot_eq_of` rewrite them into the same
expressions with computable instances, and the kernel then evaluates the *original*
definitions. `IsOrderPreserving` (via `ReflTransGen`), `muFixed`, `PLie` and `HP` are not
computable. They are checked by hand-proved lemmas and, for `μ`, by a labelled mirror.

| Quantity | Poset | Expected (`character_table.tsv`) | Lean | How |
|---|---|---|---|---|
| `\|Lin P\|` | anti3, chain3, p21, anti4, chain4, N, twoChains | 6, 1, 3, 24, 1, 5, 6 | same | kernel |
| `e_C(P)` | same | 2, 1, 2, 6, 1, 5, 5 | same | kernel |
| `\|B_P\| = e_C` | p21, base points `0` and `2` | 2, 2 | 2, 2 | kernel |
| `r_g(C)` | anti3, `g=(0 1 2)`, classes of `012`, `021` | 1, 2 | 1, 2 | kernel |
| `∑_{gC=C} ζ^{r}` | anti3, `(0 1 2)` | `1^1,2^1`: `ζ+ζ² = -1` | `ζ + ζ²`, `= -1` for primitive `ζ` | proof |
| `∑_{gC=C} ζ^{r}` | anti3, `(1 2)` | no fixed class: `0` | `0` | kernel |
| `sgn(g)` | `(0 1 2)`, `(1 2)` | 1, -1 | 1, -1 | kernel |
| set partitions enumerated | anti3, anti4 | Bell 5, 15 | 5, 15 | kernel |
| `\|OP(P)\|` | chain3, p21, anti3 | 4, 5, 5 | same | kernel (certified decision of `IsOrderPreserving`) |
| `\|OP(P)\|` | anti4, chain4, N, twoChains | 15, 8, 14, 14 | same | guard (same procedure) |
| `{0,1}\|{2}` order-preserving on chain3 | | yes | yes | kernel, `op_chain3_01_2` |
| `μ(OP(P))` (`g = id`) | chain2 | -1 | `muFixed (refl) = -1` | proof, `muFixed_chain2` |
| `μ(OP(P))` (`g = id`) | anti3, chain3, p21, anti4, chain4, N, twoChains | 2, 1, 2, -6, -1, -5, -5 | same | guard, **mirror** |
| `μ(OP(P)^g)` | anti3 `(0 1 2)`, `(1 2)`; anti4 `(0 1)(2 3)`, `(0 1 2 3)`; twoChains `(0 1)(2 3)` | -1, 0, 2, 0, 1 | same | guard, **mirror** |
| `w e_ζ` eigenvalue | all `α` | `g·we_ζ = ζ^r we_ζ` when `gw = wγ^r` | proved | proof, `relabel_wEζ_of_rot` |
| `dim PLie` | — | — | not computed | see below |

**Controls that must mismatch, and do:**

* `eC chain3 ≠ 2` and `|Lin p21| ≠ 6`: one relation more or fewer changes the value.
* Reversed `Lin` (`w_i < w_j → j < i`, linear extensions of the dual): for p21 it has the same
  size, 3, but it is a different set of words, and the kernel separates them.
* `classRot (0 1 2) [012] ≠ 2`: the opposite rotation convention would give 2.
* `{0,2}|{1}` is rejected on the 3-chain (`not_op_chain3_02_1`; `0 < 1 < 2 ~ 0` is a cycle) and
  accepted on the 3-antichain (`op_anti3_02_1`).
* `IncidenceAlgebra.mu ℤ 1̂ 0̂ = 0`: swapped arguments do not give `-1`.
* The mirror gives `μ(OP(chain3)) ≠ 2`, the antichain's value.
* An instrument failure the controls caught. In a first draft, `op_anti3_02_1` failed. The
  labelling had been written `(![0,1,0] : anti3.T → Fin 3)`, but a type ascription does not
  change the inferred type `Fin 3 → Fin 3`. Its kernel was therefore a setoid on `Fin 3`, with
  `Fin`'s *linear* order. The same slip had made `InB 0` read `0 : Fin 3`. Both now go through
  `lab`/`toT`, which fix the carrier. The wrong reading is kept as a passing negative example
  (`¬ IsOrderPreserving (ker (![0,1,0] : Fin 3 → Fin 3))`). For future Lean controls on type
  synonyms: an antichain control is what exposes a leaked linear order.

**What is not machine-checked:**

* The set partitions are enumerated as restricted growth functions, and their kernels are
  tested with the Lean predicate `IsOrderPreserving` (certified by `isOrderPreserving_ker_iff`).
  The bijection "RGFs ↔ `Setoid α`" behind reading the counts as `Nat.card (OP α)` is standard
  but not formalized.
* `muFixed` itself is evaluated only on the 2-chain. The other `μ` values come from
  `muFixedMirror`, a transcription of the Möbius recursion on the same certified partition
  lists, not the Lean definition. They agree with `compute/`, which checks the conventions
  (refinement order, `0̂` discrete, `μ(0̂,1̂)`, `g`-fixed sublattice). They do not check Mathlib's
  `mu`.
* `dim PLie` is not computed: the span of complex vectors is not decidable here. It is
  covered indirectly by the eigenvalue lemma and by the `n = 0` computation `PLie(∅) = 0`.
* `closed_formula`'s right side and `hall_mu_eq_reducedEuler` are checked by hand only (§1.2 (a), (d)).

## 3. Is `HP` the reduced homology the note means?

Yes. Degree by degree:

* `Chains L m = (Fin m ↪o L) →₀ ℂ` is spanned by the `m`-element chains, i.e. the
  `(m-1)`-simplices of `Δ(L)` with their increasing orientation. `Chains L 0 ≅ ℂ` is spanned by
  the empty chain, the `(-1)`-face of the augmented complex.
* `bd L m : Chains (m+1) → Chains m` is `∑_i (-1)^i (delete the i-th element)`, the standard
  simplicial boundary. **`∂ ∘ ∂ = 0` is now proved** (`bd_comp_bd`, by the involution
  `(i, j) ↦ (i.succAbove j, j.predAbove i)` and Mathlib's `succAbove`/`predAbove` identities).
  So `redHom` is homology, not just a quotient.
* `bd L 0` sends every vertex to the empty chain with coefficient `+1` (`bd_zero_single`). It
  is the augmentation `ε`, so `redHom L 0 = ker ε / im ∂_1 = H̃_0`.
* `redHom L d = ker ∂_d / im ∂_{d+1}` on `(d+1)`-element chains, i.e. `d`-simplices: `H̃_d`.
  `HP = redHom (ProperOP α) (n - 3)` is computed on `(n-2)`-element chains, the
  `(n-3)`-simplices. The proper part of `OP(P)` has chains of at most `n - 2` elements, so
  `im ∂_{n-2} = 0` and `HP` is the space of top cycles. That agrees with the note's proof of
  Lemma `lem:D`.
* `ProperOP` removes exactly `0̂ = ⊥` (discrete) and `1̂ = ⊤` (one block), with Mathlib's
  refinement order (`Setoid.bot_def`, `Setoid.top_def`).

No off-by-one in degree or augmentation. The only unmodelled degree is `H̃_{-1}`, which
vanishes for `n ≥ 3` (§1.2 (c)). Recommendation: move `bd_comp_bd` into `OrderComplex.lean`
when proof work starts. It is in `Test.lean` here only because this audit does not change the
scaffold files.

## 4. Sorry count and axioms

`lake build` succeeds, with 12 `declaration uses sorry` warnings, all in the stated theorems
of `Milestone.lean` (5) and `MainTheorem.lean` (7), unchanged. `Test.lean` adds no `sorry`
and no warnings. There are no `axiom` declarations (`grep -rnw axiom PosetJKS scripts` finds
one comment). `lake env lean scripts/PrintAxioms.lean`:

```
'PosetJKS.character_identity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.main_iso' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.closed_formula' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.trace_HP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.trace_PLie' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.jencaSarkoci_homology' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.hall_mu_eq_reducedEuler' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.thmS_a' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.thmS_b' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.thmPsi' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.corPsi_bijective' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.corPsi_equivariant' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.corPsi' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.actHP' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.actMP' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.muFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.fixedClassSum_g3_prim' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.muFixed_chain2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.not_op_chain3_02_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.relabel_wEζ_of_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_comp_bd' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_zero_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.corPsi_bijective_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.trace_PLie_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No control uses `native_decide`, so there is no `Lean.ofReduceBool`. The decidability instances
the controls need (`IsLinExt`, `IsUnionOfComponents`, `InB`) are `local` to `Test.lean`, so
importing `PosetJKS` changes no instance seen elsewhere.

## Reproduce

```sh
cd lean
lake exe cache get
lake build                                   # builds PosetJKS including PosetJKS/Test.lean
lake env lean scripts/PrintAxioms.lean       # the table in §4
```
