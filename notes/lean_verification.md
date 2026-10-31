# Clean-checkout verification of the Lean formalization

**Verdict: CONFIRMED.** On a fresh clone of `origin/main` at
`b7df20e3b2917bf09ccc57266c34ad1e6f9a3373`, `lake build` succeeds with no `sorry`, and
`main_iso`, `character_identity`, `trace_HP` and `jencaSarkoci_homology` depend only on
`propext`, `Classical.choice` and `Quot.sound`. Both positive controls fire. The statements and
definitions are the ones the faithfulness audit reviewed, with one change: the
`h0 : 0 < Fintype.card α` hypothesis on `trace_PLie`, `corPsi_bijective` and `corPsi`. This is the
fix the audit itself proposed (§4). Nothing that could weaken soundness was added after the
audit (§5).

Toolchain: `leanprover/lean4:v4.29.1`, Lake 5.0.0, Mathlib `v4.29.1`. `lakefile.toml`,
`lean-toolchain` and `lake-manifest.json` are unchanged since the audited commit. Nothing under
`lean/` was modified.

## 1. Fresh clone and build

```sh
git clone https://github.com/drellem2/poset-jks.git clean     # new, empty directory
cd clean && git rev-parse HEAD                                 # b7df20e3b2917bf09ccc57266c34ad1e6f9a3373
cd lean
lake exe cache get                                             # "Completed successfully!", exit 0
LEAN_NUM_THREADS=3 lake build > build.log 2>&1; echo $?        # 0
```

* `lake build` exit status **0**. Its last line is `Build completed successfully (8274 jobs).`
  All 25 `PosetJKS.*` modules and the root `PosetJKS` were compiled from source. The Mathlib
  oleans came from the cache.
* `grep -ic sorry build.log` gives **0**. The log has 313 warnings, all of them linter warnings
  (unused section variables, flexible tactics, long lines).
* `git status --porcelain` in the clone is empty after the build.

Source grep over all 27 `.lean` files (`lean/PosetJKS/*.lean`, `lean/PosetJKS.lean`,
`lean/scripts/*.lean`):

```sh
PAT='\bsorry\b|\badmit\b|^\s*(private |protected )?axiom\b|native_decide|implemented_by|@\[extern|\bunsafe\b|ofReduceBool|debug\.skipKernelTC'
grep -rnE "$PAT" PosetJKS PosetJKS.lean scripts --include='*.lean'      # no output, exit 1
```

## 2. `#print axioms` and the dependency check

```sh
LEAN_NUM_THREADS=3 lake env lean scripts/PrintAxioms.lean    # exit 0
LEAN_NUM_THREADS=3 lake env lean scripts/CheckDeps.lean      # exit 0
```

`PrintAxioms.lean` has 112 `#print axioms` lines and printed 112 results. **None mentions
`sorryAx`.** 111 of them read exactly `[propext, Classical.choice, Quot.sound]`. The other is
`'PosetJKS.isOrderPreserving_inf' depends on axioms: [propext, Quot.sound]`, a subset. The four
named results:

```
'PosetJKS.character_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.main_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.trace_HP' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.jencaSarkoci_homology' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`CheckDeps.lean` output, in full:

```
PosetJKS.checkDepsControlJS: 25235 constants; cited inputs used: [PosetJKS.jencaSarkoci_homology]
PosetJKS.checkDepsControlHall: 13334 constants; cited inputs used: [PosetJKS.hall_mu_eq_reducedEuler]
PosetJKS.mu_OP_eq: 15365 constants; cited inputs used: []
PosetJKS.prop_Mside: 18419 constants; cited inputs used: []
PosetJKS.character_identity: 23406 constants; cited inputs used: []
PosetJKS.closed_formula: 23408 constants; cited inputs used: []
PosetJKS.main_iso: 30522 constants; cited inputs used: [PosetJKS.jencaSarkoci_homology, PosetJKS.trace_HP]
PosetJKS.exists_iso_HP_PLie_of_trace: 24937 constants; cited inputs used: []
Representation.nonempty_equiv_of_character_eq: 17940 constants; cited inputs used: []
PosetJKS.hall_mu_eq_reducedEuler: 13252 constants; cited inputs used: [PosetJKS.hall_mu_eq_reducedEuler]
PosetJKS.trace_HP_of_vanishing: 22538 constants; cited inputs used: []
PosetJKS.trace_HP: 25235 constants; cited inputs used: [PosetJKS.jencaSarkoci_homology, PosetJKS.trace_HP]
```

`CheckDeps` reports which cited inputs a proof reaches. Now that those inputs are theorems,
reaching them is expected. As shipped, it does not test for `sorryAx`. I ran a scratch copy that
adds ``` ``sorryAx ``` to its `cited` list (not committed) on the clean tree. Every line is
identical to the output above, so `sorryAx` is in none of the transitive closures. The
appended `sorryAx` row only reports the constant itself.

## 3. Positive controls

**(a) A planted `sorry`.** I made an APFS clone (`cp -cR`) of the built checkout. In the clone
I replaced the whole proof of `vanish_aux` (`PosetJKS/JSHomology.lean:60`, Theorem V) with
`sorry`. Nothing was committed. Then I re-ran the same three commands:

* `lake build` exit 0. `grep -ic sorry` gives **1**:
  `warning: PosetJKS/JSHomology.lean:60:8: declaration uses `sorry``. The log has 314
  warnings, against 313 on the clean tree.
* `PrintAxioms`: 6 results now contain `sorryAx`, among them
  ```
  'PosetJKS.main_iso' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'PosetJKS.trace_HP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'PosetJKS.jencaSarkoci_homology' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'PosetJKS.vanish_aux' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  ```
  `character_identity` stays `[propext, Classical.choice, Quot.sound]`, as it should, because it
  does not use homology.
* `CheckDeps` changes in three lines (the closure sizes for `checkDepsControlJS` and `trace_HP`
  go from 25235 to 24863, and for `main_iso` from 30522 to 30210). The scratch `sorryAx` variant
  then reports `sorryAx` among the inputs of `checkDepsControlJS`, `main_iso` and `trace_HP`,
  and of nothing else.

**(b) The grep.** I appended one planted instance of each of `sorry`, `by admit`, `axiom`,
`native_decide`, `@[implemented_by …]`, `@[extern …]` and `unsafe def` to a scratch copy of
`Basic.lean`. Run with the same flags (`grep -rnE "$PAT" <dir> --include='*.lean'`), the grep
reports **7** matching lines, one per construct, with exit 0. On the clean tree it reports
**0**, with exit 1, which is grep's "no match" status and not its error status 2.

## 4. Faithfulness: statements and definitions against the audited commit

The faithfulness audit (`lean/AUDIT_FAITHFULNESS.md`) reviewed
`lean/PosetJKS/{Basic,OrderComplex,Milestone,MainTheorem}.lean` at `59391ac`. The commit that
added the audit has the same four files byte for byte. I compared `59391ac` with
`origin/main` (`b7df20e`).

* `Basic.lean` and `OrderComplex.lean` are **byte-identical**
  (`git diff --quiet 59391ac origin/main -- …` exits 0). They hold every audited definition
  except those in the next two items: `Word`, `Alg`, `rot`, `relabel`, `wEζ`, `coset`, `W`,
  `R`, `PLie`, `cyc`, `eC`, `classRot`, `fixedClassSum`, `IsUnionOfComponents`, `Chains`,
  `face`, `bd`, `cycles`, `boundaries`, `redHom`, `chainMap`, `homMap`, `IsOrderPreserving`,
  `OP`, `ProperOP`, `HP`, `actSetoid`, `actProper`, `actHP`, `OPFixed`, `muFixed`.
* The definitions in `Milestone.lean` (`InB`, `IsAdmissible`, `sLam`, `pr`, `prW`, `RinW`,
  `MP`, `psi`, `actPLie`, `actMP`) are textually identical.
* `sgnC` and the header of `MainTheorem.lean` (`open`, `set_option`, `namespace`, `variable`)
  are identical. `InF` moved from `MainTheorem.lean` to `LieSide.lean`. Its text is identical,
  and it sits under the same `variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]`
  context. `closed_formula` still uses it under `open Classical in`, as before.
* Statements, compared from `theorem` up to `:=`:
  `character_identity`, `main_iso`, `closed_formula`, `trace_HP`, `jencaSarkoci_homology`,
  `hall_mu_eq_reducedEuler`, `thmS_a`, `thmS_b`, `thmPsi` and `corPsi_equivariant` are
  **identical**.

**Finding (intended):** `trace_PLie`, `corPsi_bijective` and `corPsi` changed. Each gained the
hypothesis `(h0 : 0 < Fintype.card α)` in commit `ab4b48a`:

```
- theorem trace_PLie {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :
+ theorem trace_PLie (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α))
+     (g : α ≃o α) :
- theorem corPsi_bijective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
+ theorem corPsi_bijective (h0 : 0 < Fintype.card α) {ζ : ℂ}
+     (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
- theorem corPsi {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
+ theorem corPsi (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :
```

The audit rated these three statements UNFAITHFUL because each is false at `n = 0`, and it
proposed exactly this hypothesis. The note's objects need it (`e_ζ` has a factor `1/n`), so it
is not a new mathematical restriction. The other conclusions are unchanged. `main_iso` and
`closed_formula` carry `3 ≤ n` and discharge `h0` by `omega`. The verdict table of
`lean/AUDIT_FAITHFULNESS.md` §1 still lists the three statements as UNFAITHFUL and does not
record the fix.

Method: each statement or definition was cut out of `git show <rev>:<file>` and the two
strings were compared. As a control, the instrument reports `DIFF` for the changed
`trace_PLie` block, and every extracted block was checked to be non-empty.

## 5. Possible weakening added after the audit

I scanned the added lines of `git diff 59391ac origin/main` over `lean/` for `instance`,
`attribute`, `set_option`, `unsafe`, `axiom`, `sorry`, `native_decide`, `implemented_by`,
`extern`, `macro`, `elab`, `syntax`, `notation`, `opaque`, `csimp`, `partial`, `ofReduceBool`,
`run_cmd`, `initialize` and `local`:

* `set_option`: linter options only (`linter.unusedSectionVars`, `linter.style.longLine`,
  `linter.hashCommand`, `linter.unusedDecidableInType`, `linter.unusedFintypeInType`). There is
  no `maxHeartbeats`, no `debug.*` and no `trust`-type option. The `leanOptions` in
  `lakefile.toml` are unchanged.
* `instance`: the new instances fall into three groups:
  - Prop-valued: `Module.Finite ℂ (Alg α)`, `IsEmpty`, `Subsingleton`, `Finite` and
    `FiniteDimensional` on chain types.
  - On auxiliary types introduced in proofs: `Fintype`, `DecidableEq` and `PartialOrder` on
    `Contr a b h`.
  - On test types in `Test.lean`: the table poset `P.T` and `DecidablePred IsRGF`.

  None of them gives a second data instance on a type that occurs in a statement above.
* `attribute`: only `attribute [local instance] … in` and a file-local
  `attribute [local instance]` for decidability in `Test.lean`, plus `@[simp]`/`@[reducible]`.
* `local notation "σ" => g.toEquiv` (proof-local abbreviation). `partial def depClosure` is in
  `scripts/CheckDeps.lean`, a meta-program that is not imported by the library.
* No `unsafe`, `axiom`, `opaque`, `implemented_by`, `extern`, `native_decide`, `macro`/`elab`
  or `run_cmd`.

Whatever these additions are, they cannot introduce an unsound proof, because §2 shows every
listed result reduces in the kernel to the three standard axioms. The point of this section is
that they also do not change the meaning of any audited statement.
