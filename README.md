# poset-jks

Research program on a poset generalization of the Joyal–Klyachko–Stanley theorem.

**Status (October 2026).** The seed note's main conjecture holds as an
abstract isomorphism. For every finite poset P on n ≥ 3 points, the top
homology H_P of the proper part of the lattice of order-preserving partitions
is isomorphic, as an Aut(P)-module, to the sign twist of
Lie(P) = span{w·e_ζ : w a linear extension of P}. There is also a closed
formula for the character. The result is proved twice: once via Weisner's
theorem and once via Crapo's complementation theorem. Both proofs assume
Jenča–Sarkoci Thm 4.5, P. Hall's theorem and the Hopf trace formula, and an
independent audit found that both hold. That isomorphism is abstract, but
there is also an explicit one, for every P: truncate an element of Lie(P) to
the linear extensions and read it modulo shuffles. This truncation map is an
Aut(P)-isomorphism onto C[LinExt P]/R_P, proved by elementary word
combinatorics ("Theorem Ψ"); composed with the splitting-cycle model below it
gives H_P ⊗ sgn ≅ Lie(P) with no choices, compatible with relabelling. In the
stronger sense of naturality along order extensions, an isomorphism exists
exactly on connected posets: for disconnected P with n ≥ 3, no family of maps
compatible with the inclusions into P's own linear extensions is injective.
Both results are independently audited. The seed note's "restricted JKS image
identity" (its eq. restrictionlemma) is **false**. In its place, the splitting
cycles of the linear extensions span H_P, with an explicit basis (formerly
"Conjecture S"). That result is proved and audited, conditional on a cited
theorem of Wachs; it is checked without that input for n ≤ 6. The global
induced-module formula and b_n = n[x^n] log A(x) are proved. The
consolidated, self-contained account of the poset theorem, with the
epistemic status of every claim, is
[`notes/poset_jks_theorem.tex`](notes/poset_jks_theorem.tex).

**Lean.** The main theorem is formalized in Lean 4 + Mathlib
([`lean/`](lean/)), including its three cited inputs (Jenča–Sarkoci in its
homological form, P. Hall's theorem, the Hopf trace formula). The build has
**0 sorries**, and every declaration checked by `#print axioms` depends only
on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. This
was independently confirmed on a clean checkout (see below).

**Beyond posets.** Poset JKS is the braid-arrangement case of a theory of
top-cones of real hyperplane arrangements: a cone wedge theorem, a cone
Zaslavsky theorem, Theorem G\* (the chamber cycles of a cone span its top
homology, equivariantly; this settles parts (G1)–(G3) of Conjecture G), a
fixed-point character formula, a vanishing criterion, and the lift of all of
this to oriented matroids. Side questions on linear extensions, cyclic
sieving and moonshine are also written up. Their status is in the index
below.

`./build.sh` builds the three TeX notes to PDF if a TeX toolchain is present.

## Status tags

Each entry below carries the status its own verdict table and audit give it:

- **PROVEN + audited**: a proof is given and an independent audit note found
  that it holds (possibly with fixes, which are stated).
- **PROVEN, unaudited**: a proof is given; no independent audit exists yet.
- **COMPUTED**: checked by a script on a stated finite range.
- **CONJECTURED** / **OPEN**: stated, not proved.
- **REFUTED**: a counterexample is given.
- **STOP**: a scoping verdict that the direction should not be pursued.

"Not found" in a prior-art entry means not found in the literature searched;
it is the result of a search, not a claim of novelty. Prior-art verdicts are
quoted as the prior-art notes give them (KNOWN, PARTLY KNOWN, SPECIAL CASE
KNOWN, NOT FOUND).

## Lean formalization

- [`lean/PLAN.md`](lean/PLAN.md): plan and status, Steps 1–11. No `sorry`
  remains. Every stated theorem is proved, including the main theorem's three
  parts (characterconj), (mainiso), (closed) and all three cited inputs. Every
  declaration listed by `scripts/PrintAxioms.lean` depends only on `propext`,
  `Classical.choice` and `Quot.sound` (one, `isOrderPreserving_inf`, on
  `propext` and `Quot.sound` alone). No `axiom` declarations. Toolchain
  `leanprover/lean4:v4.29.1`, Mathlib `v4.29.1`.
- [`lean/AUDIT_FAITHFULNESS.md`](lean/AUDIT_FAITHFULNESS.md): audit of whether
  the Lean statements and definitions say what `notes/poset_jks_theorem.tex`
  says. `character_identity`, `main_iso`, `thmS_a`, `thmS_b`, `thmPsi`,
  `corPsi_equivariant` FAITHFUL; `closed_formula`, `trace_HP`,
  `jencaSarkoci_homology`, `hall_mu_eq_reducedEuler` FAITHFUL WITH NOTE.
  `trace_PLie` and `corPsi_bijective` (and so `corPsi`) were UNFAITHFUL (false
  at n = 0); the audit's own fix, a hypothesis `0 < n`, is applied. Its §4
  sorry and axiom data are historical.
- [`notes/lean_verification.md`](notes/lean_verification.md): clean-checkout
  verification. **CONFIRMED.** On a fresh clone of `origin/main` at `b7df20e`,
  `lake build` exits 0 with no `sorry`; all 112 `#print axioms` results are
  free of `sorryAx`; `main_iso`, `character_identity`, `trace_HP` and
  `jencaSarkoci_homology` depend only on `propext`, `Classical.choice` and
  `Quot.sound`; a planted `sorry` and a planted grep match both fire; the
  statements and definitions are those the faithfulness audit reviewed, except
  for the audit's own `0 < n` fix; nothing that could weaken soundness was
  added after the audit.
- [`notes/lean_js_route.md`](notes/lean_js_route.md): scoping of the last Lean
  input, `jencaSarkoci_homology`, and the proof of Route C (homological
  complementation at π_a: Lemma K, the §3.2 decomposition, Proposition C,
  Theorem V). PROVEN + audited; combinatorial claims COMPUTED on all 405
  posets with n ≤ 6. Route C is what `lean/` now implements (PLAN Steps 8–11).
- [`notes/audit_lean_js_route.md`](notes/audit_lean_js_route.md): its audit,
  HOLDS WITH FIXES (sign corrections G1–G2 in Lemma K, citation G3; none
  changes a result). Fixes applied to the note.

Build: `cd lean && lake exe cache get && lake build`, then
`lake env lean scripts/PrintAxioms.lean`.

## Notes

### Overview

- [`notes/poset_jks_theorem.tex`](notes/poset_jks_theorem.tex): the
  consolidated write-up (theorem, proof, corrections, computational record,
  open problems). Start here.
- [`notes/audit_poset_jks_theorem.md`](notes/audit_poset_jks_theorem.md):
  fidelity audit of the write-up against its sources. Nothing is presented as
  audited when it is not; no sign or quantifier error; the computational table
  matches the archived outputs. Its fixes are applied.
- [`notes/poset_jks_research_note.tex`](notes/poset_jks_research_note.tex):
  the original research note (the seed note), kept unedited. Its
  "open problems" are partly solved, and its eq. (restrictionlemma) is
  false. See the write-up above.
- [`notes/eli5_introduction.tex`](notes/eli5_introduction.tex)
  ([PDF](notes/eli5_introduction.pdf)): "Lie theory for posets and cones: a
  gentle introduction", for non-specialists. A summary with a status tag on
  every result; the proofs are in the notes it cites. Its Lean box and its
  moonshine status predate the last Lean step and the moonshine audit; the
  current status is the one on this page.

### The character identity and the main theorem

- [`notes/reproduce_character_identity_n_le_5.md`](notes/reproduce_character_identity_n_le_5.md):
  independent reproduction of the character identity, all posets n ≤ 6.
  COMPUTED (the identity for all n is now proved; see below).
- [`notes/n7_character_sweep_and_homology_crosscheck.md`](notes/n7_character_sweep_and_homology_crosscheck.md):
  all 2045 posets at n = 7, and a direct equivariant-homology cross-check.
  COMPUTED; Lemma 1 (which (P, g) can discriminate) PROVEN.
- [`notes/global_module_operations_plethlog.md`](notes/global_module_operations_plethlog.md):
  Proof I (Weisner), the global module HH_n, operations on posets, and the
  Hopf monoid behind the plethystic logarithm. §2 (Proof I) PROVEN + audited,
  given Jenča–Sarkoci; §§3–4 PROVEN (some modulo CITED results), unaudited;
  the poset cooperad and filtration CONJECTURED.
- [`notes/fixed_point_mobius_identity.md`](notes/fixed_point_mobius_identity.md):
  Proof II (Crapo complementation). PROVEN + audited, given three classical
  cited results.
- [`notes/audit_character_identity_proof.md`](notes/audit_character_identity_proof.md):
  independent audit of both proofs. Both PROOF HOLDS; no error found.
- [`notes/mu_op_elementary.md`](notes/mu_op_elementary.md): two
  homology-free proofs of μ(OP(P)) = (−1)^{n−1} e_C(P) (the write-up's
  `lem:small`). PROVEN + audited; COMPUTED for all 405 posets with n ≤ 6.
  Proof W is the one formalized in Lean. Its pairing of the e_C recursion with
  Weisner was not found in the literature searched.
- [`notes/audit_mu_op_elementary.md`](notes/audit_mu_op_elementary.md): its
  audit. Both proofs HOLD and are homology-free; fixes to citations and tags
  only, applied.
- [`notes/citation_check.md`](notes/citation_check.md): check of the main
  theorem's cited inputs (Jenča–Sarkoci, P. Hall, Hopf trace formula) and of
  Crapo, Weisner, Ree, Wachs and Aguiar–Mahajan against the sources. No cited
  statement is misstated; three imprecise pointers, fixed in the write-up.

### JKS maps, the correction, and the explicit basis

- [`notes/literature_novelty_jks_maps.md`](notes/literature_novelty_jks_maps.md):
  first literature search, explicit JKS maps (Prop. Φ), the counterexample to
  eq. (restrictionlemma) (Prop. C, PROVEN), and the statement of Conjecture S
  (since proved). Its literature search is superseded by
  `novelty_search_2.md`.
- [`notes/audit_literature_novelty_jks_maps.md`](notes/audit_literature_novelty_jks_maps.md):
  its audit. Prop. C and Prop. Φ CONFIRMED; Prop. C strengthened to
  poset-dependent maps (PROVEN there); two rows mildly overstated.
- [`notes/conjecture_s_splitting_cycles_span.md`](notes/conjecture_s_splitting_cycles_span.md):
  proof of Conjecture S via shuffle-preserving contractions. PROVEN + audited,
  given the cited inputs. Theorems A, B and Cor. 5.4 were not found in the
  literature searched.
- [`notes/audit_conjecture_s.md`](notes/audit_conjecture_s.md): its audit.
  PROOF HOLDS; wording issues only.
- [`notes/novelty_search_2.md`](notes/novelty_search_2.md): second, wider
  prior-art search for six results. Main theorem, fixed-point Möbius formula,
  splitting-cycle basis, Klyachko via contraction: PARTIALLY KNOWN (antichain
  or classical cases known; the general-P statements not found).
  Pointed-cone theorem and b_n: NOT FOUND (the pointed-cone theorem follows in
  a few lines from the Lawrence / Khovanskii–Pukhlikov valuation).

### Cone/lune Lie theory and the general theory

- [`notes/cone_lune_lie_theory.md`](notes/cone_lune_lie_theory.md): cone/lune
  Lie theory for the order cone; a lune form of Conjecture S, and
  independence of the chambers of pointed cones for every finite real
  central essential arrangement (PROVEN + audited). It states Conjecture G as
  CONJECTURED; parts (G1)–(G3) have since been proved (Theorem G\*, below),
  and (G4) is open.
- [`notes/audit_cone_lune_lie_theory.md`](notes/audit_cone_lune_lie_theory.md):
  its audit. The general-arrangement theorem HOLDS; fixes applied.
- [`notes/general_theory.md`](notes/general_theory.md): the framework in which
  poset JKS is one instance: top-cones of real hyperplane arrangements. Its
  §6 status table: Theorem 1 (cone wedge), Theorem 2 (cone Zaslavsky, an
  instance of Zaslavsky 1977), Prop. 3, Theorems 6–8 (Hopf side) PROVEN +
  audited; Theorem G\* PROVEN given Brown, + audited; (b1), (b2), comodernism
  CONJECTURED; an exact criterion for χ_V(g) ≢ 0 OPEN (taken up below).
- [`notes/audit_general_theory_cones.md`](notes/audit_general_theory_cones.md):
  audit of §§0–1. HOLDS with small fixes, and Conjecture G\* is a theorem: it
  proves Theorem C (the chamber cycles span), given Brown. COMPUTED on 6,910
  cones.
- [`notes/audit_theorem_c.md`](notes/audit_theorem_c.md): independent audit of
  that Theorem C (and Props. A, B). HOLDS WITH FIXES (to proofs and
  statements; no conclusion changes), applied in the general-theory note. As a
  by-product it proves Prop. Φ for every n given Brown, without Wachs or Ree
  (PROVEN; not separately audited).
- [`notes/audit_general_theory_hopf.md`](notes/audit_general_theory_hopf.md):
  audit of §2 (Q′, Theorems 6–8, "(b) = (a)"). HOLDS, some WITH FIXES
  (wording); applied.
- [`notes/novelty_general_theory.md`](notes/novelty_general_theory.md):
  prior art for the general theory. Theorem 1, G\* beyond V = all chambers,
  Theorems 6–8 NOT FOUND; Theorem 2 PARTLY KNOWN (a specialization of
  Zaslavsky 1977 Thm 1.2); G\* for V = all chambers KNOWN (Aguiar–Mahajan
  *Topics* Thm 14.32). Written while G\* was still called a conjecture.
- [`notes/oriented_matroid_cones.md`](notes/oriented_matroid_cones.md):
  Theorems 1, 2 and C/G\* for every T-convex set of topes of a simple
  oriented matroid, realizable or not. PROVEN + audited (C given Brown);
  COMPUTED on realizable and non-realizable oriented matroids of ranks 3 and
  4. Theorem 1-OM, Theorem 2-OM for proper V and Theorem C-OM were not found
  in the literature searched. The proof of det = c(g) for linearly induced g
  was added after the audit (PROVEN, unaudited).
- [`notes/audit_oriented_matroid_cones.md`](notes/audit_oriented_matroid_cones.md):
  its audit. Every audited claim HOLDS; realizability is never used; one
  attribution fixed (applied).

### The fixed-point formula and vanishing

- [`notes/fixed_point_formula.md`](notes/fixed_point_formula.md): the
  fixed-point character formula for cones (EZ, EZ′, CF) and Props. W, W′.
  PROVEN + audited; COMPUTED on all 7,200 pairs (V, g). KNOWN for V = all
  chambers; for proper cones not found in the literature searched.
- [`notes/audit_fixed_point_formula.md`](notes/audit_fixed_point_formula.md):
  its audit. The PROVEN claims hold; two wording fixes to hypotheses, applied.
  It proves Prop. W′.
- [`notes/audit_prop_w_prime.md`](notes/audit_prop_w_prime.md): audit of
  Prop. W′ (HOLDS) and of G\* for g outside the reflection group (HOLDS). It
  proves Theorem W″, the exact value of the Weisner sum.
- [`notes/audit_theorem_w2.md`](notes/audit_theorem_w2.md): independent audit
  of Theorem W″. HOLDS; no mathematical fix.
- [`notes/novelty_fixed_point_formula.md`](notes/novelty_fixed_point_formula.md):
  prior art for the fixed-point formula. EZ, EZ′, CF KNOWN FOR V = ALL
  CHAMBERS, NOT FOUND for proper cones; Props. W, W′ NOT FOUND.
- [`notes/vanishing_criterion.md`](notes/vanishing_criterion.md): when the cone
  Lie character χ_V(g) vanishes. Formula Z, Theorem S, Theorem A (the rule on
  all of ±S_n) PROVEN + audited twice; PC′ COMPUTED; the per-cone criterion
  PC″ OPEN (taken up below).
- [`notes/audit_vanishing_criterion.md`](notes/audit_vanishing_criterion.md):
  first audit. No proven formula is wrong; fixes to hypotheses (S3, PC(c)), applied.
- [`notes/audit2_vanishing_criterion.md`](notes/audit2_vanishing_criterion.md):
  second, independent audit. HOLDS.
- [`notes/prior_art_vanishing_criterion.md`](notes/prior_art_vanishing_criterion.md):
  prior art. Formula Z for the braid arrangement and all chambers SPECIAL
  CASE KNOWN (Hanlon 1981); Formula Z in general and for proper cones,
  Theorem S and the (A−) rule NOT FOUND.
- [`notes/per_cone_vanishing.md`](notes/per_cone_vanishing.md): per-cone
  vanishing of χ_V(g). Lemma M, Theorem Cr (Crapo relative to Fix g), Theorem
  TA (an exact type-A rule on every cone) PROVEN + audited. It states
  Conjecture CR_V, which `conjecture_cr_v.md` has since refuted. Theorem TA
  and Lemma M not found in the literature searched; Lemma Pal KNOWN in
  substance.
- [`notes/audit_per_cone_vanishing.md`](notes/audit_per_cone_vanishing.md):
  its audit. HOLDS WITH FIXES; applied.
- [`notes/prior_art_per_cone_vanishing.md`](notes/prior_art_per_cone_vanishing.md):
  prior art. Lemma Pal KNOWN; Theorem TA NOT FOUND; Theorem Cr KNOWN when U is
  a flat (Crapo), with its vanishing input NOT FOUND otherwise; CR_V NOT FOUND
  (and false for general finite lattices). Applied to the note.
- [`notes/conjecture_cr_v.md`](notes/conjecture_cr_v.md): Conjecture CR_V
  (the Crapo converse on cone lattices). **REFUTED** in rank 4: 12 hyperplanes
  of R^4, g = diag(−1, −1, 1, 1), a complemented non-modular 9-element fixed
  lattice with χ = 0; checked by hand and by two implementations. PROVEN,
  unaudited: pointed cones, Cor. V zeros, the dim L = 1 reduction, rank-3
  fixed lattices (Theorem 3, d ≤ 3). COMPUTED on 160,547 pairs. No prior-art
  check yet.

### The natural-isomorphism question

- [`notes/natural_isomorphism.md`](notes/natural_isomorphism.md): which
  notions of naturality hold; Theorem Ψ (twisted class sums are independent
  modulo shuffles) and the explicit isomorphism for every P; extension
  naturality exactly on connected posets; ordinal and disjoint sums. PROVEN +
  audited. Novelty: unclear (likely known in some form).
- [`notes/audit_natural_isomorphism.md`](notes/audit_natural_isomorphism.md):
  its audit. Theorem Ψ HOLDS; one check in the note's script was defective,
  and the count it gave is corrected.
- [`notes/wgt_check_fix.md`](notes/wgt_check_fix.md): the fix of that `[wgt]`
  check. No mathematics changed; the corrected counts are COMPUTED.

### Cyclic-compatible posets and b_n

- [`notes/cyclic_compatible_posets_bn.md`](notes/cyclic_compatible_posets_bn.md):
  proof of b_n = n[x^n] log A(x). PROVEN + audited.
- [`notes/audit_cyclic_compatible_posets_bn.md`](notes/audit_cyclic_compatible_posets_bn.md):
  its audit, and the unconditional proof of ⊕_P Lie(P) ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]).

### Linear extensions and cyclic sieving

- [`notes/linear_extensions.md`](notes/linear_extensions.md): what the poset
  Lie theory says about linear extensions. Cyclic sieving from the theory: NO,
  but Theorem U (promotion CSPs closed under disjoint union) PROVEN. Rotation
  classes and promotion: PARTIAL, with Lemma P, Theorem R, Propositions O, E, D
  PROVEN. Counting e(P): NO, Proposition F PROVEN. Structure of
  C[Lin P]/R_P: Theorem M PROVEN. All PROVEN + audited. Theorem R and
  Proposition O not found in the literature searched; Lemma P and Theorem U
  PARTLY KNOWN.
- [`notes/audit_linear_extensions.md`](notes/audit_linear_extensions.md): its
  audit. HOLDS WITH FIXES (F1–F7, applied).
- [`notes/prior_art_linear_extensions.md`](notes/prior_art_linear_extensions.md):
  prior art. PARTLY KNOWN: chains and rectangles KNOWN; Theorem R, Proposition
  O and Theorem U for general components NOT FOUND. Applied to the note.
- [`notes/cyclic_sieving_cyc.md`](notes/cyclic_sieving_cyc.md): cyclic sieving
  for Aut(P) acting on Cyc(P). The rotation CSP (Corollary T, via Theorem C) is
  PROVEN + audited and **KNOWN** as an instance of Westbury
  2016 Cor. 2.6 / Reiner–Stanton–White Thm 8.2; the §4 regular case PROVEN
  given RSW Thm 8.2. Necessity of (a) in Theorem C OPEN when gcd(k_i) > 1. One
  polynomial for all of Aut(P): NO (A_4 obstruction). (★), Theorem B(ii) at
  non-regular ζ, Theorem C beyond regular elements and the A_4 obstruction
  not found in the literature searched.
- [`notes/audit_cyclic_sieving_cyc.md`](notes/audit_cyclic_sieving_cyc.md):
  its audit. HOLDS WITH FIXES (F1–F6, applied).
- [`notes/prior_art_cyclic_sieving_cyc.md`](notes/prior_art_cyclic_sieving_cyc.md):
  prior art. Corollary T and §4 KNOWN as instances (Westbury, Sagan's survey,
  RSW); Theorem A standard; B(i) Springer; the rest NOT FOUND. Applied to the
  note.

### Moonshine

- [`notes/moonshine_scoping.md`](notes/moonshine_scoping.md): does the poset
  Lie theory carry a grading with modular traces? Four candidates, each NO
  SIGN or modular but generic. **STOP.**
- [`notes/audit_moonshine_scoping.md`](notes/audit_moonshine_scoping.md): its
  audit. **STOP HOLDS ON A NARROWER SPACE** (exact modularity); no error
  reverses a verdict; it proves Lemmas H, Q, D. Its fixes are not applied to
  the scoping note, which still describes itself as unaudited.
- [`notes/moonshine_residual.md`](notes/moonshine_residual.md): the four
  candidates the audit left open. Most excluded (PROVEN, unaudited); N^k on
  groups with several cusps OPEN; twisted traces COMPUTED, generic. STOP still
  holds.

## Computations

All code is plain Python 3 in [`compute/`](compute/). Every script, with its
reproduce command and its notes file, is listed in
[`compute/README.md`](compute/README.md).
Unit tests: `cd compute && python3 -m unittest discover -p 'test_*.py'`.
