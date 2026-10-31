# Lean formalization of the poset JKS theorem: plan and status

This directory holds a Lean 4 + Mathlib project. It states the main theorem of
`notes/poset_jks_theorem.tex` (Theorem `thm:main`) and a first, homology-free milestone M1.

* **Step 1** gave the scaffold, the ingredient map, the choice of route, and faithful
  statements (all proofs `sorry`).
* **Step 2 (M1, done)** proves Theorem S(a), S(b), Theorem Ψ and Corollary Ψ.1
  (`PLie(P) ≅ ℂ[Lin P]/R_P`, explicit and `Aut(P)`-equivariant, every finite poset with
  `n ≥ 1`). These are sorry-free and depend only on `propext`, `Classical.choice`, `Quot.sound`
  (§5). At that step the main theorem and its homological inputs were still `sorry` (§4).
* **Step 3 (M2, partial)** proves `trace_PLie` (Lemma `lem:liechar`). It also builds the
  homology-free Möbius-side infrastructure: the lattice facts about `OP(P)` and `OP(P)^g`,
  Weisner's theorem, the interval lemma and the recursion (W) (unsigned). `character_identity`
  and `closed_formula` stay `sorry`. They are **not** homology-free: their `g = 1` case is
  the base case `μ(OP(Q)) = (-1)^{|Q|-3} e_C(Q)`, which the note obtains from Jenča–Sarkoci and
  Hall (§2, §4.1).
* **Step 4 (M2b)** proves Proposition `prop:Lside`, the Lie side of (closed):
  `∑_{gC=C} ζ^{r_g(C)} = μ(o) ∑_{x ∈ F(P,g)} e_C(P|_{B₀(x)})` (`prop_Lside`, for `n ≥ 1`), by
  the weight-free route of §4.1. It builds two general inputs in their own files: the Ramanujan
  sum at `1` (`RamanujanSum.lean`) and the invariance of `e_C` under order isomorphisms
  (`ECTransport.lean`). `closed_formula` is now proved from `character_identity` and
  `prop_Lside`; it has no `sorry` of its own but still depends on `character_identity`.
* **Step 5 (M2c)** proves Lemma `lem:small` without homology: `μ(OP(P)) = (-1)^{n-1} e_C(P)`
  for every `n ≥ 1` (`mu_OP_eq`, Proof W of `notes/mu_op_elementary.md`: dual Weisner at
  `π_a` and Jenča–Sarkoci's `e_C` recursion, the latter proved here). It then proves Lemma
  `lem:interval`(ii) (`interval_sign`), the signed recursion (W), the Möbius inversion of
  Proposition `prop:Mside` (`prop_Mside`), and from `prop_Mside` and `prop_Lside` the character
  identity (`character_identity`). So `character_identity` and `closed_formula` are proved and
  depend only on `propext`, `Classical.choice`, `Quot.sound`. Neither uses
  `jencaSarkoci_homology` or `hall_mu_eq_reducedEuler` (`scripts/CheckDeps.lean`, §5).
* **Step 6 (M3b)** proves that two finite-dimensional representations of a finite group over a
  field of characteristic zero with equal characters are isomorphic, and derives `main_iso` from
  `trace_HP`, `trace_PLie` and `character_identity` (§4.2).
* **Step 7 (M3a)** proves P. Hall's theorem (`hall_mu_eq_reducedEuler`, cited input B), the
  Hopf trace formula for bounded complexes (cited input C), and `trace_HP` from the vanishing
  part of `jencaSarkoci_homology` (§4.3).
* **Step 8 (Route C, slice S1)** adds the general chain tools of `notes/lean_js_route.md` §6
  (`ChainTools.lean`: pushforward along order embeddings, vanishing criteria for `H̃_d` and
  their transport, chain insertion and its face lemmas), with a Mathlib API check (§4.4). The
  sorry count is unchanged.
* **Step 9 (Route C, slice S2)** proves Lemma K of `notes/lean_js_route.md` §3.1, with the
  signs as corrected by `notes/audit_lean_js_route.md` G1–G2 (`ConeRetract.lean`): a monotone
  retraction `p ≤ id` of a poset `R` onto `R_{≤ t}` makes the augmented chain complex of `Δ(R)`
  exact (`exact_of_retract`), through the exact homotopy identity (`bd_s_add_s_bd_eq`) and its
  filtered form (`bd_s_add_s_bd`) (§4.5). The general `p` is done, so the fallback split S2a/S2b
  was not needed. The sorry count is unchanged.

**Current status.** One `sorry` remains: the proof of `jencaSarkoci_homology` (cited input A,
the homological content of Jenča–Sarkoci). Everything else is proved. Of the stated theorems,
exactly `jencaSarkoci_homology`, `trace_HP` and `main_iso` depend on `sorryAx`, and
`scripts/CheckDeps.lean` shows that the only cited input `trace_HP` and `main_iso` use is
`jencaSarkoci_homology` (§4, §5). (characterconj) and (closed) are fully proved.

* Toolchain: `leanprover/lean4:v4.29.1`; Mathlib `v4.29.1`
  (rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6`, pinned in `lake-manifest.json`).
* `lake build` succeeds. It reports 1 `sorry` warning (`MainTheorem.lean:102`,
  `jencaSarkoci_homology`) and no errors.
* No `axiom` declarations (`grep -rnw axiom PosetJKS scripts` finds only a comment).

## Reproduce

```sh
cd lean
lake exe cache get                         # fetch prebuilt Mathlib
lake build                                 # builds PosetJKS (and PosetJKS/Test.lean); expect 1 "declaration uses sorry"
lake env lean scripts/PrintAxioms.lean     # the #print axioms table below (and of the Test.lean controls)
lake env lean scripts/CheckDeps.lean       # which theorems use (A), (B) or trace_HP; see §5
grep -rn "^  sorry" PosetJKS               # the sorry list below
```

## Files

| File | Contents |
|---|---|
| `PosetJKS/Basic.lean` | words `Fin n ≃ α`; the ambient space `ℂ[S_n]` (`Alg`); `rot` (right mult. by `γ^j`); `wEζ` (`w e_ζ`); `Lin(P)` (`IsLinExt`); unions of components; shuffles `u ⧢ v`; `Sh_n`, `W_P`, `R_P`, `PLie(P)`; `Cyc(P)`, `e_C(P)`, `r_g(C)`, the class sum `∑_{gC=C} ζ^{r_g(C)}`; the `Aut(P)` action (`relabel`) and its invariance of `PLie`, `W_P`, `R_P` (**all proved**) |
| `PosetJKS/OrderComplex.lean` | oriented chains of the order complex (`Chains`, `bd`), reduced homology `redHom`; order-preserving partitions (`IsOrderPreserving`, `OP`, `ProperOP`); `H_P` (`HP`); the `Aut(P)` action on the proper part and on `H_P` (`actProper`, `actHP`); the fixed lattice `OP(P)^g` and `μ(OP(P)^g)` (`muFixed`) (**all proved**) |
| `PosetJKS/Words.lean` | M1 core, on lists over a fixed type with an arbitrary relation `r`: shuffles `shq`, `ShL`, the contraction operator `E_{a,x}` and Lemma 1 (`map_E_ShL`); the contraction relation `rc` and Lemma 5 (`inBL_contract`); Theorem A (`eq_zero_of_inBL`) and Theorem Ψ (`eq_zero_of_eqL`) on lists; Lemma Ψ.0 (`eqL_classSum`); the measure `μ` (`muL`), the Lemma 6 step (`muL_lt_of_shuffle`) and Lemma 4 (`inBL_rotate_muL`, `rotate_eq_zero_of_inBL`) (**all proved**) |
| `PosetJKS/Bridge.lean` | words `Fin n ≃ α` ↔ lists (`toL`, the injective linear map `toLmap`, `toLmap_shuffle`, `map_Sh_le`); `rot`, `prefixSet`, `coset`, `IsLinExt` in list terms; `rot_rot`, `rot_card`, `wEζ_rot` (moved here from `Test.lean`) (**all proved**) |
| `PosetJKS/ChainTools.lean` | general chain tools (Route C, slice S1, `notes/lean_js_route.md` §6): pushforward along order embeddings (`chainMapEmb`, a chain map, injective, functorial; `chainMap` is the case of an automorphism); `H̃_d = 0` iff cycles are boundaries (`subsingleton_redHom_iff`), invariance under order isomorphisms (`subsingleton_redHom_congr`), vanishing for an empty poset; insertion of an element into a chain (`insertAt`, via `Fin.insertNth`) and its face lemmas (`face_insertAt_self`, `face_insertAt_succAbove`, `bd_single_insertAt`) (**all proved**) |
| `PosetJKS/ConeRetract.lean` | Lemma K (Route C, slice S2, `notes/lean_js_route.md` §3.1): the data `ConeRetraction` (`t`, `p`); low/high elements of a chain (`nlow`, `hcount`, `low_iff`), `τ c` (`tau`), the chain `c ∪ {τ c}` (`cone`), the homotopy `s`; the exact homotopy identity (`bd_s_add_s_bd_eq`, `bd_s_add_s_bd_of_hcount_eq_zero`), the filtration `F` and its filtered form (`bd_s_add_s_bd`); exactness (`exact_of_retract`) (**all proved**) |
| `PosetJKS/Milestone.lean` | first milestone: Theorem S(a), (b), Theorem Ψ, Corollary Ψ.1, and on words: Lemma 4 (`card_inB`, split into `inB_coset_inj` and `exists_inB_coset`), Lemma 6 (`wd_mem_SB_sup_R`), `pr_P(w e_ζ) = s_ζ(w)/n` (`pr_wEζ`) (**all proved**) |
| `PosetJKS/LieTrace.lean` | M2: the basis `{w_C e_ζ}` of `PLie(P)` (`basisPLie`, `finrank_PLie`), `r_g(C)` is realised by every word of a fixed class (`classRot_spec`), and Lemma `lem:liechar` (`trace_actPLie`) (**all proved**) |
| `PosetJKS/OPLattice.lean` | M2: Weisner's theorem (`weisner`); `OP(P)` closed under meets (`isOrderPreserving_inf`); the orbit partition `O_g` (`orbitSetoid`), order-preserving and `g`-fixed; the join `x ∨ O_g` (`joinOrbit`), order-preserving, `g`-fixed and the join in `OP(P)^g`; `x ∨ O_g = 1̂` iff `g` is transitive on blocks, and then blocks are unions of components; Weisner in `OP(P)^g` with `a = O_g` (`sum_mu_join_eq_top`) (**all proved**) |
| `PosetJKS/Interval.lean` | M2: `μ` is invariant under interval isomorphisms (`mu_eq_of_interval`); the block `B₀` through a point, its period `m` and `h = g^m|_{B₀}` (`Blk`, `per`, `hres`); Lemma `lem:interval`(i) (`mu_interval`); the recursion (W), unsigned (`recursionW`) (**all proved**) |
| `PosetJKS/RamanujanSum.lean` | general (imports only Mathlib): `∑_{ξ^n=1} ξ = [n = 1]`; the primitive `o`-th roots of unity sum to `μ(o)` (`sum_primitiveRoots_eq_moebius`), and `∑_{s<o, (s,o)=1} ω^s = μ(o)` for `ω` primitive (`sum_pow_coprime_eq_moebius`) (**all proved**) |
| `PosetJKS/ECTransport.lean` | `B_P` on lists transported along injective relation-preserving maps (`L.inBL_map`); `B_{P|_A}(x₀)` as a finite set of lists (`BL`), `|B_{P|_A}(x₀)| = e_C(P|_A)` (`card_BL`); `e_C` invariant under order isomorphisms (`eC_congr`), `e_C(P|_{φB}) = e_C(P|_B)` for `φ ∈ Aut(P)` (`eC_image`) (**all proved**) |
| `PosetJKS/LieSide.lean` | `x ∈ F(P,g)` (`InF`, moved here unchanged from `MainTheorem.lean`); block systems `{g^j B : j < o}` and `InF` (`inF_blocksOf`, `blocksOf_of_inF`, `isBlockSys_pow`, `card_eq_of_isBlockSys`); words as concatenations of chunks `h^t u` (`eq_flatMap_of_rotate`, `rotate_mul_chunks`); the `B_P(x₀)` words of `g`-stable classes (`fixedB_struct`, `exists_fixedB`, `card_fiber`); Proposition `prop:Lside` (`prop_Lside`) (**all proved**) |
| `PosetJKS/MuOP.lean` | Lemma `lem:small`, homology-free (Proof W): dual Weisner (`weisner_dual`); `π_a`, `π_ab` (`pa`, `pab`) and Lemma M; the quotient poset `P/π_ab` (`Contr`) and Lemma U (`mu_pab_top`); Lemma D (`mu_op_rec`); Lemma C, Jenča–Sarkoci's recursion `e_C(P) = ∑_b e_C(P/π_ab)` (`eC_rec`); Theorem A `μ(OP(P)) = (-1)^{n-1} e_C(P)` (`mu_OP_eq`) (**all proved**) |
| `PosetJKS/Mside.lean` | `M̃(P,g)` (`Mt`), `M̃(P,1) = e_C(P)` (`Mt_one`); `ℤ/m × B₀ ≅ P` (`blkEquiv`) and Lemma `lem:interval`(ii) (`interval_sign`); the signed recursion (W) (`recursionW_signed`); the Möbius inversion on `X(P,g)` inside `OP(P)^g` (`sum_mu_below_eq_zero`, `sum_moebius_between`, `mu_eq_moebius_mul_sum`); `F(P,g)` as setoids vs `InF` (`opOfBlocks`, `inF_blocksOf_blkSet`); Proposition `prop:Mside` (`prop_Mside`) (**all proved**) |
| `PosetJKS/MainTheorem.lean` | the main theorem (characterconj), (mainiso), (closed); the two character lemmas; the cited inputs in the form the proofs use them (`character_identity` proved from `prop_Mside` and `prop_Lside`, `closed_formula` from `character_identity` and `prop_Lside`, `main_iso` from `trace_HP`, `trace_PLie`, `character_identity` (§4.2), `trace_HP` from `trace_HP_of_vanishing` and `jencaSarkoci_homology`, `hall_mu_eq_reducedEuler` from `mu_bot_top_eq_chainSum` (§4.3); only `jencaSarkoci_homology` is `sorry`) |
| `PosetJKS/CharacterIso.lean`, `MainIso.lean`, `CharacterIsoTest.lean` | step 6, see §4.2 |
| `PosetJKS/Hall.lean`, `Hopf.lean`, `TraceHP.lean` | step 7, see §4.3 |
| `PosetJKS/Test.lean` | positive controls of the definitions on small posets against `compute/` (including `Mt`: `Mt_chain2`), `∂ ∘ ∂ = 0` (`bd_comp_bd`), two counterexamples at `n = 0`, and `H̃_0 ≠ 0` for a two-point antichain (`redHom_antichain2_ne`); the Lemma K controls (`isEmpty_coneRetraction_antichain2`, `vRetraction`, `redHom_V_subsingleton`); see `AUDIT_FAITHFULNESS.md` |
| `scripts/PrintAxioms.lean` | `#print axioms` for every stated theorem and the main controls |
| `scripts/CheckDeps.lean` | for given theorems, whether `jencaSarkoci_homology`, `hall_mu_eq_reducedEuler` or `trace_HP` occurs in the transitive closure of the constants they use, with two positive controls that do use them |

## 1. Ingredient map: what Mathlib has, what must be built

These are the declarations I actually found in the pinned Mathlib by grepping
`.lake/packages/mathlib/Mathlib`. "Absent" means a targeted grep found nothing. It does not
prove that nothing exists under another name. Sizes are rough line counts for the remaining
work.

| Ingredient | In Mathlib (found) | Built here (step 1) | Still to build | Size |
|---|---|---|---|---|
| **`OP(P)`** *(step 3: (i)–(iv) of `lem:lattice`, `lem:orbitquot`, `lem:interval`(i) done; see `OPLattice.lean`, `Interval.lean`)* | `Setoid` with `Setoid.completeLattice` (refinement order; `Setoid.bot_def`: `⊥` is `=`, `Setoid.top_def`), `Setoid.comap`, `Setoid.ker`, `Finpartition`, `Relation.ReflTransGen` | `IsOrderPreserving` (acyclic quotient), `OP`, `ProperOP`, `OPFixed`, `actSetoid`, `actProper : ProperOP ≃o ProperOP`; `isOrderPreserving_bot/top`; `OPFixed.bot_ne_top` | `OP(P)` is a lattice with meet the partition meet; `OP(P)^g` is a lattice containing `O_g`; joins with `O_g`; `{x : x ∨ O_g = 1̂} = X(P,g)` (note, Lemmas `lem:orbitquot`, `lem:lattice`) | 400–700 |
| **Order complex, reduced homology** | `PreAbstractSimplicialComplex` / `AbstractSimplicialComplex` (faces only, no homology); `SSet`, `CategoryTheory.nerve`, `mem_nerve_nonDegenerate_iff_strictMono`; `AlternatingFaceMapComplex.obj`, `alternatingFaceMapComplex`, `SimplicialObject.Augmented`, `normalizedMooreComplex`; `AlgebraicTopology.singularHomologyFunctor`; `HomologicalComplex.eulerChar`, `homologyEulerChar` (definitions only). **Absent:** simplicial homology of a simplicial complex, the order complex of a poset, geometric realisation of a poset, wedges of spheres, homotopy types of complexes | hand-rolled augmented oriented chain complex on chains `Fin m ↪o L`: `Chains`, `face`, `bd`, `cycles`, `boundaries`, `redHom`; functoriality `chainMap`, `bd_chainMap`, `homMap` | `∂∘∂ = 0` (not needed for the statements; needed for every proof) ~60; optional bridge to `alternatingFaceMapComplex (nerve L)` (normalised) ~300+ | 60–400 |
| **Möbius function, P. Hall** *(Weisner: done in step 3; Hall: done in step 7, §4.3)* | `IncidenceAlgebra.mu`, `mu_apply`, `mu_eq_neg_sum_Ico_of_ne`, `mu_eq_neg_sum_Ioc_of_ne`, `mu_mul_zeta`, `mu_toDual`, `mu_prod_mu`, `IncidenceAlgebra.eulerChar`; `ArithmeticFunction.moebius` (number-theoretic `μ(o)`). **Absent:** P. Hall's chain-count theorem, Weisner's theorem, Crapo's complementation theorem | `muFixed g = mu ℤ 0̂ 1̂` on `OP(P)^g`; statement `hall_mu_eq_reducedEuler` | Hall (`μ = ∑ (-1)^k c_k` via `(ζ-1)` expansion in the incidence algebra) ~200–400; Weisner ~150–300 | 350–700 |
| **Hopf trace formula** *(done in step 7, §4.3)* | `LinearMap.trace`, `LinearMap.trace_restrict_eq_of_forall_mem` (PID file), `HomologicalComplex.eulerChar` (definition). **Absent:** Euler–Poincaré `χ(C) = χ(H)`, the Hopf trace formula, additivity of trace over `0 → U → V → V/U → 0` | — | Pure linear algebra on a bounded complex of finite-dimensional spaces with a chain endomorphism; specialise to `Chains`/`redHom`. Uses `LinearMap.trace_eq_matrix_trace` with an adapted basis | 300–500 |
| **Jenča–Sarkoci** (`Δ(\widehat{OP(P)}) ≃ ⋁^{e_C} S^{n-3}`) | Nothing usable: no homotopy types of finite complexes, no shellability or discrete Morse theory, no Quillen fibre lemma | statement of its homological content only: `jencaSarkoci_homology` (`H̃_d = 0` for `d ≠ n-3`, `dim H_P = e_C(P)`) | The homotopy statement cannot be expressed in current Mathlib. The homological content needs a combinatorial acyclicity proof, e.g. a shelling or acyclic matching of `Δ(\widehat{OP(P)})`, or a formal transcription of the Jenča–Sarkoci argument. **This is the main obstacle of the topological route.** | 2000–5000+, research-level |
| **`Lie(P) = span{w e_ζ}`** | `Finsupp`, `Finsupp.lmapDomain`, `Finsupp.linearCombination`, `MonoidAlgebra`, `FreeLieAlgebra`, `finRotate`, `Equiv.Perm.sign`, `IsPrimitiveRoot`, `IsPrimitiveRoot.pow_eq_one_iff_dvd`, `IsPrimitiveRoot.geom_sum_eq_zero`. **Absent:** shuffle algebra / shuffle product on `ℂ[S_n]`, Ree's theorem `Lie_n^⊥ = Sh_n`, Wachs's comb basis | `Word`, `Alg` (`ℂ[S_n]` as `Word α →₀ ℂ`), `rot`, `wEζ`, `PLie`, `shuffle`, `Sh`, `W`, `R`, `cyc`, `eC`, `classRot`, `fixedClassSum`, `prefixSet`, `restrict`, `IsCut` | basis `{w_C e_ζ}` of `PLie(P)` (Lemma `lem:liechar`) ~200; contraction operator `E_{a,x}` and `E_{a,x}(Sh) ⊆ Sh` (note's "key tool") ~300; Prop. Φ (Wachs + Ree), only for Theorem S(c),(d) ~1500+ | 500 (milestone) / +1500 (Φ) |
| **`Aut(P)` actions, characters** *(equal characters ⇒ isomorphic: done in step 6, §4.2)* | `α ≃o α` is a group (`RelIso` group instance, `Mathlib/Algebra/Order/Group/End.lean`), `orderOf`; `Representation`, `Representation.character`, `Representation.char_iso`, `FDRep.character`, `FDRep.char_iso`, `FDRep.char_orthonormal`, `FDRep.simple_iff_char_is_norm_one`, Maschke `MonoidAlgebra.Submodule.exists_isCompl`. **Absent:** "equal characters imply isomorphic" for finite groups over `ℂ` (only iso ⇒ equal characters, `char_iso`) | `relabel`, `relabel_mem_PLie`, `relabel_mem_W`, `relabel_mem_R` (all proved); `actPLie`, `actMP`, `actHP`, `actProper` | equal characters ⇒ isomorphic (Maschke + orthonormality; multiplicities read off by inner products) ~300–500 | 300–500 |

## 2. Route comparison and recommendation

**Topological route (Proofs I and II).** The proof is tr(`g`|`H_P`) = `(-1)^{n-3} μ(OP(P)^g)`
(Hopf + Hall + Jenča–Sarkoci), then the Möbius computation via Weisner (Proof I) or Crapo
(Proof II), the Lie-side character computation, and "equal characters ⇒ isomorphic". Hall, Hopf,
Weisner and character theory are all finite combinatorics or linear algebra. Each is a moderate
self-contained project, listed above. But the route cannot close without Jenča–Sarkoci, even in
its homological form, and nothing in Mathlib comes close to supporting it. It is a large,
research-level formalization, and it is on the critical path of *both* proofs of (mainiso) and
of Theorem S(c),(d).

**Combinatorial targets.**

* *The character identity (characterconj)* is **not** homology-free on the note's route.
  (Correction made in step 3; step 1 claimed it needed no homology.) It is an identity between
  a Möbius value of the finite lattice `OP(P)^g` and a sum of roots of unity. Most of its proof
  is finite lattice and Möbius combinatorics: the lattice structure of `OP(P)` and `OP(P)^g`
  (Lemmas `lem:orbitquot`, `lem:lattice`), Weisner, the interval lemma, the recursion (W), the
  Möbius inversion on `X(P,g)`, and the Lie-side Proposition `prop:Lside` with Ramanujan sums.
  But the Möbius inversion in `prop:Mside` evaluates the terms with `h_x = 1` by the base case
  Lemma `lem:small`, `μ(OP(Q)) = (-1)^{|Q|-3} e_C(Q)`. For `|Q| ≥ 3` the note proves this from
  (A) Jenča–Sarkoci and (B) Hall. At `g = 1`, (characterconj) *is* this base case. So closing
  `character_identity` (and the first conjunct of `closed_formula`) needs either Hall (M3) plus
  the Euler-characteristic content of `jencaSarkoci_homology`, or a new elementary proof of
  `μ(OP(P)) = (-1)^{n-1} e_C(P)`. The latter is not in the note and is not attempted here.
  *(Step 5: the elementary proof now exists, `notes/mu_op_elementary.md`, Proof W, audited in
  `notes/audit_mu_op_elementary.md`. It is formalized (`mu_OP_eq`), and with it
  `character_identity` is proved homology-free; see §4.1.)*
* *Theorem S(a),(b), Theorem Ψ, Corollary Ψ.1* (`PLie(P) ≅ ℂ[Lin P]/R_P`, explicit and
  `Aut(P)`-equivariant, for every finite poset): **pure word combinatorics.** The proofs are
  inductions on `n` through the contraction `P/{a,x}` and the operator `E_{a,x}`, plus
  connectivity of `Lin(P)` under adjacent incomparable swaps and the cut/rotation description of
  cyclic classes ([S, Lemmas 1–6], [Nat, §3.1]). They use none of Jenča–Sarkoci, Hall, Hopf,
  Wachs or Ree. The audits ([AudS], [AudNat]) found no gaps, and the statements are
  computer-checked for `n ≤ 6`.

**Recommendation: first milestone M1 = Corollary Ψ.1, through Theorem S(a),(b) and Theorem Ψ**
(`Milestone.lean`). Reasons:

1. It needs no homology and no topology. Every ingredient is `Finsupp`, `List`, `Equiv.Perm` and
   finite sums, and all the definitions it needs are already in place and compile, including the
   `Aut(P)` actions with their invariance proofs.
2. Its proof is short, elementary and fully written out in the notes, with independent audits.
   The induction (contract an adjacent pair, apply `E_{a,x}`, read off coefficients) transcribes
   directly. Generalising the ground set to an arbitrary finite type `α`, as done here, makes the
   contraction `P/{a,x}` a new finite poset type without relabelling.
3. It is a real piece of the main theorem. It is one of its two explicit models: an explicit
   `Aut(P)`-isomorphism `PLie(P) ≅ ℂ[Lin P]/R_P`. With Theorem S(d), which needs Φ and
   Jenča–Sarkoci, it gives (mainiso) with an explicit map.
4. Its statements can be sanity-checked against the existing Python computations
   (`compute/natural_isomorphism.py`, `compute/conjecture_s.py`).

Then **M2 = the character identity (characterconj)**, after the `OP(P)` lattice and Weisner
infrastructure. Step 3 found that M2 is homology-free only up to the base case `lem:small`
(see above), so M2 cannot close before `jencaSarkoci_homology` is available. Then **M3 = Hall and Hopf** (finite combinatorics and linear
algebra), which reduce (mainiso) to `jencaSarkoci_homology`, `trace_PLie` and "equal characters
⇒ isomorphic". `jencaSarkoci_homology` stays the last open input. Alternatively, Theorem S(c)
plus Prop. Φ gives the lower bound `dim H_P ≥ e_C(P)` without it. The matching upper bound and
the vanishing outside degree `n-3` still need it.

## 3. Statements: informal vs Lean (for a faithfulness audit)

Common setup. The poset `P` is a finite type `α` with `[PartialOrder α]`, `[Fintype α]` and
`[DecidableEq α]`, and `n = Fintype.card α`. `Aut(P)` is `α ≃o α`. `sgn(g)` is
`Equiv.Perm.sign g.toEquiv` (`sgnC g`, cast to `ℂ`). `ζ` is any complex number with
`IsPrimitiveRoot ζ n`.

| Informal (note) | Lean | Remarks |
|---|---|---|
| poset on `[n]`; words `w = w_1⋯w_n ∈ S_n` | ground set any finite type `α`; `Word α := Fin n ≃ α`; `ℂ[S_n]` is `Alg α := Word α →₀ ℂ` | Equivalent after choosing a labelling `α ≃ [n]`. Left action (relabel letters) and right action (permute positions) are as in the note. `sgn(w)` of a word is labelling-dependent and is not used in the stated theorems |
| `(wγ^j)_i = w_{i+j}` | `rot w j := (finRotate n ^ j).trans w`, so `rot w j i = w (i + j)` | |
| `w e_ζ = (1/n)∑_j ζ^{-j} wγ^j` | `wEζ ζ w := ∑_{j<n} (n⁻¹ (ζ^j)⁻¹) • wd (rot w j)` | |
| `Lin(P)` | `IsLinExt α w := ∀ i j, w i < w j → i < j` | |
| union of components | `IsUnionOfComponents S := ∀ x y, x ≤ y → (x ∈ S ↔ y ∈ S)` | closed under comparability, i.e. a union of components of the comparability graph |
| `π` order-preserving (`P/π` acyclic) | `IsOrderPreserving s`: mutual reachability along steps `a ≤ b` or `a ~ b` forces `x ~ y` | equivalent to acyclicity (see the module docstring of `OrderComplex.lean`) |
| `OP(P)`, `0̂`, `1̂`, refinement order | subtype of `Setoid α`; `⊥` = discrete, `⊤` = one block, `≤` = refinement (Mathlib's order on `Setoid`) | |
| `H_P = H̃_{n-3}(Δ(\widehat{OP(P)});ℂ)` | `HP α := redHom (ProperOP α) (n - 3)` = `ker ∂ / im ∂` on the augmented oriented chain complex of chains `Fin m ↪o ProperOP α` | `n - 3` is natural subtraction; every statement about `H_P` assumes `3 ≤ n`, as the note does |
| `g` acts on `H_P` | `actHP g := homMap (actProper g) _` (pushforward of chains) | well-definedness proved |
| `μ(OP(P)^g) = μ(0̂,1̂)` | `muFixed g := IncidenceAlgebra.mu ℤ (OPFixed.bot g) (OPFixed.top g)` | Mathlib's recursively defined Möbius function |
| `Cyc(P)`, `e_C(P)` | `cyc α` = image of `coset` on `Lin(P)`; `eC α := (cyc α).card` | |
| `r_g(C)` for `gC = C` | `classRot g C` = least `r < n` with `g ∘ w = rot w r` for some `w ∈ C` | the note proves `r` is independent of `w`; rotations `r < n` of a word are distinct, so `r` is unique |
| `∑_{gC=C} ζ^{r_g(C)}` | `fixedClassSum ζ g` (sum over `C ∈ cyc α` with `C.image (· ∘ g) = C`) | |
| `PLie(P)` | `PLie α ζ := span {wEζ ζ w : IsLinExt α w}` | |
| **(characterconj)** `(-1)^{n-3} μ(OP(P)^g) = sgn(g) ∑_{gC=C} ζ^{r_g(C)}`, `n ≥ 3` | `character_identity (hn : 3 ≤ n) (hζ) g` | hypotheses: `n ≥ 3` and `ζ` primitive, both from the note |
| **(mainiso)** `H_P ≅ sgn ⊗ PLie(P)` as `Aut(P)`-modules | `main_iso hn hζ : ∃ e : HP α ≃ₗ[ℂ] PLie α ζ, ∀ g x, (e (actHP g x) : Alg α) = sgnC g • relabel g (e x)` | equivariance is stated in the ambient `ℂ[S_n]`, so no action on the submodule `PLie` is needed in the statement |
| **(closed)** `sgn(g)(-1)^{n-3}μ = ∑ ζ^{r} = μ(o) ∑_{x∈F(P,g)} e_C(P|_{B_0(x)})` | `closed_formula hn hζ g B₀ hB₀` | `x ∈ F(P,g)` is `InF g x`: `x` is a set of blocks forming a partition into `orderOf g` blocks, each a nonempty union of components, `g` maps blocks to blocks, transitively. `B₀` is an arbitrary choice of one block per `x` (`hB₀`). The note says "any one block"; the Lean form quantifies over all choices. `e_C(P|_B)` is `eC ↥B` with the induced order |
| `tr(g|H_P) = (-1)^{n-3}μ(OP(P)^g)` (Lemma `lem:homchar`) | `trace_HP hn g` | the note proves it *from* (A)–(C). Here it is proved from the vanishing part of (A), with (B) and (C) proved (§4.3) |
| `tr(g|PLie) = ∑ ζ^{r_g(C)}` (Lemma `lem:liechar`) | `trace_PLie h0 hζ g` | `h0 : 0 < n`, the note's implicit `n ≥ 1` (§4) |
| (A) Jenča–Sarkoci | `jencaSarkoci_homology hn`: `H̃_d = 0` for `d ≠ n-3`, `dim H_P = e_C(P)` | homological content only (all that the proofs use); the homotopy-type statement is not expressible in Mathlib today |
| (B) P. Hall | `hall_mu_eq_reducedEuler L (h : ⊥ ≠ ⊤)` | the hypothesis `0̂ ≠ 1̂` belongs to the *cited result*, not to the main theorem. It is needed: for a one-point `L`, `μ = 1` while `χ̃(∅) = -1` |
| (C) Hopf trace formula | `IsChainMap.hopf_trace` (`Hopf.lean`), for a bounded complex of finite-dimensional spaces | proved in step 7 (§4.3) |
| `B_P` (first block contains the base component `P_1`) | `InB x₀ w`: `w ∈ Lin(P)` and `x₀` lies in every nonempty union-prefix of `w` | base component = component of the base point `x₀`. Union-prefixes are nested and are unions of components, so "first block ⊇ `P_1`" ⇔ "`x₀` ∈ every nonempty union-prefix" |
| **Theorem S(a)** | `thmS_a x₀`: `B_P` independent mod `Sh_n`, `|B_P| = e_C(P)`, and `P` connected ⇒ `W_P ∩ Sh_n = 0` | connected: `IsConnectedPoset α` = nonempty and only `∅`, `univ` are unions of components |
| **Theorem S(b)** | `thmS_b x₀`: `span B_P ⊔ R_P = W_P`, `span B_P ⊓ R_P = 0`, `W_P ⊓ Sh_n = R_P`, `dim R_P = |Lin P| − e_C(P)` | |
| `Sh_n`, `R_P`, `u ⧢ v` | `Sh α`, `R α`, `shuffle S u v` = sum of the words whose subwords on `S` and `Sᶜ` are `u` and `v` | for words `u`, `v` on complementary letter sets these are exactly the interleavings |
| admissible `λ : [n] → ℂ^×` | `IsAdmissible lam` (`lam : α → ℂ`, `∏ lam = 1`, `∏_U lam ≠ 1` for nonempty proper unions `U`) | `∏ lam = 1` forces values in `ℂ^×` |
| **Theorem Ψ** | `thmPsi lam hlam rep hrep`: class sums `s_λ(rep C)` independent mod `Sh_n` for every choice of representatives `rep C ∈ C ∩ Lin(P)` | |
| **Corollary Ψ.1**: `ψ_P : L_P → M_P` is an `Aut(P)`-isomorphism, every finite `P` | `corPsi_bijective h0 hζ`, `corPsi_equivariant ζ g`, and packaged `corPsi h0 hζ` (`∃ e : PLie ≃ₗ MP`, `e = ψ_P`, equivariant) | `MP α := W_P ⧸ R_P` and `ψ_P(y) = pr_P(y) mod R_P`. The note writes the target as `(W_P + Sh_n)/Sh_n`; the two agree under the identification given by `W_P ∩ Sh_n = R_P` (Theorem S(b)) |

**Hypotheses audit.** Every hypothesis of a stated theorem is present in the note's statement:
`3 ≤ n` (main theorem, `trace_HP`, `jencaSarkoci_homology`), `IsPrimitiveRoot ζ n`,
admissibility of `λ`, the choice data `x₀`, `rep`, `B₀` with their defining properties, and
`⊥ ≠ ⊤` in the cited Hall theorem. The one hypothesis not written in the note is
`h0 : 0 < Fintype.card α` on `trace_PLie`, `corPsi_bijective` and `corPsi`. It is the note's
implicit `n ≥ 1` (its objects use `1/n`), and the statements are false without it (§4).

## 4. Sorries (1) and gaps

`sorry` occurrences, all in theorem proofs (`grep -rn "^  sorry" PosetJKS`; a scan of all of
`PosetJKS` that skips comments and docstrings finds the same single occurrence). No definition
depends on a `sorry`: `#print axioms` on `actHP`, `actMP` and `muFixed` shows no `sorryAx`.

| # | Location | Theorem | What it blocks |
|---|---|---|---|
| 6 | `MainTheorem.lean:105` | `jencaSarkoci_homology` (cited input A) | `trace_HP` (its vanishing part, via `trace_HP_of_vanishing`) and hence `main_iso`. Nothing else: (characterconj) and (closed) do not use it (§5) |

Numbering as in step 1. #2 `main_iso` is closed in step 6 (§4.2), from `trace_HP`. #4
`trace_HP` and #7 `hall_mu_eq_reducedEuler` are closed in step 7 (§4.3); `trace_HP` uses the
first conjunct of `jencaSarkoci_homology` (vanishing outside degree `n - 3`), and the second
conjunct (`dim H_P = e_C(P)`) is used by no proof in `PosetJKS` (the only use of
`jencaSarkoci_homology` there is `(jencaSarkoci_homology hn).1` in `trace_HP`). #5
`trace_PLie` is closed in step 3 (§4.1). #3 `closed_formula` has no `sorry` of its own since step 4: its second conjunct is `prop_Lside` (closed), and its first
conjunct is `character_identity` multiplied by `sgn(g)` (`sgn(g)² = 1`). #1
`character_identity` is closed in step 5, from `prop_Mside` and `prop_Lside` (§4.1). So both are
sorry-free; neither uses the cited inputs (A), (B) (§5).

The five M1 sorries of step 1 (`thmS_a`, `thmS_b`, `thmPsi`, `corPsi_bijective`,
`corPsi_equivariant`) are closed. `corPsi` follows from the last two.

**Statement changes.** None in steps 6 and 7 (§4.2, §4.3). None in step 5: the types of
`character_identity` and `closed_formula` are unchanged, and no hypothesis was added. None in step 4. `InF` moved from `MainTheorem.lean` to `LieSide.lean`
with the same body, so the type of `closed_formula` is unchanged.

**Statement changes in step 2.** Following `AUDIT_FAITHFULNESS.md` §1.1, three statements
gained the hypothesis `h0 : 0 < Fintype.card α`. Nothing else in any statement changed.

| Theorem | Before | After |
|---|---|---|
| `trace_PLie` (`MainTheorem.lean:81`) | `theorem trace_PLie {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :` | `theorem trace_PLie (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) (g : α ≃o α) :` |
| `corPsi_bijective` (`Milestone.lean`) | `theorem corPsi_bijective {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :` | `theorem corPsi_bijective (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :` |
| `corPsi` (`Milestone.lean`) | `theorem corPsi {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :` | `theorem corPsi (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α)) :` |

The `n = 0` counterexamples `Test.corPsi_bijective_false` and `Test.trace_PLie_false` are
kept; they show the statements without `h0` are false.

**How M1 is proved** (`Words.lean`, `Bridge.lean`, `Milestone.lean`). The proofs follow
`notes/conjecture_s_splitting_cycles_span.md` §2–§5 and `notes/natural_isomorphism.md` §3.1,
with one change of route.

* The induction is carried out on lists over the fixed type `α`, for a letter set
  `A : Finset α` and an *arbitrary* relation `r` (linear extensions: words that never put `q`
  before `p` when `r p q`). The contraction `P/{a,x}` is the relation `rc r a x` on
  `A ∖ {x}`. The note takes its transitive closure, which has the same linear extensions and
  the same unions of components, so the ambient type never changes.
* Because `r` is arbitrary, the induction step applies `E_{a,x}` to *every* pair of distinct
  letters, not only to pairs adjacent in some linear extension. The induction hypothesis then
  gives `X(…pq…) = X(…qp…)` for all adjacent transpositions, so `X` is constant on all
  arrangements of `A`. The final step is the note's: some arrangement is outside `B_P` (resp.
  the cyclic relation (Ψ.1) at a singleton `{y}` gives `c = λ(y)⁻¹ c`). This replaces the
  note's use of connectivity of `Lin(P)` under swaps (Lemma 3) and of a cover relation
  realised adjacently. Lemma 3 is not needed.
* Theorem Ψ is proved on lists for every `X` supported on linear extensions satisfying the
  cyclic relation (Ψ.1), `X(ts)·λ(s) = X(st)` for every union-prefix `s`. Lemma Ψ.0
  (`eqL_classSum`) shows each class sum `s_λ(w)` satisfies it. This avoids indexing the
  induction by cyclic classes and needs no case `n ≥ 3`.
* Corollary Ψ.1: injectivity from Theorem Ψ with `λ ≡ ζ` via `pr_P(w e_ζ) = s_ζ(w)/n`;
  surjectivity from `dim PLie(P) = e_C(P) = dim ℂ[Lin P]/R_P` (Theorem S(b)).

### 4.1 How M2 (partial) is proved, deviations, and what remains

`trace_PLie` follows the note's proof of `lem:liechar`. The vectors `w_C e_ζ`, one chosen
linear extension `w_C` per class, are independent because `w_D e_ζ` has coefficient
`n⁻¹ [C = D]` at `w_C`. They span because `(w γ^j) e_ζ = ζ^j w e_ζ`. In this basis `g` acts
monomially, `g · w_C e_ζ = ζ^j w_{gC} e_ζ`, and for `gC = C` the rotation `j` equals `r_g(C)`,
since rotations `< n` of a word are distinct. The statement is unchanged.

Möbius side (homology-free parts). Deviations from the note's route:

* **No lattice instance on `OP(P)^g`.** Weisner (`weisner`) is stated for a finite poset with
  `0̂`, `1̂` in which every `x` has a least upper bound `j x` with the fixed element `a`. That is
  exactly what the note uses (only joins with `a = O_g`), and Lemma `lem:lattice`(iii) supplies
  it (`OPFixed.join_le_iff`). The proof is the note's.
* **`O_g` and `x ∨ O_g` are explicit setoids.** `a ~ b` iff `g^k a = b`, resp. `g^k a ~_x b`,
  for some `k ∈ ℕ`. Acyclicity is proved on the element-level reachability relation of
  `IsOrderPreserving`. A closed walk `a ⇝ g^h a` is reversed by iterating `o - 1` more times
  (`rel_back`). This is the note's argument for `lem:orbitquot` and `lem:lattice`(iv).
* **`X(P,g)` is `{x ∈ OP(P)^g : x ∨ O_g = 1̂}`**, used directly. `joinOrbit_eq_top_iff` and
  `rel_of_le_of_joinOrbit_eq_top` are the content of `lem:lattice`(iv): transitive on blocks,
  and blocks are unions of components. Conversely, `isOrderPreserving_of_rel_of_le` shows
  every partition into unions of components is order-preserving. Matching this with the
  `Finset`-of-blocks form `InF` used in the statement of `closed_formula` is not yet done.
* **Interval lemma.** `B₀` is the block through a base point `p` (any block is of this form),
  `m` is the least `m > 0` with `g^m p ∈ B₀`, and `per_dvd` proves that the stabiliser of `B₀`
  is generated by `g^m`. The isomorphism `[0̂, x] ≅ OP(P|_{B₀})^h` is restriction to `B₀`
  (`resP`), with explicit inverse `liftP`. Möbius values transfer by `mu_eq_of_interval`
  (well-founded induction on Mathlib's recursive `μ`).
* **(W) is proved unsigned**: `∑_{x ∈ X(P,g)} μ(OP(P|_{B₀(x)})^{h_x}) = 0` for `g ≠ 1`
  (`recursionW`). The sign identity `lem:interval`(ii), `(-1)^{n-3} sgn(g) = (-1)^{k-3} sgn(h)`,
  was not formalized in step 3; step 5 adds it and the signed (W) (`interval_sign`,
  `recursionW_signed`).

What was remaining for `character_identity` after step 3, all done:

1. ~~`lem:interval`(ii)~~ **done in step 5** (`interval_sign`).
2. ~~The Möbius inversion of `prop:Mside`~~ **done in step 5** (`prop_Mside`), by a different
   route (below).
3. ~~The base case `lem:small`~~ **done in step 5** (`mu_OP_eq`, `Mt_one`), without Hall or
   Jenča–Sarkoci's homotopy type.
4. ~~`prop:Lside`~~ **done in step 4** (`prop_Lside`, see below).

**How `lem:small` is proved (step 5)** (`MuOP.lean`). Proof W of `notes/mu_op_elementary.md`
(audited, homology-free). Induction on `n` over all finite posets in one universe
(`mu_OP_eq_aux`); `n = 1` by hand. For `n ≥ 2` pick a minimal `a`.

* *Lemma D* (`mu_op_rec`). `OP(P)` is `OP(P)^1`. `π_a ∈ OP(P)` and `π_a ≠ 1̂`, so dual Weisner
  (`weisner_dual`, proved directly like `weisner`) gives `∑_{x ∧ π_a = 0̂} μ(x, 1̂) = 0`. The
  meet is the partition meet (`isOrderPreserving_inf`), and `x ∧ π_a = 0̂` iff `x = 0̂` or
  `x = π_ab`, `b ≠ a` (`inf_pa_eq_bot_iff'`).
* *Lemma U* (`mu_pab_top`). `P/π_ab` is the type `Contr a b h` of points `≠ b`, ordered by
  reachability in the quotient digraph (antisymmetric because `π_ab ∈ OP(P)`). Pulling back
  along `P → P/π_ab` (`b ↦ a`) maps `OP(P/π_ab)` isomorphically onto `[π_ab, 1̂]`, and
  `mu_eq_of_interval` transports `μ`.
* *Lemma C* (`eC_rec`), Jenča–Sarkoci's recursion, proved here. Instead of necklaces it uses
  `B_P(a)` (one word per cyclic class, `card_inB`) on lists. For `n ≥ 2`, `a` is never last in
  a word of `B_P(a)` (`exists_split`); let `b` be the next letter (`nxt`). Then `π_ab ∈ OP(P)`
  (`isOrderPreserving_pab_of_lin`, via `reach_pab_cases`: for `a` minimal, `v` is reachable from
  `u` in `P/π_ab` iff `u ≤ v` or `u` is below and `v` above the block `{a, b}`), and deleting `b`
  gives a word of `B_{P/π_ab}(a)` (`inBL_erase`). Inserting `b` after `a` is the inverse
  (`inBL_insert`, `lemmaC_equiv`). `B_{P/π_ab}(a)` is transported from lists over `Contr` to
  lists over `P` by `inBL_map` (`card_TL`).
* *Theorem A.* `μ = -∑_b (-1)^{n-2} e_C(P/π_ab) = (-1)^{n-1} e_C(P)`.

**How `prop:Mside` is proved (step 5)** (`Mside.lean`). Deviation from the note: the Möbius
inversion is done inside `OP(P)^g`, without passing to the posets `P|_{B₀(x)}` or to the
poset `X(P,g)`.

* `M̃(P,g) = (-1)^{n+1} sgn(g) μ(OP(P)^g)` (`Mt`). The note writes `(-1)^{n-3}`; the two agree
  for `n ≥ 3`, and `n + 1` avoids natural subtraction for blocks of size `k ≤ 2`
  (`Test.lean` has the mismatch control at `n = 2`).
* `lem:interval`(ii) (`interval_sign`): `(j, v) ↦ g^j v` is a bijection
  `ℤ/m × B₀ ≅ P` (`blkEquiv`), so `n = mk`, and under it `g = H ∘ D` with `D` the rotation of the
  `ℤ/m` factor (`k` cycles of length `m`) and `H = h` on the layer `0`. So
  `sgn(g) = sgn(h)(-1)^{(m-1)k}` (`sign_eq_sign_hres`). This replaces the note's cycle count.
* For `x ∈ X(P,g)` with `m` blocks: `x` relates `u` to `g^j u` iff `m ∣ j`
  (`rel_pow_self_iff`), `m ∣ o`. `F(P,g)` is `Fset`: the `x ∈ X(P,g)` with `m = o`.
  For `m < o`, Weisner in the interval `[0̂, x]` of `OP(P)^g` with `a = O_{g^m} ≠ 0̂`, whose
  joins are `z ∨ O_{g^m}` (`joinPow`), gives `∑_{z ∈ X(P,g), z ≤ x} μ(0̂, z) = 0`
  (`sum_mu_below_eq_zero`). Under `lem:interval`(i) this is the note's (W) for
  `(P|_{B₀(x)}, h_x)`. For `m = o` nothing of `X(P,g)` lies below `x` (`eq_of_le_of_per`).
* For `w ∈ F(P,g)`, the `z ∈ X(P,g)` with `w ≤ z` are the `w ∨ O_{g^d}`, `d ∣ o`, with
  `m(z) = d` (`eq_joinPow`, `per_joinPow`). So `∑_{z ∈ X, w ≤ z ≤ x} μ(o/m(z)) =
  ∑_{m(x) ∣ d ∣ o} μ(o/d) = 0` for `m(x) < o` (`sum_moebius_between`). This replaces
  `[x, 1̂]_X ≅` divisor lattice and `μ_X(x, 1̂) = μ(o)`.
* By well-founded induction on `x`: `μ(0̂, x) = μ(o/m(x)) ∑_{w ∈ F(P,g), w ≤ x} μ(0̂, w)`
  (`mu_eq_moebius_mul_sum`). At `x = 1̂`, with `μ(0̂, w) = μ(OP(P|_{B₀(w)})^{h_w})`
  (`mu_interval`), `h_w = 1` (`hres_eq_one`), `interval_sign` and `Mt_one`:
  `M̃(P,g) = μ(o) ∑_{w ∈ F(P,g)} e_C(P|_{B₀(w)})` (`Mt_eq_sum_Fset`).
* `F(P,g)` as setoids matches `InF` (`w ↦ {g^j B₀(w)}`, inverse `opOfBlocks`), and `e_C` of
  any block equals `e_C(P|_{B₀(w)})` (`eC_image`, `eC_congr`); this gives `prop_Mside` in the
  form of `prop_Lside`.
* `character_identity`: `prop_Mside` and `prop_Lside` with the same choice of blocks give
  `M̃(P,g) = ∑_{gC=C} ζ^{r_g(C)}`; multiply by `sgn(g)`.

`prop_Mside` has the hypothesis `0 < Fintype.card α` (the note's `n ≥ 1`), as `prop_Lside`
does. The new definition in a stated theorem's type is `Mt` (in `prop_Mside`); its control is
`Test.Mt_chain2` (table `n2_001`). `Test.lean` also checks `mu_OP_eq` on the 3-antichain
against `mu_OP_g = 2` (`n3_000`). `IsX`, `Fset`, `Contr`, `Bset`, `pa`, `pab`, `joinPow`,
`orbitPow`, `blkSet`, `opOfBlocks` occur only in proofs.

**How `prop:Lside` is proved (step 4)** (`LieSide.lean`). The route avoids the note's weights
`1/|K(w)|`. Fix `x₀`.

* By Lemma 4 (`inB_coset_inj`, `exists_inB_coset`) each class contains exactly one word of
  `B_P(x₀)`, so `∑_{gC=C} ζ^{r_g(C)}` is a sum over the set `fixedB` of words `w ∈ B_P(x₀)`
  whose class is `g`-stable, `g w = w γ^r` with `r = r_g(C) < n`.
* For such `w` let `k = gcd(r, n)` and `s = r/k` (`fixedB_struct`). Since `g^j w = w γ^{jr}` and
  rotations of a word of distinct letters are distinct, `g^j = 1` iff `n/k ∣ j`, so `o = n/k`
  and `s` is a unit mod `o`. With `s s' ≡ 1 (mod o)` and `h = g^{s'}`, `w γ^k = h w`, and then
  `w` is the concatenation of the chunks `h^t (w_1 ⋯ w_k)`, `t < o` (`eq_flatMap_of_rotate`).
  The first chunk `A` is a union of components, because `w` and `w γ^k = h w` are both linear
  extensions (`isLinExt_rot_iff`). It contains `x₀` (definition of `B_P`). The sets `h^t A`
  partition the ground set, hence so do the `g^j A`, `j < o` (`isBlockSys_pow`), and
  `x(w) = {g^j A : j < o} ∈ F(P,g)` (`inF_blocksOf`). The first chunk `w_1 ⋯ w_k` lies in
  `B_{P|_A}(x₀)`.
* Conversely (`exists_fixedB`), for `x ∈ F(P,g)`, its block `B ∋ x₀`, a unit `s` and
  `u ∈ B_{P|_B}(x₀)`, the concatenation of the chunks `h^t u` is a word on the ground set
  (`blocksOf_of_inF` gives the block system). It is a linear extension, since the blocks are
  pairwise incomparable unions of components. It lies in `B_P(x₀)` (a union-prefix is either a
  union-prefix of `u` or contains `u`), and `g w = w γ^{s|B|}` (`rotate_mul_chunks`). Its data is
  `(x, s, u)`.
* So the fibre of `w ↦ (x(w), s(w))` over `(x, s)` is in bijection with `B_{P|_B}(x₀)`, and on
  it `r = s|B|` (`card_fiber`). With `|P| = o|B|` (`card_eq_of_isBlockSys`), `ζ^{|B|}` is a
  primitive `o`-th root of unity, and the Ramanujan sum gives
  `∑_{s ∈ (ℤ/o)^×} (ζ^{|B|})^s = μ(o)` (`sum_pow_coprime_eq_moebius`). Finally
  `|B_{P|_B}(x₀)| = e_C(P|_B)` (`card_BL`), and `e_C(P|_B) = e_C(P|_{B₀(x)})` since
  `B = g^j B₀(x)` (`eC_image`).

`prop_Lside` has the hypothesis `0 < Fintype.card α` (the note's `n ≥ 1`). It is false at
`n = 0` (checked by hand, not in `Test.lean`): there `Cyc(P)` is `{∅}`, so the left side is
`1`, while `F(P,1)` is empty. The new definitions (`fixedB`, `blocksOf`, `BL`, `chunks`, `invMod`, `unitsMod`, …) occur only in the
proof. No stated theorem's type depends on them.

Gaps and deliberate modelling choices:

* The Hopf trace formula (C) is not yet stated in Lean.
* `∂ ∘ ∂ = 0` is proved for `bd` (`bd_comp_bd`, in `Test.lean`). Move it to `OrderComplex.lean`
  when proof work starts.
* `H̃_{-1}` is not modelled, since `redHom` is indexed by `d : ℕ`. It plays no role for `n ≥ 3`.
* Jenča–Sarkoci is represented only by its homological content. See §1 and §2.
* Theorem S(c),(d), Prop. Φ and Lemma D (splitting cycles `ρ_w`) are not yet stated. They need
  `sgn(w)` for words, which requires fixing a labelling `α ≃ Fin n`, and the cycles `ρ_w` as
  elements of `Chains`.
* The `x ∈ F(P,g)` data in `closed_formula` is a `Finset (Finset α)` of blocks rather than a
  `Setoid`. This is equivalent, and convenient for "`g` permutes the blocks".
* Positive controls on small posets are in `Test.lean`, and the faithfulness audit is
  `AUDIT_FAITHFULNESS.md`. Its one defect (`trace_PLie`, `corPsi_bijective`, `corPsi` false at
  `n = 0`) is fixed by `h0` (above).

### 4.2 M3b: equal characters imply isomorphic, and (mainiso) from the characters

`main_iso` is proved from `trace_HP` (still `sorry` at this step; closed in §4.3), `trace_PLie` and `character_identity`.
Sorry count 4 → 3 (`trace_HP`, `jencaSarkoci_homology`, `hall_mu_eq_reducedEuler`). No
statement changed and no hypothesis was added. The one other edit to `MainTheorem.lean` is
needed because Lean has no forward references: `main_iso` (docstring and statement
byte-identical) now comes after `trace_PLie`, so that its proof can cite `trace_HP`.

| File | Contents |
|---|---|
| `PosetJKS/CharacterIso.lean` | general (imports only Mathlib): for a finite group `G` and a field `k` of characteristic zero, two finite-dimensional representations with equal characters are isomorphic (`Representation.nonempty_equiv_of_character_eq`). Also the iff with Mathlib's `char_iso` (`nonempty_equiv_iff_character_eq`), the unbundled form `∃ e : V ≃ₗ[k] W, ∀ g x, e (ρ g x) = σ g (e x)` (`exists_linearEquiv_of_trace_eq`), the character of `V × W` (`char_prod`), `Equiv.prodCongr`, and `V ≅ S × T` for complementary subrepresentations (`Subrepresentation.prodEquivOfIsCompl`) (**all proved**) |
| `PosetJKS/MainIso.lean` | functoriality of `homMap` (`homMap_refl`, `homMap_trans`), `actProper_one`, `actProper_mul`, `H_P` finite-dimensional (`finiteDimensional_HP`); `H_P` and `sgn ⊗ PLie(P)` as representations of `Aut(P)` (`repHP`, `repSgnPLie`); `tr(g \| sgn ⊗ PLie) = sgn(g) ∑_{gC=C} ζ^{r_g(C)}` (`trace_repSgnPLie`); (mainiso) from `tr(g \| H_P) = sgn(g) ∑_{gC=C} ζ^{r_g(C)}` (`exists_iso_HP_PLie_of_trace`) (**all proved**) |
| `PosetJKS/CharacterIsoTest.lean` | controls on `S_2` (below) |

**Proof of the general lemma.** Mathlib has the parts at the level of `Representation`:
`card_inv_mul_sum_char_mul_char_eq_finrank` (`|G|⁻¹ ∑ χ_σ(g) χ_τ(g⁻¹) = dim Hom_G(τ, σ)`), and
Maschke in the form `IsSemisimpleRepresentation` (complements of subrepresentations). The plan
of §1 was to decompose into irreducibles and read off multiplicities by `char_orthonormal`. The
proof instead runs by induction on `dim V`, with no decomposition, no orthonormality and no
algebraic closedness:

* Let `S ⊆ V` be a nonzero subrepresentation of least dimension (`Nat.find`).
* `dim Hom_G(S, W) = dim Hom_G(S, V)` because the characters agree, and this is `≥ 1` (the
  inclusion). Let `f : S → W` be a nonzero `G`-map.
* `ker f`, viewed inside `V`, is a subrepresentation of dimension `< dim S`, so it is `0`
  (minimality). So `f` is injective and `S ≅ f(S)`.
* By Maschke, `V ≅ S × S'` and `W ≅ f(S) × T'`. Characters are additive (`char_prod`), so
  `χ_{S'} = χ_{T'}`. Also `dim S' < dim V`, and induction gives `S' ≅ T'`.
* If `dim V = 0`, then `dim W = χ_W(1) = χ_V(1) = 0`, and any linear equivalence intertwines.

Characteristic zero is used twice: to make `|G|` invertible, and to read the dimensions as
natural numbers from their images in `k`.

**(mainiso).** `actHP` and `g ↦ sgn(g) · actPLie ζ g` are monoid homomorphisms `Aut(P) →
End(-)`. For `actHP` this needs `actProper (g h) = actProper h ≫ actProper g` and the functoriality
of `chainMap` and `homMap`. For the sign this needs `(g h).toEquiv = g.toEquiv * h.toEquiv`
(definitional) and `Perm.sign_mul`. `Aut(P)` is finite: it injects into `Perm α`. `H_P` is
finite-dimensional: chains are finitely supported functions on the finite type `Fin m ↪o
ProperOP α`. Without this, `LinearMap.trace` would be `0` by convention, and `trace_HP` would
say nothing about `H_P`. The characters agree:
`tr(g | H_P) = (-1)^{n-3} μ(OP(P)^g)` (`trace_HP`) `= sgn(g) ∑_{gC=C} ζ^{r_g(C)}`
(`character_identity`) `= tr(g | sgn ⊗ PLie(P))` (`trace_repSgnPLie`, from `trace_actPLie`).
The isomorphism `e` from `exists_linearEquiv_of_trace_eq` satisfies
`e (actHP g x) = sgn(g) • actPLie ζ g (e x)`. Coerced to `Alg α`, this is the equation in
`main_iso`, by definition of `actPLie`.

**Controls** (`CharacterIsoTest.lean`, `G = S_2`, over `ℂ`). There are three 2-dimensional
representations: the permutation representation on `Fin 2 → ℂ` (character `(2, 0)`), trivial ⊕
sign on `ℂ × ℂ` (`(2, 0)`), and trivial on `Fin 2 → ℂ` (`(2, 2)`). The characters are computed
in Lean by matrix traces. The lemma gives `trivial ⊕ sign ≅ permutation`
(`trivSgn_equiv_permRep`). The modules are different, so the isomorphism is not an identity.
Trivial `≇` permutation (`not_triv2_equiv_permRep`): same module, same dimension, different
characters. `trivial ≇ sign` on `ℂ` (`not_triv_equiv_sgn`). So the lemma's conclusion is not
automatic for representations of equal dimension, and the hypothesis does real work.

**Axioms and dependencies.** `#print axioms` (in `scripts/PrintAxioms.lean`):
`nonempty_equiv_of_character_eq`, `nonempty_equiv_iff_character_eq`,
`exists_linearEquiv_of_trace_eq`, `exists_iso_HP_PLie_of_trace` and the three controls depend
only on `propext`, `Classical.choice`, `Quot.sound`. `main_iso` depends on those and `sorryAx`.
`scripts/CheckDeps.lean`, which now also tracks `trace_HP`: `main_iso` uses `trace_HP`, and
not `jencaSarkoci_homology` or `hall_mu_eq_reducedEuler` directly.
`exists_iso_HP_PLie_of_trace` and `nonempty_equiv_of_character_eq` use none of the three. So
the only `sorry` under `main_iso` is the one in `trace_HP`. Once `trace_HP` is proved from
`jencaSarkoci_homology`, `main_iso` depends on `jencaSarkoci_homology` alone.

The earlier parts of this file (the status lines, the §1 row "Aut(P) actions, characters", and
the §4 table entry for `main_iso` at its old line) were written before this step. They have
since been brought up to date with steps 6 and 7.

### 4.3 M3a: P. Hall, the Hopf trace formula, and `trace_HP`

Sorry count `3 → 1` after §4.2 (`4 → 2` on its own). Closed: `hall_mu_eq_reducedEuler`
(cited input B, now a theorem) and `trace_HP` (Lemma `lem:homchar`). The one remaining
`sorry` is `jencaSarkoci_homology`. With §4.2, `main_iso` now depends on it alone. No
statement changed and no hypothesis was added. In `MainTheorem.lean` the two `sorry`s are
replaced by calls. The "Cited inputs" section (statements unchanged) now comes before
`trace_HP`, which uses `jencaSarkoci_homology`. The order is now: cited inputs, `trace_HP`,
`trace_PLie`, `main_iso`.

* **P. Hall** (`Hall.lean`, imports only Mathlib). An `m`-element chain of the open interval
  `(x, y)` is a strictly increasing `Fin m → L` with values in `(x, y)` (`chainsIn x y m`).
  Deleting the top element `z` gives `#chains_{m+1}(x, y) = ∑_{z ∈ (x,y)} #chains_m(x, z)`
  (`card_chainsIn_succ`, via `Fin.init`/`Fin.snoc`). So the signed count
  `∑_{m ≤ |L|} (-1)^{m+1} #chains_m(x, y)` satisfies Mathlib's recursion
  `μ(x, y) = -∑_{x ≤ z < y} μ(x, z)`. This is the `(ζ - 1)` expansion read one step at a time,
  and gives `mu_eq_chainEuler` by well-founded induction on `y`. Chains with more than `|L|`
  elements do not exist, which closes the range. `mu_bot_top_eq_chainSum` is the statement of
  `hall_mu_eq_reducedEuler`, with order embeddings `Fin m ↪o` proper part matched to
  increasing tuples.
* **Hopf trace formula** (`Hopf.lean`, imports only Mathlib). It starts from trace additivity
  `tr f = tr(f|_W) + tr(f on V/W)` (`trace_eq_trace_restrict_add_trace_mapQ`). The proof takes
  a complement `W'`, writes `f = ι_W p f + ι_{W'} q f`, cycles the traces, and uses
  `V/W ≅ W'`. Then for any complex `d m : C_{m+1} → C_m` of finite-dimensional spaces with
  `d ∘ d = 0`, a chain map `f` (`IsChainMap`) and `C_K = 0`:
  `∑_{m ≤ K} (-1)^m tr(f|C_m) = tr(f | C_0/∂C_1) + ∑_{j<K} (-1)^{j+1} tr(f | H_j)`
  (`IsChainMap.hopf_trace`), with `H_j = ker d_j / im d_{j+1}` built as in `redHom`. The proof
  telescopes `tr(f|C_{m+1}) = R_{m+1} + tr(f|H_m) + R_m`, where `R_m = tr(f | im d_m)`.
* **Specialisation** (`TraceHP.lean`). `Chains L m` is finite-dimensional for finite `L`.
  `∂∘∂ = 0` is `bd_comp_bd'`, the proof of `Test.bd_comp_bd` restated outside the test file.
  `homMap φ j` is by definition the Hopf homology map of `chainMap φ` (`homMap_eq`, `rfl`).
  `tr(φ | C_m)` is the number of `φ`-fixed `m`-chains (`trace_chainMap`, from the basis of
  chains). A chain of `\widehat{OP(P)}` is `g`-fixed iff each element is, so the fixed
  `m`-chains are the `m`-chains of the proper part of `OP(P)^g` (`fixedChains_equiv`,
  `card_fixedChains`). Hall on `OP(P)^g` is applied with the bounded order `0̂`, `1̂`
  (`OPFixed.boundedOrder`, a local instance). It turns the alternating fixed-chain count into
  `-μ(OP(P)^g)`.
* **Degree `-1`.** `redHom` has no `H̃_{-1}`. Its role is played by the term
  `tr(f | C_0/∂C_1)` of the Hopf formula, which vanishes because the proper part of `OP(P)` is
  nonempty for `n ≥ 3`: it contains `π_a` for a minimal `a` (`properOP_nonempty`, `range_bd_zero`).
* `trace_HP_of_vanishing hn hvan g` proves `tr(g | H_P) = (-1)^{n-3} μ(OP(P)^g)` from the
  hypothesis `H̃_d = 0` for `d ≠ n-3` only. It uses no `sorry`, and the dimension part of
  Jenča–Sarkoci is not needed. `trace_HP` is this theorem applied to
  `(jencaSarkoci_homology hn).1`.

`#print axioms`: `hall_mu_eq_reducedEuler`, `mu_bot_top_eq_chainSum`, `IsChainMap.hopf_trace`
and `trace_HP_of_vanishing` depend only on `propext`, `Classical.choice`, `Quot.sound`.
`trace_HP` adds `sorryAx`. `scripts/CheckDeps.lean`:

```
PosetJKS.hall_mu_eq_reducedEuler: … cited inputs used: [PosetJKS.hall_mu_eq_reducedEuler]   (itself)
PosetJKS.trace_HP_of_vanishing: … cited inputs used: []
PosetJKS.trace_HP: … cited inputs used: [PosetJKS.jencaSarkoci_homology]
```

So the only open dependency of `trace_HP` is `jencaSarkoci_homology`.

### 4.4 S1 (Route C): general chain tools

Slice S1 of the route to `jencaSarkoci_homology` in `notes/lean_js_route.md` §6. New file
`ChainTools.lean` (imports only `OrderComplex.lean`). Sorry count unchanged (1,
`jencaSarkoci_homology`). No existing statement changed. `chainMap` is untouched;
`chainMap_eq_chainMapEmb` identifies it with the new map (`rfl`).

**Mathlib API check** (the names `notes/lean_js_route.md` §7 lists as not checked, grepped in
the pinned Mathlib and used in `ChainTools.lean`, so each one compiles):

* Present, as expected: `Fin.insertNth` (`Data/Fin/Tuple/Basic.lean`, dependent:
  `insertNth (i : Fin (n+1)) (x : α i) (p : ∀ j, α (i.succAbove j))`; a non-dependent use
  needs `(α := fun _ => L)` or a type ascription), `Fin.insertNth_apply_same`,
  `Fin.insertNth_apply_succAbove`, `Fin.insertNth_eq_iff` (`g = insertNth p a f ↔ g p = a ∧
  removeNth p g = f`), `Fin.removeNth`, `Fin.insertNth_self_removeNth`,
  `Fin.insertNth_comp_succAbove`. In `Data/Fin/SuccPred.lean`: `Fin.succAbove_succAbove_predAbove`
  (`(i.succAbove j).succAbove (j.predAbove i) = i`) and
  `Fin.succAbove_succAbove_succAbove_predAbove` (the two ways of leaving holes at `i` and
  `i.succAbove j`); these two are exactly what the re-indexing
  `insertNth j t c ∘ (j.succAbove i).succAbove = insertNth (i.predAbove j) t (c ∘ i.succAbove)`
  needs. Also `Fin.exists_succAbove_eq`, `Fin.lt_succAbove_iff_le_castSucc`,
  `Fin.succAbove_lt_iff_castSucc_lt`, `Fin.strictMono_succAbove`,
  `Fin.succAbove_of_castSucc_lt`, `Fin.succAbove_of_le_castSucc`, `Fin.succAboveOrderEmb`,
  `Fin.sum_univ_succAbove` (the additive form of `Fin.prod_univ_succAbove`).
* Absent: a strict-monotonicity lemma for `Fin.insertNth`. Mathlib has the order isomorphism
  `Fin.insertNthOrderIso` and `Fin.insertNth_le_iff` (componentwise order on tuples), which are
  about a different order. It is proved here (`strictMono_insertNth`, from betweenness).
* Finsupp side: `Finsupp.lmapDomain`, `Finsupp.mapDomain_single`, `Finsupp.mapDomain_injective`,
  `Finsupp.mapDomain_comp`, `Finsupp.mapDomain_id`; `Submodule.Quotient.subsingleton_iff`
  (`Subsingleton (M ⧸ p) ↔ p = ⊤`). `Finsupp.lmapDomain_apply` does not rewrite through the
  `Chains` wrapper (a `def`); the proofs `change` to `Finsupp.mapDomain` first.

**Contents.**

* `chainMapEmb f m`, for `f : L ↪o L'`: `bd_chainMapEmb` (a chain map),
  `chainMapEmb_injective`, `chainMapEmb_comp_apply`, `chainMapEmb_symm_apply`.
* `subsingleton_redHom_iff`, `subsingleton_redHom_of_orderIso`, `subsingleton_redHom_congr`,
  `subsingleton_redHom_of_isEmpty` (with instances `IsEmpty (Fin (m+1) ↪o L)` and
  `Subsingleton (Chains L (m+1))` for empty `L`).
* `insertAt c t j h : Fin (m+1) ↪o L` for `c : Fin m ↪o L`, where `h` says that
  `Fin.insertNth j t c` is strictly increasing. `strictMono_insertNth` supplies `h` from
  betweenness (`c i < t` for `i.castSucc < j`, `t < c i` for `j ≤ i.castSucc`). Faces:
  `face_insertAt_self` (`face (insertAt c t j h) j = c`) and `face_insertAt_succAbove`
  (`face (insertAt c t j h) (j.succAbove i) = insertAt (face c i) t (i.predAbove j) _`). The
  hypothesis for the inserted face is derived (`strictMono_insertNth_face`), not assumed.
  `insertAt_face` writes any chain as an insertion into one of its faces.
* `bd_single` (the boundary of a basis chain), `bd_single_insertAt`
  (`∂[c ∪ t] = (-1)^j [c] + ∑_i (-1)^{j.succAbove i} [face c i ∪ t]`), its degree-0 case, and
  the sign `neg_one_pow_succAbove` (`(-1)^i` below `j`, `-(-1)^i` from `j` on), which is the
  case split of the cone computation in `notes/lean_js_route.md` §3.1.
* `nilChain`, `ptChain` (one-element chains), `bd_single_ptChain`.

**Control** (`Test.lean`): `redHom_antichain2_ne`. On the two-point antichain `Unit ⊕ Unit`,
`H̃_0 ≠ 0`: `[a] - [b]` is a cycle and there are no 2-element chains. This shows that
`subsingleton_redHom_iff` does not hold vacuously.

### 4.5 S2 (Route C): Lemma K

Slice S2 of `notes/lean_js_route.md` §6. New file `ConeRetract.lean` (imports `ChainTools.lean`
and, for `bd_comp_bd'`, `TraceHP.lean`). Sorry count unchanged (1, `jencaSarkoci_homology`). No
existing statement changed. The signs are those of the corrected §3.1, i.e. with
`notes/audit_lean_js_route.md` G1–G2 applied. Lemma K is classical: at the homotopy level it is
Quillen's order-homotopy lemma (Quillen 1978, Prop. 1.6), in the form of Björner 1995,
Cor. 10.12. The proof formalized is the homology-level one of the note.

**Statement.** `ConeRetraction R` packages `t : R` and `p : R → R` with `p` monotone,
`p x ≤ x`, `p x ≤ t`, and `p x = x` for `x ≤ t`. `ConeRetraction.exact_of_retract K d :
Subsingleton (redHom R d)` for every `d`. No finiteness of `R` is needed.

**Contents.**

* `nlow c` (the number of elements `≤ t`, i.e. `j = |c_≤|`) and `hcount c`. `low_iff`: the low
  elements are exactly the positions `< nlow c`. How `nlow` and `hcount` change under faces and
  insertions: `nlow_face`, `hcount_face_le`, `hcount_face_of_not_le`, `hcount_insertAt`.
* `hval c` (the least high element `h = c_j`, or `t`) and `tau c = p (hval c)`. `le_tau` and
  `tau_lt`: `τ c` lies above the low part and strictly below the high part.
  `tau_mem_range_iff`: if `τ c = c_i`, then `i + 1 = nlow c`, so `τ c` is at position
  `j' = j − 1` (audit G1). `tau_face`: deleting any element other than `h` leaves `τ` unchanged.
* `cone c h = insertAt c (τ c) ⟨nlow c, _⟩ _` for `τ c ∉ c`. `s m` is the linear extension of
  `c ↦ (−1)^{nlow c} [cone c]` (`τ c ∉ c`) and `c ↦ 0` (`τ c ∈ c`). `cone_face`:
  `cone (c ∖ c_i) = (cone c) ∖ c_i` for `c_i ≠ h`, with the position re-indexed by `predAbove`.
* `bd_s_term_eq_zero`: for `τ c ∉ c` and `c_i ≠ h`, the two terms indexed by `c_i` cancel.
  `s_single_face_tau`: for `τ c = c_{j'}`, `s (c ∖ c_{j'}) = (−1)^{j'} [c]`, and the face
  removing `c_{j'}` has sign `(−1)^{j'}`, so the product is `+[c]` (audit G1).
* `bd_s_add_s_bd_eq` (the exact identity, audit G2), for `c` with a high element `h = c_j`:

      (∂s + s∂)(c) − c = −[face (cone c) (j+1)] + (−1)^j s(c ∖ h)     if τ c ∉ c,
      (∂s + s∂)(c) − c = (−1)^j s(c ∖ h)                              if τ c ∈ c.

  `face (cone c) (j+1)` is `(c ∖ h) ∪ τ c`. `bd_s_add_s_bd_of_hcount_eq_zero`: with no high
  element, `(∂s + s∂)(c) = c`.
* `F m k`: the span of the `m`-element chains with at most `k` high elements. It is stable
  under `bd` and `s` (`bd_mem_F`, `s_mem_F`) and is everything for `k = m` (`mem_F_self`).
  `bd_s_add_s_bd`: `(∂s + s∂)(c) − c ∈ F (hcount c − 1)`. Hence `homotopy_mem_F`
  (`∂s + s∂ − id` maps `F (k+1)` into `F k`) and `homotopy_F_zero` (`∂s + s∂ = id` on `F 0`).
* `exact_F`: a cycle in `F k` is a boundary, by induction on `k` (§3.1, "Exactness"):
  `z − ∂(s z) ∈ F (k−1)` is again a cycle. `exact_of_retract` is the case `k = d + 1`.

**Controls** (`Test.lean`). Negative: on the two-point antichain `Unit ⊕ Unit` the hypotheses
fail (`isEmpty_coneRetraction_antichain2`, directly: `p x ≤ x` forces `p x = x`, and then
`p x ≤ t` forces both points to equal `t`), and its `redHom 0` is nonzero
(`redHom_antichain2_ne`, from S1). `isEmpty_coneRetraction_antichain2'` derives the same failure
from Lemma K and `redHom_antichain2_ne`. Positive: on the cone `V = {⊥ < a, ⊥ < b}` over that
antichain, `t = ⊥`, `p ≡ ⊥` is a cone retraction other than the identity (`vRetraction`), and
Lemma K gives `H̃_d(Δ(V)) = 0` for every `d` (`redHom_V_subsingleton`). So the hypotheses are
satisfiable and not vacuous.

## 5. `#print axioms` (output of `lake env lean scripts/PrintAxioms.lean`)

```
'PosetJKS.character_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.main_iso' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.closed_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.trace_HP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.trace_PLie' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.jencaSarkoci_homology' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.hall_mu_eq_reducedEuler' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.thmS_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.thmS_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.thmPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.corPsi_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.corPsi_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.corPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.L.map_E_ShL' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.L.eq_zero_of_inBL' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.L.eq_zero_of_eqL' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.L.eqL_classSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.card_inB' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.wd_mem_SB_sup_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.pr_wEζ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.actHP' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.actMP' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.muFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.trace_actPLie' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.finrank_PLie' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.weisner' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.isOrderPreserving_inf' depends on axioms: [propext, Quot.sound]
'PosetJKS.isOrderPreserving_orbitSetoid' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.isOrderPreserving_joinOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.rel_of_le_of_joinOrbit_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.sum_mu_join_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_eq_of_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.recursionW' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.prop_Lside' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.fixedB_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.exists_fixedB' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.card_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.inF_blocksOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.blocksOf_of_inF' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.sum_primitiveRoots_eq_moebius' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.sum_pow_coprime_eq_moebius' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.L.inBL_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.card_BL' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.eC_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.eC_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_OP_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.weisner_dual' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_op_rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_pab_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.eC_rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Mt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.interval_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.recursionW_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.sum_mu_below_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_eq_moebius_mul_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.prop_Mside' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.fixedClassSum_g3_prim' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.muFixed_chain2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.Mt_chain2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.not_op_chain3_02_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.relabel_wEζ_of_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_comp_bd' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_zero_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.corPsi_bijective_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.trace_PLie_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Representation.nonempty_equiv_of_character_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Representation.nonempty_equiv_iff_character_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Representation.exists_linearEquiv_of_trace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.exists_iso_HP_PLie_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.CharacterIsoTest.trivSgn_equiv_permRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.CharacterIsoTest.not_triv2_equiv_permRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.CharacterIsoTest.not_triv_equiv_sgn' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_eq_chainEuler' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.mu_bot_top_eq_chainSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.trace_eq_trace_restrict_add_trace_mapQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.IsChainMap.hopf_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_comp_bd'' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.trace_chainMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.card_fixedChains' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.properOP_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.trace_HP_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_chainMapEmb' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.chainMapEmb_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.subsingleton_redHom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.subsingleton_redHom_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.subsingleton_redHom_of_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.face_insertAt_succAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_single_insertAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.redHom_antichain2_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.ConeRetraction.bd_s_add_s_bd_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.ConeRetraction.bd_s_add_s_bd_of_hcount_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.ConeRetraction.bd_s_add_s_bd' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.ConeRetraction.exact_of_retract' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.isEmpty_coneRetraction_antichain2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.isEmpty_coneRetraction_antichain2'' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.redHom_V_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every listed declaration depends only on `propext`, `Classical.choice`, `Quot.sound`
(`isOrderPreserving_inf` does not even use `Classical.choice`), except three, which also depend
on `sorryAx`: `jencaSarkoci_homology` (the one visible `sorry`, §4), `trace_HP` and `main_iso`.
In particular the M1 theorems, `trace_PLie`, `prop_Lside`, `mu_OP_eq`, `prop_Mside`,
`character_identity`, `closed_formula`, the general lemma `nonempty_equiv_of_character_eq` and
`exists_iso_HP_PLie_of_trace` (step 6), and `hall_mu_eq_reducedEuler`,
`IsChainMap.hopf_trace` and `trace_HP_of_vanishing` (step 7), and Lemma K
(`exact_of_retract`, step 9) are `sorry`-free. The definitions
are `sorry`-free.

`sorryAx` stands for every `sorry`, so `#print axioms` alone cannot show which `sorry` a
theorem uses. `scripts/CheckDeps.lean` walks the constants used by a declaration's type and
value, transitively, and reports which of `jencaSarkoci_homology`, `hall_mu_eq_reducedEuler`
and `trace_HP` occur:

```
PosetJKS.checkDepsControlJS: 16398 constants; cited inputs used: [PosetJKS.jencaSarkoci_homology]
PosetJKS.checkDepsControlHall: 13334 constants; cited inputs used: [PosetJKS.hall_mu_eq_reducedEuler]
PosetJKS.mu_OP_eq: 15365 constants; cited inputs used: []
PosetJKS.prop_Mside: 18419 constants; cited inputs used: []
PosetJKS.character_identity: 23406 constants; cited inputs used: []
PosetJKS.closed_formula: 23408 constants; cited inputs used: []
PosetJKS.main_iso: 30199 constants; cited inputs used: [PosetJKS.jencaSarkoci_homology, PosetJKS.trace_HP]
PosetJKS.exists_iso_HP_PLie_of_trace: 24937 constants; cited inputs used: []
Representation.nonempty_equiv_of_character_eq: 17940 constants; cited inputs used: []
PosetJKS.hall_mu_eq_reducedEuler: 13252 constants; cited inputs used: [PosetJKS.hall_mu_eq_reducedEuler]
PosetJKS.trace_HP_of_vanishing: 22538 constants; cited inputs used: []
PosetJKS.trace_HP: 22736 constants; cited inputs used: [PosetJKS.jencaSarkoci_homology, PosetJKS.trace_HP]
```

The two controls (defined in the script, each using one cited input) are detected.
`character_identity`, `closed_formula`, `mu_OP_eq` and `prop_Mside` use none of the three.
`trace_HP` and `main_iso` use `jencaSarkoci_homology` and not `hall_mu_eq_reducedEuler`
(the Hall step inside `trace_HP_of_vanishing` goes through `mu_bot_top_eq_chainSum`
directly). Since `jencaSarkoci_homology` is the only `sorry`, it is the only thing `trace_HP`
and `main_iso` wait on. A proof of its first conjunct alone (vanishing of `H̃_d` for
`d ≠ n-3`), passed to `trace_HP_of_vanishing`, would make both `sorry`-free; the second
conjunct (`dim H_P = e_C(P)`) is needed only to close `jencaSarkoci_homology` as stated.
