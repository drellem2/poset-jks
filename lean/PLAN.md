# Lean formalization of the poset JKS theorem: plan and status

This directory holds a Lean 4 + Mathlib project. It states the main theorem of
`notes/poset_jks_theorem.tex` (Theorem `thm:main`) and a first, homology-free milestone M1.

* **Step 1** gave the scaffold, the ingredient map, the choice of route, and faithful
  statements (all proofs `sorry`).
* **Step 2 (M1, done)** proves Theorem S(a), S(b), Theorem Ψ and Corollary Ψ.1
  (`PLie(P) ≅ ℂ[Lin P]/R_P`, explicit and `Aut(P)`-equivariant, every finite poset with
  `n ≥ 1`). These are sorry-free and depend only on `propext`, `Classical.choice`, `Quot.sound`
  (§5). The main theorem and its homological inputs are still `sorry` (§4).
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

* Toolchain: `leanprover/lean4:v4.29.1`; Mathlib `v4.29.1`
  (rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6`, pinned in `lake-manifest.json`).
* `lake build` succeeds. It reports 5 `sorry` warnings, all in `MainTheorem.lean`, and no errors.
* No `axiom` declarations (`grep -rnw axiom PosetJKS scripts` finds only a comment).

## Reproduce

```sh
cd lean
lake exe cache get                         # fetch prebuilt Mathlib
lake build                                 # builds PosetJKS (and PosetJKS/Test.lean); expect 5 "declaration uses sorry"
lake env lean scripts/PrintAxioms.lean     # the #print axioms table below (and of the Test.lean controls)
grep -rn "^  sorry" PosetJKS               # the sorry list below
```

## Files

| File | Contents |
|---|---|
| `PosetJKS/Basic.lean` | words `Fin n ≃ α`; the ambient space `ℂ[S_n]` (`Alg`); `rot` (right mult. by `γ^j`); `wEζ` (`w e_ζ`); `Lin(P)` (`IsLinExt`); unions of components; shuffles `u ⧢ v`; `Sh_n`, `W_P`, `R_P`, `PLie(P)`; `Cyc(P)`, `e_C(P)`, `r_g(C)`, the class sum `∑_{gC=C} ζ^{r_g(C)}`; the `Aut(P)` action (`relabel`) and its invariance of `PLie`, `W_P`, `R_P` (**all proved**) |
| `PosetJKS/OrderComplex.lean` | oriented chains of the order complex (`Chains`, `bd`), reduced homology `redHom`; order-preserving partitions (`IsOrderPreserving`, `OP`, `ProperOP`); `H_P` (`HP`); the `Aut(P)` action on the proper part and on `H_P` (`actProper`, `actHP`); the fixed lattice `OP(P)^g` and `μ(OP(P)^g)` (`muFixed`) (**all proved**) |
| `PosetJKS/Words.lean` | M1 core, on lists over a fixed type with an arbitrary relation `r`: shuffles `shq`, `ShL`, the contraction operator `E_{a,x}` and Lemma 1 (`map_E_ShL`); the contraction relation `rc` and Lemma 5 (`inBL_contract`); Theorem A (`eq_zero_of_inBL`) and Theorem Ψ (`eq_zero_of_eqL`) on lists; Lemma Ψ.0 (`eqL_classSum`); the measure `μ` (`muL`), the Lemma 6 step (`muL_lt_of_shuffle`) and Lemma 4 (`inBL_rotate_muL`, `rotate_eq_zero_of_inBL`) (**all proved**) |
| `PosetJKS/Bridge.lean` | words `Fin n ≃ α` ↔ lists (`toL`, the injective linear map `toLmap`, `toLmap_shuffle`, `map_Sh_le`); `rot`, `prefixSet`, `coset`, `IsLinExt` in list terms; `rot_rot`, `rot_card`, `wEζ_rot` (moved here from `Test.lean`) (**all proved**) |
| `PosetJKS/Milestone.lean` | first milestone: Theorem S(a), (b), Theorem Ψ, Corollary Ψ.1, and on words: Lemma 4 (`card_inB`, split into `inB_coset_inj` and `exists_inB_coset`), Lemma 6 (`wd_mem_SB_sup_R`), `pr_P(w e_ζ) = s_ζ(w)/n` (`pr_wEζ`) (**all proved**) |
| `PosetJKS/LieTrace.lean` | M2: the basis `{w_C e_ζ}` of `PLie(P)` (`basisPLie`, `finrank_PLie`), `r_g(C)` is realised by every word of a fixed class (`classRot_spec`), and Lemma `lem:liechar` (`trace_actPLie`) (**all proved**) |
| `PosetJKS/OPLattice.lean` | M2: Weisner's theorem (`weisner`); `OP(P)` closed under meets (`isOrderPreserving_inf`); the orbit partition `O_g` (`orbitSetoid`), order-preserving and `g`-fixed; the join `x ∨ O_g` (`joinOrbit`), order-preserving, `g`-fixed and the join in `OP(P)^g`; `x ∨ O_g = 1̂` iff `g` is transitive on blocks, and then blocks are unions of components; Weisner in `OP(P)^g` with `a = O_g` (`sum_mu_join_eq_top`) (**all proved**) |
| `PosetJKS/Interval.lean` | M2: `μ` is invariant under interval isomorphisms (`mu_eq_of_interval`); the block `B₀` through a point, its period `m` and `h = g^m|_{B₀}` (`Blk`, `per`, `hres`); Lemma `lem:interval`(i) (`mu_interval`); the recursion (W), unsigned (`recursionW`) (**all proved**) |
| `PosetJKS/RamanujanSum.lean` | general (imports only Mathlib): `∑_{ξ^n=1} ξ = [n = 1]`; the primitive `o`-th roots of unity sum to `μ(o)` (`sum_primitiveRoots_eq_moebius`), and `∑_{s<o, (s,o)=1} ω^s = μ(o)` for `ω` primitive (`sum_pow_coprime_eq_moebius`) (**all proved**) |
| `PosetJKS/ECTransport.lean` | `B_P` on lists transported along injective relation-preserving maps (`L.inBL_map`); `B_{P|_A}(x₀)` as a finite set of lists (`BL`), `|B_{P|_A}(x₀)| = e_C(P|_A)` (`card_BL`); `e_C` invariant under order isomorphisms (`eC_congr`), `e_C(P|_{φB}) = e_C(P|_B)` for `φ ∈ Aut(P)` (`eC_image`) (**all proved**) |
| `PosetJKS/LieSide.lean` | `x ∈ F(P,g)` (`InF`, moved here unchanged from `MainTheorem.lean`); block systems `{g^j B : j < o}` and `InF` (`inF_blocksOf`, `blocksOf_of_inF`, `isBlockSys_pow`, `card_eq_of_isBlockSys`); words as concatenations of chunks `h^t u` (`eq_flatMap_of_rotate`, `rotate_mul_chunks`); the `B_P(x₀)` words of `g`-stable classes (`fixedB_struct`, `exists_fixedB`, `card_fiber`); Proposition `prop:Lside` (`prop_Lside`) (**all proved**) |
| `PosetJKS/MainTheorem.lean` | the main theorem (characterconj), (mainiso), (closed); the two character lemmas; the cited inputs in the form the proofs use them (`closed_formula` proved from `character_identity` and `prop_Lside`; the rest `sorry`) |
| `PosetJKS/Test.lean` | positive controls of the definitions on small posets against `compute/`, `∂ ∘ ∂ = 0` (`bd_comp_bd`), and two counterexamples at `n = 0`; see `AUDIT_FAITHFULNESS.md` |
| `scripts/PrintAxioms.lean` | `#print axioms` for every stated theorem and the main controls |

## 1. Ingredient map: what Mathlib has, what must be built

These are the declarations I actually found in the pinned Mathlib by grepping
`.lake/packages/mathlib/Mathlib`. "Absent" means a targeted grep found nothing. It does not
prove that nothing exists under another name. Sizes are rough line counts for the remaining
work.

| Ingredient | In Mathlib (found) | Built here (step 1) | Still to build | Size |
|---|---|---|---|---|
| **`OP(P)`** *(step 3: (i)–(iv) of `lem:lattice`, `lem:orbitquot`, `lem:interval`(i) done; see `OPLattice.lean`, `Interval.lean`)* | `Setoid` with `Setoid.completeLattice` (refinement order; `Setoid.bot_def`: `⊥` is `=`, `Setoid.top_def`), `Setoid.comap`, `Setoid.ker`, `Finpartition`, `Relation.ReflTransGen` | `IsOrderPreserving` (acyclic quotient), `OP`, `ProperOP`, `OPFixed`, `actSetoid`, `actProper : ProperOP ≃o ProperOP`; `isOrderPreserving_bot/top`; `OPFixed.bot_ne_top` | `OP(P)` is a lattice with meet the partition meet; `OP(P)^g` is a lattice containing `O_g`; joins with `O_g`; `{x : x ∨ O_g = 1̂} = X(P,g)` (note, Lemmas `lem:orbitquot`, `lem:lattice`) | 400–700 |
| **Order complex, reduced homology** | `PreAbstractSimplicialComplex` / `AbstractSimplicialComplex` (faces only, no homology); `SSet`, `CategoryTheory.nerve`, `mem_nerve_nonDegenerate_iff_strictMono`; `AlternatingFaceMapComplex.obj`, `alternatingFaceMapComplex`, `SimplicialObject.Augmented`, `normalizedMooreComplex`; `AlgebraicTopology.singularHomologyFunctor`; `HomologicalComplex.eulerChar`, `homologyEulerChar` (definitions only). **Absent:** simplicial homology of a simplicial complex, the order complex of a poset, geometric realisation of a poset, wedges of spheres, homotopy types of complexes | hand-rolled augmented oriented chain complex on chains `Fin m ↪o L`: `Chains`, `face`, `bd`, `cycles`, `boundaries`, `redHom`; functoriality `chainMap`, `bd_chainMap`, `homMap` | `∂∘∂ = 0` (not needed for the statements; needed for every proof) ~60; optional bridge to `alternatingFaceMapComplex (nerve L)` (normalised) ~300+ | 60–400 |
| **Möbius function, P. Hall** *(Weisner: done in step 3)* | `IncidenceAlgebra.mu`, `mu_apply`, `mu_eq_neg_sum_Ico_of_ne`, `mu_eq_neg_sum_Ioc_of_ne`, `mu_mul_zeta`, `mu_toDual`, `mu_prod_mu`, `IncidenceAlgebra.eulerChar`; `ArithmeticFunction.moebius` (number-theoretic `μ(o)`). **Absent:** P. Hall's chain-count theorem, Weisner's theorem, Crapo's complementation theorem | `muFixed g = mu ℤ 0̂ 1̂` on `OP(P)^g`; statement `hall_mu_eq_reducedEuler` | Hall (`μ = ∑ (-1)^k c_k` via `(ζ-1)` expansion in the incidence algebra) ~200–400; Weisner ~150–300 | 350–700 |
| **Hopf trace formula** | `LinearMap.trace`, `LinearMap.trace_restrict_eq_of_forall_mem` (PID file), `HomologicalComplex.eulerChar` (definition). **Absent:** Euler–Poincaré `χ(C) = χ(H)`, the Hopf trace formula, additivity of trace over `0 → U → V → V/U → 0` | — | Pure linear algebra on a bounded complex of finite-dimensional spaces with a chain endomorphism; specialise to `Chains`/`redHom`. Uses `LinearMap.trace_eq_matrix_trace` with an adapted basis | 300–500 |
| **Jenča–Sarkoci** (`Δ(\widehat{OP(P)}) ≃ ⋁^{e_C} S^{n-3}`) | Nothing usable: no homotopy types of finite complexes, no shellability or discrete Morse theory, no Quillen fibre lemma | statement of its homological content only: `jencaSarkoci_homology` (`H̃_d = 0` for `d ≠ n-3`, `dim H_P = e_C(P)`) | The homotopy statement cannot be expressed in current Mathlib. The homological content needs a combinatorial acyclicity proof, e.g. a shelling or acyclic matching of `Δ(\widehat{OP(P)})`, or a formal transcription of the Jenča–Sarkoci argument. **This is the main obstacle of the topological route.** | 2000–5000+, research-level |
| **`Lie(P) = span{w e_ζ}`** | `Finsupp`, `Finsupp.lmapDomain`, `Finsupp.linearCombination`, `MonoidAlgebra`, `FreeLieAlgebra`, `finRotate`, `Equiv.Perm.sign`, `IsPrimitiveRoot`, `IsPrimitiveRoot.pow_eq_one_iff_dvd`, `IsPrimitiveRoot.geom_sum_eq_zero`. **Absent:** shuffle algebra / shuffle product on `ℂ[S_n]`, Ree's theorem `Lie_n^⊥ = Sh_n`, Wachs's comb basis | `Word`, `Alg` (`ℂ[S_n]` as `Word α →₀ ℂ`), `rot`, `wEζ`, `PLie`, `shuffle`, `Sh`, `W`, `R`, `cyc`, `eC`, `classRot`, `fixedClassSum`, `prefixSet`, `restrict`, `IsCut` | basis `{w_C e_ζ}` of `PLie(P)` (Lemma `lem:liechar`) ~200; contraction operator `E_{a,x}` and `E_{a,x}(Sh) ⊆ Sh` (note's "key tool") ~300; Prop. Φ (Wachs + Ree), only for Theorem S(c),(d) ~1500+ | 500 (milestone) / +1500 (Φ) |
| **`Aut(P)` actions, characters** | `α ≃o α` is a group (`RelIso` group instance, `Mathlib/Algebra/Order/Group/End.lean`), `orderOf`; `Representation`, `Representation.character`, `Representation.char_iso`, `FDRep.character`, `FDRep.char_iso`, `FDRep.char_orthonormal`, `FDRep.simple_iff_char_is_norm_one`, Maschke `MonoidAlgebra.Submodule.exists_isCompl`. **Absent:** "equal characters imply isomorphic" for finite groups over `ℂ` (only iso ⇒ equal characters, `char_iso`) | `relabel`, `relabel_mem_PLie`, `relabel_mem_W`, `relabel_mem_R` (all proved); `actPLie`, `actMP`, `actHP`, `actProper` | equal characters ⇒ isomorphic (Maschke + orthonormality; multiplicities read off by inner products) ~300–500 | 300–500 |

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
| `tr(g|H_P) = (-1)^{n-3}μ(OP(P)^g)` (Lemma `lem:homchar`) | `trace_HP hn g` | the note proves it *from* (A)–(C). Here it is stated outright |
| `tr(g|PLie) = ∑ ζ^{r_g(C)}` (Lemma `lem:liechar`) | `trace_PLie h0 hζ g` | `h0 : 0 < n`, the note's implicit `n ≥ 1` (§4) |
| (A) Jenča–Sarkoci | `jencaSarkoci_homology hn`: `H̃_d = 0` for `d ≠ n-3`, `dim H_P = e_C(P)` | homological content only (all that the proofs use); the homotopy-type statement is not expressible in Mathlib today |
| (B) P. Hall | `hall_mu_eq_reducedEuler L (h : ⊥ ≠ ⊤)` | the hypothesis `0̂ ≠ 1̂` belongs to the *cited result*, not to the main theorem. It is needed: for a one-point `L`, `μ = 1` while `χ̃(∅) = -1` |
| (C) Hopf trace formula | not stated in Lean yet | step 2 (linear algebra; see §1) |
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

## 4. Sorries (5) and gaps

`sorry` occurrences, all in theorem proofs (`grep -rn "^  sorry" PosetJKS`). No definition
depends on a `sorry`: `#print axioms` on `actHP`, `actMP` and `muFixed` shows no `sorryAx`.

| # | Location | Theorem |
|---|---|---|
| 1 | `MainTheorem.lean:40` | `character_identity` |
| 2 | `MainTheorem.lean:49` | `main_iso` |
| 4 | `MainTheorem.lean:74` | `trace_HP` |
| 6 | `MainTheorem.lean:90` | `jencaSarkoci_homology` (cited input A) |
| 7 | `MainTheorem.lean:101` | `hall_mu_eq_reducedEuler` (cited input B) |

(#1 `character_identity` is at `MainTheorem.lean:41`, #2 `main_iso` at `MainTheorem.lean:50`.)
Numbering as in step 1. #5 `trace_PLie` is closed in step 3 (§4.1). #3 `closed_formula` has no
`sorry` of its own since step 4: its second conjunct is `prop_Lside` (closed), and its first
conjunct is `character_identity` multiplied by `sgn(g)` (`sgn(g)² = 1`). So `#print axioms
closed_formula` still lists `sorryAx`, through `character_identity` only (§4.1).

The five M1 sorries of step 1 (`thmS_a`, `thmS_b`, `thmPsi`, `corPsi_bijective`,
`corPsi_equivariant`) are closed. `corPsi` follows from the last two.

**Statement changes.** None in step 4. `InF` moved from `MainTheorem.lean` to `LieSide.lean`
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
  is not formalized.

Remaining for `character_identity` (and through it the first conjunct of `closed_formula`):

1. `lem:interval`(ii), the cycle-count sign identity.
2. The Möbius inversion of `prop:Mside`: the bijection `X(P|_{B₀(x)}, h_x) ≅ {z ∈ X(P,g) : z ≤ x}`
   compatible with (block, induced automorphism), and `[x, 1̂]_X ≅` the divisor lattice of `o`
   for `x ∈ F(P,g)`, so `μ_X(x, 1̂) = μ(o)`.
3. **The base case `lem:small` for `|Q| ≥ 3`**: needs Hall (`hall_mu_eq_reducedEuler`) and the
   Euler-characteristic content of `jencaSarkoci_homology` (or a new elementary proof). This
   blocks #1 (and so the first conjunct of #3) independently of items 1 and 2.
4. ~~`prop:Lside`~~ **done in step 4** (`prop_Lside`, see below).

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

## 5. `#print axioms` (output of `lake env lean scripts/PrintAxioms.lean`)

```
'PosetJKS.character_identity' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.main_iso' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.closed_formula' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.trace_HP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.trace_PLie' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.jencaSarkoci_homology' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'PosetJKS.hall_mu_eq_reducedEuler' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
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
'PosetJKS.Test.fixedClassSum_g3_prim' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.muFixed_chain2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.not_op_chain3_02_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.relabel_wEζ_of_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_comp_bd' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.bd_zero_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.corPsi_bijective_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'PosetJKS.Test.trace_PLie_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The M1 theorems (`thmS_a`, `thmS_b`, `thmPsi`, `corPsi_bijective`, `corPsi_equivariant`,
`corPsi`), `trace_PLie`, the M2 infrastructure (step 3) and `prop_Lside` with the Ramanujan sum
and the `e_C` transport (step 4), with their supporting results,
depend only on the three standard axioms (`isOrderPreserving_inf` does not even use
`Classical.choice`). The remaining
stated theorems also depend on `sorryAx`, from the visible `sorry`s in §4 (`closed_formula`
through `character_identity`). The definitions are
`sorry`-free.
