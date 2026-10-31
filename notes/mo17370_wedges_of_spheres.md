# MO 17370, "Why do wedges of spheres often appear in combinatorics?": what this repo's results say

**Verdict.** We do not answer the MathOverflow question. Two of our results prove the
homotopy type of a whole order complex Δ(Λ̄(V)) as a wedge of spheres: the cone wedge
theorem (Theorem 1 of `notes/general_theory.md`), which reproves Jenča–Sarkoci, and its
oriented-matroid generalization, Theorem 1-OM of `notes/oriented_matroid_cones.md`,
which has its own proof. Their mechanism is a known one, the fiber lemma plus "a
codimension-one skeleton of a contractible cell complex", the same mechanism as Folkman's
theorem. It is applied to a new class, the non-pointed cones. A few further results prove
*contractibility*, also a homotopy type (§1). Everything else we have is
about homology over ℂ (Route C and the Lean formalization), characters (the main theorem,
Theorem G\*), Möbius numbers (cone Zaslavsky, the vanishing criteria, Theorem TA-CR,
the CR_V refutation), or counting (Theorem G). None of those implies a homotopy type. On
the "why" question, the most we can say is this: for one family, the lattices of supports
of convex cones (OP(P) is one of them), the spheres come from convexity. There are also
two equivariant by-products. They concern fixed-point sets, not the representation
sgn ⊗ Lie(P):
- **(E1)** On every zero of the type-A character, the fixed subcomplex is contractible.
  This is Theorem TA-CR together with a cited theorem of Kozlov (1998, Thm 2.4), which
  generalizes Björner 1981, Thm 3.3. The case of unequal cycle lengths was already
  recorded in `notes/fixed_point_mobius_identity.md`, Consequence (iii).
- **(E2)** A candidate theorem, **OPEN**: for connected P, the order complex is
  Aut(P)-homotopy equivalent to a wedge of spheres that Aut(P) permutes freely.

This is a note, not a post. Nothing here has been sent to MathOverflow.

Tags, as in the rest of the repo:
- **PROVEN**: a proof is given, in this note or in the repo note cited.
- **CITED**: a published result. We say whether we re-read it.
- **COMPUTED**: checked by a script (here `compute/mo17370_homotopy_checks.py`; output in
  `compute/output/mo17370_homotopy_checks.txt`).
- **OPEN**: not proved.

"Not found" means not found in the MO thread or in the sources this repo has read. It
is the result of a search, not a claim of novelty. No new literature search was made for
this note beyond the MO thread itself (§0).

Abbreviations:
- [GT] = `notes/general_theory.md`
- [OM] = `notes/oriented_matroid_cones.md`
- [FPM] = `notes/fixed_point_mobius_identity.md`
- [AudMO] = `notes/audit_mo17370.md`, the audit of this note
- [JSR] = `notes/lean_js_route.md`, with its audit [AudJSR] = `notes/audit_lean_js_route.md`
- [Thm] = `notes/poset_jks_theorem.tex`
- [Cit] = `notes/citation_check.md`
- [CVA] = `notes/cr_v_type_a.md`
- [PACVA] = `notes/prior_art_cr_v_type_a.md`
- [CRV] = `notes/conjecture_cr_v.md`
- [PCV] = `notes/per_cone_vanishing.md`
- [VC] = `notes/vanishing_criterion.md`
- [GCD] = `notes/cyclic_sieving_gcd.md`
- L̄ = the proper part of OP(P), and Δ(·) = the order complex.

---

## 0. The question and its answers

The question was asked by Michał Kukieła in March 2010, with the tags co.combinatorics,
at.algebraic-topology and soft-question. It quotes Robin Forman, *A User's Guide to
Discrete Morse Theory*:

> "The fact that wedges of spheres can, in fact, be identified by this numerical data
> partly explains why the main theorem of many papers in combinatorial topology is that a
> certain simplicial complex is homotopy equivalent to a wedge of spheres. Namely such
> complexes are the easiest to recognize. However, that does not explain why so many
> simplicial complexes that arise in combinatorics are homotopy equivalent to a wedge of
> spheres. I have often wondered if perhaps there is some deeper explanation for this."

The question itself: "Why so many simplicial complexes that arise in combinatorics are
homotopy equivalent to a wedge of spheres?" **It is a homotopy question.**

There are five answers. We read all of them and all ten comments, through the Stack
Exchange API on 2026-10-31. The parts we rely on, verbatim:

- **Allen Hatcher** (score 36):
  - "This is indeed a mystery. I presume the question refers to wedges of spheres of
    the same dimension, where there's a simple criterion (n-dimensional and
    (n-1)-connected, for some n)."
  - "Even when it's known that a complex has the homotopy type of a wedge of n-spheres,
    it can be difficult to find cycles representing a basis for the homology."
  - "Ideally such a proof would proceed by showing that after deleting the interiors of
    some top-dimensional cells, the resulting subcomplex was contractible, hopefully by
    an explicit contraction."
  - "It almost seems like a metatheorem in this area that any naturally-defined complex
    is either contractible or homotopy equivalent to a wedge of spheres."
- **Matthew Kahle** (score 23): a probabilistic answer. For random clique complexes,
  homology concentrates in the middle degree; in an update, "for every k ≥ 3, there is a
  range of edge probability so that the random clique complex … is rationally homotopy
  equivalent to a wedge of k-dimensional spheres."
- **Allen Knutson** (score 17): "I think it's because we have well-developed techniques
  with which to prove that this condition holds, and when those fail, people don't put
  that much effort into trying to describe the (more difficult) homotopy types."
- **Gil Kalai** (score 16):
  - "Various simplicial complexes arising in combinatorics have the Cohen Macaulay
    property. Such complexes are always (homologically) a wedge of spheres of the same
    dimension …"
  - "Shellability is an important combinatorial property that again implies the complex
    and all links to be wedge of spheres."
  - Kalai also mentions shifted complexes, and complexes that are not wedges, such as
    the chessboard complex.
- **Dan Ramras** (score 15): Hom complexes that are not wedges of spheres
  (Csorba–Lutz, Schultz, Dochtermann).
- **Comments.**
  - Richard Stanley, under Hatcher's answer: "Wedges of spheres of different dimensions
    do appear naturally in combinatorics in connection with nonpure shellability and
    the sequential Cohen-Macaulay property."
  - Russ Woodroofe, under Kahle's answer: algebraic shifting says "any simplicial
    complex can be slightly perturbed … to become a bouquet of spheres."
  - Ryan Budney, under the question: "Perhaps because the underlying combinatorial data
    either isn't very complicated, or it's not well reflected in the simplicial complex?"

**What the thread does and does not contain.** The work item lists shellability,
lexicographic shellability, discrete Morse theory, Björner–Walker homotopy
complementation, Cohen–Macaulayness and fiber lemmas as "the standard explanations".
The thread itself names only some of them:
- Cohen–Macaulayness and shellability: Kalai.
- Nonpure shellability and sequential CM: Stanley's comment.
- Shifting: Kalai, and Woodroofe's comment.
- The connectivity criterion: Hatcher.
- Discrete Morse theory appears only in the question, through the Forman quote.

Lexicographic shellability, Björner–Walker, Quillen's fiber lemma and the
Björner–Wachs–Welker fiber theorem are **not mentioned** in the thread. Below we treat
them as standard tools, citing them from the repo's sources, not as "MO answers". No
answer claims a general explanation. Hatcher calls it "a mystery", and Knutson's answer
is that it is a selection effect of the available techniques.

## 1. The first distinction: homotopy type vs homology

| Result (where) | What kind of statement it is | Does it prove a homotopy type? |
|---|---|---|
| Jenča–Sarkoci Thm 4.5 ([Cit] §2.1, read verbatim) | Homotopy: Δ(L̄) ≃ ⋁^{e_C(P)} S^{n−3} | Yes. **CITED** (discrete Morse theory) |
| Main theorem (poset JKS) [Thm] | Characters: H_P ≅ sgn ⊗ Lie(P) as Aut(P)-modules, over ℂ | No. It uses only the ℂ-homology consequence of JS ([Cit] §2.1, "How the write-up uses it") |
| `jencaSarkoci_homology` (Lean) and Route C [JSR] | Homology over ℂ: H̃_d(Δ(L̄); ℂ) = 0 for d ≠ n − 3, dim H_P = e_C(P) | No. The argument is chain-level (§2.2) |
| Cone wedge theorem, Theorem 1 of [GT] | Homotopy: Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{d−2} for every top-cone V | **Yes.** PROVEN given the Björner–Wachs–Welker fiber theorem (CITED, re-checked in the repo), which is removable |
| Cone Zaslavsky, Theorem 2 of [GT] | A count: #V = Σ_X m(V_X) (Euler characteristic) | No |
| Theorem G\* ([GT] §1.5) | Homology: the chamber cycles span H̃_{d−2}; an equivariant isomorphism of homology | No. It uses Theorem 1 for concentration |
| Vanishing criteria [VC], [PCV]; Theorem TA-CR [CVA] | Möbius numbers of fixed lattices, χ_V(g) = (−1)^d det(g) μ(Λ(V)^g) | Not by themselves. Combined with a cited theorem they give contractibility of fixed subcomplexes on zeros (§2.5) |
| CR_V rank-4 refutation [CRV] | A lattice with μ = 0 and every element complemented | No. We add a homotopy computation: the fixed subcomplex is still contractible (§2.6, COMPUTED) |
| Theorem G [GCD] | Nonvanishing of a fake-degree polynomial at roots of unity (cyclic sieving) | No. There is no topology in it |

**PROVEN (by reading the cited notes; corrected after [AudMO] §2):** among our own
results, the ones that prove the homotopy type of a whole order complex Δ(Λ̄(V)) are:
- Theorem 1 of [GT] and Corollary 1.4 of [GT] (JS reproved), in the realizable setting.
- Theorem 1-OM of [OM]: Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{r−2} for every T-convex set V of a simple
  oriented matroid, realizable or not. It is a generalization of Theorem 1 with its own
  proof (Lemma 2.1-OM, gluing, simple connectivity of tope boundaries), not a corollary.
  Status: PROVEN for r ≤ 4; for r ≥ 5 it also uses shellability (BLSWZ, CITED).

Several further results prove *contractibility*, which is also a homotopy type:
- [GT] Lemma 0.2: C ∩ S is contractible or a sphere (a standard ingredient).
- [OM] Lemma 0.2-OM: the closed face complex of a T-convex set is contractible or
  ≃ S^{r−1}, with a new proof by deletion and Quillen's fiber lemma.
- [FPM] Consequence (iii), and the remark after the fixed-point identity in [Thm]: for
  unequal cycle lengths, the proper part of OP(P)^g is contractible (Björner–Walker,
  CITED). This is a special case of (E1).
- (E1) of this note (§2.5): the fixed subcomplex is contractible on every type-A zero.
- §2.6 of this note: the fixed subcomplex of the rank-4 CR_V counterexample is a tree.

Everything about Route C and the Lean formalization is homology over ℂ.

## 2. Result by result

For each result we say what it gives on MO 17370, using the work item's three labels: a
new explanation, a known explanation in new clothing, or nothing.

### 2.1 The main theorem and the Jenča–Sarkoci input

- **The statement.** For every finite poset P on n ≥ 3 points, H_P ≅ sgn ⊗ Lie(P) as
  Aut(P)-modules, together with the character formula ([Thm], thm:main). **PROVEN +
  audited**, given three cited inputs.
- **The Jenča–Sarkoci input.** [Cit] §2.1 reads JS Thm 4.5 verbatim: "Δ(Ô(P)) is
  homotopy equivalent to a wedge of e_C(P) spheres of dimension n − 3." That is a
  homotopy statement, proved by JS with discrete Morse theory: [JSR] §2.2 describes
  their Thm 3.8 matching, built with Kozlov's patchwork theorem. **CITED.** The main
  theorem uses only its consequence that reduced homology over ℂ is concentrated in
  degree n − 3, with dimension e_C(P). [Cit] states this explicitly.
- **On MO 17370: nothing.**
  - The wedge of spheres in this setting is JS's theorem.
  - JS's proof is discrete Morse theory, the tool of the Forman quote that the question
    starts from. A known explanation, and not ours.
  - The main theorem takes the wedge as input and computes the representation on top
    homology. It does not explain the wedge.

### 2.2 Route C and the Lean `jencaSarkoci_homology`

**What Route C proves.** [JSR] §3, PROVEN + audited:
- **Lemma K.** An explicit chain contraction s, with ∂s + s∂ − id lowering a
  filtration. So the augmented chain complex of Δ(Q) is exact.
- **Proposition C.** The strip/cons maps split C(L̄)/C(Q) into suspended interval
  complexes.
- **Theorem V.** H̃_d(Δ(L̄)) = 0 for d ≠ n − 3, by induction on n.

The Lean code formalizes exactly this, over ℂ (`redHom` is a ℂ-vector space).

**Chain level or space level? Chain level.**
- Every object in [JSR] §3 is a chain complex of vector spaces: `Chains`, `bd`,
  `redHom`, s, `strip_b`, `cons_b`. The conclusion is that a quotient vector space
  vanishes.
- No continuous map, no CW structure and no homotopy of spaces appears. [JSR] says so
  itself: "No shelling, no Morse lemma, no topology", and "The homology-level proof
  below is self-contained and needs no topology."
- **PROVEN (by inspection of [JSR] §3).**

**What the homotopy versions would be.** Both are **CITED**, from [JSR] §2.5 and its
audit [AudJSR] G3. Neither source was re-read in the repo.
- *Lemma K at space level* is Quillen's order-homotopy lemma. In the form of Björner,
  *Topological methods*, Cor. 10.12: a monotone p ≤ id makes Δ(p(R)) a deformation
  retract of Δ(R). Here p(R) = R_{≤t} is a cone, so Δ(Q) is contractible.
- *Route C as a whole, at space level* is the Björner–Walker homotopy complementation
  formula:
  - The complements of π_a are the atoms π_ab, an antichain.
  - Δ(0̂, π_ab) = ∅.
  - So BW gives Δ(L̄) ≃ ⋁_b Σ Δ((π_ab, 1̂)) ≅ ⋁_b Σ Δ(L̄(P/π_ab)).

**A homotopy proof is one step away, but the repo does not write it.** Suppose BW holds
in the form above (CITED, not re-read). Induction on n then gives
Δ(L̄) ≃ ⋁_b Σ ⋁^{e_C(P/π_ab)} S^{n−4} = ⋁^{Σ_b e_C(P/π_ab)} S^{n−3}, and
Σ_b e_C(P/π_ab) = e_C(P) is the recursion `eC_rec` (Lemma C of `notes/mu_op_elementary.md`,
PROVEN + formalized). No Hurewicz or Whitehead step is needed, because the suspension of
a wedge is a wedge of suspensions. **Status: CITED (BW) plus a two-line induction.** It is
not written in the repo outside this paragraph, and not formalized.

**Integral homology.** The chain contraction s of Lemma K has coefficients ±1, and
Proposition C divides by nothing. So the argument of [JSR] §3, read over ℤ, gives
H̃_*(Δ(L̄); ℤ) concentrated in degree n − 3. That group is free: Δ(L̄) has no
(n − 2)-simplices, so H̃_{n−3} is a subgroup of a free chain group.
- **Status: PROVEN by inspection here, unaudited, not formalized.** The Lean statement
  is over ℂ only.
- Even over ℤ this is not a homotopy type. Hatcher's criterion needs (n − 4)-connectivity
  of an (n − 3)-dimensional complex, which includes π_1 = 1 when n ≥ 5. π_1 is not a
  homological invariant, and Route C says nothing about it.

**On MO 17370: a known explanation in new clothing.**
- Route C is the Björner–Walker / Quillen argument run on chains, and it is the same
  induction as JS's matching ([JSR] §2.2: "Route C below is the same induction").
- It is strictly weaker than JS. It proves homology concentration, not a homotopy type.
- **The Lean formalization proves no homotopy statement. Nothing in `lean/` proves
  a homotopy type.**

### 2.3 The cone wedge theorem and cone Zaslavsky ([GT] §§1.1–1.3)

**Theorem 1.** Every top-cone V of a real central essential arrangement of rank d has
Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{d−2} with m(V) ≥ 1. **PROVEN + audited**, given the
Björner–Wachs–Welker poset fiber theorem (CITED, re-checked in the repo; removable by
[GT]'s Prop. A). **This is a genuine homotopy statement.** The proof ([GT] §1.1, Steps 1–5)
runs as follows:
1. The face map f : Q′ → Λ̄(V), F ↦ span F, has fibers that are spheres or contractible.
   So Δ(Λ̄(V)) is a retract of a wedge containing Δ(Q′), by the fiber theorem.
2. Δ(Q′) ≅ X, the (d − 2)-skeleton of Z = |V| ∩ S^{d−1}. Here Z is a regular CW complex,
   contractible or a sphere, and its (d − 1)-cells are the chambers of V.
3. So X is (d − 3)-connected, with H̃_{d−2}(X) free. These properties pass to the
   retract, which is (d − 2)-dimensional.
4. Hurewicz and Whitehead give the wedge for d ≥ 4. The cases d ≤ 3 are done by hand.

**Corollary 1.4.** The braid case, Λ(C_P) ≅ OP(P)^op: Δ(L̄) ≃ ⋁^{e_C(P)} S^{n−3}.
Jenča–Sarkoci, reproved. **PROVEN** (given the fiber theorem).

**Theorem 2 (cone Zaslavsky).** #V = Σ_{X ⊆ lin V} m(V_X). **PROVEN + audited**, an
instance of Zaslavsky 1977 Thm 1.2. It is an Euler-characteristic count, not a homotopy
statement.

**On MO 17370: a known explanation in new clothing, applied to a new class.**
- *Known mechanism.* The wedge comes from a contractible (or spherical) regular cell
  complex whose top cells are the chambers. Removing the top cells leaves a
  (d − 3)-connected skeleton, and the lattice is a retract of that skeleton, by a fiber
  lemma.
  - For V = all chambers this is Folkman's theorem ([GT] §1.1, "Specializations").
  - For pointed V it is Quillen's fiber lemma alone.
  - The tools are the fiber lemma and the connectivity criterion. The connectivity
    criterion is the one Hatcher states ("n-dimensional and (n-1)-connected").
- *New class.* Theorem 1 for non-pointed cones was "not found" ([GT] §1.2, citing
  `notes/novelty_general_theory.md` §2). This is a search result.
- *Relation to Hatcher's "ideal" proof.* Hatcher asks for a proof that "after deleting
  the interiors of some top-dimensional cells, the resulting subcomplex was
  contractible". Theorem 1 runs the other way round. The complex X of interest *plus*
  the chamber cells is the contractible complex Z, so X is Z with the interiors of its
  top cells deleted. This gives one sphere per chamber, up to the lineality correction
  m(V) ≤ #V.
  - The contraction of Z is explicit: the straight-line homotopy to an interior point,
    [GT] Lemma 0.2.
  - The passage from X to Δ(Λ̄(V)) is not explicit. It is a fiber theorem, or the
    retraction of [GT]'s Prop. A.
  - **PROVEN** ([GT]). The comparison with Hatcher's wording is ours.
- *Hatcher's second point,* "it can be difficult to find cycles representing a basis
  for the homology". Here we do have explicit cycles:
  - The chamber cycles ρ_C span H̃_{d−2} for every cone (Theorem G\*, [GT] §1.5,
    PROVEN given Brown, audited).
  - In the poset case the splitting cycles give an explicit basis (Theorem S of [Thm],
    PROVEN + audited, given Wachs).
  - This answers Hatcher's practical complaint *for this family*. It says nothing about
    the general "why".
- *What it does say about "why".* [GT] §3 records the relevant negative fact: "Any
  meet-closed family in Π_n containing 0̂ and 1̂ is a lattice, and such lattices can have
  arbitrary homotopy type. So 'closure system' is too weak to imply a wedge of spheres
  … What makes OP(P) special is that it is Λ(C_P), a lattice of supports of a convex
  cone." So for OP(P) our answer to "why a wedge?" is **convexity**: L̄ is homotopy
  dominated by the codimension-one skeleton of a contractible cell complex. That is a
  reason for one family. It is not a reason for Forman's general phenomenon, and the
  mechanism is the classical one for geometric lattices.

### 2.4 Theorem G\* and the equivariant structure (sgn ⊗ Lie(P))

**The statements.**
- Theorem G\* ([GT] §1.5): the chamber cycles of V span H̃_{d−2}(Δ(Λ̄(V))), and
  H̃_{d−2} ≅ det ⊗ (Γ_V + Lune)/Lune as Stab_G(V)-modules. **PROVEN given Brown,
  audited.**
- In the braid case this gives the sgn twist of H_P ≅ sgn ⊗ Lie(P).

**Does the equivariant structure add an explanation the standard answers lack?**
**Not for the existence of the wedge.**
- The isomorphism H_P ≅ sgn ⊗ Lie(P) identifies the top homology as a representation.
- It *assumes* that the homology is concentrated in one degree. Through the Hopf trace
  formula ([JSR] §2.4(b)), concentration is what lets the character determine the module.
- So the representation theory sits downstream of the wedge, not upstream. **PROVEN
  (logical dependency, [Thm] and [JSR] §2.4).**
- None of the MO answers discusses group actions or representations on the top homology.
  The equivariant theme is "not found in the answers".

**What the equivariant data does give at the level of spaces.** It concerns fixed-point
sets, by the Lefschetz/Hopf identity. For an order-preserving g, the fixed subcomplex
Δ(L̄)^g equals Δ(L̄^g), because g fixes a chain setwise only if it fixes it pointwise
(`notes/audit_literature_novelty_jks_maps.md` row 21; [Thm] eq. homchar). The character
value χ(g) is ± the reduced Euler characteristic of that fixed subcomplex. This gives
one consequence, (E1) in §2.5, and suggests one candidate, (E2) in §3, which is OPEN.

**Does the equivariant structure realize the wedge equivariantly, with G permuting the
spheres? In general, no.** Example: P = antichain on 3 points, G = S_3.
- L̄ = Π̄_3 is three points, permuted by S_3, and H̃_0 is the 2-dimensional standard
  representation.
- Suppose H̃_0 were a signed permutation module on two lines. A 3-cycle permutes 2 lines
  with an order dividing 3, so it fixes both. It then acts on each line by a scalar ±1
  whose cube is 1, so by +1, and has trace 2. But the standard representation has trace
  −1 at a 3-cycle.
- So no S_3-equivariant wedge of two 0-spheres (each line spanned by one sphere, G
  permuting spheres up to orientation) realizes Π̄_3.
- **PROVEN** (the computation above). In general sgn ⊗ Lie(P) is induced from a
  non-trivial cyclic character (Klyachko for the antichain), not from a sign character.
- So "G permutes the spheres" can hold only when sgn ⊗ Lie(P) is a signed permutation
  module. Free modules are one such case; see (E2).

### 2.5 The vanishing criteria and Theorem TA-CR

**The statements.**
- [VC] and [PCV] give criteria for χ_V(g) = (−1)^d det(g) μ(Λ(V)^g) = 0. **PROVEN +
  audited.**
- Theorem TA-CR ([CVA]): on every cone C_P of the braid arrangement and for every
  g = ±τ, χ_{C_P}(g) = 0 iff OP(P)^τ has an element with no complement, and the element
  is explicit. **PROVEN + audited.**
- These are statements about Möbius numbers, that is, Euler characteristics of fixed
  subcomplexes. By themselves they imply no homotopy type.

**(E1) A homotopy reading, on type A.**
- *Statement.* For every poset P on n ≥ 3 points and every g = ±τ with g C_P = C_P:
  χ_{C_P}(g) = 0 iff the fixed subcomplex Δ(Λ̄(C_P))^g ≅ Δ(proper part of OP(P)^τ) is
  contractible.
- *Proof.*
  - "If": a contractible complex has reduced Euler characteristic 0, and
    χ = ± that Euler characteristic.
  - "Only if": TA-CR gives an element of OP(P)^τ with no complement. The proper part of
    a finite lattice with an uncomplemented element is contractible, indeed
    collapsible. Primary source: Kozlov, *Order complexes of noncomplemented lattices
    are nonevasive*, Proc. AMS 1998 (arXiv:math/9704225), Thm 2.4, read in full by
    [AudMO] §4.1 (arXiv version): for a finite lattice L, x ∈ L̄ and P = L ∖ Co(x),
    Δ(P̄) is nonevasive. Taking x with Co(x) = ∅ gives P = L, so Δ(L̄) is collapsible.
    No modularity or rank hypothesis is needed. Kozlov's theorem generalizes Björner 1981,
    Thm 3.3; see also Björner–Walker 1983. **Neither Björner 1981 nor Björner–Walker 1983
    was obtained**; they are cited via Kozlov.
  - The order reversal does not come from the sign of g. For both signs, Λ(C_P)^g is
    dual to OP(P)^τ ([CVA] S1). (For g = −τ, τ is an anti-automorphism of P, but it
    still acts on OP(P) = OP(P^op) as a lattice automorphism.) Order complexes and
    complementation are self-dual, so the duality changes nothing.
- *Status:* **PROVEN given TA-CR (PROVEN + audited) and Kozlov 1998 Thm 2.4 (CITED,
  read in full in [AudMO]).**
- *Check:* **COMPUTED** in §5 [TA] for n ≤ 6 (607 zeros). Every zero has an acyclic
  fixed subcomplex, and its Stong core is a point, which certifies contractibility
  directly, without TA-CR or Kozlov's theorem. [AudMO] §4.3 reproduces this with
  independent code.
- *Prior record:* the special case of unequal cycle lengths (g = +w) is already in [FPM]
  Consequence (iii) and in the remark after the fixed-point identity in [Thm], via
  Björner–Walker.

**On MO 17370: a known explanation in new clothing.**
- Hatcher's "metatheorem" is a dichotomy ("either contractible or homotopy equivalent to
  a wedge of spheres"). (E1) identifies the contractible branch of that dichotomy on the
  fixed subcomplexes of type A: the zero-character cases are exactly the contractible
  ones. It says nothing about the nonzero cases; the wedge branch is **OPEN**.
- The mechanism, Crapo complementation upgraded to contractibility by Björner,
  Björner–Walker and Kozlov, is a standard tool.
- The new input is TA-CR's "only if" direction (not found in the sources [PACVA] read).
- The wedge branch is **OPEN** here. In the nonzero cases, we have not
  proved that the fixed subcomplex is a wedge of spheres. §5 [TA]: for n ≤ 6, all 497
  nonzero fixed subcomplexes have homology (mod p) in a single degree (COMPUTED), so
  they are at least homology wedges of spheres of one dimension. The homotopy type is
  not computed.

### 2.6 The CR_V rank-4 refutation

**The statement.** [CRV] §0: a 12-hyperplane arrangement in R^4, g = diag(−1, −1, 1, 1),
and a cone V with a 9-element Λ(V)^g. Every element is complemented, and
μ = 0 = χ_V(g). **PROVEN + audited (refutation holds).** So Crapo complementation does
not explain every zero of χ_V(g).

**A homotopy computation on top of it (new here).** The proper part of the 9-element
lattice has 7 elements: the lines a, b, c and the planes L, B, C, D, with
a < L, B; b < L; c < B, C, D ([CRV] §0.2). Its order complex is the graph with these 7
vertices and the 6 edges a–L, a–B, b–L, c–B, c–C, c–D.
- The graph is connected (b–L–a–B–c–C and c–D), and has 7 vertices and 6 edges. So it is
  a tree, and contractible. **PROVEN** (by hand, from [CRV] §0.2).
- Equivalently, by beat points: remove D, C and b; then L and c become beat points;
  removing them leaves the single edge a–B, and removing one of a and B leaves one point.
- §5 [R4] reports the same check on all 36 counterexample pairs of the arrangement.

**On MO 17370: nothing new for the question.** One clarification about our own
programme:
- The refutation shows that the *lattice-theoretic* certificate (an uncomplemented
  element) fails in rank 4.
- On the pairs we computed, it does not show that the *topological* dichotomy
  ("χ_V(g) = 0 iff the fixed subcomplex is contractible") fails.
- The fixed subcomplex of the counterexample is contractible for a different reason:
  beat points, not complements.
- So the topological form of CR_V, call it **CR_V^top: χ_V(g) = 0 iff Δ(Λ̄(V))^g is
  contractible**, is **not refuted** by [CRV] §0. It holds on type A by (E1), and on the
  36 rank-4 counterexample pairs by §5. In general it is **OPEN**.

### 2.7 Theorem G (cyclic sieving)

**The statement.** For e ≥ 6 with e > max k_i, X_P(e^{2πi/e}) ≠ 0, with one exception
([GCD]). **PROVEN + audited.** X_P is a fake-degree (Molien-type) polynomial in the
cyclic sieving set-up for Cyc(P). The proof is analytic: the terms lie on four rays, and
an inequality bounds them.

**On MO 17370: nothing.** Theorem G has no topological content and does not mention
Δ(L̄). Its only link to the wedge is the count e_C(P), and that count is an input to
Theorem G, not a consequence of it.

## 3. The candidate equivariant statement (E2), OPEN

The equivariant structure gives one thing that the MO answers and the sources read lack:
a candidate *equivariant* homotopy type. It covers only the case where the representation
is free.

**Candidate Theorem E.** Assume:
- A is a finite real central essential arrangement of rank d ≥ 3.
- V is a *pointed* top-cone.
- G is a finite group of linear maps preserving A and V that acts *freely* on the
  chambers of V.

Then Δ(Λ̄(V)) is G-homotopy equivalent to the wedge ⋁_{C ∈ V} S^{d−2}, with G permuting
the summands as it permutes the chambers. In particular H̃_{d−2}(Δ(Λ̄(V)); ℤ) is a
free ℤG-module.

**Poset case.** Let P be connected, n ≥ 4, and G = Aut(P).
- C_P is pointed after essentialization, since lin C_P = ℝ·1.
- Aut(P) acts freely on Lin(P) ([Thm], cor:connected).
- So Theorem E would give Δ(L̄) ≃_{Aut(P)} ⋁_{w ∈ Lin P} S^{n−3}.
- This is a space-level form of the corollary "H_P is a free Aut(P)-module" ([Thm],
  cor:connected) and of "μ(OP(P)^g) = 0 for g ≠ 1".

**Proof sketch, with the gaps marked.**
1. *f is a G-homotopy equivalence.* Let f : Q′ → Λ̄(V) be the face map of [GT] §1.1;
   it is G-equivariant. Take Y ∈ Λ̄(V) and H ≤ G_Y.
   - The fiber f^{-1}(Λ̄_{≤Y}) realizes |V| ∩ Y ∩ S.
   - Its H-fixed set is |V| ∩ Y ∩ Fix(H) ∩ S. That set is nonempty: the H-average of a
     nonzero point of a pointed cone is nonzero. It is also convex-on-the-sphere, so
     contractible.
   - The equivariant Quillen fiber lemma (Thévenaz–Webb 1991, *Homotopy equivalence of
     posets with a group action*, JCTA 56; **CITED from memory, not re-read**) then
     makes f a G-homotopy equivalence Δ(Q′) ≃_G Δ(Λ̄(V)).
   - *Gap:* the identification of the fixed set of |Δ(fiber)| with the geometric fixed
     set needs an equivariant homeomorphism |Δ(face poset)| ≅ |V| ∩ Y ∩ S. Barycenters
     of normalized ray generators should give one; this is not written.
2. *Fixed sets of X are contractible.* Let X = Δ(Q′), the (d − 2)-skeleton of
   Z = |V| ∩ S, and take H ≠ 1.
   - H fixes no chamber, so no interior point of a chamber is H-fixed, and Z^H ⊆ X.
   - Hence X^H = Z^H = |V| ∩ Fix(H) ∩ S. This is nonempty and contractible, as in step 1.
3. *Map a free wedge into X.*
   - Pick a base point x_0 ∈ X^G. It exists, by averaging.
   - X is (d − 3)-connected ([GT] Step 4), and H_{d−2}(X) ≅ ℤ^{chambers} with G acting
     by signed permutations. Since the action is free, this is a free ℤG-module, with
     basis the boundaries of one chamber per orbit.
   - Represent each basis element by a based map S^{d−2} → X (Hurewicz, d ≥ 4) and
     extend G-equivariantly over the free G-wedge W.
4. *Conclude.*
   - For H ≠ 1: W^H = {x_0} and X^H is contractible, so f^H is a weak equivalence.
   - For H = 1: the map is an isomorphism on H_{d−2} between simply connected complexes
     with free homology in one degree, so it is a homotopy equivalence (Whitehead).
   - The equivariant Whitehead theorem for finite G-CW complexes (CITED, tom Dieck,
     *Transformation Groups*, II.2.7; from memory, not re-read) gives W ≃_G X.
   - Combined with step 1: W ≃_G Δ(Λ̄(V)).

**What remains to prove.**
- (i) The equivariant homeomorphism in step 1, and a G-CW structure on X. Use the
  barycentric subdivision.
- (ii) A re-read of Thévenaz–Webb and of the equivariant Whitehead theorem, with exact
  statements.
- (iii) The low-rank cases. For d = 3 the wedge is a graph, and simple connectivity is
  not available, so an equivariant argument for graphs is needed. For d = 2 it is a set
  of points.
- (iv) A literature search. Equivariant homotopy types of partition-type complexes are
  studied (from memory: Arone–Dwyer–Lesh on fixed points of Π̄_n under p-subgroups).
  Nothing was searched for this note.
- (v) An independent audit.

**Status: OPEN** (a proof sketch, unaudited, with no prior-art search).

**What Theorem E would and would not explain.**
- It would explain the wedge *and* the free action at once, from convexity plus a free
  action on chambers.
- It does **not** reach the interesting representation theory. That appears exactly
  when P is disconnected (the cone is not pointed) and Lie(P) is not free. There, §2.4
  shows that "G permutes the spheres" is false in general (Π̄_3).
- The equivariant homotopy type is then governed by the fixed subcomplexes, about which
  we know only (E1): contractible on zeros, in type A.

**The general equivariant question is OPEN.** For disconnected P, describe the
Aut(P)-homotopy type of Δ(L̄), that is, the fixed subcomplexes Δ(L̄^g) up to homotopy,
in the nonzero cases.

## 4. Do we explain *why* the spheres appear?

**For a single family, partly. For the MO question, no.**
- **For OP(P) and every cone lattice Λ(V):**
  - The reason is convexity, by Theorem 1 of [GT]. The lattice is (homotopy-)dominated
    by the codimension-one skeleton of a contractible regular cell complex whose top
    cells are the chambers, and that skeleton is a wedge of spheres for elementary
    reasons. The spheres correspond to chambers, minus a lineality correction counted by
    cone Zaslavsky.
  - This is the Folkman / fiber-lemma explanation, extended from all chambers and
    pointed cones to every cone. It is a known explanation in new clothing.
  - [GT] §3 records that the purely lattice-theoretic property (a closure system in
    Π_n) does not suffice. So the reason is geometric, not order-theoretic.
- **For OP(P), as an analogue of Π_n:** we also know four other standard routes to the
  wedge. JS use discrete Morse theory. Schweig–Woodroofe show CL-shellability via
  comodernism (CITED in [JSR] §2.1, not re-read). There is Björner–Walker complementation
  (§2.2), and the BWW fiber theorem ([GT]). This fits Knutson's answer: OP(P) is a wedge,
  and every well-developed technique proves it. It does not tell us why OP(P) "had to
  be" a wedge, beyond convexity.
- **For Forman's general question:** nothing. None of our results applies to complexes
  outside cone lattices and their fixed sublattices. [GT] §3 also says that the nearest
  lattice-theoretic generalization fails.

## 5. Computations

`compute/mo17370_homotopy_checks.py` (new; it imports `conjecture_cr_v.py` and
`cr_v_type_a.py`). Output: `compute/output/mo17370_homotopy_checks.txt`.

**Method.**
- Reduced Betti numbers of order complexes are ranks mod 2^31 − 1. A mod-p Betti number
  of 0 is 0 over ℚ.
- **Stong cores:** repeated deletion of beat points. A beat point is an element whose
  strict down-set has a maximum, or whose strict up-set has a minimum. Deleting one
  preserves the homotopy type of the order complex (Stong 1966; Barmak, LNM 2032, ch. 1;
  CITED, not re-read). A one-point core certifies contractibility.

Run: `cd compute && python3 mo17370_homotopy_checks.py --nmax 6` (about 15 min on one
core; the [R4] sweep is most of it). Output archived in
`compute/output/mo17370_homotopy_checks.txt`, ending `ALL CHECKS PASSED`.

- **[CTL] controls** (all pass): B_3 (proper part S^1: Betti 1 in degree 1, Stong core
  all 6 points); a chain (core one point); the 8-element complemented lattice with
  μ = 0 of `notes/prior_art_per_cone_vanishing.md` §3.2 (acyclic, core one point); a crown (S^1, no beat point, core
  stays 4 points: the core routine does not over-shrink).
- **[TA]** every poset with 3 ≤ n ≤ 6 up to isomorphism, every automorphism and
  anti-automorphism τ up to Aut(P)-conjugacy, M = OP(P)^τ. 1,104 pairs.
  - τ = id (and −id for the antichain): 406/406 have reduced Betti numbers e_C(P) in
    degree n − 3 and 0 elsewhere (positive control: Jenča–Sarkoci).
  - Zeros (μ(M) = 0): 607. All 607 have acyclic Δ(M̄), and all 607 have a one-point
    Stong core, so Δ(M̄) is contractible. **COMPUTED.** This is (E1) on n ≤ 6,
    checked without TA-CR or Kozlov's theorem.
  - Nonzeros: 497. All 497 have reduced homology (mod p) concentrated in a single
    degree. **COMPUTED.** So on n ≤ 6, every fixed subcomplex is contractible or a
    homology wedge of spheres of one dimension: the homological form of Hatcher's
    "metatheorem", on the fixed subcomplexes. Whether the nonzero ones are homotopy
    wedges is **OPEN** (not checked: no π_1 or Stong-core computation is claimed for
    them).
- **[R4]** the C6 × C4 arrangement of [CRV] §0 (12 hyperplanes in R^4), every class
  representative g and every g-stable top-cone: 38,400 pairs, 60 zeros (both numbers
  match `compute/output/conjecture_cr_v.txt`).
  - The 36 CR_V counterexample pairs (μ = 0, every element complemented): 12 with
    |Λ(V)^g| = 9, 12 with 10, 12 with 11. All 36 have acyclic Δ(M̄) and a one-point
    Stong core: **contractible. COMPUTED.**
  - The other 24 zeros (with an uncomplemented element): all 24 contractible by the
    Stong core, as Kozlov's theorem (generalizing Björner 1981) predicts (control).
  - So CR_V^top ("χ_V(g) = 0 iff the fixed subcomplex is contractible") holds on all 60
    zeros of this arrangement, including the 36 where CR_V fails. Its general status is
    **OPEN**.

## 6. Summary table

| Our result | Proves a homotopy type? | On MO 17370 |
|---|---|---|
| Main theorem H_P ≅ sgn ⊗ Lie(P) | No (characters over ℂ) | Nothing. It identifies the representation on a wedge that JS provide |
| Jenča–Sarkoci input | Yes, but CITED (discrete Morse) | A known explanation, not ours |
| Route C / Lean `jencaSarkoci_homology` | No. Chain-level, over ℂ. Over ℤ by inspection (unaudited); no π_1 | A known explanation in new clothing (BW / Quillen on chains); weaker than JS |
| Cone wedge theorem (Theorem 1) | **Yes** (PROVEN given BWW, removable) | A known explanation in new clothing (fiber lemma + skeleton of a contractible complex, as for Folkman), on a new class (non-pointed cones, not found) |
| Cone Zaslavsky (Theorem 2) | No (a count) | Nothing beyond counting the spheres |
| Theorem G\* | No (homology, equivariant) | Explicit spanning cycles, which answers Hatcher's practical point for this family; no "why" |
| Vanishing criteria, TA-CR | No by themselves. With Kozlov 1998 Thm 2.4 (CITED, read): fixed subcomplexes contractible on every type-A zero (E1) | A known explanation in new clothing; identifies the contractible branch of Hatcher's "metatheorem" on fixed subcomplexes (the wedge branch is OPEN) |
| CR_V rank-4 refutation | No. Its fixed subcomplex is a tree (contractible; §2.6, §5) | Nothing for MO. CR_V^top is not refuted (OPEN) |
| Theorem G | No | Nothing |
| Candidate Theorem E (pointed cones, free action) | Would give a G-homotopy type | A candidate equivariant explanation. **OPEN** |
