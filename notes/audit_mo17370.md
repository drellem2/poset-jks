# Audit of `notes/mo17370_wedges_of_spheres.md` (MO 17370, wedges of spheres)

This is an independent, adversarial audit of the note [MO] =
`notes/mo17370_wedges_of_spheres.md`. The checks below were rebuilt from the definitions
and from primary sources where these could be obtained. The new script
`compute/audit_mo17370.py` imports nothing from the repository.

## Verdicts

| # | Claim in [MO] | Verdict |
|---|---|---|
| V1 | Headline: our work does not answer MO 17370 | **HOLDS** |
| V2 | "Among our own results, only Theorem 1 of [GT] and its corollaries prove a homotopy type" (§1, headline) | **FIXABLE.** True for the homotopy type of a whole complex Δ(Λ̄(V)) in the realizable setting. As written it is too strong: Theorem 1-OM is a generalization with its own proof, not a corollary, and (E1), §2.6 and two earlier notes prove contractibility statements (§2 below) |
| V3 | (E1), §2.5: on every braid cone and every g = ±τ, χ_{C_P}(g) = 0 iff the fixed subcomplex is contractible | **HOLDS.** The cited input is now confirmed from a primary source (Kozlov 1998, Thm 2.4, read in full). Björner 1981 and Björner–Walker 1983 could not be obtained. The "order reversal for g = −τ" sentence is misattributed but harmless (FIXABLE wording). Recomputed independently for n ≤ 6, with a positive control |
| V4 | §2.2: Route C read over ℤ gives integral homology concentrated in degree n − 3 and free ("PROVEN by inspection, unaudited") | **HOLDS.** Every step was re-read. No step divides or uses a field. Consistent with mod-2, mod-3 and mod-large-p Betti numbers on all 402 posets with 3 ≤ n ≤ 6 |
| V5 | §2.6: the fixed complex of the rank-4 CR_V counterexample is a tree, hence contractible | **HOLDS.** Rebuilt from the coordinates of [CRV] §0.2 by exact rank computations |
| V6 | §0: quotations from the MO thread | **HOLDS.** All five answers, all ten comments and the question were re-fetched and compared. Every quotation checked is verbatim |
| V7 | §0, §2: the "known explanation in new clothing" framing | **HOLDS**, with one overstatement: "(E1) is Hatcher's metatheorem, half-verified" (FIXABLE wording, §6) |
| V8 | Candidate Theorem E is labelled OPEN everywhere | **HOLDS** (one loose word, §7) |

Abbreviations follow [MO]. [GT] = `notes/general_theory.md`, [OM] =
`notes/oriented_matroid_cones.md`, [JSR] = `notes/lean_js_route.md`, [CVA] =
`notes/cr_v_type_a.md`, [CRV] = `notes/conjecture_cr_v.md`, [FPM] =
`notes/fixed_point_mobius_identity.md`, [Thm] = `notes/poset_jks_theorem.tex`.

---

## 1. V1: the headline verdict

MO 17370 asks why so many complexes in combinatorics are *homotopy equivalent* to wedges of
spheres (question text re-fetched, §5). The repository has no result about complexes outside
cone lattices, their oriented-matroid analogues and their fixed sublattices. The one
homotopy theorem about whole complexes, [GT] Theorem 1 with [OM] Theorem 1-OM, runs on the
fiber lemma plus the connectivity of a codimension-one skeleton. That is the classical
Folkman mechanism, as [MO] §2.3 says. **"We do not answer the question" HOLDS.**

## 2. V2: "only Theorem 1 proves a homotopy type"

The claim is about every result in the repository. I grepped all of `notes/`, `lean/` and the
`.tex` files for homotopy, contractible, collapse, nonevasive, Stong and ≃, and read every
hit that is a claim rather than a citation. The homotopy-level statements I found are these.

| Where | Statement | Homotopy level? | Mentioned in [MO]? |
|---|---|---|---|
| [GT] Thm 1, Cor. 1.4 | Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{d−2}; JS reproved | yes | yes |
| [GT] Lemma 0.2 | C ∩ S is contractible or a sphere | yes (an ingredient, standard) | implicitly |
| [OM] Lemma 0.2-OM | closed face complex of a T-convex set is contractible or ≃ S^{r−1}; new proof by deletion and Quillen | yes | no |
| [OM] Thm 1-OM | Δ(Λ̄(V)) ≃ ⋁^{m(V)} S^{r−2} for every simple OM, realizable or not. PROVEN for r ≤ 4; for r ≥ 5 it uses shellability (CITED) | yes | as "the oriented-matroid version", counted as a corollary |
| [FPM] Consequence (iii); [Thm] remark after the fixed-point identity | in the unequal-cycle-length case, the proper part of OP(P)^g is contractible (Björner–Walker, CITED) | yes (a special case of (E1)) | no |
| [MO] (E1) | contractible fixed subcomplex on every type-A zero | yes | yes, as a "by-product" |
| [MO] §2.6 | the counterexample's fixed complex is a tree | yes | yes |
| [MO] §2.2 | BW plus a two-line induction gives JS | yes, CITED + induction, explicitly not written elsewhere | yes |
| `lean/` | `ConeRetract.lean` etc. | no. "homotopy" there means a *chain* homotopy s with ∂s + s∂ = id + (lower filtration) | yes ("nothing in `lean/` proves a homotopy type": HOLDS) |

Also checked, with nothing at homotopy level: Route C (§3 of this note), the character
theorems, Theorem G\*, the vanishing criteria, Theorem G, `observation_cc.md`,
`cone_lune_lie_theory.md`, `per_cone_vanishing.md` and the moonshine notes.

**Verdict: FIXABLE.** Two corrections are needed.
- (a) Theorem 1-OM is not a corollary of [GT] Theorem 1. It covers non-realizable oriented
  matroids, and it has its own proof (Lemma 2.1-OM, gluing, simple connectivity of tope
  boundaries). It should be listed separately, together with its status (PROVEN for r ≤ 4;
  given cited shellability for r ≥ 5).
- (b) The sentence should be restricted to "a homotopy type of a whole order complex
  Δ(Λ̄(V))". Otherwise it contradicts the note's own (E1) and §2.6, which are contractibility
  results, that is, homotopy types. (E1) is also not first recorded in [MO]. The special case
  of unequal cycle lengths (+w) is already in [FPM] (iii) and in the remark in [Thm], via
  Björner–Walker. [MO] should cite these.

Neither correction changes V1.

## 3. V4: Route C over ℤ ([JSR] §3)

I re-read Lemma K, the decomposition (i)–(vi), Proposition C and Theorem V, asking at
each step whether a field is used.
- **Lemma K.** s has coefficients ±1. The filtration F_k (at most k high elements) is by
  subcomplexes. "z ∈ F_k a cycle ⇒ z − ∂(sz) ∈ F_{k−1} is a cycle" holds over any ring.
  So the augmented complex of Δ(Q) is exact over ℤ.
- **(i)–(vi).** These are order-theoretic facts and identities of chain maps with signs ±1.
  The strip maps give an isomorphism of ℤ-complexes C(L̄)/C(Q) ≅ ⊕_b C((π_ab, 1̂))[−1].
- **Proposition C over ℤ.**
  - d ≥ 1: the hypothesis H̃_{d−1}((π_ab, 1̂); ℤ) = 0 gives c_b = ∂e_b with e_b integral.
  - d = 0: c_b = m·[∅] with m ∈ ℤ. Then ∂_0(m·[v]) = m·[∅] for any vertex v, since the
    augmentation is onto over ℤ.
  - The correction w = z + Σ ∂ cons_b(e_b) and Lemma K finish the proof with no division.
- **Theorem V.** The induction transports along the order isomorphism (iii), which is
  ring-free.

So H̃_d(Δ(L̄); ℤ) = 0 for d ≠ n − 3. Since OP(P) ⊆ Π_n has length n − 1, Δ(L̄) has
dimension n − 3. So H̃_{n−3} = Z_{n−3} ⊆ C_{n−3} is free. **HOLDS.**

[MO]'s caveat also holds: this is not a homotopy type. For n ≥ 5, Hatcher's criterion
needs π_1 = 1, which homology does not give.

The BW paragraph of §2.2 was also checked, against the statement of Björner–Walker
Thm 1.1 as reproduced in Živaljević, arXiv:math/9801147, Thm 4.1 (secondary). That
statement is: L̄ ≃ ⋁_{y ∈ Co(z)} Σ(Δ(L̄_{<y}) ∗ Δ(L̄_{>y})) when Co(z) is an antichain.
- With z = π_a, Co(π_a) = A is the set of atoms π_ab. So L̄_{<y} = ∅, and the join is
  Δ(L̄_{>y}).
- At n = 3 this gives |A| + 1 points ≃ ⋁^{|A|} S^0.
- The induction is as [MO] states. The suspension of a wedge is ≃ the wedge of the
  suspensions, and an empty wedge is a point.

**COMPUTED ([ZZ] below).** For all 402 posets with 3 ≤ n ≤ 6 and τ = id, the reduced Betti
numbers of Δ(L̄) mod 2, mod 3 and mod 2^31 − 1 agree. They are concentrated in degree n − 3,
with value |μ(OP(P))|. This is a consistency check (no 2- or 3-torsion), not a proof over ℤ.
The mod-p instrument does detect torsion: on the 6-vertex RP², the mod-2 Betti numbers are
{1: 1, 2: 1} and the mod-large-p Betti numbers vanish.

## 4. V3: (E1)

### 4.1 The cited theorem, from a primary source

[MO] cites Björner 1981, *Homotopy type of posets and lattice complementation*, JCTA 30,
90–100, Thm 3.3 (doi 10.1016/0097-3165(81)90042-X), and Kozlov 1998, both through
secondary quotation. Here is what I could obtain.
- **Björner 1981, and Björner–Walker 1983** (*A homotopy complementation formula for
  partially ordered sets*, European J. Combin. 4, 11–19, doi 10.1016/S0195-6698(83)80003-1).
  The publisher's open-archive PDFs returned HTTP 403, and no other copy was found. **Not
  read.**
- **Kozlov, *Order complexes of noncomplemented lattices are nonevasive*, arXiv:math/9704225
  (Proc. AMS 1998).** **Read in full** (the arXiv version; the published version was not
  compared). Its Theorem 2.4, verbatim:

  > Let L be a finite lattice. Let x ∈ L̄ and let P = L \ Co(x). Then ∆(P̄) is
  > nonevasive, in particular it is collapsible.

  Here Co(x) = {y ∈ L : x ∧ y = 0̂, x ∨ y = 1̂} and P̄ = P ∖ {0̂, 1̂}. The proof is a
  three-page induction on |P̄| and needs no topology. The abstract says it reproves and
  generalizes "[Bj81, Theorem 3.3], that order complexes of noncomplemented lattices are
  contractible".
- **Živaljević's statement of Björner–Walker Thm 1.1** (arXiv:math/9801147, Thm 4.1,
  secondary). Part 1 reads: "the poset L̃ ∖ Co(z) is contractible" for every z ∈ L̃.

**The hypothesis.** Take x ∈ L̄ with Co(x) = ∅. Then P = L, and Kozlov's theorem says that
Δ(L̄) is collapsible, hence contractible. The hypothesis is exactly "some element of the
proper part has no complement". That is the same as "some element has no complement", since
0̂ and 1̂ are complements of each other. Kozlov needs nothing else: no modularity, no rank.
**The input of (E1) is confirmed.**

*Recommendation:* cite Kozlov 1998, Thm 2.4 (read, primary) as the source of (E1), and
keep Björner 1981 as "cited via Kozlov".

### 4.2 The rest of the proof

- *M is a lattice with the same 0̂ and 1̂.* g acts on Λ(C_P) by a lattice automorphism, and
  the fixed points of a lattice automorphism are closed under ∧ and ∨. (COMPUTED as well:
  `is_lattice` holds on all 1,104 fixed posets.)
- *Fixed subcomplex.* g preserves order, so a chain fixed setwise is fixed pointwise.
  Hence |Δ|^g = |Δ(L̄^g)|. The proper part of Λ(C_P)^g is the proper part of the fixed
  lattice.
- *"If".* Contractible ⇒ μ = χ̃ = 0 ⇒ χ_{C_P}(g) = ±μ = 0.
- *"Only if".* By TA-CR, M has an uncomplemented element. Kozlov then gives contractibility.
- *The order-reversal step.* [MO] writes: "For g = −τ it is OP(P)^τ with the order reversed".
  - The reversal is real, but it does not come from the sign. Λ(C_P) is dual to OP(P) for
    **every** g ([CVA] S1). So Λ(C_P)^g ≅ (OP(P)^τ)^op for both signs.
  - For g = −τ, τ is an anti-automorphism of P. It still acts on OP(P) as a lattice
    automorphism, not an anti-automorphism. The reason is that OP(P) = OP(P^op) as sets
    of partitions: the quotient digraph is reversed, and acyclicity is unchanged.
  - Order complexes and complementation are both self-dual, so the step is harmless.
  - **FIXABLE (wording):** say "for both signs, Λ(C_P)^g is dual to OP(P)^τ ([CVA] S1)".

**(E1) HOLDS**, given TA-CR (PROVEN + audited) and Kozlov 1998 Thm 2.4 (read here).

### 4.3 Independent recomputation, n ≤ 6 ([E1])

Model (`compute/audit_mo17370.py`):
- Posets up to isomorphism are generated by natural labelings and canonized by brute force.
- Aut(P) and the anti-automorphisms are found by checking all permutations.
- g ranges over Aut(P)-conjugacy classes, with g = +τ for automorphisms and g = −τ for
  anti-automorphisms (both signs for the antichain).
- M = the τ-stable set partitions with acyclic quotient, ordered by refinement.
- The lattice property, μ and complements come from the definitions only: a complement of
  x is a y whose only common lower bound with x is 0̂ and whose only common upper bound is 1̂.
- Contractibility is certified by a Stong core: repeated deletion of beat points (down-set
  with a maximum, or up-set with a minimum) until one point remains.
- Reduced Betti numbers are computed mod 2 and mod 2^31 − 1 for every pair.

Results. All pass, ending `ALL CHECKS PASSED`.

| n | pairs (+w, −τ) | zeros |
|---|---|---|
| 3 | 14 (9, 5) | 5 |
| 4 | 50 (34, 16) | 22 |
| 5 | 174 (144, 30) | 99 |
| 6 | 866 (758, 108) | 481 |
| total | 1,104 | 607 |

These reproduce the pair and zero counts of [MO] §5 and of [CVA] §4, from independent code.
- **(E1), computed.** All 607 zeros have a one-point Stong core, so they are contractible.
  All 607 are acyclic mod 2 and mod large p.
- **Positive control.** All 497 nonzeros have a Stong core that is *not* one point (it is
  empty or has ≥ 2 points). This must hold, since μ ≠ 0 rules out contractibility. The
  controls on single complexes also fire:
  - B_3: core of 6 points, β̃_1 = 1;
  - crown: core of 4 points;
  - Π_4: core of 13 points, β̃_1 = 6 mod 2;
  - a chain: core of 1 point;
  - Π_4^{(1234)}: μ = 0, uncomplemented.
- **Kozlov's hypothesis.** Exactly 607 pairs have an uncomplemented element, and all of
  them have a one-point core. "μ = 0 ⇔ uncomplemented element" holds on all 1,104 pairs, a
  reproduction of TA-CR for n ≤ 6.
- **The nonzeros.** All 497 have reduced homology mod 2^31 − 1 in a single degree. This
  reproduces [MO]'s homological claim. Their homotopy type is not computed, as [MO] says.

## 5. V6, V7: the MO thread

Re-fetched on 2026-10-31 through the Stack Exchange API: the question, 5 answers, 1 comment
on the question and 9 comments on answers, so 10 comments in all, as [MO] says.
- *Question.* Michał Kukieła, 2010-03-07, with the tags co.combinatorics,
  at.algebraic-topology and soft-question. The Forman quote and the question sentence are
  verbatim.
- *Hatcher* (36). All four quoted sentences are verbatim: "This is indeed a mystery…", the
  cycles sentence, "Ideally such a proof would proceed…" and the "metatheorem" sentence.
- *Knutson* (17). Verbatim.
- *Kalai* (16). Both sentences are verbatim (the "…" elides "(the dimension of the complex) and
  also locally have this property"). The chessboard complex and shifted complexes are mentioned, as [MO] says.
- *Kahle* (23). The quoted update sentence is verbatim.
- *Ramras* (15). The Csorba–Lutz, Schultz and Dochtermann content is as summarized.
- *Comments.*
  - Stanley's is under Hatcher's answer (answer 17387), verbatim.
  - Woodroofe's is under Kahle's answer (39653), verbatim, with an ellipsis.
  - Budney's is under the question, verbatim.

"Lexicographic shellability, Björner–Walker, Quillen's fiber lemma and BWW are not
mentioned in the thread": confirmed for the answers and comments as fetched.

*Framing.*
- "Known explanation in new clothing" for Route C and Theorem 1 is fair, and arguably
  generous to us. [MO] already says that Theorem 1 is the Folkman mechanism.
- "Nothing" for the main theorem and Theorem G is right.
- One overstatement: "(E1) is Hatcher's 'metatheorem' …, half-verified on the fixed
  subcomplexes". Hatcher's metatheorem is a dichotomy (contractible *or* a wedge). (E1)
  identifies which complexes fall in the contractible branch, the zeros. It verifies the
  dichotomy only there, and says nothing about the nonzero ones. *FIXABLE:* "(E1) identifies
  the contractible branch of Hatcher's dichotomy on these fixed subcomplexes; the wedge
  branch is OPEN".

## 6. V5: the rank-4 tree ([R4])

The 9 elements were rebuilt from the vectors of [CRV] §0.2: a = (−3, 1, 0, 0), b = ⟨e_3⟩,
c = ⟨e_4⟩, L = ⟨a, e_3⟩, B = ⟨a, e_4⟩, C = ⟨(1, 2, 0, 0), e_4⟩, D = ⟨(−2, 3, 0, 0), e_4⟩, 0
and R^4. Containment was decided by exact rational ranks.
- **COMPUTED.** The order relations of the proper part are exactly the 6 edges a–B, a–L,
  b–L, c–B, c–C and c–D.
- It is a lattice, with μ = 0 and every element complemented.
- The proper part is acyclic, and its Stong core is one point.

By hand: the graph is connected, with 7 vertices and 6 edges, so it is a tree. The order
complex of a height-one poset is its comparability graph. **HOLDS.**

[MO]'s "D, C and b are beat points, and successive removal leaves one point" is true, but
the removal needs further beat points after those three (L, c, then one of a and B).

Not re-checked here: that [CRV] §0.2's list of the 9 fixed flats is complete (that belongs
to [CRV] and its audit), and the other 35 counterexample pairs of [MO] §5 [R4].

## 7. V8: Candidate Theorem E

Theorem E occurs only in [MO], at the headline, §3 (title and status line) and the §6 table.
It is marked **OPEN** at each of these. It is not mentioned in the README or in any other
note. One loose word: §2.4 says that "two consequences follow, (E1) … and (E2)". (E2) is a
candidate, not a consequence (FIXABLE wording). Theorem E itself was not audited.

## 8. Not checked

- The text of Björner 1981 Thm 3.3 and of Björner–Walker 1983 (both inaccessible here).
  (E1) now rests on Kozlov's Thm 2.4 instead.
- The [MO] claim that its own script takes about 15 minutes. The [R4] sweep over 38,400
  pairs was not rerun.
- The §2.4 Π̄_3 argument was read and is correct. No other part of §§2.3–2.4 was re-derived.

## Reproduce

    cd compute && python3 audit_mo17370.py --nmax 6 --cap 20000 > output/audit_mo17370.txt

This takes about 2 minutes on one core. The output is archived in
`compute/output/audit_mo17370.txt` and ends `ALL CHECKS PASSED`. `--nmax 5` runs in under
a second.
