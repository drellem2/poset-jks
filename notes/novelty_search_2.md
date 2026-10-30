# Novelty search 2: prior art for the proved results

Work item: mg-0505f. This is a second, wider prior-art search. The first was
§1 of `notes/literature_novelty_jks_maps.md` ("[Lit]"), done while the main
conjecture was still open. That search said it was not exhaustive.

The search covers six results, each stated as in `notes/poset_jks_theorem.tex`
("[Thm]"):

1. the main theorem, [Thm, Thm 3.1]: H_P ≅ sgn ⊗ Lie(P), with the closed
   character formula (eq. closed);
2. the fixed-point Möbius formula for OP(P)^g, [Thm, Prop. Mside], proved
   by the Weisner and Crapo routes;
3. the splitting-cycle basis ([Thm, Thm S], formerly Conjecture S), and
   C[Lin P]/R_P ≅ H_P ⊗ sgn;
4. the pointed-cone theorem ([Cone, Thm 5.2] in
   `notes/cone_lune_lie_theory.md`);
5. b_n = n[x^n] log A(x) ([Thm, Thm bn]);
6. Klyachko's theorem via contraction ([Thm, Cor. klyachko];
   `notes/natural_isomorphism.md`, Cor. Ψ.2).

Every claim below carries one of these tags:
- **CITED**: an exact source, with a theorem or page number where one was
  seen.
- **PROVEN**: a proof is given here.
- **COMPUTED**: the command that reproduces it is in "Reproduce".
- **CONJECTURED**.

Each result also gets a verdict: **KNOWN**, **PARTIALLY KNOWN** or **NOT
FOUND**. A NOT FOUND comes with the queries and sources actually checked.
It is the result of a search, not a proof of novelty.

## Summary of verdicts

| # | Result | Verdict |
|---|---|---|
| 1 | Main theorem H_P ≅ sgn ⊗ Lie(P) | **PARTIALLY KNOWN.** The antichain case is Stanley 1982 Thm 7.3 (with Klyachko). The proof architecture is Stanley's §7: Hopf–Lefschetz, then μ of the fixed lattice, then an induced character. The statement for general P was **not found**. |
| 2 | Fixed-point Möbius formula for OP(P)^g | **PARTIALLY KNOWN.** The antichain case is Hanlon 1981 Thm 4 (as quoted in Stanley 1982 Lemma 7.1). Hanlon's key objects, the "hinge" h (= our orbit partition O_g) and its complements c(f) (= our F(P,g)), already appear in his §3. Hanlon's route goes through the crosscut and supersolvability, not Weisner. The poset formula was **not found**. One relevant paper (Baclawski–Björner 1981) could not be read. |
| 3 | Splitting-cycle basis; C[Lin P]/R_P ≅ H_P ⊗ sgn | **PARTIALLY KNOWN.** The antichain case is classical: Wachs's splitting basis, and the fact that the words beginning with a fixed letter form a basis modulo shuffles. Early 2017 states the same fact in plate language. General P: **not found**. |
| 4 | Pointed-cone theorem | **NOT FOUND as a statement.** However, it follows in a few lines from the classical Lawrence / Khovanskii–Pukhlikov valuation (Laplace transform of cones), §4.3. So it should be presented as an easy consequence of known tools, not as a deep new result. |
| 5 | b_n = n[x^n] log A(x) | **NOT FOUND.** Neither b_n nor the irreducible count is in the OEIS (searched, with positive controls). The method, a cycle construction giving a logarithm, is textbook. |
| 6 | Klyachko via contraction | **PARTIALLY KNOWN.** Klyachko's theorem itself is KNOWN (Klyachko 1974). A proof by contraction operators modulo shuffles was **not found**. A close analogue of the admissibility condition in Theorem Ψ appears in McNamara–Reutenauer 2005. |

**Bottom line for the publication decision.** The main theorem (1), its
fixed-point formula for general P (2), and the basis theorem for general P
(3) were not found in the literature. In each case the antichain
specialization is classical, and the proof follows the classical template
closely: Stanley §7 for (1); Hanlon's hinge and complements for (2); Wachs's
splitting cycles and Ree for (3). A write-up should say so explicitly. It
should present the results as a poset generalization of
Hanlon–Stanley–Wachs, not as a new method.

Result (4) should be presented with the valuation proof of §4.3, or at
least with that proof acknowledged. Result (5) looks new, but it is
elementary enumerative combinatorics.

Before submission, three sources not read here should be checked by a
human with library access: Baclawski–Björner 1981, Barcelo 1990, and
Reutenauer's book Ch. 8 (§7).

---

## 0. Sources and instruments

### 0.1 Forward citations of Jenča–Sarkoci (JCTA 122 (2014) 28–38; arXiv:1112.5782)

- **OpenAlex.** The work ID is W2050207319, with `cited_by_count = 3`. The
  query `filter=cites:W2050207319` returned three works:
  - Bonnier–Oberhauser, arXiv:1908.06496;
  - Schweig–Woodroofe, arXiv:1604.03115;
  - Borenstein–Shashkov, arXiv:1909.04215.
- **Semantic Scholar.** Citations were looked up both by arXiv:1112.5782 and
  by DOI 10.1016/j.jcta.2013.09.010. The two lookups gave the same four real
  records: the three above plus Williams, arXiv:2303.03765. The fifth record
  is a Bernoulli journal issue (a parse artefact).
- **Google Scholar.** It returned "The system can't perform the operation
  now" and no results, so it is effectively **blocked**, as in [Lit].
- **Not reached by any citation index, but found by search.** T. Li, *EL-shelling on
  comodernistic lattices*, arXiv:1907.06824. It does not cite J–S in a way
  the indexes record, but §5 treats O(P).

New against [Lit]:
- **Borenstein–Shashkov, arXiv:1909.04215, "Garland recurrences".** [Lit]
  had it as unchecked. Its abstract and arXiv record were read. The paper is
  **withdrawn** (v2, 23 Sep 2019). It enumerates the linear extensions of
  garland (double-fence) posets. Irrelevant.
- **Li, arXiv:1907.06824, §5 (full text read).** It gives an EL-shelling of
  the order congruence lattice O(P), with labels built from a fixed linear
  extension of P. There is no group action, no homology basis, and no Lie
  module. A grep for "basis", "homology", "group" and "automorph" found
  nothing relevant. This is a shelling-basis alternative to our splitting
  cycles, but it is not equivariant.

### 0.2 arXiv API (export.arxiv.org)

**Instrument note.** The first batch of queries went over `http://`. Every
query returned an empty feed, including queries whose answer is known to be
positive, so that instrument was broken. Over `https://` the positive
control `ti:"Linear extensions and order-preserving"` returns exactly
1112.5782v2. All counts below are from the https runs.

| Query (abstract field) | Hits | Relevant hits |
|---|---|---|
| `"order-preserving partitions"` | 2 | 1112.5782 only |
| `"order-preserving poset partitions"` | 0 | — |
| `"order congruences"` / `"order congruence"` | 12 / 12 | 1112.5782, 1604.03115, 1907.06824 |
| `"linear extensions" AND "Lie"` | 2 | none |
| `"linear extensions" AND "shuffle"` | 3 | none (Markov chains; T-partitions) |
| `"linear extensions" AND "homology"` | 1 | none |
| `"linear extensions" AND "wedge of spheres"` | 1 | 1112.5782 only |
| `"cyclic classes" AND "linear extensions"` | 0 | — |
| `"acyclic partitions"` | 1 | none (DAG partitioning, CS) |
| `"top-lune"` OR `"top-lunes"` | 0 | — |
| `"fixed-point partition lattice"` (both spellings) | 0 | — |
| `"Lie elements" AND "cone"` | 0 | — |
| `"Lie elements" AND "arrangement"` | 2 | Norledge–Ocneanu 1901.03243 (adjoint braid arrangement; covered in [Lit]) |
| `"Dynkin" AND "cone"` | 19 | none |
| `"Klyachko" AND "Lie"` | 15 | McNamara–Reutenauer math/0509125 (§6); 1808.06043, 1909.04460 (Lie characters, not relevant) |
| `"Lie representation" AND "poset" AND "homology"` | 1 | Fresse math/0301365 (Koszul duality for partition posets; not about P) |
| `"Lie representation" AND "automorphism"` | 0 | — |
| `"poset cone"` OR `"poset cones"` | 1 | none |
| `"naturally labeled/labelled posets"` | 5 | none uses log A or rotations (§5) |
| `"splitting basis"` | 8 | Wachs math/0401006 only |
| `au:Aguiar AND au:Mahajan` | 5 | 1902.07325 "Characteristic elements…" (characteristic polynomials; no cones or lunes) |
| `au:Dorpalen-Barry` | 14 | 2208.04855, 2507.06365, 2204.05829 (abstracts read: Varchenko–Gelfand rings and COMs; no top homology or group action) |
| `au:Norledge` | 9 | all covered in [Lit] |

### 0.3 Web searches (standard and extended modes)

Each line is one query. Results that were opened are discussed in the
sections below.

- Jenča Sarkoci "order-preserving partitions" homology symmetric group
  action (extended)
- "linear extensions" poset "free Lie" "cyclic" Lie representation homology
  … Joyal Klyachko Stanley (extended)
- "order congruences" poset lattice Möbius function automorphism fixed points
- "acyclic partitions" directed graph lattice homology "wedge of spheres"
  symmetric group Lie (extended)
- Möbius function fixed point sublattice group action "geometric lattice"
  Hanlon "fixed-point partition lattices" generalization
- Aguiar Mahajan Lie elements cone "top-lunes" chambers linearly
  independent pointed cone (extended)
- "linear extensions" connected poset "sum of shuffles" OR "shuffle
  relations" … (extended)
- Klyachko theorem … new proof "modulo shuffles" … Lie idempotent
  (extended)
- Garsia "Combinatorics of the free Lie algebra and the symmetric group"
  Klyachko proof
- "splitting basis" OR "splitting cycles" Wachs … "linear extensions"
- "order-preserving partitions" poset Lie module OR "Lie representation" OR
  "equivariant" 2024–2026 (extended)
- arXiv Aguiar Mahajan Bastidas Lie elements cones lunes 2022–2024
- Nick Early plates blades permutohedral "characteristic functions" … lines
- "lattice of order congruences" OR "order congruence lattice" …
- Stanley "Some aspects of groups acting on finite posets" pdf
- Baclawski Björner "Fixed points and complements in finite lattices"
- Develin Macauley Reiner "toric partial orders" …
- "cyclic classes of linear extensions" OR "cyclic equivalence classes of
  linear extensions"

Two papers surfaced that were new against [Lit]:
- Delcroix-Oger–Dupont, *Lie-operads and operadic modules from poset
  cohomology*, arXiv:2505.06094. The full text was grepped. "acyclic",
  "order-preserving", "linear extension", "digraph", "congruence" and
  "Klyachko" have no hits; the only "Jen" hit is a reference to Jensen–
  McCammond–Meier. The positive control "Joyal" fires. The paper builds
  operad structures on the cohomology of families of partition-type posets
  (decorated partitions, hypertrees). O(P) is not among its examples.
- Macauley–Mortveit, arXiv:0709.0291, "Equivalences on acyclic
  orientations". Their cyclic shifts turn a source into a sink, so they
  change the poset. J–S's cyclic classes are C_n-orbits of words for a
  fixed P. These are different notions, and the paper is not relevant.

### 0.4 OEIS (oeis.org, `fmt=text` search)

| Search | Result |
|---|---|
| **positive control** `1,2,7,40,357,4824` (a_n) | A006455 (and A028441), as expected |
| `1,3,16,131,1561,26532` (b_n) | **no matches** |
| `3,16,131,1561` (b_n, shorter) | **no matches** |
| `32,786,37464` (= Σ_P e_C(P) = (n−1)! b_n, n = 3..5) | **no matches** |
| `1,1,4,27,275,4070,86278` (irreducible naturally labelled posets, I = 1 − 1/A) | **no matches** |

Two entries were read in full:
- A006455. Its references and cross-references were read. It lists
  A323502 (connected natural posets: 1,1,1,3,18,181,…, a different
  sequence) and an e.g.f. relation exp(S(x) − 1). It has no ordinary log
  transform and no "b(n)".
- A323502.

The 2025–26 papers cited from A006455 were grepped:
- Cheon–Giraudo, arXiv:2512.17749: "irreducib", "indecomposab",
  "logarithm", "log", "cyclic", "rotation".
- Cheon et al., arXiv:2602.04533: the same words.
- Bevan–Cheon–Kitaev, arXiv:2311.08023: abstract only.

The only hits were join-irreducibles of lattices and one cyclic column
permutation. None of them is our decomposition.

### 0.5 Full texts read or grepped (new against [Lit])

| Source | What was looked for | Outcome |
|---|---|---|
| Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981) 319–341 (msp.org PDF) | method for μ(Π_n^σ) | §§2–5 read; see §2 |
| Stanley, *Some aspects of groups acting on finite posets*, JCTA 32 (1982) 132–161 (author's PDF, pubfiles/50.pdf) | §§1, 3, 7 | see §§1–2 |
| Wachs, *Poset topology: tools and applications*, arXiv:math/0602226 | §4.4, §4.6 | see §1 |
| Aguiar–Mahajan, *Topics in Hyperplane Arrangements*, authors' preliminary version (pi.math.cornell.edu/~maguiar/surv-226.pdf) | "pointed", "lineality", "Klyachko", "fixed point", Notes to Chs. 10, 14 | see §§1, 4, 6 |
| Early, *Canonical bases for permutohedral plates*, arXiv:1712.08520 | non-pointed quotients | see §§3–4 |
| McNamara–Reutenauer, arXiv:math/0509125 | multi-parameter Klyachko | see §6 |
| Li, arXiv:1907.06824 | O(P) | §0.1 |
| Delcroix-Oger–Dupont, arXiv:2505.06094 | O(P), linear extensions | §0.3 |
| Aguiar–Bastidas–Mahajan, arXiv:1902.07325 | cones, lunes | first page and grep; nothing relevant |

**Could not read:**
- Baclawski–Björner, *Fixed points and complements in finite lattices*, JCTA
  30 (1981), doi:10.1016/0097-3165(81)90030-3. ScienceDirect returned 403,
  and OpenAlex has no abstract.
- Barcelo 1990 (as in [Lit]).
- Reutenauer, *Free Lie Algebras* (book; no online copy).
- Still unchecked from [Lit]: the Hossain thesis, the Dorpalen-Barry thesis,
  and Norledge arXiv:2301.00702.

---

## 1. The main theorem: H_P ≅ sgn ⊗ Lie(P)

### 1.1 What is known (CITED)

- **The antichain case is classical.** Stanley 1982, Theorem 7.3: for S_n
  acting on Π_n, β_[n−2] = (sgn) ψ_n, with ψ_n = Ind_{C_n}^{S_n} ζ
  (Stanley's eq. (17)). With Klyachko 1974 (Lie_n ≅ Ind_{C_n}^{S_n} ζ) this
  is H̃_{n−3}(Π̄_n) ≅ sgn ⊗ Lie_n, i.e. [Thm, Cor. examples (a)]. The same
  theorem appears as Wachs, Poset Topology, Thm 4.4.7, with a second proof
  by Sundaram's Whitney homology. Aguiar–Mahajan, Topics, Notes to Ch. 14
  (p. 423 of the preliminary version) give the history: Brandt, Stanley,
  Hanlon, Joyal Thm 4 Ch. 4, Barcelo Thm 10.1, Wachs Thm 5.4, Fresse.
- **The proof architecture is Stanley's.** Stanley 1982 §7 proves Thm 7.3
  in three steps:
  - (i) the character of top homology of a CM poset is ± μ of the fixed
    subposet (his eq. (8), Thm 1.2);
  - (ii) Hanlon's value of μ(Π_n^π) (his Lemma 7.1);
  - (iii) the induced character from C_n (his Lemma 7.2), compared term by
    term.

  [Thm]'s proof of eq. (mainiso) has exactly this shape:
  - Lemma homchar is (i). Our version uses Jenča–Sarkoci's wedge of spheres
    in place of Cohen–Macaulayness. The underlying statement is Wachs,
    Poset Topology, Thm 4.6.1, which Wachs attributes to Baclawski–Björner.
  - Props. Mside and Lside replace (ii) and (iii).
- Stanley 1982 Cor. 7.4 (for p an odd prime, the representation is "1/p of
  the regular representation") is the antichain analogue of [Thm, Cor.
  prime].

### 1.2 What was not found

No source states any of the following, for any poset other than the
antichain:
- a group action on the homology of O(P) / OP(P);
- the module Lie(P) = span{w e_ζ : w ∈ Lin P};
- eq. (characterconj) or eq. (closed);
- the free-module corollary for connected P ([Thm, Cor. connected]).

The sources checked are §0.1–§0.3, together with the citing works of
Jenča–Sarkoci (§0.1), all of which are now read.

Aguiar–Mahajan (Topics, Notes to Ch. 10, p. 286) write: "Lie elements for
arbitrary arrangements do not seem to have been explicitly considered in the
literature" (CITED). That supports the absence of a cone or poset version as
of 2017.

**Verdict: PARTIALLY KNOWN.** The antichain case and the method are
classical (Stanley 1982 §7; Hanlon 1981; Klyachko 1974). The statement for
general P was not found.

## 2. The fixed-point Möbius formula for OP(P)^g

### 2.1 Hanlon 1981, as read (CITED)

- **Abstract and §2.** Hanlon analyses L = Π(N)^σ through the meet
  sublattice 𝓜 generated by the coatoms. Lemma 2 classifies the coatoms
  into two types:
  - (a) two σ-invariant blocks;
  - (b) p blocks permuted cyclically, with p prime.
- **Lemma 4** reduces to the case of m cycles of equal square-free length j.
- **§3: the hinge.** Hanlon defines the *hinge* h, "the partition in L which
  puts each cycle in a block by itself" (p. 324). This is exactly our orbit
  partition O_g.
  - **Lemma 5:** [h, 1̂] ≅ Π(M) and [0̂, h] ≅ D_j.
  - **Lemma 6:** h has exactly j^{m−1} complements c(f) in 𝓜. Each c(f) is
    a partition into j blocks that σ permutes cyclically, with one element
    of every cycle in each block.

  For the antichain, these complements are precisely our F(P, g).
- **Thm 1 / Thm 3:** 𝓜 is supersolvable, and gives rise to a geometric
  lattice G. The Möbius value follows from Stanley's theory of
  supersolvable lattices together with the crosscut theorem.
- Stanley 1982, Lemma 7.1, quotes the outcome: μ(Π_n^π) = (−1)^{d−1}
  μ(n/d)(d−1)!(n/d)^{d−1} when π has d cycles of length n/d, and 0
  otherwise. Stanley credits it to Hanlon's Thm 4. Stanley's Remark after
  Lemma 7.1 explains that Hanlon computes μ on 𝓜 and transfers it to L via
  the crosscut theorem.

### 2.2 Comparison with [Thm]

- **Proof I** applies Weisner's theorem in L^g with a = O_g = the hinge.
  Its sum runs over X(P, g), the elements x with x ∨ O_g = 1̂; these
  include the complements of the hinge. Möbius inversion on X(P, g) then
  leaves only the F(P, g) terms ([Thm, Prop. Mside]).
- **Proof II** uses Crapo's complementation theorem on one maximal orbit.

So Proof I uses Hanlon's distinguished element and his complements, but
replaces the coatom, supersolvability and crosscut machinery by Weisner plus
a Möbius inversion. Neither Hanlon nor Stanley states the Weisner route; the
grep for "Weisner" in the Hanlon text had no hits, while the positive control
"complement" had several. Proof I needs neither supersolvability nor
geometricity. That is why it extends to OP(P)^g, which is in general neither:
OP(P) is a meet-sublattice of Π_n and is only comodernistic
(Schweig–Woodroofe Thm 1.5, from [Lit]).

### 2.3 More general frameworks checked

- **Baclawski–Björner 1981, *Fixed points and complements in finite
  lattices*.** From its title and from Wachs's attribution of Thm 4.6.1, it
  is the closest general framework, but it **could not be read** (§0.5).
  Whether it contains a fixed-point Möbius formula that implies Prop. Mside
  is **unknown**. This is the single most important unread source for
  result 2.
- **Fixed points in other lattices.** Gill computes the fixed-point Möbius
  function for Π_{n,k} (EJC 7 (2000) R23). Hanlon's *generalized Dowling
  lattices* (Trans. AMS 325 (1991)) treat Dowling-type lattices. Both are
  the geometric/Dowling-type relatives named in the ticket. Both concern
  specific families of geometric or semimodular lattices; neither covers
  OP(P), which is not semimodular in general. Known from the search
  abstracts only, not read.
- **Stanley 1982 Thm 3.1 (geometric lattices).** It gives a basis with
  entries 0, ±1 for any group acting on a geometric lattice. It is not a
  Möbius formula.

**Verdict: PARTIALLY KNOWN.**
- The antichain value is Hanlon Thm 4 / Stanley Lemma 7.1.
- The hinge O_g and its complements (= F(P, g) for the antichain) are
  Hanlon's §3, Lemmas 5–6.
- The poset formula, eq. (closed) for general P, was **not found**.
- Whether it is a corollary of Baclawski–Björner 1981 is **open**: that
  paper was not read.

## 3. The splitting-cycle basis and C[Lin P]/R_P ≅ H_P ⊗ sgn

### 3.1 Known special case (CITED)

- **Antichain.** Wachs 1998 Prop. 2.3 gives the splitting basis of
  H̃(Π̄_n), and Wachs 1998 Thms 4.3 and 5.4 the correspondence (pointers from
  [Lit]; Topics p. 423 confirms them: "The bases (14.59) and (14.60) are
  also considered by Wachs [403, Proposition 2.3] under the name splitting
  basis"). The fact that the words beginning with a fixed letter form a
  basis of C[S_n]/Sh_n is classical (Radford; Reutenauer Ch. 6; cited in
  [Thm, Remark on Thm S]).
- **The same fact in plate language.** Early, arXiv:1712.08520, Def. 24 and
  Thm 28, works in the quotient P_1^n of the plate space. That quotient kills
  the lower-dimensional and the non-pointed permutohedral cones. Early shows
  it has the canonical basis {[[1, i_2, …, i_n]]}: the permutations with
  first label 1, of dimension (n−1)!. This is the antichain case of
  Theorem S(a), in a dual (plate) model. Early does not treat sub-cones,
  posets or homology.

### 3.2 Not found

The general-P statements were not found:
- B_P (the words whose first block contains the base component) is a basis
  modulo shuffles;
- W_P ∩ Sh_n = R_P;
- the splitting cycles of linear extensions span H_P;
- C[Lin P]/R_P ≅ H_P ⊗ sgn.

Li's EL-shelling (§0.1) and Schweig–Woodroofe's CL-shelling ([Lit]) give
other, non-equivariant bases of the homology of O(P) through decreasing
chains. Neither paper states a basis.

**Verdict: PARTIALLY KNOWN** (the antichain case is classical); **NOT
FOUND** for general P. Queries: §0.2 rows "linear extensions AND shuffle",
"splitting basis", "linear extensions AND homology"; §0.3 rows on splitting
cycles and on shuffle relations.

## 4. The pointed-cone theorem

The statement ([Cone, Thm 5.2]) is: for a finite real central essential
arrangement, the chambers of a pointed top-cone are linearly independent
modulo the span of the non-singleton top-lunes.

### 4.1 Searched (CITED negatives)

- **Aguiar–Mahajan, *Topics*.** The full text was grepped. "pointed" occurs
  only for *pointed arrangements* (a pair (A, C) with a reference chamber,
  §5.1.5), never for pointed cones. "lineality", "contains a line" and
  "contain a line" do not occur. "top-cone" occurs 236 times and "lune" 975
  times, which is the positive control. The Ree criterion (Lemmas 10.7–10.8)
  and Exercise 10.9 are as described in [Lit] and [Cone].
- **Early 2017.** Quotienting by non-pointed plates is a main theme, but only
  for the braid arrangement and only for the full space, i.e. the antichain
  case (§3.1).
- **Other negatives.** The arXiv rows "top-lune", "Lie elements AND cone" and
  "Dynkin AND cone" (§0.2) found nothing. Aguiar–Bastidas–Mahajan 1902.07325
  has nothing on cones or lunes.

### 4.2 Verdict

**NOT FOUND as a statement.** However, it follows in a few lines from a
classical theorem, as shown next.

### 4.3 A short proof from classical valuation theory (PROVEN; sketch; not independently audited)

**Cited input (CITED; theorem number not checked).** This is the theorem of
Lawrence (1991) and Khovanskii–Pukhlikov (1992); see Barvinok, *Integer
Points in Polyhedra* (EMS 2008), Ch. on exponential valuations. There is a
linear map F, a valuation, from the algebra of indicator functions of
polyhedra in R^d to meromorphic functions on C^d, with these properties:
- F([Q])(ξ) = ∫_Q e^{⟨ξ,x⟩} dx whenever the integral converges absolutely
  near ξ;
- F([Q]) = 0 whenever Q contains a line.

In particular F vanishes on lower-dimensional polyhedra: the integral is 0
where it converges, and the valuation extends that.

**Proof of the theorem.**

1. *Set-up.* Let V be a pointed top-cone, and suppose
   Σ_{C∈V} c_C C = Σ_L d_L Σ_{C∈L} C in Γ[A], where L runs over
   non-singleton top-lunes.

2. *Pass to indicator functions.* Consider
   g = Σ_C c_C [C̄] − Σ_L d_L [|L|].
   Decompose every indicator of a union of closed faces into indicators of
   relatively open faces of A. Every open chamber then has coefficient 0 in
   g, so g = Σ a_F [F°] over lower-dimensional faces F. Each [F°] is a
   signed sum of indicators of closed faces G ≤ F, by Möbius inversion on
   the face poset of a cone. Those closed faces are lower-dimensional. Hence
   F(g) = 0.

3. *Apply the valuation.* A non-singleton top-lune L = L(H, D), with H ≠ O,
   has the nonzero subspace spanned by H in its closure |L|. So |L| contains
   a line, and F([|L|]) = 0. Therefore Σ_C c_C F([C̄]) = 0.

4. *Use pointedness.* Since |V| is pointed, there is an open set U of ξ with
   ⟨ξ, x⟩ < 0 on |V| \ {0}. For ξ ∈ U every integral converges, so the
   Laplace transform of the step function f = Σ_C c_C 1_C, which is supported
   in |V|, vanishes on U.

5. *Conclude.* That Laplace transform is holomorphic on the tube U + iR^d,
   so it vanishes there. Hence the Fourier transform of the L¹ function
   f e^{⟨ξ₀,x⟩} is zero for any ξ₀ ∈ U, and f = 0 almost everywhere. So every
   c_C = 0. ∎

For the braid arrangement taken modulo the line R·(1, …, 1), C_P is pointed
iff P is connected. So the same few lines reprove [Thm, Thm S(a)] in the
connected case, W_P ∩ Sh_n = 0. That proof is independent of the
contraction argument of [S].

The argument does **not** reach the non-pointed case. Theorem S(b) and
Conjecture G of [Cone] need the lunes of the lineality flat, and F kills all
of those.

**Consequence for presentation.** A specialist in valuations would likely
regard the pointed-cone theorem as a quick consequence of
Lawrence–Khovanskii–Pukhlikov. A write-up should cite that theorem, give
this proof or note it, and keep the claimed novelty for the non-pointed,
poset-specific statements: Theorem S(b)–(d) and Theorem Ψ.

## 5. b_n = n[x^n] log A(x)

- **OEIS (§0.4).** b_n = 1, 3, 16, 131, 1561, 26532 has **no OEIS match**.
  Neither do its 4-term tail, the totals (n−1)! b_n = Σ_P e_C(P), or the
  irreducible counts I_n = 1, 1, 4, 27, 275, 4070, 86278 (where
  A = 1/(1 − I)). The positive control, a_n → A006455, works.
- **A006455.** Its references, including the 2025–26 papers, contain no
  ordinary logarithm of A(x) and no rotation-closed class of posets (§0.4).
  Its formula section has only the e.g.f. relation with A323502, which
  counts *connected* natural posets. A323502 is a different notion from
  irreducibility with respect to the arc order: its terms are 1,1,1,3,18,181
  against I_n = 1,1,4,27,275.
- **Method.** The proof is a cyclic-factorization bijection plus the
  identity n[x^n] log 1/(1 − I(x)) = #(cyclic arrangements of irreducibles
  on n marked points). This is the standard "pointed cycle" form of the
  cycle construction (e.g. Flajolet–Sedgewick, *Analytic Combinatorics*,
  the sequence/cycle constructions; item not re-checked; CITED from memory).
  The unique factorization A = 1/(1 − I) is the elementary splitting of a
  naturally labelled poset at every k such that no relation crosses from
  [1, k] to [k+1, n].

**Verdict: NOT FOUND** (identity and sequence). The technique is textbook.
The values b_n, I_n and (n−1)! b_n are **COMPUTED** from A006455 (see
"Reproduce"). These values agree with `notes/cyclic_compatible_posets_bn.md`,
where b_n is also computed by direct enumeration.

## 6. Klyachko's theorem via contraction ([Thm, Cor. klyachko])

- **Klyachko's theorem.** Lie_n ≅ Ind_{C_n}^{S_n} ζ is **KNOWN**: Klyachko
  1974, Sibirsk. Mat. Zh. 15, 1296–1304. Several other proofs are known:
  - the Kraśkiewicz–Weyman route;
  - Garsia 1990;
  - Stanley's route through Hanlon's computation (Stanley 1982 Thm 7.3 with
    Lemma 7.2; it identifies homology, not Lie_n);
  - Johnson's combinatorial proof (Manchester thesis; search result only,
    not read).

  Topics p. 423 credits a direct proof of Prop. 14.73 to Garsia (CITED).
- **The intermediate statement.** C[S_n] e_ζ ∩ Sh_n = 0, i.e. x ↦ x e_ζ is
  injective on Lie_n. By Ree's theorem it is equivalent to Klyachko's
  statement plus an explicit form of the isomorphism. No source was found
  that proves it by the contraction operators E_{a,x} modulo shuffles.
  Reutenauer's book Ch. 8, where Klyachko's idempotent is treated, could not
  be checked.
- **Analogue of Theorem Ψ (CITED).** McNamara–Reutenauer 2005
  (arXiv:math/0509125, Def. 1.2, Thms 1.7–1.9) define a multi-parameter
  Klyachko element κ_n(q). It lives over K[q] localized at the
  1 − q_{u(1)}⋯q_{u(i)}, with q_1⋯q_n = 1 (§2, the proof of Thm 1.7: "because
  of the conditions on q and because r, s < n"). They prove it is a Lie
  idempotent for a twisted product. Their conditions are the "admissible λ"
  condition of Theorem Ψ: λ([n]) = 1 and λ(U) ≠ 1 for proper U, here for the
  antichain.

  Whether McNamara–Reutenauer imply the antichain case of Theorem Ψ, the
  independence of the λ-twisted class sums modulo Sh_n, was **not checked**
  (CONJECTURED plausible). A write-up of Theorem Ψ must cite them.

**Verdict: PARTIALLY KNOWN.** The theorem is classical, and a parametrized
analogue of the admissibility condition exists. The contraction proof was
not found. [Thm] already calls this "plausibly folklore-adjacent", and that
remains the right description.

## 7. Recommendations

1. **The novelty claims that survive** are: Theorem 3.1 and eq. (closed) for
   general P; Prop. Mside (the poset fixed-point formula); Theorem S(b)–(d)
   for disconnected P; Theorem Ψ for general P (modulo McNamara–Reutenauer);
   and the b_n identity. Each should be framed as generalizing a named
   classical result: Stanley Thm 7.3, Hanlon Thm 4, Wachs's splitting basis,
   Klyachko.
2. **Present the pointed-cone theorem as a corollary of known tools.** Give
   the valuation proof of §4.3 or at least cite it. The connected case of
   Theorem S(a) should mention it too.
3. **Three items need a human with library access before submission:**
   - Baclawski–Björner 1981: does it contain a fixed-point Möbius or
     complement formula that implies Prop. Mside?
   - Barcelo 1990.
   - Reutenauer, *Free Lie Algebras*, Ch. 8: is C S_n e_ζ ∩ Sh_n = 0 stated
     there?
4. **Experts to ask** (as in [Lit]): Wachs and Sundaram for 1–3, Reiner or
   Dorpalen-Barry for the cone results, and Reutenauer for 6.

## Reproduce

The only computation here is the OEIS search input. Run from the repository
root (plain Python 3):

    python3 -c "
    from fractions import Fraction as F
    a=[1,1,2,7,40,357,4824,96428,2800472]   # A006455, n=0..8
    N=len(a); inv=[F(0)]*N; inv[0]=F(1)
    for n in range(1,N): inv[n]=-sum(a[k]*inv[n-k] for k in range(1,n+1))
    print('I', [int(-x) for x in inv[1:]])
    b=[0]*N
    for n in range(1,N): b[n]=n*a[n]-sum(b[k]*a[n-k] for k in range(1,n))
    print('b', b[1:])"
    # prints: I [1, 1, 4, 27, 275, 4070, 86278, 2600369]
    #         b [1, 3, 16, 131, 1561, 26532, 637890, 21580043]

The OEIS searches are `https://oeis.org/search?q=<terms>&fmt=text` with the
term lists in §0.4. The arXiv queries are
`https://export.arxiv.org/api/query?search_query=<query>` with the queries
of §0.2 (https; see the instrument note there).
