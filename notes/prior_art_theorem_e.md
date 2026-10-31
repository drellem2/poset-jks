# Prior art for theorem_e_equivariant_wedge.md (Theorem E, poset corollary, Theorem S)

This note checks the claims of `notes/theorem_e_equivariant_wedge.md` ("[TE]") against
the literature. The note's own literature search ([TE §4], gap (iv)) was a single web
query. The claims:
- **Theorem E** ([TE §2]): V a pointed top-cone of a finite real central essential
  arrangement of rank d ≥ 2, G a finite group of linear maps preserving A and V and
  acting freely on the chambers of V. Then Δ(Λ̄(V)) ≃_G G_+ ∧ ⋁^{#V/|G|} S^{d−2}, and
  H̃_{d−2}(Δ(Λ̄(V)); ℤ) is a free ℤG-module.
- **Poset corollary** ([TE §2.5]): P connected, n ≥ 3 elements, L = OP(P). Then
  Δ(L̄) ≃_{Aut P} Aut(P)_+ ∧ ⋁^{e(P)/|Aut P|} S^{n−3}, and H̃_{n−3}(Δ(L̄); ℤ) is a free
  ℤ[Aut P]-module.
- **Theorem S** ([TE §3.1]): V pointed, G any finite group preserving A and V. Then
  Σ^u Δ(Λ̄(V)) ≃_G ⋁_{[C] ∈ V/G} G_+ ∧_{G_C} S^{U_C}, with U_C = ℝ^d/ℝp_C; and its
  consequences (S1)–(S4).

Verdicts are used as in `notes/prior_art_observation_cc.md`:
- **KNOWN**: stated in a source read here, with the exact reference.
- **KNOWN IN SUBSTANCE**: follows from a stated result of a source read here by a step
  that the source does not write down but that needs no new idea. The step is named.
- **NOT FOUND**: not in the sources of §0. This is the result of a search, not a proof
  of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is not counted either way.

## Verdict

| Claim of [TE] | Verdict | Closest prior art (read) |
|---|---|---|
| **Theorem E**, general pointed cone, free action | **NOT FOUND.** No source read gives an equivariant homotopy type of Δ(Λ̄(V)) for cone lattices, Folkman-type lattices of flats, or OP(P) with a group action. The closest statements are of the same *form* for other objects: the partition complex restricted to Σ_{n−1} or to a Young subgroup with gcd 1 (Arone 2015, Ex. 1.4; Arone–Brantner 2021, Thm 5.10 and the Example after it), and the Tits building restricted to a parabolic (Arone–Brantner, Lemma 5.17) (§1.1, §1.2) | Arone 2015; Arone–Brantner 2021 |
| Theorem E, Step 1 (Corollary F1: the face map is a G-homotopy equivalence) | **KNOWN technique.** It is the equivariant Quillen fiber lemma (Thévenaz–Webb 1991, Thm 1; restated as BWW 2005, Cor. 7.2), applied with fixed fibers checked one subgroup at a time, as [TE] itself says. The fiber computation (Lemma F) is specific to cones and was not found | BWW 2005 §7; Thévenaz–Webb 1991 (via [TE] and BWW) |
| Theorem E, §2.1 (free ℤG basis from chambers) | **NOT FOUND** for cones. Same pattern as the Solomon–Tits apartment basis indexed by chambers opposite a fixed chamber, which the unipotent radical permutes simply transitively; in Arone–Brantner this is Lemma 5.17 / Cor. 5.18 (§1.2). Not the same object | Arone–Brantner, Lemma 5.17, Cor. 5.18 |
| Theorem E, the assembly step ((k−1)-connected, contractible singular fixed sets, free ℤG homology ⇒ free G-wedge; tree lifting for d = 3) | **NOT FOUND stated as a lemma** in the sources read. It is a standard equivariant-Whitehead argument; no source read writes it down | — |
| **Poset corollary, P = claw K_n** (one minimum below n − 1 maximal elements) | **KNOWN.** OP(K_n) = Π_n (every set partition is order-preserving; §2.1, COMPUTED n ≤ 7) and Aut(K_n) = Σ_{n−1} acting simply transitively on the (n − 1)! linear extensions. The corollary then reads \|Π_n\| ≃_{Σ_{n−1}} Σ_{n−1,+} ∧ S^{n−3}, which is Arone 2015, Examples 1.4 ("This equivalence is a well-known result", citing Donau), and Arone–Brantner 2021, Example after Thm 5.10 | Arone 2015, Ex. 1.4; Arone–Brantner, Ex. after Thm 5.10; Donau 2012 |
| Poset corollary, integral freeness, P = claw | **KNOWN** (a corollary of the homotopy statement in the previous row: H̃_{n−3}(Σ_{n−1,+} ∧ S^{n−3}; ℤ) = ℤΣ_{n−1}). Over ℂ it is Stanley 1982 (as reported in Wachs 2007, (3.2.2)); integrally it is also KNOWN IN SUBSTANCE from the falling-chain basis in Wachs 2007, §3.2: the basis c̄_σ, σ(n) = n, is permuted freely and transitively by Σ_{n−1} (step: τ c̄_σ = c̄_{τσ}, plus duality Hom_ℤ(ℤG, ℤ) ≅ ℤG if the basis is read as a cohomology basis) | Wachs 2007 (3.2.1)–(3.2.2); Arone 2015 |
| **Poset corollary, general connected P** | **NOT FOUND.** Jenča–Sarkoci give the non-equivariant wedge for OP(P) and no group action (as already recorded in `notes/prior_art_observation_cc.md` §0.3); no source read treats OP(P) with Aut(P) at the level of homotopy | Jenča–Sarkoci (via the earlier note) |
| Poset corollary, integral freeness, general P | **NOT FOUND.** | — |
| **Theorem S** (one suspension, wedge of induced representation spheres indexed by chamber orbits) | **NOT FOUND.** The same *shape* — a G-equivalence to ⋁ Ind_{G_x}^G of representation spheres, with unreduced suspension used because there is no invariant base point — is the form of Arone 2015, Thm 1.2 and Arone–Brantner, Thm 5.10 for partition complexes under Young subgroups (§1.1). It does not cover Theorem S: for Π_n = OP(K_n), the non-free Young subgroups do not preserve the cone C_{K_n} (§2.2) | Arone 2015, Thm 1.2; Arone–Brantner, Thm 5.10 |
| (S1)–(S2), fixed-set homology and emptiness of T^H | **NOT FOUND** for cones. Analogous fixed-point computations exist for Π_n (Arone–Brantner, Thm 6.2, Lemma 6.3, Cor. 6.8; Arone–Dwyer–Lesh 2016) | as stated |
| (S3), H̃_{d−2}(T) ≅ ⊕ Ind_{G_C}^G(det) | **NOT FOUND** for cones. Orientation-character twists of induced modules are the form of the Sundaram–Welker equivariant Goresky–MacPherson formula (Wachs 2007, Thm 5.4.2), a homology statement about subspace-arrangement links, not cone lattices | Wachs 2007, Thm 5.4.2 |
| (S4), homotopy type of T^H | **NOT FOUND.** | — |
| Remark: stably free ≠ free (Swan) | KNOWN (standard; not re-read here) | — |
| MathOverflow 17370 answers | The answers contain no equivariant statement; this is recorded in `notes/mo17370_wedges_of_spheres.md` §2.4 ("None of the MO answers discusses group actions"), which read all five answers and ten comments. Not re-read here | [MO] |

**Bottom line.**
- The poset corollary is **KNOWN** for the claw K_n and its dual, where it is the
  classical Σ_{n−1}-equivariant splitting of the partition complex. These are exactly
  the connected posets with OP(P) = Π_n (§2.2), and the only connected posets found for
  which the statement is in the literature read. For general
  connected P, and for Theorem E on general pointed cones: **NOT FOUND**.
- The method of Theorem E (equivariant Quillen fiber lemma, then equivariant Whitehead)
  is standard. The shape of its conclusion, and of Theorem S, matches Arone's and
  Arone–Brantner's branching rules for Π_n. Those rules are proved differently
  (complementary collapse, via discrete Morse theory), for a different object.
- Theorem S and (S1)–(S4): **NOT FOUND**.
- No statement was found that would make Theorem E or Theorem S a direct specialization
  of complementary collapse (Arone–Brantner, Thm 3.14). Whether Λ(V) admits an
  orthogonality fan whose orthogonal chains reproduce the chamber count was not
  examined, and is a natural place to look for a second proof.

---

## 0. Sources

### 0.1 Read

PDFs were fetched with `curl` and converted with `pdftotext -layout`, then grepped. The
listed parts were read.

| Source | Obtained from | What was read |
|---|---|---|
| G. Z. Arone, *A branching rule for partition complexes* | arXiv:1508.05086 (v2) | §1: Theorem 1.2, the explanation of its terms, Examples 1.4 (Σ_{n−1} and Σ_{n−2} × Σ_2 cases) |
| G. Z. Arone, D. L. B. Brantner, *The action of Young subgroups on the partition complex*, Publ. Math. IHÉS 133 (2021) 47–156 | arXiv:1801.01491 (v3) | Exposition; §1 Statement of results: Def. 3.16, Thm 3.14 (complementary collapse), Thm 6.2, Lemma 6.3, Cor. 6.8, Lemma 6.6, Thm 5.10 and the Example and Remark 1.2 after it, (1.3), Cor. 5.13, Remark 1.4, Thm 5.15, Lemma 5.17, Cor. 5.18, the strict-orbits paragraph |
| A. Björner, M. L. Wachs, V. Welker, *Poset fiber theorems*, Trans. AMS 357 (2005) ("BWW") | math.miami.edu/~wachs/papers/fibers.pdf | §7 in full: Thm 7.1 (equivariant fiber theorem), Cor. 7.2 (Thévenaz–Webb), Cor. 7.3, Example 7.4 |
| M. L. Wachs, *Poset topology: tools and applications* (2007) | arXiv:math/0602226 | §3.2 (partition lattice, (3.2.1)–(3.2.3)); §5.2 (Quillen fiber lemma, equivariant versions, Thm 5.2.1–5.2.3, Exercises 5.2.6–5.2.7, Example 5.2.8); §5.4 (Thm 5.4.1 Ziegler–Živaljević and its proof via the face poset; Thm 5.4.2 Sundaram–Welker) |
| R. Donau, *A nice acyclic matching on the nerve of the partition lattice* | arXiv:1204.2693 (v4) | Abstract, §1 (Theorems 1.1, 1.2, the C_p counterexample), statement of Thm 3.4 (Freij) |
| G. Z. Arone, W. G. Dwyer, K. Lesh, *Bredon homology of partition complexes*, Doc. Math. 21 (2016) | arXiv:1306.0056 | grep for free actions and wedge statements; main theorem (fixed points of p-subgroups, Bredon homology vanishing) |
| L. Moci, G. M. Pezzoli, *Representations of automorphism groups on the homology of matroids* | arXiv:2001.03760 (v2) | Abstract and contents (equivariant cross-cut theory; homology representations only) |
| E. Delucchi, M. J. Falk, *An equivariant discrete model for complexified arrangement complements* | arXiv:1305.0134 | Abstract (not relevant: ℤ_4-action on a Salvetti-type model) |
| J. P. May, M. Stephan, I. Zakharevich, *The homotopy theory of equivariant posets* | arXiv:1601.02521 | Introduction (history: Thévenaz–Webb, then Welker 1995) |

Thévenaz–Webb 1991 is cited through [TE] (which re-read the EPFL typescript) and through
BWW Cor. 7.2. A fresh attempt to open the EPFL record returned HTTP 429.

### 0.2 Not accessible or not read

- **V. Welker, *Equivariant homotopy of posets and some applications to subgroup
  lattices*, J. Combin. Theory Ser. A 69 (1995) 61–86.** NOT ACCESSIBLE (no open copy
  found). Known here only through the one-sentence description in May–Stephan–Zakharevich.
- **S. Sundaram, V. Welker, *Group actions on arrangements of linear subspaces and
  applications to configuration spaces*, Trans. AMS 349 (1997) 1389–1420.** The author's
  copy is on an FTP server that did not respond. Read only through Wachs 2007, Thm 5.4.2
  (a homology formula).
- **G. Lehrer; P. Orlik, L. Solomon** (characters of Orlik–Solomon algebras / complements
  of reflection arrangements): not read. These are character (homology) results about
  arrangement complements; nothing in the sources read points to a homotopy statement
  for cone lattices there.
- **R. Freij, *Equivariant discrete Morse theory*, Discrete Math. 309 (2009).** Not read;
  known through Donau and Arone–Brantner (Σ_2 × Σ_{n−2}-homotopy type of the complex of
  non-connected graphs).
- **G. Z. Arone, W. G. Dwyer, *Partition complexes, Tits buildings and symmetric
  products*** (Proc. LMS 2001). Not read.
- **Ayzenberg et al.** Searched; the hits concern torus actions of complexity one and
  nerves of hemisphere coverings. Nothing on group actions on order complexes of cone or
  flat lattices was found.

### 0.3 Web searches

- Arone Brantner action of Young subgroups on the partition complex Σ_{n−1} free wedge;
- Welker "equivariant homotopy of posets and some applications to subgroup lattices";
- Sundaram Welker "group actions on arrangements of linear subspaces" equivariant
  homotopy wedge (and a second query for the AMS page);
- Arone Dwyer Lesh "Bredon homology of partition complexes";
- Freij "equivariant discrete Morse theory" partition lattice;
- Ayzenberg poset equivariant wedge of spheres representation sphere order complex
  arrangement; Ayzenberg Cherepanov "wedge of spheres" equivariant;
- hyperplane arrangement cone "lattice of flats" group action free module top homology
  Folkman complex equivariant;
- order complex lattice order-preserving partitions poset automorphism group homology
  free module linear extensions;
- G-CW complex fixed points contractible for nontrivial subgroups homology free
  ℤG-module equivalent to G_+ wedge of spheres lemma;
- Welker 1995 J. Combin. Theory Ser. A "equivariant homotopy of posets" abstract.

None returned an equivariant homotopy type for a cone lattice, for a lattice of flats of
a real arrangement restricted to a cone, or for OP(P) with Aut(P).

---

## 1. The closest results

### 1.1 Partition complexes under Young subgroups

Arone 2015, Theorem 1.2 (restated as Arone–Brantner, Theorem 5.10): for n = n_1 + … + n_k
and g = gcd(n_1, …, n_k) there is a Σ_{n_1} × … × Σ_{n_k}-equivariant equivalence

  |Π_n| ≃ ⋁_{d | g} ⋁_{B(n_1/d, …, n_k/d)} (Σ_{n_1} × … × Σ_{n_k})_+ ∧_{Σ_d} (S^{n−d−1} ∧ |Π_d|^⋄),

where |Π_d|^⋄ is the unreduced suspension and S^{n−d−1} carries a representation-sphere
action of Σ_d. "By a G-equivariant equivalence we mean a map of G spaces that induces an
equivalence of H-fixed points for every subgroup H of G" (Arone 2015, before Thm 1.2), the
same notion as (W) in [TE].
- For gcd = 1 this is a free wedge: "|Π_n| is Σ_{n_1} × … × Σ_{n_k}-equivariantly
  equivalent to a wedge sum of copies of S^{n−3}, that are freely permuted"
  (Arone 2015, Examples 1.4).
- For Σ_{n−1} × Σ_1: "|Π_n| ≃_{Σ_{n−1}} Σ_{n−1,+} ∧ S^{n−3}. This equivalence is a
  well-known result. For example, see [Donau] for a closely related statement."
- Arone–Brantner prove it by complementary collapse (Thm 3.14), an equivariant
  discrete-Morse collapse on a G-lattice, which also recovers the Björner–Walker
  complementation formula and its generalizations by Kozlov and Welker.

**Relation to [TE].** Same form as Theorem E (free case) and Theorem S (induced
representation spheres, unreduced suspension when there is no invariant base point).
Different object: Π_n with Young subgroups. §2 shows that exactly one instance overlaps.

### 1.2 Tits buildings under parabolics

Arone–Brantner, Lemma 5.17: for a flag A of a vector space V over a finite field, with a
complementary flag B, |BT(V)| ≃_{P_A} Ind_{L_AB}^{P_A}(Σ^r ⋀_i |BT(gr_i B)|). For a
complete flag the factors are BT of lines, i.e. S^{−1}, and the statement is the
Borel-equivariant form of Solomon–Tits: the building is a wedge of spheres indexed by the
chambers opposite a fixed chamber, which the unipotent radical permutes simply
transitively. Cor. 5.18 derives projectivity of the Steinberg module from it.

**Relation to [TE].** This is the building-theoretic analogue of [TE §2.1]: a free
ℤG-basis indexed by chambers on which G acts freely. It is not the same object.

### 1.3 The equivariant fiber theorems

BWW 2005, Theorem 7.1: if f : P → Q is a G-poset map whose fibers f^{−1}(Q_{≤q}) are
(Stab_G(q), ℓ(f^{−1}(Q_{<q})))-connected, then
Δ(P) ≃_G Δ(Q) ∨ ⋁_q (Δ(f^{−1}(Q_{≤q})) ∗ Δ(Q_{>q})). Cor. 7.2 is Thévenaz–Webb.
Example 7.4 shows that the equivariant connectivity hypothesis cannot be dropped; the
failing example is a reflection of a circle, the same phenomenon as [TE §3.2].

**Relation to [TE].** Step 1 of Theorem E (Corollary F1) is an instance of Cor. 7.2 with
contractible fibers, checked one subgroup at a time ([TE] notes that only the H-fixed
fibers are needed). Theorem 1 of [GT], which [TE] builds on, uses the non-equivariant BWW
theorem with sphere fibers; the equivariant Thm 7.1 does not apply directly there,
because a sphere fiber with a non-trivial stabilizer is not equivariantly connected
(Example 7.4). That is consistent with [TE]'s route, which uses only contractible fibers
and gets the spheres from the chambers.

---

## 2. The claw

### 2.1 OP(K_n) = Π_n

Let K_n be the poset on {0, 1, …, n − 1} with 0 < i for all i ≥ 1 and no other relations.
It is connected.
- **Every set partition is order-preserving.** In the quotient digraph K_n/π, every edge
  leaves the block of 0, so there is no cycle. Hence OP(K_n) = Π_n.
- **Aut(K_n) = Σ_{n−1}**, permuting the leaves and fixing 0. As a subgroup of Σ_n it is
  the Young subgroup Σ_{n−1} × Σ_1.
- **Linear extensions** are the words with 0 first, so e(K_n) = (n − 1)!, and Σ_{n−1}
  acts on them simply transitively. So r = e(P)/|Aut P| = 1.

COMPUTED for 3 ≤ n ≤ 7 by `compute/prior_art_theorem_e.py` (see Reproduce), with
controls: the 3-chain and the N-poset each have a partition that is not
order-preserving, and the instrument reports it.

With these, [TE §2.5] for P = K_n reads

  |Π̄_n| ≃_{Σ_{n−1}} Σ_{n−1,+} ∧ S^{n−3},  H̃_{n−3}(Π̄_n; ℤ) ≅ ℤΣ_{n−1},

which is the statement quoted in §1.1, KNOWN. Over ℂ, the homology statement is
Stanley 1982 (Wachs 2007, (3.2.2)).

### 2.2 Why the overlap stops there

- For P = K_n, Theorem E is used with G ≤ Aut(K_n) = Σ_{n−1}. Every subgroup of a group
  acting freely on chambers also acts freely. So no non-free case of Theorem S arises
  from K_n with its automorphisms.
- The non-free Young subgroups of Arone's theorem (for example Σ_{n−2} × Σ_2 with n even)
  do not fix the element 0 of K_n, hence do not preserve the cone C_{K_n}. They act on
  Π_n = Λ(full space) instead, which is not a pointed cone. So Arone's representation
  spheres are not instances of Theorem S, and Theorem S is not an instance of Arone's.
- **K_n and its dual are the only connected posets with OP(P) = Π_n** (n ≥ 3).
  Proof: a 3-chain a < b < c gives the cyclic quotient of {a, c} | {b}, so P has height
  ≤ 1 and its comparability graph is bipartite (minima, maxima). Two disjoint relations
  a < b, a′ < b′ give the cyclic quotient of {a, b′} | {a′, b}. A connected bipartite
  graph on ≥ 3 vertices with no two disjoint edges is a star. The dual claw K_n^op gives
  the same lattice (OP(P) = OP(P^op)) and the same Σ_{n−1}-action. For every other
  connected P, no source read describes the Aut(P)-homotopy type of OP(P).
  COMPUTED for 3 ≤ n ≤ 5 over all connected labeled posets (12, 146 and 3,060 of them,
  which are the known counts of connected labeled posets and so control the
  enumeration): OP(P) = Π_n exactly for the 2n labelings of K_n and K_n^op.

---

## 3. What the search did not settle

- Whether Welker 1995 or Sundaram–Welker 1997 contains an equivariant homotopy statement
  for lattices of flats restricted to cones. Both were not accessible; what is reported
  of them (Wachs 2007, May–Stephan–Zakharevich) is a homology formula and a general
  G-poset framework, respectively.
- Whether complementary collapse (Arone–Brantner, Thm 3.14) applied to Λ(V) with a
  suitable orthogonality fan gives Theorem E. Not examined.
- Lehrer and Orlik–Solomon were not read.

---

## Reproduce

From `compute/` (plain Python 3, no third-party packages, imports nothing from the repo,
single process):

    python3 prior_art_theorem_e.py --nmax 7 > output/prior_art_theorem_e.txt   # ~3 s, ends "ALL CHECKS PASS: True", exit 0

Output lines:
- `[CTL]`: the 3-chain and the N-poset; each must report `all_OP=False` (not every
  partition is order-preserving).
- `[CLAW] K_n`, 3 ≤ n ≤ 7: `#OP = |Pi_n|` (Bell number), `|Aut| = e(P) = (n−1)!`,
  `free=True`, `orbits=1`.
- `[CLASS] n=3,4,5`: all connected labeled posets (12, 146, 3060); those with
  OP(P) = Π_n are exactly the 2n labelings of the claw and its dual, `mismatches=0`.

The literature part was done by fetching each arXiv PDF with
`curl -sL -o X.pdf https://arxiv.org/pdf/<id>` and `pdftotext -layout X.pdf X.txt`, then
reading the parts listed in §0.1.
