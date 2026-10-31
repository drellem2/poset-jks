# Prior art for the per-cone vanishing note (Lemma Pal, Theorem TA, Theorem Cr, Conjecture CR_V)

This note checks four claims of `notes/per_cone_vanishing.md` ("[PCV]")
against the literature:
- **Lemma Pal** ([PCV] §2): an anti-automorphism t of a finite poset Q
  admits a linear extension w with t(w_i) = w_{n+1−i} iff t² = 1 and t has
  at most one fixed point;
- **Theorem TA** ([PCV] §3): the criterion (TA1)–(TA4) for
  χ_{C_P}(−τ) ≠ 0 on the poset cones of the braid arrangement, with its
  closed formula;
- **Theorem Cr** ([PCV] §1): Formula Z on all chambers, with Lemma M
  substituted, is Crapo's complementation theorem relative to U = Fix g;
- **Conjecture CR_V** ([PCV] §4): χ_V(g) = 0 iff Λ(V)^g has an element
  without a complement.

Notation is that of [PCV]. Verdicts are used as in
`notes/prior_art_vanishing_criterion.md` ("[PA]"):
- **KNOWN**: stated in a source read here, with the exact reference.
- **SPECIAL CASE KNOWN**: a narrower case is in a source read here.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is never counted
  as evidence either way. A statement about it that comes from another
  paper is marked "(secondary, via …)".

## Verdict

| Claim of [PCV] | Verdict | Closest prior art (read) |
|---|---|---|
| **Lemma Pal**, "only if" | **KNOWN** (folklore). The proof is two lines, and t² = 1 is a real condition: a self-dual poset can have no involutive anti-automorphism (Ziegler's example, Stanley EC1 2nd ed., Exercise 3.8 and Fig. 3.69) | EC1 Ex. 3.8 |
| **Lemma Pal**, "if" | **KNOWN in substance, as type-B linear extensions.** After relabelling (§1.1), (Q, t) is a *B_n poset* in Chow's sense, and the t-palindromic extensions are its *type-B linear extensions*. The "if" direction says that every B_n poset has a type-B linear extension. That follows at once from Chow's fundamental lemma for type-B P-partitions (Chow 2001, Thm 2.1.4; secondary, via Kim–Searles 2026, Thm 2.8), together with the existence of one type-B P-partition (§1.1). For Reiner's signed posets, a subclass, it is stated: "every signed poset has a linear extension (see the proof of [Reiner 1993, Theorem 3.3])" (Csar 2014, §3.3). The iff, in the form "t² = 1 and at most one fixed point", was not found stated | Chow (secondary); Reiner, *Signed posets*, JCTA 62 (1993), Thm 3.3; Csar 2014 §3.3; Petersen 2005 Def. 2.5 and Lemma 2.7; Kim–Searles 2026 §2 |
| **Lemma Pal**, the count pal_t(Q) and Lemmas Sh, E | **NOT FOUND** as used. The palindromic extensions are the fixed points of the involution w ↦ t(rev w) on L(Q), that is, of the *swap* map of Banaian–Barnard–Chepuri–Striker 2025 (Def. 5.1) on linear extensions. That paper does not study its fixed points. They are **not** the self-evacuating extensions of Stembridge's q = −1 phenomenon (Stanley 2009, Thm 3.1), which use evacuation and need no self-duality. Lemma E(i) is the exponential formula (EC2 §5.1, as [PCV] says). E(iii) was not searched separately | Stanley, *Promotion and evacuation* (2009) §3; Banaian et al. arXiv:2508.19440 §5 |
| **Theorem TA**, (TA1)–(TA4) and the closed formula (3.3)–(3.5) | **NOT FOUND.** No source read gives a character value, Lie-type or otherwise, of an element of ±S_n on a single poset cone, or treats −τ for an anti-automorphism τ. The all-chambers values are classical (Hanlon 1981; Stanley 1982 Lemma 7.1; [PA]). The {m, 2m} rule (TA1) is Theorem A (A−) of [VC], already NOT FOUND in [PA]. The cone literature (Dorpalen-Barry–Kim–Reiner; Dorpalen-Barry–Proudfoot–Wang) has no group actions. The type-B poset literature (Reiner, Chow, Petersen, Csar, Kim–Searles) has palindromic extensions but no characters of −τ on C_P | §0; [PA] §0; `notes/novelty_search_2.md` for the per-cone +w side |
| **Theorem Cr**, U a flat | **KNOWN** as a theorem: it *is* Crapo's complementation theorem for the element U of M = L(A)^g (Crapo 1966, Thm 3; stated as EC1 Ex. 3.92). **NOT FOUND**: Lemma M, i.e. that the multiplicities m_X(all) of Formula Z are the inner sums ±Σ_{Z ⊇ X, Z ∈ Z\*} μ(Z, R^d) of Crapo's double sum. **SPECIAL CASE KNOWN**: Hanlon's case (braid arrangement, g = w ∈ S_n), where the complements form an antichain ([PA] §2.1) | Crapo via EC1 Ex. 3.92 (Crapo primary NOT ACCESSIBLE); Hanlon 1981 §5 via [PA] |
| **Theorem Cr**, U not a flat (the "virtual element") | **The lattice identity is KNOWN in a more general form; its vanishing input is NOT FOUND.** Z\*(g) is a convex subset of M (§2). The Björner–Walker complementation formula for a convex subset K (Björner–Walker 1983, as stated by Gálvez-Carrillo–Kock–Tonks 2024, abstract and §1) gives μ(M) = μ_{M∖Z\*}(0̂, 1̂) + Σ_{X ≤ Z in Z\*} μ(0̂, X) μ(Z, 1̂). So (Cr) is equivalent to μ_{M∖Z\*}(0̂, 1̂) = 0. That vanishing is what Lemma M adds. It was not found. COMPUTED on the braid arrangement (§2) | Gálvez-Carrillo–Kock–Tonks arXiv:2409.03742; Björner–Walker 1983 (NOT ACCESSIBLE, secondary) |
| **CO** (uncomplemented element ⇒ χ_V(g) = 0) | **KNOWN**: EC1 Ex. 3.92, "Deduce that if μ(0̂, 1̂) ≠ 0, then L is complemented", applied to the finite lattice Λ(V)^g | EC1 Ex. 3.92 |
| **Conjecture CR_V** (the converse) | **NOT FOUND.** It is false for general finite lattices: the smallest complemented lattice with μ(0̂, 1̂) = 0 has 8 elements (COMPUTED, §3.2). **SPECIAL CASE KNOWN** for lattice classes that do not include the Λ(V)^g in general: for a finite *modular* lattice, μ(0̂, z) ≠ 0 iff [0̂, z] is complemented (Knop, arXiv:2209.10337, Lemma A.2). This covers fixed sublattices Λ^g of a modular Λ (Knop, after (A.8)). For *distributive* lattices, complemented ⇔ boolean ⇔ μ ≠ 0 (EC1 §3.4 list and Example 3.9.6). CR_V also holds trivially when Λ(V)^g has length ≤ 2 (§3.3). No converse of Crapo's corollary was found for fixed lattices L(A)^g, for cone lattices Λ(V), or for any non-semimodular class | Knop App. A; EC1 §§3.4, 3.9, Ex. 3.92 |

**Bottom line.**
- Lemma Pal is a known fact in another language. A write-up should say so
  and cite Chow's B_n posets (via Petersen 2005 or Kim–Searles 2026) and
  Reiner 1993 Thm 3.3. Its proof can stay, since it is shorter than the
  translation.
- Theorem TA and its closed formula were not found.
- Theorem Cr for U a flat is Crapo's theorem by construction. Lemma M was
  not found. For U not a flat, the Björner–Walker convex-subset form of
  Crapo is the right frame: (Cr) says exactly that the Möbius number of
  M ∖ Z\* vanishes.
- CR_V was not found. The "if" half is Crapo's corollary (EC1 Ex. 3.92). The
  converse is known for modular and distributive lattices only.

---

## 0. Sources

### 0.1 Read

Full text. PDFs were converted with `pdftotext -layout` and grepped. The
listed sections were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., author's online version of 15 July 2011 ("EC1") | math.mit.edu/~rstan/ec/ec1.pdf (the copy used by `notes/citation_check.md`) | §3.3 (complemented, Prop. 3.3.3); §3.4 (FTFDL and the list a.–i. of equivalent conditions); Cor. 3.9.5 and Example 3.9.6; Prop. 3.10.1; Exercises 3.8 (with solution and Fig. 3.69), 3.28, 3.92–3.93 with solution 3.92. Grep: "self-dual", "antiautomorphism", "complemented", "join of atoms" |
| Stanley, *Promotion and evacuation*, Electron. J. Combin. 16(2) (2009) #R9 | arXiv:0806.4717 | §3 in full (Thm 3.1, Lemma 3.2, the q = −1 paragraph); references [26]–[29]. Grep: "self-dual", "anti", "dual", "order-reversing", "palindrom", "involution" |
| Reiner, *Signed posets*, J. Combin. Theory Ser. A 62 (1993) 324–360 | author's page, `Papers/SignedPosets.pdf` (scan; OCR is poor) | Theorem 3.3 statement and the start of its proof (the r = 0 base case) |
| Petersen, *Enriched P-partitions and peak algebras* (extended abstract), arXiv:math/0512366 | arXiv | §2: Def. 2.5 (B_n poset), the paragraph defining L_B(P), Fig. 4, Def. 2.6, Lemma 2.7 |
| Kim–Searles, *Poset modules of the 0-Hecke algebras of type B*, arXiv:2601.22926 | arXiv | Abstract; §1; §2 around Def. 2.7 and Thm 2.8 (Chow's Thm 2.1.4); §3.1. Grep: "linear extension" |
| Csar, *Root and weight semigroup rings for signed posets*, PhD thesis, Minnesota 2014, arXiv:2311.06387 | arXiv | Props. 3.1.5–3.1.6 (signed posets as posets on [−n, n]); §3.3 (Def. 3.3.1–3.3.2 and the sentence on existence of linear extensions; Prop. 3.3.3) |
| Banaian–Barnard–Chepuri–Striker, *Orbitmesy and promotion on self-dual posets*, arXiv:2508.19440 | arXiv | Abstract; §1; §5 to Lemma 5.7 (Def. 5.1, swap). Grep: "palindrom", "fixed", "linear extension", "κ" |
| Knop, *Multiplicities and dimensions in enveloping tensor categories*, arXiv:2209.10337v2 | arXiv | Appendix A in full (Lemma A.2, Thm A.3, Cor. A.4, Thm A.6, (A.8) and the paragraph after it) |
| Gálvez-Carrillo–Kock–Tonks, *Convex decomposition spaces and Crapo complementation formula*, arXiv:2409.03742 | arXiv | Abstract; §1 (the formula μ_X = μ_{X∖K} + μ_X ∗ ζ_K ∗ μ_X and the attribution to Björner–Walker); end of §5.4; references |
| Dorpalen-Barry–Kim–Reiner, *Whitney numbers for poset cones*, arXiv:1906.00036 (Order 2021) | arXiv | Grep: "equivariant", "automorphism", "anti", "character", "order-reversing", "symmetr", "question". The only "character" hits are the characterization of L_int(K_P) and det over a parabolic. Open problems §5 (5.5–5.7) concern Poincaré polynomials |
| Dorpalen-Barry–Proudfoot–Wang, *Equivariant cohomology and conditional oriented matroids*, arXiv:2208.04855 | arXiv | Grep: "group act", "automorphism", "character", "symmetric group". "Equivariant" refers to the circle group T = U(1) (§2), not a finite group acting on a cone |

### 0.2 Web searches

- self-dual poset linear extensions fixed by duality involution
  anti-automorphism palindromic (extended)
- Stembridge "q = −1 phenomenon" self-evacuating linear extensions poset
- "involutory dimension" involution posets Order linear extensions
  isotropic orthogonal; Al-Agha Greechie involutory linear extension (extended)
- Stanley "Promotion and evacuation" self-dual poset linear extensions
- Reiner signed posets type B linear extensions poset on ±[n]
  order-reversing involution
- converse Crapo complementation theorem lattice Möbius function zero every
  element complemented (extended)
- complemented lattice with μ(0̂, 1̂) = 0 example; Björner "On complements in
  lattices of finite length" (extended)
- Möbius function fixed point lattice group action complement vanishing iff
  uncomplemented element
- Möbius function lattice of acyclic partitions of a poset, fixed points,
  anti-automorphism, braid arrangement cone (extended)
- poset cone / preposet braid arrangement Lie character signed permutation
  order-reversing linear extensions palindromic
- Dorpalen-Barry Proudfoot Wang equivariant cohomology conditional oriented
  matroids group action

None returned a character value of −τ on a poset cone, an {m, 2m} rule, or a
converse of Crapo's corollary for a non-semimodular class. The fixed-lattice
search returned Knop's appendix (§3.3).

**Positive controls for the negative greps.**
- EC1: "complemented" finds §3.3, the §3.4 list and Ex. 3.92–3.93.
  "antiautomorphism" finds Fig. 3.69. So EC1 statements about
  complementation and anti-automorphisms are found when present.
- Stanley 2009: "involution" finds Thm 2.1(a) ("evacuation is an
  involution") and the q = −1 paragraph. No hit is a self-duality of P.
- Banaian et al.: "κ" finds Def. 5.1 and Lemma 5.7, so the swap involution is
  found. "fixed" has no hit about swap-fixed labelings.
- DKR and DPW: "symmetric group" finds the A_{n−1} discussion (DKR line 16),
  so the grep sees group language. No hit concerns a group acting on a
  cone.

### 0.3 NOT ACCESSIBLE

- **Chow, *Noncommutative symmetric functions of type B*, PhD thesis, MIT
  2001.** Not opened. Content (secondary, via Kim–Searles §2 and Petersen
  §2): B_n posets on {0, ±1, …, ±n} with i <_P j ⇒ −j <_P −i; type-B linear
  extensions; the fundamental lemma A^B(P) = ⊔_{E ∈ L^B(P)} A^B(E)
  (Thm 2.1.4).
- **Al-Agha–Greechie, *The involutory dimension of involution posets*,
  Order 18 (2001) 323–337.** Springer redirected to a login, and DeepDyve
  returned 403. Content (secondary, via search snippets of the abstract):
  "involution posets" (P, ≤, ′) with ′ an order-reversing involution; the
  involutory dimension is the least number of linear extensions "involutory
  with respect to ′" whose intersection is ≤. It "exists iff any pair of
  isotropic elements are orthogonal". A linear order with an involutive
  anti-automorphism is palindromic, so these are the t-palindromic
  extensions of Lemma Pal. Whether the paper states the existence of one
  such extension, and under which condition on fixed points, could not be
  checked. This is the most likely place for a verbatim Lemma Pal.
- **Björner–Walker, *A homotopy complementation formula for partially
  ordered sets*, European J. Combin. 4 (1983) 11–19.** Not opened. Used
  only as stated by Gálvez-Carrillo–Kock–Tonks.
- **Crapo, *The Möbius function of a lattice*, J. Combin. Theory 1 (1966)
  126–131.** Not opened, as in [PA] and `notes/citation_check.md` §3.4. Used
  as stated in EC1 Ex. 3.92, whose solution names it Thm 3.
- **Stembridge, *Canonical bases and self-evacuating tableaux*, Duke Math.
  J. 82 (1996) 585–606**, and Stembridge's 1994 papers. Not opened. Content
  (secondary, via Stanley 2009 §3): the q = −1 phenomenon.
- **Dorpalen-Barry, PhD thesis (Minnesota).** The repository URL
  returned an HTML page, not the PDF. Its content appears in arXiv:2104.02740
  and DKR, which [FP] and `notes/general_theory.md` already record as having
  no finite-group action.
- **Birkhoff, *Lattice Theory*, 3rd ed.** Not opened. Used only through
  Knop's citation for "1̂ a join of atoms ⇒ complemented" in modular lattices.

---

## 1. Lemma Pal

### 1.1 Translation to type-B linear extensions

Let t be an involutive anti-automorphism of Q with at most one fixed point.
- Label one element of each 2-orbit {x, t x} by i ∈ [k] and the other by −i.
  Label the fixed point 0, or adjoin an isolated point 0 if there is none.
- Then x < y ⇒ t y < t x reads i <_P j ⇒ −j <_P −i. So Q ∪ {0} is a
  B_k poset in Chow's sense (Petersen Def. 2.5; Kim–Searles §2).
- A linear order on {0, ±1, …, ±k} is itself a B_k poset iff its unique
  anti-automorphism, reversal, is i ↦ −i, i.e. iff it is palindromic with 0
  in the middle. So the type-B linear extensions are exactly the
  t-palindromic extensions with 0 inserted in the middle. If 0 was adjoined,
  deleting it is a bijection back to the t-palindromic extensions of Q.

**Existence from Chow's lemma.**
- Kim–Searles Thm 2.8 (Chow's Thm 2.1.4): A^B(P) = ⊔_{E ∈ L^B(P)} A^B(E),
  where A^B(P) is the set of f : [−k, k] → Z with f order-preserving, strict
  on i ⪯ j with i > j, and f(−i) = −f(i).
- A^B(P) ≠ ∅: f(x) = h↓(x) − h↑(x) works, with h↓, h↑ the lengths of the
  longest chains below and above x. It is strictly increasing
  (x < y ⇒ f(y) − f(x) ≥ 2), and f(t x) = −f(x) because t swaps h↓ and h↑.
- So L^B(P) ≠ ∅. This is the "if" direction of Lemma Pal.

This short derivation is ours. None of the sources read states the corollary
for Chow posets. For Reiner's signed posets, which are the B_k posets that
also satisfy i < −i ⇒ i < 0 < −i (Csar Prop. 3.1.5), Csar §3.3 states it
with a pointer to the proof of Reiner's Thm 3.3. That proof is an induction
that adds one root at a time (read for the base case).

The (Q, t) of [PCV] need not satisfy Reiner's extra condition. Example:
Q = {a < b} ⊔ {p}, t = (a b) and p fixed, so a < t(a) with a, p incomparable.
So Reiner's statement alone is a special case, and Chow's framework is needed
for the general one.

### 1.2 The condition t² = 1

EC1 Exercise 3.8 asks for a self-dual poset with no order-reversing
involution. The solution gives Ziegler's example, Fig. 3.69, which with 0̂
and 1̂ adjoined is a lattice. By Lemma Pal no anti-automorphism of that poset
has a palindromic linear extension. So the hypothesis is not vacuous among
self-dual posets.

### 1.3 Not the q = −1 phenomenon

Stanley 2009 Thm 3.1: W′_P(−1) = #dual P-domino tableaux = #self-evacuating
linear extensions, for every finite natural P. There, self-evacuation is
w = wε, with no duality of P involved. The palindromic extensions are the
fixed points of a different involution, w ↦ t(rev w), which exists only for
self-dual P. In Banaian et al. this involution is "swap" (Def. 5.1:
swap(f)(x) = q + 1 − f(κ(x)), at q = |P|). Neither source counts its fixed
points. No q = −1 statement for pal_t(Q) was found.

## 2. Theorem Cr and the Björner–Walker split

*Z\*(g) is convex in M = L(A)^g.* Let X ⊆ Y ⊆ Z with X, Z ∈ Z\*. Then
Y ∩ U ⊆ Z ∩ U = 0, and Y + U ⊇ X + U lies in no hyperplane. So Y ∈ Z\*.

Gálvez-Carrillo–Kock–Tonks (§1) state the Björner–Walker formula for a
convex K in a finite poset: μ_X = μ_{X∖K} + μ_X ∗ ζ_K ∗ μ_X. At (0̂, 1̂),
with 0̂, 1̂ ∉ K, this reads

  μ(M) = μ_{M∖Z\*}(0̂, 1̂) + Σ_{X ≤ Z in Z\*} μ_M(0̂, X) μ_M(Z, 1̂).

Since μ(M) = (−1)^{dim U} χ_all(g), (Cr) is equivalent to
μ_{M∖Z\*}(0̂, 1̂) = 0. When U is a flat, Z\* is the set of complements of U,
and this vanishing is the content of Crapo's theorem: in M ∖ U^⊥, U has no
complement. When U is not a flat, the vanishing follows from Lemma M and
Formula Z ([PCV] §1). No source read proves it directly.

COMPUTED (`compute/prior_art_per_cone_vanishing.py`, check BW). For every
g = ±w ∈ ±S_n with 3 ≤ n ≤ 6, U ≠ 0 and R^d ∉ Z\*, the script checks three
statements: Z\* is convex, the split holds, and μ_{M∖Z\*}(0̂, 1̂) = 0. That is
1,306 group elements, 434 with Z\* ≠ ∅ and 200 with μ(M) ≠ 0. They include
the −w, whose U is not a flat (for example −(1 2), with U spanned by
e_1 − e_2). Control: removing one element of Z\* from the convex set breaks
the vanishing on 4 elements at n = 4 and 1 at n = 5.

## 3. Conjecture CR_V

### 3.1 The "if" half (CO)

EC1 Ex. 3.92 states Crapo's formula and adds: "Deduce that if μ(0̂, 1̂) ≠ 0,
then L is complemented." Applied to the finite lattice Λ(V)^g, this is CO.
The [PCV] citation (Crapo, via Stanley 1982 §7) is correct. EC1 Ex. 3.92 is
a sharper pointer, since it states the corollary itself.

### 3.2 The converse fails for general lattices

[PCV] §5 says, without an example, that a lattice can have μ = 0 with every
element complemented. Confirmed. An exhaustive search over lattices with at
most 8 elements (COMPUTED, check CL) finds none with 7 or fewer elements and
61 labelled 8-element ones. One of them, with atoms a, b, c and coatoms
x, y, z:

  a < y, a < z;  b < x, b < y;  c < x   (and 0̂ < a, b, c;  x, y, z < 1̂).

- μ(a) = μ(b) = μ(c) = −1, μ(x) = μ(y) = 1, μ(z) = 0, so μ(0̂, 1̂) = 0.
- Every element has a complement. For example, z ∧ b = 0̂ and z ∨ b = 1̂.
- EC1 Cor. 3.9.5 does not apply, since 1̂ = x ∨ y ∨ z is a join of atoms
  and 0̂ is a meet of coatoms.

So any proof of CR_V must use the geometry of Λ(V)^g, as [PCV] §5 says.

### 3.3 Classes where the converse is known

- **Modular lattices.** Knop, Lemma A.2: for a finite modular lattice Λ and
  z ∈ Λ, μ(0̂, z) ≠ 0 ⇔ z is a join of atoms ⇔ [0̂, z] is complemented
  ⇔ z ≤ soc Λ. The proof cites EC1 3.9.5, Birkhoff IV §5 Thm 6, and the
  argument of EC1 Prop. 3.10.1. After (A.8), Knop applies this to the fixed
  sublattice Λ^g of a group acting on a modular Λ. Since Λ^g is again
  modular, μ(Λ^g) = 0 unless every g-stable element has a g-stable
  complement. With Lemma A.2 this is an "iff". It is the exact analogue of
  CR_V, in the case where Λ(V)^g is modular.
- **Distributive lattices.** EC1 §3.4 lists "boolean ⇔ complemented" for
  finite distributive lattices, and Example 3.9.6 gives μ = ±1 on boolean
  intervals and 0 otherwise.
- **Length ≤ 2.** A lattice 0̂ < a_1, …, a_k < 1̂ has μ(0̂, 1̂) = k − 1. It has
  an uncomplemented element iff k = 1. So CR_V holds whenever Λ(V)^g has
  length ≤ 2, in particular for every arrangement in R^2. This is our
  remark; no source was needed.

These classes do not cover the lattices of [PCV]. L(A) is geometric, but
L(A)^g is in general not semimodular. Λ(V) is not even closed under
intersection ([PCV] §4). For the braid arrangement, Π_n is not modular for
n ≥ 4, and neither are the fixed lattices Π_n^w in general. Results for
semimodular lattices (EC1 §3.10) do not apply either, for the same reason.

## 4. Corrections and remarks on [PCV] (not applied)

- Lemma Pal: add the type-B reference (§1.1). The lemma is the existence of
  type-B linear extensions of Chow's B_n posets. Its proof can stay.
- CO: EC1 Ex. 3.92 states the corollary "μ ≠ 0 ⇒ complemented" verbatim. It
  is a better pointer than Stanley 1982 §7 for that sentence.
- §5, "a lattice can have μ = 0 with every element complemented": true. The
  8-element example of §3.2 can be cited, and it is the smallest.
- §5, CR_V: the modular case is known (Knop Lemma A.2 and the remark after
  (A.8)). It is worth a sentence, with the caveat of §3.3 that the lattices
  of [PCV] are not modular.
- Theorem Cr, Remarks: "(Cr) is Crapo's formula for a 'virtual' element" can
  be made precise. By Björner–Walker for the convex set Z\*, (Cr) is
  equivalent to μ_{M∖Z\*}(0̂, 1̂) = 0 (§2).
- No claim of [PCV] was found to be wrong.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 prior_art_per_cone_vanishing.py > output/prior_art_per_cone_vanishing.txt   # ~5 s, ends "ALL CHECKS PASSED", exit 0

Checks: BW (Z\* convex, the Björner–Walker split and μ_{M∖Z\*} = 0, for
±S_n with 3 ≤ n ≤ 6, plus a control that must fail) and CL (smallest
complemented lattice with μ = 0). The archived log is
`compute/output/prior_art_per_cone_vanishing.txt`.

Source texts were fetched with `curl` from the URLs of §0.1 and converted
with `pdftotext -layout`.

References: [PCV] = `notes/per_cone_vanishing.md`; [PA] =
`notes/prior_art_vanishing_criterion.md`; [VC] =
`notes/vanishing_criterion.md`; [FP] = `notes/fixed_point_formula.md`.
