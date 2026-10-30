# Prior art for the fixed-point character formula for cones

This note checks the results of `notes/fixed_point_formula.md` ("[FP]")
against the literature. The results are:
- Theorem EZ (equivariant cone Zaslavsky) and Corollary EZ′ (cone PBW);
- Theorem CF (closed formula for μ(Λ(V)^g)) and its Corollaries P, V,
  Full and CF-braid;
- Proposition W (Weisner recursion), with the weaker hypothesis of
  Prop. W′ from `notes/audit_fixed_point_formula.md` ("[AFP]").

It also checks the step [FP] §1 uses to turn μ(Λ(V)^g) into a character
(the "homchar" step), and [FP] §6's account of Baclawski–Björner 1981.

Other notes cited: [GT] = `notes/general_theory.md`; [Thm] =
`notes/poset_jks_theorem.tex`; [NovGT] = `notes/novelty_general_theory.md`.
This note does not repeat the searches of [NovGT].

Verdicts:
- **KNOWN**: stated in a source read here, with the exact reference.
- **KNOWN FOR V = ALL CHAMBERS**: the case V = all chambers follows in a
  few lines from statements in sources read here; proper cones were not
  found.
- **SPECIAL CASE KNOWN**: a narrower special case is in a source read here.
- **NOT FOUND**: not in the sources of §0.1. This is the result of a
  search, not a proof of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is never counted
  as evidence either way. A statement about such a source that comes from
  another paper is marked "(secondary, via …)".

## Summary

| Claim of [FP] | Verdict | Closest prior art (read) |
|---|---|---|
| Homchar step: tr(g \| H̃_{d−2}(Λ̄(V))) = (−1)^d μ(Λ(V)^g), given Thm 1 | **KNOWN** (general poset fact) | Wachs, *Poset Topology*, Thm 4.6.1, attributed there to Baclawski–Björner 1981; AM *Topics*, Ch. 14 notes, attribute it to Baclawski–Björner 1979, Thm 1.1 |
| EZ (#V^g = Σ_{X ∈ 𝓛^g} χ_{V_X}(ḡ)) | **KNOWN FOR V = ALL CHAMBERS** (any finite group of linear symmetries). **NOT FOUND** for proper cones. | Moseley, Prop. 6.1 / Thm 1.4(b), combined with Sundaram–Welker Thm 2.5 (as stated in Wachs, Thm 5.4.2) and Wachs Thm 4.6.1 (§2.1) |
| EZ′ (C[V] ≅ ⊕ Ind_{G_X}^G Lie(V_X)) | same as EZ | same; for W = S_n, the classical case. DPR Prop. 4.7(a) is a different decomposition of C[W] over the same index set (§2.2) |
| Lemma F (fixed chambers ↔ chambers of the restriction to Fix g) | **KNOWN** (folklore; the averaging argument is in print) | Kamiya–Takemura–Terao, Prop. 2.7 |
| CF | **KNOWN FOR V = ALL CHAMBERS**, by Möbius inversion of the known full case of EZ. Not found stated. **NOT FOUND** for proper cones. | as EZ |
| Cor. Full | as CF: a formal consequence of known results, not found stated | as EZ |
| Cor. CF-braid, P an antichain | **SPECIAL CASE KNOWN**: the Möbius coefficients μ_{Π(K)^g}(σ, 1̂) are fixed-point partition-lattice Möbius numbers | Hanlon 1981, Thm 4 with Lemma 4 (§3.2) |
| Cor. CF-braid, general P | **NOT FOUND** here. Its value is [Thm, eq. closed], whose prior art [Thm] already discusses | — |
| Cor. P (pointed V: χ_V(g) = #V^g; free module) | **NOT FOUND** | — |
| Cor. V (vanishing) | **NOT FOUND** | — |
| Prop. W, and W′ | **NOT FOUND**, including for V = all chambers. The input, Weisner's theorem, is classical. The braid case is [Thm] (W). | — |
| Baclawski–Björner 1981 | **NOT ACCESSIBLE**. [FP] §6 mis-describes it (§5) | Wachs Thm 4.6.1 (secondary) |
| Lehrer 1987; Orlik–Solomon 1980 | **NOT ACCESSIBLE**. Secondary accounts concern H^*(M_C), the cohomology of the *complexified* complement, not chambers or cones (§4) | DPR §1–2; Felder–Veselov §1–2 |

**Bottom line.** For V = all chambers, EZ, EZ′ and CF are prior art in
substance, for every finite group of linear symmetries of A. The route is
Moseley's identification of the chamber space with H^*(M_3(A)) plus the
equivariant Goresky–MacPherson formula. A write-up should say so and cite
both. For proper cones (L ≠ R^d), no source read here states EZ, EZ′, CF,
Cor. P, Cor. V or Prop. W. The closest work on cones is Dorpalen-Barry and
Dorpalen-Barry–Proudfoot–Wang. It has no finite-group action, and it
indexes by the flats meeting the interior of the cone, not by the flats in
its lineality space (§2.3). Prop. W is not found even for the whole
arrangement.

## 0. Sources

### 0.1 Read

Full text: PDFs converted with `pdftotext -layout` and grepped. The listed
sections were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981) 319–341 | msp.org PDF (doi:10.2140/pjm.1981.96.319) | §1 (preliminaries; the fixed-point sublattice P^σ); §2 Lemmas 1–4; §5 Thm 4 and its proof; Thm 4A |
| Douglass–Pfeiffer–Röhrle, *Cohomology of Coxeter arrangements and Solomon's descent algebra*, arXiv:1101.2075v6 (Trans. AMS 2014) ("DPR") | arXiv PDF | §1 (introduction); §2.2–2.5 including Conjecture 2.1; Prop. 4.7. Grep: "regular representation", "Theorem", "Corollary" |
| Aguiar–Mahajan, *Topics in Hyperplane Arrangements* (AMS Surveys 226), authors' preliminary version, pi.math.cornell.edu/~maguiar/surv-226.pdf ("AM") | PDF | Table of contents; §3.3 in full; Ch. 14 notes (the paragraph on the character of H_{r−2}(Π[n])); App. C.4.6 and its notes. Grep: "Zaslavsky" (all 40 hits scanned), "fixed point", "equivariant", "stabiliz", "character of", "finite group", "group action", "Lefschetz" |
| Dorpalen-Barry, *The Varchenko–Gel'fand ring of a cone*, arXiv:2104.02740 ("DB") | arXiv PDF | §1.1–1.2 in full (definitions, Thm 1, Poin(K, t), eq. (1)); §2 opening. Grep: "symmetr", "equivariant", "stabiliz", "finite group", "character of" |
| Dorpalen-Barry–Proudfoot–Wang, *Equivariant cohomology and conditional oriented matroids*, arXiv:2208.04855 ("DPW") | arXiv PDF | §1.1–1.2 in full (Thm 1.1, Remark 1.2); §2 headings. Grep as for DB |
| Moseley, *Equivariant cohomology and the Varchenko–Gelfand filtration*, arXiv:1110.5369v2 (J. Algebra 2017) | arXiv PDF | Abstract; §1 (Thm 1.4, Remarks 1.5–1.6); §3 (Prop. 3.1, Cors. 3.2–3.3); §6 in full (Prop. 6.1, Examples 6.2–6.4) |
| Wachs, *Poset topology: tools and applications*, arXiv:math/0602226v2 | arXiv PDF | §1.3 (Goresky–MacPherson, Thm 1.3.8); §4.4 (Thm 4.4.1); §4.6 in full (Thm 4.6.1); §5.4 (Thm 5.4.2 and the text before it); reference list entries [13], [184] |
| Felder–Veselov, *Coxeter group actions on the complement of hyperplanes and special involutions*, arXiv:math/0311190v2 | arXiv PDF | §1–2 (introduction; Lefschetz-number argument; Prop. 2, attributed to Lehrer 1987) |
| Kamiya–Takemura–Terao, *Arrangements stable under the Coxeter groups*, arXiv:1103.5179v2 ("KTT") | arXiv PDF | §2 (Lemmas 2.1–2.5, Thm 2.6, eq. (1), Prop. 2.7); the paragraph citing Postnikov–Stanley |
| Kozlov, *Order complexes of noncomplemented lattices are nonevasive*, arXiv:math/9704225 (Proc. AMS 1998) | arXiv PDF | §1 (introduction); reference list |

### 0.2 Web searches

- Baclawski Björner "Fixed points and complements in finite lattices" pdf
- equivariant Zaslavsky theorem real hyperplane arrangement chambers fixed
  by group element Möbius function fixed lattice
- Moseley "Equivariant cohomology and the Varchenko-Gelfand filtration"
- Sundaram Welker "Group actions on arrangements of linear subspaces and
  applications to configuration spaces"
- Orlik Solomon "Unitary reflection groups and cohomology" trace fixed point
- Lehrer "On the Poincaré series associated with Coxeter group actions on
  complements of hyperplanes"

The second search returned no formula of the shape "#chambers fixed by g =
Σ over g-stable flats". Its nearest hit was KTT (read; §1.2).

**Positive controls for the negative greps.** DB has 0 hits for "symmetr",
"equivariant", "stabiliz", "finite group" or "character of". The same
grep instrument finds 22 hits for "Zaslavsky|chamber" in DB, so the text
layer is fine. DPW's hits for "equivariant" are all about the circle
T = U(1) (e.g. §2, "Background on Equivariant Cohomology"). Its one hit for
"stabiliz" is a T-stabilizer (line "the stabilizer of every point is
{±1} ⊂ T"). In Moseley, the same grep finds Thm 1.4(b) and §6, which are
the finite-group statements used below.

### 0.3 NOT ACCESSIBLE

- **Baclawski–Björner, *Fixed points and complements in finite lattices*,
  J. Combin. Theory Ser. A 30 (1981) 335–338.** The DOI is
  10.1016/0097-3165(81)90030-3. Crossref confirms the PII is
  0097316581900303. ScienceDirect (article page and /pdf), the Elsevier
  API, and WebFetch all returned HTTP 403. [FP] §6 tried PII
  0097316581900383, which is a different article. See §5.
- **Baclawski–Björner, *Fixed points in partially ordered sets*, Adv. Math.
  31 (1979) 263–287**: not attempted beyond the citation in AM.
- **Lehrer, *On the Poincaré series associated with Coxeter group actions
  on complements of hyperplanes*, J. London Math. Soc. (2) 36 (1987)
  275–294.** Not found open; used only via DPR and Felder–Veselov.
- **Orlik–Solomon, *Combinatorics and topology of complements of
  hyperplanes*, Invent. Math. 56 (1980) 167–189**, and **Orlik–Solomon,
  *Unitary reflection groups and cohomology*, Invent. Math. 59 (1980)
  77–94.** Springer returned a landing page, not the PDF. Used only via DPR
  §2.2.
- **Sundaram–Welker, *Group actions on arrangements of linear subspaces and
  applications to configuration spaces*, Trans. AMS 349 (1997)
  1389–1420.** ams.org returned 403, and the author's ftp copy did not
  download. Its Theorem 2.5 is used **as stated in Wachs, Thm 5.4.2**.
- **Stanley, *Some aspects of groups acting on finite posets*, JCTA 32
  (1982)** and **Postnikov–Stanley, *Deformations of Coxeter
  arrangements*** (cited in KTT for fixed chambers of a braid-type
  arrangement): not opened.
- **Douglass–Pfeiffer–Röhrle, *An inductive approach to Coxeter
  arrangements and Solomon's descent algebra*** (J. Algebraic Combin. 2012),
  and [DPR, refs. 6, 7, 12] (the rank ≤ 6 and rank 2 checks of
  Conjecture 2.1): not opened.

---

## 1. The homchar step and Lemma F

### 1.1 Homchar: KNOWN

[FP] §1 uses tr(g | H̃_{d−2}(Λ̄(V))) = (−1)^d μ(Λ(V)^g), given that the
homology is concentrated in degree d − 2 ([GT] Thm 1). This is the general
fixed-point Möbius theorem for posets. Wachs, Thm 4.6.1: "For any G-poset
P and g ∈ G, χ_P(g) = µ(P̂^g)." Here χ_P is the character of the virtual
representation ⊕_i (−1)^i H̃_i(P). Wachs (§4.6) says this consequence of
the Hopf–Lefschetz theorem "first appeared in the combinatorics literature
in the work of Baclawski and Björner [13]". Her [13] is the 1981 JCTA paper.

AM's notes to Ch. 14 attribute the same step to the 1979 Adv. Math. paper:
"Via Hopf-Lefschetz Theorem [36, Theorem 1.1], it coincides with the
Möbius number of the subposet of Π[n] fixed by the permutation". Their [36]
is Baclawski–Björner, *Fixed points in partially ordered sets*, Adv. Math.
31 (1979).

Both papers are NOT ACCESSIBLE here, so it is not settled which theorem
number in which paper is the right citation. Either way, the step is
standard and should be cited, not presented as part of the new work.

### 1.2 Lemma F: KNOWN (folklore)

KTT Prop. 2.7 and its proof contain the averaging argument of Lemma F, for
a W-stable real arrangement B:
- the average z(x) of a point x of a chamber b over the stabilizer W_b lies
  in b and is W_b-fixed;
- w fixes z(x) only if wb = b.

KTT eq. (1) is the Burnside count |Ch(C)| = Σ_{w ∈ W} Fix(w, Ch(B)). KTT
cite Postnikov–Stanley, Lemma 7.6, for "Fix(w, Ch(B_m)) = |Ch(B_k)|, where
k is the number of cycles of w". That is a chamber count of the
arrangement restricted to Fix(w), exactly the shape of Lemma F. Lemma F
does not need a citation as a new result. A one-line pointer to KTT
Prop. 2.7 is enough.

---

## 2. Theorem EZ and Corollary EZ′

### 2.1 V = all chambers: KNOWN, by combining three published statements

Take V = all chambers of A, so L = R^d, 𝓛 = L(A), and V_X is the whole
arrangement A_X/X in R^d/X. Let G be a finite group of linear symmetries
of A. Choose a G-invariant inner product, so G acts orthogonally.

1. **Moseley, Prop. 6.1** (also Thm 1.4(b)). "Suppose that a finite group
   W acts on A. Then W acts on both M1(A) and M3(A), and
   H^*(M3(A)) ≅ H^*(M1(A)) as W-representations." Here M1(A) is the
   complement of A in R^d, so H^0(M1(A)) = C[chambers]. M3(A) is the
   complement in (R^d)^3 of the codimension-3 subspaces H ⊗ R^3, H ∈ A.
   Moseley's Example 6.2 notes that for a Coxeter arrangement and its
   Weyl group this is the regular representation.
2. **Sundaram–Welker, Thm 2.5, as stated in Wachs, Thm 5.4.2, eq. (5.4.4).**
   For a G-arrangement 𝒜 of linear subspaces in R^D, with G orthogonal,

     H̃^i(M_𝒜) ≅_G ⊕_{x ∈ (L(𝒜)∖0̂)/G} (H̃_{D−2−i−dim x}((0̂, x)) ⊗ sgn_x ⊗ sgn_0̂)↑_{G_x}^G,

   where sgn_x(g) = det(g|_x). Apply this to 𝒜 = {H ⊗ R^3}, with D = 3d
   and g acting as g ⊗ 1:
   - The intersection lattice is L(A), with x = X ⊗ R^3, and the open
     interval (0̂, x) is the proper part of L(A_X/X).
   - sgn_x(g) sgn_0̂(g) = det(g|_X)^3 det(g)^3 = det(ḡ), where ḡ is the
     map induced on R^d/X.
   - For codim X = c, the homology degree is c − 2 exactly when i = 2c.

   So

     H^{2c}(M_3(A)) ≅ ⊕_{[X], codim X = c} Ind_{G_X}^G (det_{R^d/X} ⊗ H̃_{c−2}(proper part of L(A_X/X))).

   For c ≥ 1 the summand is [FP]'s Lie(V_X) for V = all chambers. The
   X = R^d term is H^0 = C, the trivial module.
3. **Wachs, Thm 4.6.1** (§1.1), together with Folkman's theorem (homology
   of a geometric lattice is concentrated in the top degree; quoted in
   Wachs §1.3). Together they give the character of Lie(V_X) at ḡ as
   (−1)^c det(ḡ) μ(L(A_X/X)^ḡ), which is [FP]'s χ_{V_X}(ḡ).

Combining 1–3:
- C[chambers] ≅ ⊕_{[X]} Ind_{G_X}^G Lie(A_X/X) as G-modules. This is EZ′
  for V = all chambers.
- Its character at g is EZ for V = all chambers.

No source read here writes the combined statement down. Each step is a
direct application, so EZ and EZ′ for the whole arrangement should be
presented as known. For G = S_n acting on the braid arrangement this is
the classical PBW decomposition of C[S_n]. Moseley's Remark 1.5 recovers
the related fact that H^*(Conf_n(R^3)) is the regular representation of
S_n.

The det(ḡ) twist that [FP] §2 calls "forced" is exactly the
sgn_x ⊗ sgn_0̂ orientation character of the equivariant Goresky–MacPherson
formula. This is an independent check on [FP]'s sign: the full-arrangement
case of EZ agrees with Sundaram–Welker plus Moseley, twist included.

### 2.2 Douglass–Pfeiffer–Röhrle: a different decomposition over the same index set

Let W be a finite Coxeter group. DPR Prop. 4.7(a) gives
E_λ ≅ Ind_{N_W(W_L)}^W(e_L CW_L), and §2.3 gives CW ≅ ⊕_λ E_λ:
- λ runs over the W-orbits of flats ("shapes");
- e_L is a BBHT idempotent of the descent algebra.

So DPR has a decomposition of the regular representation over W-orbits of
flats, into modules induced from N_W(W_X), which DPR §2.2 identifies with
the setwise stabilizer of X (citing Orlik–Solomon). Our EZ′ for
V = all chambers and G = W has the same index set and the same inducing
subgroups. Its summands are det_{R^d/X} ⊗ H̃_{c−2}, and by §2.1 these are
the summands of H^*(M_3(A)).

DPR's Conjecture 2.1 relates the Orlik–Solomon summand A_λ to E_λ through
the twist ε_c α_c with α_X(n) = det(n|_X). On N_W(W_X), εα_X is
det_{R^d/X}, the same twist as in EZ′. DPR prove Conjecture 2.1 for
symmetric groups (Thm 6.3). They report it proved in rank 2 and checked by
computer up to rank 6 (refs. [12], [6], [7]; not opened).

We did not determine whether e_L CW_L ≅ Lie(A_X/X) as N_W(W_X)-modules,
orbit by orbit. EZ′ asserts only the total isomorphism. The "general W"
case that [FP] §2 says it did not search for is covered by §2.1, without
needing DPR.

### 2.3 Proper cones: NOT FOUND

- **DB (arXiv:2104.02740).** For an open cone K cut out by hyperplanes of
  A, DB counts the chambers of A in K. The formula is
  #C(K) = Σ_{X ∈ L^int(K)} |µ(V, X)|, quoted from Zaslavsky [31, Example A]
  in DB §1.2 and §2. Thm 1 interprets Poin(K, t) as the Hilbert series of
  gr VG(K). L^int(K) is the set of flats meeting K. This index set is
  different from EZ's 𝓛 = {flats contained in L = lin V}. DB has no group
  action (0 hits; §0.2).
- **DPW (arXiv:2208.04855).** Thm 1.1 gives canonical isomorphisms
  gr VG(A, K) ≅ H^*(M_3(A, K); Z), and similarly for VG and Rees. Remark 1.2
  notes that K = V recovers Moseley. The only group in DPW is the circle T.
  DPW state no finite-group equivariance. Their isomorphisms are called
  canonical, so a G-equivariant version for symmetries g with gA = A and
  gK = K is plausible. If it holds, it would give a second character
  formula for C[V], from H^*(M_3(A, K)). That formula would presumably be
  indexed by L^int(K), not by 𝓛, and would not be EZ. This is a remark on
  what the literature would need, not a result.
- **AM.** AM treats cones, lunes, the lune decomposition of a cone over a
  flat in its base (§3.3.4, Prop. 3.22, eq. (3.23)), and invariant
  (W-fixed) subalgebras (Ch. 16). We found no statement about characters of
  a symmetry group on the chambers of a cone, and no fixed-point formula.
  The grep hits for "character of" are characters of the Tits and Birkhoff
  algebras (Ch. 9–13, App. D). Those are algebra characters, not group
  characters.
- **[NovGT]** already records that EZ at g = 1 ([GT] Thm 2) is an instance
  of Zaslavsky 1977. EZ is its Lefschetz refinement, and that refinement
  was not found.

**Verdict.** EZ and EZ′ for proper cones: NOT FOUND. For V = all chambers:
KNOWN, as a combination (§2.1).

---

## 3. Theorem CF and its corollaries

### 3.1 CF and Cor. Full

CF is the Möbius inversion of EZ over 𝓛^g. For V = all chambers it is
therefore a formal consequence of the known case of EZ (§2.1), together
with Lemma F. Cor. Full is that case. Neither CF nor Cor. Full was found
stated in this form, with the Möbius function of the fixed lattice L(A)^g
weighted by chamber counts of restrictions to Fix(g). They should be
presented as easy consequences of known results for the whole arrangement.
For proper cones, CF: **NOT FOUND**.

### 3.2 Cor. CF-braid, P an antichain: the coefficients are Hanlon's

For P an antichain on [n], Π(K) = Π_n, and CF-braid has coefficients
μ_{Π_n^g}(σ, 1̂). An upper interval [σ, 1̂] of Π_n^g is the fixed-point
lattice of the permutation that g induces on the blocks of σ. This
identification is our step; it is immediate from the definitions. So
every coefficient is a fixed-point partition-lattice Möbius number.

**What Hanlon proves (read).**
- Hanlon §1 notes that P^σ is a sublattice for any lattice P.
- Lemma 4 reduces Π(N)^σ to the case of m cycles of a common length j,
  where j is the squarefree part of gcd(l_1, …, l_m). The reduction is
  through 𝓜, the meet-sublattice of coatom meets together with 1̂.
- **Thm 4** gives the Birkhoff (characteristic) polynomial of 𝓜:
  (λ − 1)^r (λ − j)(λ − 2j)⋯(λ − (m − 1)j), with r the number of prime
  divisors of j. "In particular" it gives μ(0̂, 1̂) = μ(j)(−1)^{m−1}(m − 1)! j^{m−1},
  with μ(j) the number-theoretic Möbius function.

Thm 4 is stated for 𝓜, not for L = Π(N)^σ. The step to μ_L(0̂, 1̂) is the
crosscut theorem, and it is not in Hanlon as read:
- μ_L(0̂, 1̂) = μ_𝓜(0̂, 1̂) when 0̂_L ∈ 𝓜;
- μ_L(0̂, 1̂) = 0 otherwise.

Example: for σ = (12)(3), 𝓜 = {12|3, 1̂} but L is the chain
0̂ < 12|3 < 1̂, so μ_L(0̂, 1̂) = 0. AM's Ch. 14 notes say the same: the
Möbius number of the fixed subposet "follows from a result of Hanlon [207,
Theorem 4]".

So [FP] §6's sentence "Hanlon … computes μ(Π_n^σ)" is right in substance,
with the theorem number now checked: Thm 4, via Lemma 4 and the crosscut
theorem. Hanlon does not treat order-preserving partitions, cones or
nontrivial P.

### 3.3 Cor. P and Cor. V: NOT FOUND

Neither the statement that χ_V(g) = #V^g on pointed cones, nor the
freeness of H̃_{d−2}(Λ̄(V)) over C[Stab_W(V)], nor the vanishing criterion
"a hyperplane contains both L and Fix(g)" appears in the sources read.

For V = all chambers, Cor. P is empty (L = R^d is never 0 for d ≥ 1) and
Cor. V says nothing either: then L = R^d, so no hyperplane contains L.
They are genuinely cone statements.

The braid case of Cor. P is [Thm, Cor. connected], and its prior art is
discussed in [Thm].

---

## 4. Lehrer, Orlik–Solomon and the complexified complement

Both are NOT ACCESSIBLE (§0.3). From the secondary accounts read:
- **DPR §1.** "In 1987, Lehrer determined the character of the
  representation of W on H^*(M_W) when W = S_n … by explicitly computing
  the equivariant Poincaré polynomials P_{S_n}(g, t) =
  Σ_p trace(g, H^p(M_W)) t^p." Blair–Lehrer (2001) give a general form over
  the centralizer. Felder–Veselov describe how the character of H^*(M_W)
  differs from the regular character.
- **DPR §2.2**, citing Orlik–Solomon and Lehrer–Solomon:
  - N_W(W_X) is the setwise stabilizer of X;
  - A ≅ ⊕_X A_X;
  - A_λ ≅ Ind_{N_W(W_X)}^W(A_X).
- **Felder–Veselov, §2.** They compute characters of H^*(M_G) as Lefschetz
  numbers, that is, Euler characteristics of fixed sets of g on the
  *complex* complement. Prop. 2 is attributed to Lehrer. The twisted action
  (reflections combined with complex conjugation) gives the regular
  representation for S_n (their Prop. 3).

All of this concerns M_W = the complexified complement, whose total
cohomology is *not* the regular representation (DPR §1: "A simple
computation for S_3 shows that this is not the case"). [FP]'s EZ′ for
V = all chambers lives on M_3, not M_W. The two differ exactly by the
twist det_{R^d/X} on each summand (§2.1–2.2). None of these secondary
accounts mentions chambers fixed by g, cones, or the lineality space.

Unverified expectation: Orlik–Solomon's fixed-point/trace results are
about H^*(M_C), so they would not contain EZ for proper cones. This stays
unverified until the papers are read.

---

## 5. Proposition W (Weisner recursion): NOT FOUND

Weisner's theorem itself is classical; [Thm, Lemma weisner] states and
proves it. No source read here applies it to a fixed-point lattice L^g or
Λ(V)^g with a = Fix(g) or cl(Fix g). That includes V = all chambers, where
Prop. W reads μ(L(A)^g) = −Σ_{0 ≠ X ∈ L(A)^g, X ∩ Fix g = 0} μ(L(A_X/X)^ḡ).
Hanlon's computation (§3.2) goes through supersolvability and modular
elements, not this recursion. The braid case is [Thm] (W). The weakened
hypothesis of [AFP] Prop. W′ ("Fix(g) lies in a hyperplane") was not found
either.

---

## 6. Baclawski–Björner 1981: what [FP] §6 says, and what the sources say

[FP] §6 reports, from a search summary of the MathSciNet record, that this
paper proves "a non-evasiveness (hence collapsibility) statement for the
proper part of a finite lattice with a set of elements removed that
contains all complements of an element x". It concludes that "nothing in
the record suggests a formula for μ(L^g)". The sources read here do not
support that description.

- **Wachs, Thm 4.6.1**, attributes exactly the fixed-point Möbius formula
  χ_P(g) = µ(P̂^g) to Baclawski–Björner [13], the 1981 JCTA paper (§1.1).
  So, per Wachs, the paper does contain a fixed-point Möbius result. It is
  the general poset fact behind [FP]'s homchar step, not a formula for
  cones.
- **Kozlov, arXiv:math/9704225**, is the source of the *non-evasiveness*
  theorem for noncomplemented lattices. Its introduction traces that line
  through Crapo, Baclawski (Z-acyclicity), Björner 1981 *Homotopy type of
  posets and lattice complementation* (contractibility, [Bj81, Thm 3.3]),
  Björner–Walker and Kozlov. It does not cite Baclawski–Björner 1981. The
  non-evasiveness description in [FP] §6 appears to conflate Baclawski–
  Björner 1981 with Kozlov 1998 and/or Björner 1981.
- **Web-search summary only (not read):** an AMS Notices article (2022) is
  reported to state Baclawski–Björner 1981's theorem as "for a finite
  non-complemented lattice L, the truncated lattice L ∖ {0, 1} has the
  fixed-point property". This is the order-theoretic fixed-point property.
  The URL ams.org/notices/202202/rnoti-p190.pdf returned 403.

**Bearing on [FP].** Even on the most generous reading, Baclawski–Björner
1981 supplies the general fixed-point Möbius identity (already used in
[FP] §1) and possibly a fixed-point property for noncomplemented lattices.
Neither is EZ, CF or Prop. W. A Crapo-type or fixed-point-property argument
on 𝓛^g or Λ(V)^g remains a candidate for [FP] §5's OPEN vanishing
criterion. That is a suggestion, not a finding.

---

## 7. Suggested changes to [FP] (not applied)

Per the standing constraints, [FP] is not edited. Suggested changes:
- §1 (homchar): cite the fixed-point Möbius theorem as Wachs, Thm 4.6.1 /
  Baclawski–Björner (1979 Thm 1.1 per AM; 1981 per Wachs).
- §2 (after Cor. EZ′) and §6: replace "We did not search for the general-W
  case in the literature" and "Douglass–Pfeiffer–Röhrle; NOT CHECKED" with
  the following:
  - for V = all chambers and any finite group G of linear symmetries, EZ′
    is Moseley Prop. 6.1 combined with Sundaram–Welker Thm 2.5 (Wachs
    Thm 5.4.2), and EZ is its character;
  - DPR Prop. 4.7(a) gives a different decomposition of C[W] over the same
    index set;
  - novelty is claimed only for proper cones.
- §3: present Cor. Full as the Möbius inversion of that known case. Cite
  KTT Prop. 2.7 for the averaging step of Lemma F.
- §6, Hanlon: "Thm 4 (with Lemma 4 and the crosscut theorem)". The
  formula is for the coatom-meet lattice 𝓜, and μ(Π_n^σ) = 0 when
  0̂ ∉ 𝓜.
- §6, Baclawski–Björner: replace the non-evasiveness description with §6
  above. Correct the PII (0097316581900303) and keep the paper marked NOT
  ACCESSIBLE.
- Verdict table, row BB: "inaccessible; per Wachs Thm 4.6.1 it contains the
  fixed-point Möbius theorem χ_P(g) = μ(P̂^g), a general poset fact used in
  §1, not a cone formula".
