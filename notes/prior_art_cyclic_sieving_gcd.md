# Prior art for `notes/cyclic_sieving_gcd.md`: Theorem G (non-vanishing of X_P at roots of unity) and the iff form of Theorem C

This note checks the two claims of `notes/cyclic_sieving_gcd.md` ([GCD])
against the literature. [GCD] itself says that no literature search was made
for them (§6, last paragraph).

The notation is that of [GCD] §0. W = ∏_i S_{k_i}, X_P is the fake-degree
polynomial of the W-set Cyc(P), ζ = e^{2πi/e}, and a(e) = Σ_i ⌊k_i/e⌋.
Theorem G is about the regime e > max k_i, that is, a(e) = 0.

The verdict labels are those of `notes/prior_art_cyclic_sieving_cyc.md`
([PACSC]) and `notes/prior_art_cyclic_sieving_cyc_2.md` ([PACSC2]):
- **KNOWN**: stated in a source read here, with the exact reference and
  statement.
- **PARTLY KNOWN**: a special case, or the main mechanism, is in a source
  read here. The rest was not found.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.

## Verdict

| Claim of [GCD] | Verdict | Closest prior art (read) |
|---|---|---|
| **Theorem G**: X_P(ζ) ≠ 0 for e ≥ 6, e > max k_i, except P = A_3 at e = 6 | **NOT FOUND.** Every evaluation of a fake degree, q-binomial or Molien term at a root of unity found in the sources is in the regime where e divides a degree (a(e) ≥ 1). There the numerator vanishes, and the work is a pole count (§1.2). None of them treats a(e) = 0, where X_P(ζ) is the defining Molien sum at ζ with nothing cancelled. None asks whether a *nonnegative combination* of fake degrees can vanish there. The phase/ray argument (Lemma 3, the projection S3, Lemma 4) was not found. The closest mechanism is a sign-coherence argument of Alexandersson–Pfannerer–Rubey–Uhlin, used at regular roots of unity for skew characters (§1.3). Two easy facts sit next to Theorem G and were not found stated as such either. Each irreducible fake degree of W is nonzero at ζ when e > max k_i; this follows at once from Stanley's q-hook formula (§1.1). And Lam–Leung's theorem shows that no argument from coefficient positivity alone can give Theorem G when e has two prime factors (§1.4) | Stanley's q-hook formula (as restated in Billey–Konvalinka–Swanson Thm 2.11); Alexandersson–Pfannerer–Rubey–Uhlin Cor. 27; Lam–Leung Main Theorem; Sagan Cor. 2.5; RSW Prop. 4.2; Swanson Thm 8 proof; Morita–Nakajima Prop. 2 |
| **Corollary H / Theorem C as an iff**: X_P sieves ⟨g⟩ (g conjugate into W) iff (a) and (b) hold, for every gcd(k_i) | **PARTLY KNOWN** (unchanged from [PACSC], [PACSC2]). Sufficiency at regular elements is Springer's theorem in CSP form ([PACSC]). Necessity reduces to evaluating X_P at the right roots of unity; that reduction is RSW Prop. 2.1(i) and is the definition of a CSP. No source read gives a CSP criterion for the fake degree at a *non-regular* element, or any iff criterion for a fixed action. The necessity of (a) when gcd(k_i) > 1, which is the new content of [GCD], was not found. The iff statements that do exist have a different form. Alexandersson–Amini (quoted in APRU §1) characterise when f ∈ N[q] is a CSP polynomial for *some* action of C_n. APRU's main theorem uses that criterion for the long cycle, which is regular. Stucky Thm 3.2 gives sufficient conditions for elements of cycle type (m^{(n−1)/m}, 1) or (m^{(n−2)/m}, 1, 1), and a failure example (§1.5) | RSW Prop. 2.1, Remark 2.3; Sagan §8 (via [PACSC]); APRU §1, Cor. 27; Stucky Thm 3.2; Springer [Sp74] Prop. 4.5 (via [PACSC2]) |

**Bottom line.** Neither claim of [GCD] was found. A write-up could add
three citations as context. None of them changes a label:
1. Stanley's q-hook formula, for "each irreducible constituent alone does
   not vanish at ζ; the content of Theorem G is that the nonnegative sum
   X_P = Σ_χ m_χ f_χ does not cancel".
2. Lam–Leung, for "positivity of coefficients alone cannot rule out
   cancellation when e is not a prime power". This applies to every e used
   in Corollary H.
3. APRU Cor. 27, as the nearest relative of the phase argument: a
   cancellation-free evaluation, but at regular roots of unity (e | n).

The gap left open by [PACSC2] §0.4 is still open: Lehrer–Taylor Ch. 11 §6
("Eigenvalues of pseudoregular elements") was again not obtainable (§0.4).
It concerns the a(e) ≥ 1 regime, eigenspaces of maximal dimension a(e). It
is therefore unlikely to contain Theorem G, which lives at a(e) = 0.

## 1. What the sources say

### 1.1 Irreducible fake degrees: non-vanishing is immediate

Stanley's formula ([Sta99] 7.21.5, restated as Billey–Konvalinka–Swanson
[BKS] Thm 2.11, read):

  SYT(λ)^maj(q) = q^{b(λ)} [n]_q! / ∏_{c ∈ λ} [h_c]_q,

and by Lusztig–Stanley this is the fake degree f^λ(q) of S^λ ([BKS]
abstract and §2). For W = ∏ S_{k_i}, the fake degree of an irreducible
⊠_i S^{λ^i} is the product of the factors f^{λ^i}(q).

*Consequence (derived here, not stated in [BKS]).* Let e > max k_i. Every
q-integer [j]_q with j ≤ k_i < e is nonzero at ζ, and every hook length is
at most k_i. So every irreducible fake degree of W is nonzero at ζ. The
claim of Theorem G is therefore a non-cancellation statement for the
nonnegative combination X_P = Σ_χ ⟨C[Cyc P], χ⟩ f_χ ([PACSC], Theorem A
row). The A_3 exception shows that cancellation really can happen:
X_{A_3} = 1 + q³ = f^{(3)} + f^{(1³)}, with f^{(3)} = 1 and f^{(1³)} = q³.
The sum vanishes at ζ_6 although neither term does. (This decomposition is
a 3-line check: Cyc(A_3) consists of the 2 classes of S_3/C_3, and
Ind_{C_3}^{S_3} 1 = S^{(3)} ⊕ S^{(1³)}.)

No source read makes the observation above, or asks the question it leads
to.

### 1.2 Evaluations at roots of unity in the literature: all with a(e) ≥ 1

Each of the following evaluates a q-analogue at a root of unity whose order
divides a degree. The mechanism is to count vanishing factors in the
numerator and the denominator.
- **Sagan, survey, Cor. 2.5** (arXiv:1008.0790, read): for ω = ω_d and
  d | n, [n+k−1 choose k]_ω = (n/d + k/d − 1 choose k/d) if d | k, and 0
  otherwise. The proof counts the zero factors of the numerator and the
  denominator.
- **RSW Prop. 4.2(i)–(iv)** (read): the same type of evaluation for q-binomials at
  ω of order d | n, for an, an + k, and so on.
- **Swanson, *On the existence of tableaux with given modular major index***
  (arXiv:1701.04963, read: §1, §2, the proof of Thm 8 and Lemma 4). It
  evaluates f^λ at ω_n^s of order ℓ, with n = ℓs. "The order of vanishing of
  the numerator at q = ω_n^s is then #{i ∈ [n] : i ≡_ℓ 0} = s, and the order
  of vanishing of the denominator is #{c ∈ λ : h_c ≡_ℓ 0}." This is
  Fomin–Lulov's formula for χ^λ at rectangles. Swanson's main Theorem 3
  ("a_{λ,r} is positive except in the following cases") is a positivity
  statement about the *coefficients* of f^λ mod q^n − 1, not about
  evaluations at e > n.
- **Morita–Nakajima, *The coinvariant algebra of the symmetric group as a
  direct sum of induced modules***, Osaka J. Math. 42 (2005) 217–231 (read:
  §1, Props. 1–2, Lemma 3). Prop. 2 applies "Stembridge's argument" to the
  Molien terms at a primitive d-th root of unity with d | n. A term survives
  only if "all the vanishing factors in the numerator are canceled by
  corresponding factors in the denominator". This is the pole-order mechanism
  of [PACSC2] Proposition E.
- **Springer, Stembridge, Lehrer–Michel**: the same mechanism, for regular ζ,
  as recorded in [PACSC2] §2 (read there, not re-read here).

At a(e) = 0 the numerator ∏(1 − q^{d_i}) does not vanish at ζ, so there
is nothing to count, and none of these sources says anything there.

### 1.3 Alexandersson–Pfannerer–Rubey–Uhlin: a cancellation-free evaluation

*Skew characters and cyclic sieving* (arXiv:2004.01140v2; read: abstract,
§1, Cor. 27 with Lemma 26, and the proof at the end of §8).
- Cor. 27: for a skew shape λ/μ of size n = dm, the Murnaghan–Nakayama sum
  for χ^{λ/μ}((m^d)) "is cancellation-free". "In particular,
  f^{λ/μ}(ξ^d) = χ^{λ/μ}((m^d)) = ε|BST(λ/μ, m)|", with ξ a primitive n-th
  root of unity and ε a single sign. The proof shows that all border-strip
  tableaux have the same height parity (Lemma 26, via Pak's flips).
- The end of §8: "f^λ(ξ^d) is non-zero only if and only if BST(a^b, m) is
  non-empty."

This is a non-vanishing criterion for fake degrees at roots of unity, and
it is proved by putting every term on one ray, as in Theorem G. But the
regime and the object are different. The root of unity ξ^d has order m | n,
so it is regular for the long cycle and a(m) ≥ 1. The object is a skew
character of S_n, not a nonnegative sum of fake degrees at a(e) = 0. It
also has no analogue of Lemma 4 (the ratio bound using y ≥ 1). In Theorem G
the terms lie on four rays, and they are controlled by magnitude, not by a
sign-coherence bijection.

### 1.4 Lam–Leung: positivity alone cannot give Theorem G

T. Y. Lam, K. H. Leung, *On vanishing sums of roots of unity*, J. Algebra
224 (2000) 91–109 (arXiv:math/9511209, read: §1 and the Main Theorem).
"For any m = p_1^{a_1} ⋯ p_r^{a_r} …, the weight set W(m) is exactly given
by N p_1 + ⋯ + N p_r." In particular, "if 6 | m, then W(m) consists of all
non-negative integers ≠ 1."

X_P has nonnegative integer coefficients and X_P(1) = e_C(P) ([PACSC],
Theorem A row). So X_P(ζ) is a sum of e-th roots of unity of weight e_C(P).
Two consequences (derived here):
- For e = p^a a prime power, X_P(ζ) = 0 forces p | e_C(P), since
  Φ_{p^a}(1) = p. This is a cheap partial version of Theorem G at
  prime-power e. Those e are not needed for Corollary H.
- For e with at least two prime factors, which is every e that Corollary H
  uses, every weight ≥ 2 is realised by some vanishing sum. Positivity of
  the coefficients therefore gives no obstruction. Theorem G has to use the
  structure of X_P, as [GCD] does (Lemmas 1–4).

### 1.5 Necessity and iff statements for cyclic sieving

- **RSW Prop. 2.1** (read): the CSP is equivalent to (i) the evaluations
  X(ω(c)) = |X^c|, (ii) the coefficient description mod q^n − 1, and (iii)
  the isomorphism C[X] ≅ A_X of C-modules. Remark 2.3 says that a CSP for C
  restricts to every subgroup. Corollary H is a failure of (i) at
  c = g^{N/e}, so it is in the framework of Prop. 2.1(i). RSW contains no
  statement about non-regular elements (grep "not regular / non-regular": 0
  hits, as in [PACSC] §0.3).
- **Sagan, survey** (read for this note: abstract, §2 through Cor. 2.5, §9
  opening. §6 and §8 were read in [PACSC]). There is no necessity theorem
  for fake degrees at non-regular elements. Sagan Thm 8.2 is the
  regular-element CSP ([PACSC]).
- **Rhoades, *Cyclic sieving, promotion, and representation theory***
  (arXiv:1005.2568, read: §1 to the statement of Thm 1.3, Remark 3.2, the
  paragraph after Example 5.2, and grep). Its necessity remarks are of the
  form "the hypothesis that λ be rectangular … is necessary". That is,
  the CSP fails for non-rectangular shapes, shown by example. The
  "nonvanishing" hits (2) are about Kazhdan–Lusztig immanants. There is no
  root-of-unity non-vanishing statement.
- **Alexandersson–Amini criterion** (quoted in APRU §1, not opened): "f ∈
  N[q] is a cyclic sieving polynomial for a group action of the cyclic group
  of order n, if and only if for a primitive nth root of unity ξ and all
  k | n we have that f(ξ^k) ∈ N and" a Möbius-sum condition. This is an iff
  for the *existence* of some action. Theorem C is about the given action of
  ⟨g⟩ on Cyc(P).
- **Stucky, *Parity-unimodality and a cyclic sieving phenomenon for
  necklaces*** (arXiv:1812.04578v3, read: §1, Prop. 3.1, Thm 3.2 and the
  remarks after it). Molien's formula is used for τ of cycle type
  (m^{(n−1)/m}, 1) or (m^{(n−2)/m}, 1, 1), both Springer-regular in S_n.
  Necessity is shown only by an example: "the desired sieving fails for
  H = ⟨(1234)(5678)(90)⟩ ≤ S_10 and τ = (1)(2408)(3795)(6)". It also says:
  "when n ≢ 1, 2 mod m the situation appears much more delicate, and we do
  not have a general conjecture."
- **Ahlbach–Swanson, *Cyclic sieving, necklaces, and branching rules
  related to Thrall's problem*** (arXiv:1808.06043, read: abstract, §1, grep).
  They give a CSP approach to Kraśkiewicz–Weyman, Stembridge and Schocker
  for C_a ≀ S_b ↪ S_ab, all at regular elements. Nothing on evaluations at
  e > n.
- **Kraśkiewicz–Weyman** (2001), via the restatement of Swanson Thm 2
  (read): ⟨S^λ, χ^r↑_{C_n}^{S_n}⟩ = a_{λ,r} = #{T ∈ SYT(λ) : maj T ≡ r mod n}.
  For P = A_k this identifies X_{A_k} = Σ_λ a_{λ,0} f^λ ([PACSC], antichain
  row). The literature on a_{λ,0} (Sundaram's conjecture, proved as Swanson
  Thm 3) is about which a_{λ,0} are positive. The single-type antichain case
  of Theorem G, X_{A_k}(ζ_e) ≠ 0 for e > k, e ≥ 6, is a statement about this
  same polynomial. It was not found.

## 0. Sources

### 0.1 Read for this note

PDFs were downloaded into a scratch directory, converted with
`pdftotext -layout`, and grepped. The parts listed in §1 were read in full.
The text read is the version in the second column. Journal data for the
arXiv items (and for Lam–Leung in §1.4) come from search results, and were
not checked against the published versions.

| Source | Obtained from |
|---|---|
| [RSW] Reiner–Stanton–White, *The cyclic sieving phenomenon*, JCTA 108 (2004) 17–50 | published version, S. Billey's course page (washington.edu); pp. 17–50 complete |
| [Sag] Sagan, *The cyclic sieving phenomenon: a survey* | arXiv:1008.0790 |
| Rhoades, *Cyclic sieving, promotion, and representation theory*, JCTA 117 (2010) | arXiv:1005.2568v1 |
| Swanson, *On the existence of tableaux with given modular major index*, Algebraic Combinatorics 1 (2018) | arXiv:1701.04963v2 |
| Ahlbach–Swanson, *Cyclic sieving, necklaces, and branching rules related to Thrall's problem* | arXiv:1808.06043v1 |
| [BKS] Billey–Konvalinka–Swanson, *Tableau posets and the fake degrees of coinvariant algebras*, Adv. Math. (2020) | arXiv:1809.07386v2 (abstract, §2.3 through Thm 2.11 and Remark 2.12, §2.4 opening) |
| Stucky, *Parity-unimodality and a cyclic sieving phenomenon for necklaces* | arXiv:1812.04578v3 |
| Morita–Nakajima, *The coinvariant algebra of the symmetric group as a direct sum of induced modules*, Osaka J. Math. 42 (2005) | Osaka University repository (doi 10.18910/4880) |
| Lam–Leung, *On vanishing sums of roots of unity* | arXiv:math/9511209v1 |
| [APRU] Alexandersson–Pfannerer–Rubey–Uhlin, *Skew characters and cyclic sieving*, Forum Math. Sigma (2021) | arXiv:2004.01140v2 |

Springer 1974, Stembridge 1989, Lehrer–Michel 2003, Geck–Malle and Koonin
were read for [PACSC2] (§0.1 there). They are used here only through that
note, and were not re-read.

### 0.2 Web searches

- fake degree polynomial nonzero at root of unity order greater than degrees
  reflection group permutation representation (extended)
- cyclotomic factors of fake degrees symmetric group "Phi_d" divides fake
  degree Young subgroup induced representation
- cyclic sieving phenomenon necessary condition polynomial must vanish
  characterization "if and only if" non-regular element symmetric group
  (extended)
- "major index" "divisible by n" permutations generating function q
  evaluated at root of unity nonzero Ind_{C_n}^{S_n} trivial graded
  multiplicity coinvariant
- Molien series sum over group 1/det(1 − q g) evaluated at root of unity
  nonvanishing phase argument sum of terms positive real
- Lehrer Taylor "pseudoregular" element eigenvalues reflection group fake
  degree pdf
- cyclic sieving "fake degree" non-regular elements criterion Young subgroup
  product of symmetric groups 2023 OR 2024 OR 2025 arXiv (extended)

These returned the papers of §0.1 and some tangential ones: Reiner–Yun
arXiv:1201.0032 (the root-permutation fake degree is divisible by [h]_q, a
vanishing statement at regular ζ, already listed in [PACSC]); Lehrer
arXiv:1812.03606 (opened in [PACSC2]); Adin–Roichman arXiv:0708.1675;
Westbury arXiv:0912.1512 (read in [PACSC]). None of them returned a
non-vanishing statement at roots of unity of order exceeding every degree,
or a CSP criterion at non-regular elements.

### 0.3 Positive controls for the negative greps

Case-insensitive match counts in the text files:

| file | "root(s) of unity" | "regular" | "nonvanish / non-vanish" | "cyclotomic" | "Molien" | "poset" | "linear extension" |
|---|---|---|---|---|---|---|---|
| RSW | 12 | 28 | 0 | 0 | 0 | 0 | 0 |
| Sagan | 10 | 35 | 0 | 0 | 0 | 2 | 1 |
| Rhoades | 14 | 8 | 2 | 1 | 0 | 3 | 1 |
| Swanson 2017 | 4 | 1 | 0 | 0 | 0 | 0 | 0 |
| Ahlbach–Swanson | 8 | 5 | 0 | 0 | 1 | 1 | 0 |
| BKS | 3 | 0 | 0 | 5 | 0 | 25 | 0 |
| Stucky | 8 | 1 | 0 | 0 | 3 | 0 | 0 |
| Morita–Nakajima | 6 | 6 | 0 | 0 | 0 | 0 | 0 |
| Lam–Leung | 44 | 3 | 0 | 5 | 0 | 0 | 0 |
| APRU | 19 | 1 | 0 | — | — | — | — |

- "root(s) of unity" fires in every file, and it located the statements
  quoted in §1 (Sagan Cor. 2.5, Swanson Thm 8, Morita–Nakajima Prop. 2,
  APRU Cor. 27). So the text extraction works.
- "nonvanish" is a working instrument: it fires twice in Rhoades, on the
  Kazhdan–Lusztig immanant passages (lines about Skandera's theorem). It
  fires nowhere else.
- "Molien" fires in Stucky (3) and Ahlbach–Swanson (1), and finds the
  regular-element uses quoted in §1.5. Its 0 in RSW and Sagan is consistent
  with their wording ("principal specialization", "Hilbert series").
- BKS's 25 "poset" hits are its tableau posets. Sagan's one "linear
  extension" is "acts on CX by linear extension" ([PACSC] §0.3). The
  Rhoades "linear extension" hit was not followed up, since the paper has
  no root-of-unity non-vanishing statement.
- APRU was grepped for "root(s) of unity" (19), "regular" (1, a citation
  of [Sp74]), "nonvanish" (0), "if and only if" (15, each statement scanned)
  and "fake degree" (5). The other columns were not run on it (—).

### 0.4 Not accessible / not read

- Lehrer–Taylor, *Unitary Reflection Groups*, Ch. 11 §6. Still not
  obtained; the search in §0.2 again returned no copy. See [PACSC2] §0.4.
- Kraśkiewicz–Weyman 2001 and Alexandersson–Amini 2019. Not opened. They
  are used only as quoted in Swanson 2017 Thm 2 and APRU §1.
- Stanley, EC2 7.21.5. Not opened. It is used as restated in BKS Thm 2.11.
- Lehrer–Springer 1999, Broué–Malle–Michel 1993: as in [PACSC2] §0.4.

## References

[GCD] = `notes/cyclic_sieving_gcd.md`; [CSC] = `notes/cyclic_sieving_cyc.md`;
[PACSC] = `notes/prior_art_cyclic_sieving_cyc.md`; [PACSC2] =
`notes/prior_art_cyclic_sieving_cyc_2.md`. Other sources are as listed in §0.1.
