# Prior art for cyclic sieving on Cyc(P), part 2: Springer and Lehrer–Springer eigenspace theory

This note follows up `notes/prior_art_cyclic_sieving_cyc.md` ([PACSC]).
[PACSC] left one gap open: it had not read the eigenspace theory of
Springer and Lehrer–Springer, which it named as the most likely place for
prior art on Theorem B(ii) and Theorem C of `notes/cyclic_sieving_cyc.md`
([CSC]). This note reads that theory, as far as it could be obtained (§0),
and gives a verdict on three claims of [CSC]: Theorem B(ii), Theorem C, and
the closed form (★) of [CSC] §3, which the ELI5 introduction prints as (⋆).

Notation is that of [CSC]. W = ∏_i S_{k_i} acts on V = ⊕_i C^{k_i} by
permuting coordinates, F(w) = |Cyc(P)^w|, and X_P is the fake-degree
polynomial of [CSC] §3. For a finite complex reflection group G on V with
degrees d_1, …, d_n, and for e ≥ 1, let a(e) = #{i : e | d_i}. For
W = ∏ S_{k_i} the degrees are 1, …, k_i for each i, so
a(e) = Σ_i ⌊k_i/e⌋.

The verdicts are those of [PACSC]:
- **KNOWN**: stated in a source read here, with the exact reference and
  statement.
- **PARTLY KNOWN**: a special case, or the main mechanism, is in a source
  read here. The rest was not found.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.

## Verdict

| Claim of [CSC] | Verdict | Closest prior art (read) |
|---|---|---|
| **Theorem B(ii)**: X_P(ζ) = 0 for ζ a primitive e-th root of unity when e ∤ some k_i and e ≤ max k_i | **PARTLY KNOWN.** The upgrade from [PACSC] is that the *method* is Springer's. At q = ζ, only the elements whose ζ-eigenspace has the maximal dimension a(e) contribute to the Molien sum. This is the argument of the proof of [Sp74] Prop. 4.5, and it rests on [Sp74] Thm 3.4(i): max_g dim V(g, ζ) = a(e). The same pole-order computation is the proof of Lehrer–Michel 2003 Thm 2.3 and of Stembridge 1989 (2.6b). Every source read uses it only for regular ζ, or for the sums Σ T^{d(g,ζ)} det′(1 − ζ^{−1}g)^{σ−1} over all of G. None states the resulting evaluation for an arbitrary module at a non-regular ζ (Proposition E below), and none applies it to a set like Cyc(P). The step special to [CSC] is Lemma 1 (the support of F). It is not in any source read | [Sp74] Thm 3.4(i), Prop. 4.5 and its proof; Lehrer–Michel 2003 Thm 2.3 and its proof; Stembridge 1989 §2, Thm 2.2 and sketch of proof, (2.6b) |
| **Theorem C**: X_P sieves ⟨g⟩, g ∈ W, iff (a) and (b) (sufficiency PROVEN; necessity of (b) PROVEN; necessity of (a) PROVEN when gcd(k_i) = 1) | **PARTLY KNOWN** (unchanged from [PACSC]). The regular case is Springer's theorem in CSP form, as [PACSC] says. The non-regular powers go through B(ii), whose mechanism is Springer's (row above). No source read states a cyclic sieving result, or any fake-degree evaluation, at a non-regular *element*. None gives an iff criterion, or the necessity statements (b) and Proposition 3. [Sp74] §8 does extend some results to non-regular elements, but only rationality of characters (8.5) and products of two involutions (8.7). It says nothing about eigenvalues or fake degrees | [Sp74] Prop. 4.5, §8; Geck–Malle 2003 Thms 1.10–1.12 |
| **(★)**: X_{T^{⊔k}}(q) = Σ_{d∣k} (φ(d)/d)(c_{k/d}/(k/d)!)(q;q)_k/(1 − q^d)^{k/d} | **NOT FOUND** (unchanged from [PACSC]). The eigenspace theory is about general reflection groups and their (sub)quotients. No source read specialises it to permutation modules of S_k, writes out the cycle index, or mentions posets or linear extensions (§0.3) | — |

**Bottom line.** Nothing in [CSC] turned out to be KNOWN outright in the
sources read here. The one attribution to add is that the proof of
Theorem B, in both parts, is Springer's evaluation argument. Part (ii) is
that argument run at a root of unity that need not be a regular
eigenvalue, combined with Lemma 1. The source that remains most likely to
state the general evaluation principle at non-regular ζ is Lehrer–Taylor
Ch. 11 §6, "Eigenvalues of pseudoregular elements". It could not be
obtained (§0.4), and it remains the one open gap.

## 1. The general evaluation principle

The following is the statement that the sources of §0 use without stating
it in this generality. It is included so that the attribution in the
Verdict can be checked.

**Proposition E (PROVEN; the method is that of [Sp74] Prop. 4.5).** Let
G ≤ GL(V) be a finite complex reflection group with degrees d_1, …, d_n.
Let χ be any class function on G, and let
f_χ(q) = ∏_i (1 − q^{d_i}) · |G|^{−1} Σ_{g ∈ G} χ(g)/det(1 − qg).
Let ζ be a primitive e-th root of unity, A = {i : e | d_i}, a = |A|, and
M = {g ∈ G : dim V(g, ζ^{−1}) = a}. Then

  f_χ(ζ) = |G|^{−1} ∏_{i ∈ A} d_i ∏_{i ∉ A} (1 − ζ^{d_i}) · Σ_{g ∈ M} χ(g) ∏_{λ} (1 − ζλ)^{−1},

where λ runs over the eigenvalues of g other than ζ^{−1}, with
multiplicity. In particular, if χ vanishes on M, then f_χ(ζ) = 0.

*Proof.* At q = ζ the numerator ∏(1 − q^{d_i}) has a zero of order exactly
a. Each factor 1 − q^{d_i} with i ∈ A is d_i(1 − q/ζ) + O((q − ζ)²). The
term of g has a pole of order dim V(g, ζ^{−1}) ≤ a, by [Sp74] Thm 3.4(i)
(applied to ζ^{−1}, which has the same order). So the terms with
dim V(g, ζ^{−1}) < a vanish at q = ζ. For g ∈ M, each eigenvalue ζ^{−1}
gives a factor 1 − q/ζ, which cancels against one factor d_i(1 − q/ζ). ∎

For W = ∏ S_{k_i} on ⊕ C^{k_i}, dim V(w, ζ^{−1}) is the number of cycles
of w whose length is divisible by e. A cycle of length p with e | p
contributes p, and a cycle with e ∤ p contributes 1 − ζ^p. For one type
(W = S_k) the formula reads

  X(ζ) = Σ_{λ ⊢ k, #{parts divisible by e} = ⌊k/e⌋} (F(λ)/z_λ) · e^{⌊k/e⌋}⌊k/e⌋! · ∏_{j ≤ k, e ∤ j}(1 − ζ^j) / (∏_{e | p} p · ∏_{e ∤ p}(1 − ζ^p)),

with p running over the parts of λ. The type-A formula was checked
numerically while writing this note. The check used random integer class
functions F on S_k, every k from 2 to 7 and every e from 2 to k, and
compared the formula with the exact polynomial f_F(q) evaluated at
ζ = exp(2πi/e): 21 of 21 cases agreed. As a positive control, the same
comparison without the factor e^{⌊k/e⌋}⌊k/e⌋! failed in 21 of 21. The
check script is not committed; the proof above does not depend on it.

**How [CSC] Theorem B follows.** By [CSC] Lemma 1, F(w) ≠ 0 forces every
cycle of w on the copies to have the same length d, with d dividing every
k_i. Such a w lies in M only if a(e) = 0, or if e | d and Σ k_i/d = a(e).
- In case (ii), e ≤ max k_i gives a(e) ≥ 1. Then e | d would force e to
  divide every k_i, so F vanishes on M and X_P(ζ) = 0.
- In case (i), the elements of M ∩ supp F are contained in the class of
  cycle type (e^{k_i/e})_i (they are equal iff F(w_e) ≠ 0), and the formula
  gives F(w_e).

This is the proof [CSC] already gives, in its own notation. [CSC] counts
the orders of the zeros of T_λ(q) by hand instead of quoting [Sp74]
Thm 3.4(i), which is legitimate for type A. Proposition E also explains
the role of clause (a) of Theorem C. When e > max k_i, a(e) = 0, so M = W.
Then X_P(ζ) = ∏_i (ζ; ζ)_{k_i} · (1/|W|) Σ_w F(w)/det(1 − ζw), the
definition evaluated at ζ. The prefactor is nonzero, and nothing forces
the sum to vanish. This is the case a(e) = 0. For gcd(k_i) = 1 it is
settled by [CSC] Proposition 3; for gcd(k_i) > 1 it is
`notes/cyclic_sieving_gcd.md` Theorem G and Corollary H (PROVEN; audit
HOLDS, `notes/audit_cyclic_sieving_gcd.md`), which answer [CSC] §9
problem 2. (Corrections F1–F3 of the audit
`notes/audit_prior_art_cyclic_sieving_cyc_2.md` are applied in this
paragraph and the one above.)

## 2. What each source says

**Springer 1974** ([Sp74], read directly, §0.1).
- Thm 3.4: (i) max_g dim V(g, ζ) = a(d); (ii) every V(g, ζ) lies in one of
  maximal dimension; (iii) the maximal ones are G-conjugate.
- Prop. 3.5: bounds and properties of H_0 = H/H′, where H is the stabiliser
  of a maximal V(g, ζ) and H′ its pointwise stabiliser. It is a reflection
  group when equality holds in (i), and in particular when H′ = 1.
- Thm 4.2: for regular g, (i)–(v), including the eigenvalues ζ^{−p_i} of g.
- Prop. 4.5: for g as in 4.2 and χ irreducible, χ(g^i) = f_χ(ζ^{−i}).
  Its proof reads: "Multiply both sides of (1) by (1 − T)^{a(d)} and then
  put T = 1. In the left-hand side of (1) we get nonzero contributions only
  from the h with dim V(h, ζ) = a(d), all of which are conjugate to g by
  4.2(iv)." The first sentence is the mechanism of Proposition E. The
  second, "all of which are conjugate to g", is where regularity is used.
- §8: "a result about elements of Weyl groups (8.4) which will allow us to
  extend 4.6 and 4.8 to nonregular elements". 4.6 is about products of two
  involutions and 4.8 about rationality of characters. Neither concerns
  eigenvalues on modules or fake degrees.

**Lehrer–Michel 2003** (read in full).
- Thm 2.3: for σ ∈ Gal(Q̄/Q), the identity
  Σ_g T^{d(g,ζ)} det′(1 − ζ^{−1}g)^{σ−1} = ∏_{j ∈ B_σ(d)}(T + m_j(σ)) · (explicit constant)
  when a(d) = b_σ(d), and 0 otherwise. Here d(g, ζ) = dim V(g, ζ).
- Corollaries 2.4–2.7 are special cases of Thm 2.3.
- Thm 3.1: d is regular iff a(d) = b(d), the number of codegrees divisible
  by d.
- The proof of Thm 2.3 is the pole-order computation of Proposition E,
  applied to the Orlik–Solomon two-variable Molien series of the Galois
  conjugates V^σ (Prop. 2.2), not to an arbitrary module.
- §3 uses only the coefficient of T^{a(d)} to recover the Lehrer–Springer
  theorems (Theorems 1.1, 1.2: N/C is a reflection group on a maximal
  eigenspace E, and the regularity criterion).
- In the proof of Thm 3.1 the set {g : V(g, ζ) = E} is identified as a
  coset g_0 C of the pointwise stabiliser C of E. M in Proposition E at a
  non-regular ζ is the union of such cosets over the conjugates of E.
- There is no statement about fake degrees of a general module at ζ.

**Stembridge 1989** (§§0–2 and §3 through Lemma 3.4 read).
- Thm 2.2 restates [Sp74] (4.5) for ω-regular g. Its sketch of proof
  contains (2.6b), whose proof notes: "The numerator of (2.4) has a zero of
  order |{i : m | d_i}| at q = ω, whereas the denominator has a zero of
  order dim V(h, ω^{−1}) …".
- Everything in §2 is for regular elements. Thm 3.3 (conjectured by
  Stanley) does treat every w ∈ S_n, regular or not. It gives the
  eigenvalues of w on S^λ through the μ-index of standard tableaux, a
  polynomial that depends on the cycle type μ of w. It is proved by
  restricting to the Young subgroup S_{μ_1} × ⋯ × S_{μ_l}, in which each
  cycle of w is a regular element (Lemma 3.4, via skew characters). So it
  describes non-regular elements by a polynomial other than the fake
  degree, and it says nothing about the fake degree at a non-regular ζ.

**Geck–Malle 2003**, Handbook of Algebra chapter "Reflection groups"
(§§1.7–1.12 read). Thm 1.10 restates [Sp74] Thm 3.4 and 6.2. Thm 1.11
restates [Sp74] Thm 6.4 and Prop. 4.5 (regular elements). Thm 1.12 states
the Lehrer–Springer theorem: N/C is a reflection group on a Sylow
Φ-torus, with basic invariants the restrictions of the f_i with
ε_i ζ^{d_i} = 1. All of these are structural statements. No evaluation of
fake degrees at non-regular ζ is listed.

**Koonin 2013**, arXiv:1208.1799 (§2.5–2.10 read). It quotes Lehrer–Taylor
Thm 12.19 (maximal eigenspaces in a reflection coset have dimension a(ζ)
and are conjugate), Thm 12.20 (N(E)/C(E) is a reflection group on E) and
Prop. 12.21 (eigenvalues on a module M of a *regular* element of γG). By
the table of contents (§0.1), Ch. 12 §3 is the coset analogue of Ch. 11.
So the Ch. 11 statements that are quoted secondhand are structural, or
about regular elements.

## 3. Attribution fixes

Nothing turned out KNOWN, so no verdict label in [CSC] or the ELI5
changes. These are the wording and citation changes this note supports.
Neither file is edited here.

**For `notes/cyclic_sieving_cyc.md`:**
1. Theorem B, paragraph "Prior art ([PACSC])". Add after its first
   sentence: "The proof above, in both parts, is Springer's evaluation
   argument: at q = ζ only the w whose ζ-eigenspace has the maximal
   dimension a(e) = Σ_i ⌊k_i/e⌋ ([Sp74] Thm 3.4(i)) survive, as in the
   proof of [Sp74] Prop. 4.5 (see also Lehrer–Michel 2003, proof of
   Thm 2.3). Part (ii) is that argument at a root of unity that need not be
   a regular eigenvalue, combined with Lemma 1 ([PACSC2] §1)." The last
   sentence, "part (ii) was not found in the literature searched", should
   then read: "part (ii) as a statement was not found in the literature
   searched ([PACSC], [PACSC2]); its method is Springer's."
2. Theorem C, paragraph "Prior art ([PACSC])". Add [PACSC2] to the
   citation. Optionally add that the powers needing B(ii) are handled by
   Springer's method at a non-regular ζ, not by his theorem. The verdict
   (not found beyond regular elements) stands.
3. §10, "Prior art" bullet. Replace "The search did not read the
   Lehrer–Springer eigenspace theory (Lehrer–Taylor, *Unitary Reflection
   Groups*, Ch. 11; Lehrer–Michel 2003). It is the most likely place for
   prior art on B(ii) and Theorem C." with: "[PACSC2] read [Sp74] directly,
   and Lehrer–Michel 2003. The method of Theorem B is Springer's; no
   statement of B(ii) at non-regular ζ, of Theorem C beyond regular
   elements, or of (★) was found. Lehrer–Taylor Ch. 11 (§6, 'Eigenvalues of
   pseudoregular elements') and Lehrer–Springer 1999 could not be obtained
   and remain unread."
4. References. Replace "Lehrer–Taylor … (not read)" with "(not read;
   [PACSC2] §0.4)". Replace "Lehrer–Michel 2003 (not read; as listed in
   [PACSC])" with "G. I. Lehrer, J. Michel, *Invariant theory and
   eigenspaces for unitary reflection groups*, C. R. Acad. Sci. Paris,
   Ser. I 336 (2003) 795–800 (read, [PACSC2])". Add [PACSC2] =
   `notes/prior_art_cyclic_sieving_cyc_2.md`. [Sp74] is now read directly.
5. [CSC]'s Theorem B prior-art paragraph says Springer's theorem "says
   nothing" about non-regular ζ (the wording of [PACSC]). That is true of
   the statement of [Sp74] Prop. 4.5, but not of its proof. The fix in item
   1 covers this. [PACSC]'s Verdict row for B(ii) has the same wording and
   could get a pointer to this note.

**For `notes/eli5_introduction.tex`** (§ "Cyclic sieving on rotation
classes"):
1. The footnote after "None of it was found in the literature searched"
   says the eigenspace theory "was not read". Replace with: "Springer's
   1974 paper and Lehrer–Michel (2003) were then read
   (`notes/prior_art_cyclic_sieving_cyc_2.md`). The proof of the vanishing
   behind Theorem C is Springer's argument, used at roots of unity where
   his theorem does not apply. No statement of the closed form, of
   Theorem C beyond regular elements, or of the A_4 obstruction was found.
   The Lehrer–Taylor book chapter on eigenspace theory could not be
   obtained and was not read."
2. The footnote to Theorem C ("the part beyond regular elements is what was
   not found") may add "(its proof uses Springer's evaluation argument at
   non-regular roots of unity; `notes/prior_art_cyclic_sieving_cyc_2.md`)".
   No label changes.

## 0. Sources

### 0.1 Read

PDFs were converted with `pdftotext -layout` and grepped. The listed parts
were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| [Sp74] T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. 25 (1974) 159–198 | scan of the published paper, copy on N. Wallach's UCSD page (`Springer-reg.pdf`, 40 pp., OCR text) | Introduction; §2.5–2.9 (Prop. 2.6, fake degrees f_χ); §3 in full (Prop. 3.2, Thm 3.4 with proof, Prop. 3.5); §4.1–4.8 (Thm 4.2, Prop. 4.5 with proof, 4.6–4.8); §6.1–6.5 statements (twisted case, regular only); §8.4–8.7 (the "extension to nonregular elements") |
| Lehrer–Michel, *Invariant theory and eigenspaces for unitary reflection groups*, C. R. Acad. Sci. Paris, Ser. I 336 (2003) 795–800 | Numdam (CRMATH_2003__336_10_795_0) | in full |
| Stembridge, *On the eigenvalues of representations of reflection groups and wreath products*, Pacific J. Math. 140 (1989) 353–396 | msp.org | §0, §1 statements, §2 (Thms 2.1–2.2 and the sketch of proof), §3 through Lemma 3.4 |
| Geck–Malle, *Reflection groups*, Handbook of Algebra chapter | arXiv:math/0311012v2 | §§1.7–1.12; grep "fake", "eigenspace", "regular" |
| Koonin, *Topology of eigenspace posets for unitary reflection groups* | arXiv:1208.1799v2 | §§2.5–2.10 (definitions; quotations of Lehrer–Taylor Thms 12.19, 12.20, Prop. 12.21) |
| Lehrer–Taylor, *Unitary Reflection Groups*, CUP 2009: front matter only | assets.cambridge.org (front matter PDF) | Table of contents. Ch. 11, "Eigenspace theory and reflection subquotients", pp. 208–227: §1 Basic affine algebraic geometry; §2 Eigenspaces of elements of reflection groups; §3 Reflection subquotients of unitary reflection groups; §4 Regular elements; §5 Properties of the reflection subquotients; §6 Eigenvalues of pseudoregular elements (p. 222). Ch. 12 §3: Eigenspace theory for reflection cosets |

Also opened and checked by grep, without a relevant hit: Lehrer,
*A factorisation theorem for the coinvariant algebra of a unitary
reflection group* (arXiv:1812.03606), and W. Miller, *Rational Catalan
numbers for complex reflection groups* (arXiv:2310.12354). Both use fake
degrees only at regular elements, or not at all at non-regular ζ.

### 0.2 Web searches

- Lehrer Michel "Invariant theory and eigenspaces for unitary reflection
  groups" arXiv
- Springer "Regular elements of finite reflection groups" Inventiones 1974
  pdf (two variants)
- Lehrer Taylor "Unitary Reflection Groups" chapter 11 "eigenspace theory"
  fake degree pdf
- Lehrer Springer "Reflection subquotients of unitary reflection groups"
  Canadian Journal of Mathematics 51 1999 pdf
- "pseudoregular" OR "pseudo-regular" element unitary reflection group
  Lehrer Taylor eigenvalues maximal eigenspace definition
- Stembridge "On the eigenvalues of representations of reflection groups
  and wreath products" pdf
- fake degree evaluated at root of unity non-regular "maximal eigenspace"
  coset "pointwise stabiliser" character formula reflection group theorem

None of them returned a statement of a fake-degree evaluation at a
non-regular root of unity, or the definition of "pseudoregular".

### 0.3 Positive controls for the negative greps

Case-insensitive match counts in the text files:

| file | "regular" | "non-regular / nonregular / not regular" | "a(d)" | "fake" | "poset" | "linear extension" |
|---|---|---|---|---|---|---|
| [Sp74] | 121 | 6 | 12 | 0 | 0 | 0 |
| Lehrer–Michel | 15 | 1 | 22 | 1 | 0 | 0 |
| Stembridge | 20 | 0 | 0 | 6 | 1 | 0 |
| Geck–Malle | 28 | 0 | 0 | 13 | 0 | 0 |
| Koonin | 26 | 0 | 0 | 1 | 70 | 0 |

"regular" fires in every file and finds the statements quoted in §2, so
the text extraction works. [Sp74] has no hit for "fake" because it does not
use the term. Its fake degree is f_χ of 2.5–2.6, which was read directly.
The 6 [Sp74] hits for "nonregular / not regular" were each read: a
vector in the proof of Lemma 4.11; two in §5.4 (the non-regular number
d = 18, and an element with a primitive 8th root of unity as eigenvalue);
the §8 sentence quoted in §2; the type H_4 case in the proof of 8.7; and a
non-regular nilpotent element in 9.12. None concerns an evaluation of f_χ.
The Lehrer–Michel hit is "d is not regular" in the proof of Thm 3.1(ii).
The single Stembridge hit for "poset" is the title of a Stanley paper in
the reference list. Koonin's 70 hits are posets of eigenspaces, not posets
in the sense of [CSC]. Geck–Malle writes the dimension as a(d, φ), which
the exact string "a(d)" does not match; Thm 1.10 was read directly.

### 0.4 Not accessible / not read

- **Lehrer–Taylor, *Unitary Reflection Groups*, Ch. 11 (and Ch. 12).** Not
  read. Only the table of contents was obtained (§0.1). The publisher's
  book is paywalled; the Google Books search inside the book returned a
  captcha. §11.6, "Eigenvalues of pseudoregular elements", is the one
  remaining place where a general evaluation of the type of Proposition E
  at non-regular ζ could be stated. Since the ζ-eigenvalue data of the
  elements of M determine f_χ(ζ) by Proposition E, an eigenvalue theorem
  for such elements could contain B(ii) as a special case. This should be
  checked against a library copy before any novelty claim for B(ii) is
  made in print.
- **Lehrer–Springer, *Reflection subquotients of unitary reflection
  groups*, Canad. J. Math. 51 (1999) 1175–1193**, and *Intersection
  multiplicities and reflection subquotients of unitary reflection groups
  I*, de Gruyter 1999, 181–193. Not read. The Cambridge PDF returned
  HTTP 403, and no author copy is linked from G. Lehrer's publication list.
  Their main theorems are known here through Lehrer–Michel 2003 (Theorems
  1.1, 1.2, with case-free proofs) and Geck–Malle Thm 1.12.
- **Broué–Malle–Michel, *Generic blocks of finite reductive groups*
  (Astérisque 212, 1993)** and the wider d-Harish-Chandra theory. Not
  opened. They concern generic degrees and relative Weyl groups N/C of
  Sylow Φ_d-tori. They may contain evaluations of fake degrees at ζ_d for
  Weyl groups, but they do not concern permutation modules of posets.

## References

[CSC] = `notes/cyclic_sieving_cyc.md`; [PACSC] =
`notes/prior_art_cyclic_sieving_cyc.md`; [PACSC2] = this note. Other
sources are as listed in §0.
