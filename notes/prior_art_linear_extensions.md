# Prior art for the linear-extensions note (Lemma P, Theorem R, Proposition O, Theorem U)

This note checks four claims of `notes/linear_extensions.md` ("[LE]")
against the literature:
- **Lemma P** ([LE] §1), with Corollaries P1 and P2: on a disjoint union,
  promotion rotates the shuffle pattern and promotes only the component of
  the first letter;
- **Theorem R** ([LE] §2): if ∂_T^{|T|} = id on every component T, each
  cyclic class lies inside one promotion orbit;
- **Proposition O** ([LE] §2): #(∂-orbits on Lin P) ≤ e_C(P);
- **Theorem U** ([LE] §3.2): promotion CSPs are closed under disjoint
  union, with polynomial [n; m_1, …, m_k]_q · ∏_i X_i(q).

It also verifies the bibliographic details of [St09], [Rh] and [RSW].
Notation is that of [LE]. Verdicts:
- **KNOWN**: stated in a source read here, with the exact reference.
- **PARTLY KNOWN**: a special case, or the statement without proof, is in a
  source read here.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.

## Verdict

| Claim of [LE] | Verdict | Closest prior art (read) |
|---|---|---|
| **Lemma P**, two chains | **KNOWN.** Stanley [St09, p. 8, published version only] encodes w ∈ L(m + n) as a word of 1's and 2's and states Φ(w∂) = Φ(w)ψ, adding that ∂ on m + n "is relatively easy to analyze. We omit the details." Striker–Williams [SW12, §3.1 after Thm 3.3, and §6.1 with Thm 6.1] state the rotation explicitly: L([n] ⊕ [k]) under Pro is in equivariant bijection with the k-subsets of [n + k] under the cycle (1, 2, …, n + k), i.e. binary words under rotation | [St09] p. 8; [SW12] Thm 3.3, Thm 6.1 |
| **Lemma P**, k chains | **KNOWN.** In the proof of [AKL21, Thm 31] with n = 1: on standard fillings of a disjoint union of rows, "∂ acting on T … simply corresponds to cyclic rotation of the columns one step left in M(T)". For n = 1, M(T) is the 0/1 matrix whose column j marks the row holding j, i.e. the pattern word p(w) | [AKL21] §4, proof of Thm 31 |
| **Lemma P**, rectangles (SSYT) | **KNOWN as an assertion.** [AKL21, proof of Thm 37]: "since ∂ acts on each rectangle independently", with the content distributed among the rectangles. No proof is given there; for jeu-de-taquin promotion on a disconnected skew shape it is immediate | [AKL21] Thm 37 |
| **Lemma P**, general P, and P1, P2 | **PARTLY KNOWN.** The mechanism of the proof is Stanley's (after Haiman) description of ∂ = δ = τ_1 ⋯ τ_{p−1} on words: factor w into the longest factors whose first letter is incomparable with the rest, and cyclically shift each factor [St09, §2, proof of Thm 2.1]. Lemma P is that description read on a disjoint union. The general statement (any union of components A, the pattern rotates, only the first letter's part is promoted) and the coordinatewise formula P1 for ∂^d were **NOT FOUND** stated. [Hop24, §2] says that the properties of promotion it studies "decompose in a natural way over disjoint unions" without giving the decomposition | [St09] §2; [Hop24] §2 |
| **Theorem R** | **NOT FOUND.** The cyclic classes (rotation at cuts) are objects of the poset Lie theory of [Thm]; no source read relates them to promotion orbits. The hypothesis ∂_T^{\|T\|} = id is known for rectangles, shifted double staircases and shifted trapezoids [St09, Thm 4.1(a, c, d)] and for all minuscule posets [Hop24, Thm 4.5] | — |
| **Proposition O** | **NOT FOUND.** Given Lemma P it is a two-line consequence; no bound of the number of promotion orbits by e_C(P), or by the number of words with first letter in a fixed component, was found | — |
| **Theorem U**, general components | **PARTLY KNOWN.** [Hop24, §2] asserts without proof that the promotion properties it considers, which include cyclic sieving with e(P; q) (§1.1, §4.4), decompose naturally over disjoint unions, and restricts to connected posets for that reason. No source read states or proves the closure with the q-multinomial factor for arbitrary components | [Hop24] §§1.1, 2, 4.4 |
| **Theorem U**, components chains | **KNOWN.** Lin(⊔ C_{m_i}) under ∂ is words of content m under rotation (Lemma P, k chains, above), and that CSP with the q-multinomial is [RSW, Prop. 4.4] (as [LE] uses it). The same set and action are [AKL21, Thm 31] with n = 1, with the Kostka–Foulkes polynomial K_{λ/μ,1^m}(q) | [RSW] Prop. 4.4; [AKL21] Thm 31 |
| **Theorem U**, components rectangles | **KNOWN.** [AKL21, Thm 37] with standard content γ = (1^n), d = 1: (SYT(a^b), ⟨∂⟩, q^E K_{a^b,(1^n)}(q)) is a CSP for any disjoint union of rectangles a^b. Its polynomial is not [LE]'s [n; m]_q ∏ (q-hook), but the two sieve the same action, so they agree modulo q^n − 1. [LE]'s remark "Theorem U gives, for example, a CSP for any disjoint union of rectangles" is therefore a special case of [AKL21, Thm 37], which also covers semistandard content | [AKL21] Thm 37, Lemma 36 |

**Bottom line.**
- Lemma P is known for two chains (Stanley, implicitly; Striker–Williams,
  explicitly), for any number of chains, and for rectangles (both in
  Alexandersson–Kantarci Oğuz–Linusson). Its proof is Stanley's factor
  description of ∂. The general statement was not found. A write-up should
  cite [St09] §2 for the mechanism, and [SW12] and [AKL21] for the special
  cases.
- Theorem R and Proposition O were not found. Their content is the link
  between promotion and the cut/rotation-class structure of the theory,
  which no source read uses.
- Theorem U was not found for general components. Its special cases for
  chains and for rectangles are [RSW] Prop. 4.4 and [AKL21] Thms 31 and 37.
  Hopkins's survey treats the closure as evident. A write-up should present
  Theorem U as the general form of [AKL21, Thm 37] (standard content), not
  as new in the rectangle case.

## Corrections to [LE]

1. **[LE] §1, after Lemma P**: "The special case of two disjoint chains,
   where promotion is rotation of a binary word, is Stanley's [St09]."
   - The two-chain passage is in the **published** version of [St09]
     (EJC 16(2) #R9, p. 8) and **not** in arXiv:0806.4717v2 (version of
     19 July 2008), which is the latest arXiv version. A reader following
     the arXiv copy will not find it.
   - [St09] does not state the rotation in words. It gives the bijection
     Φ : L(m + n) → A(m × n) and Φ(w∂) = Φ(w)ψ, and omits the details. The
     explicit statement that ∂ on L([n] ⊕ [k]) is rotation of binary words
     is in [SW12] (§3.1 after Thm 3.3, attributing the bijection to
     Stanley; §6.1, Thm 6.1).
   - Suggested wording: "The case of two disjoint chains is implicit in
     [St09, p. 8] and explicit in [SW12, §3.1 and Thm 6.1]; the case of k
     chains is in the proof of [AKL21, Thm 31]. The proof is Stanley's
     factor description of ∂ [St09, §2]."
2. **[LE] §1**: "A quick search found no statement of the general lemma,
   which may be folklore." This search confirms that no general statement
   was found, and adds the special cases above.
3. **[LE] §3.2, after the positive controls**: "So Theorem U gives, for
   example, a CSP for any disjoint union of rectangles." This is
   [AKL21, Thm 37] for γ = (1^n). It should be cited.
4. **[LE] §6, problem 4** ("Is Lemma P in the literature beyond [St09]'s
   two-chain case? Is Theorem U?") is answered as above: partly, in both
   cases.
5. **Bibliography.** [St09], [Rh] and [RSW] are correct as given in [LE]
   (checked again, §0.3). No correction.

---

## 0. Sources

### 0.1 Read

PDFs were converted with `pdftotext -layout` and grepped; the listed
sections were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| [St09] Stanley, *Promotion and evacuation*, published version | combinatorics.org, article v16i2r9 (24 pp.) | §2 in full (Thm 2.1 and its proof via δ = τ_1 ⋯ τ_{p−1}, Thms 2.4–2.5 and the passage on m + n, p. 8); §4 (Thms 4.1, 4.2 and the questions). Grep: "disjoint", "binary", "rotat", "cyclic shift", "Brouwer", "Fon-der" |
| [St09] arXiv:0806.4717v2 | arXiv | Same grep. "disjoint" hits only the hook shapes of §4; the m + n passage is absent |
| [SW12] Striker–Williams, *Promotion and rowmotion*, Eur. J. Combin. 33 (2012) 1919–1942 | arXiv:1108.1172 | Abstract; §3.1 (Thms 3.1–3.3 and the paragraph after 3.3); §6.1 (proof of Thm 3.3, Thm 6.1) |
| [AKL21] Alexandersson–Kantarci Oğuz–Linusson, *Promotion and cyclic sieving on families of SSYT*, Ark. Mat. 59 (2021) 247–274 | published PDF (intlpress); arXiv:2007.10478v1 | §2.1 (jeu-de-taquin promotion); §4 in full: Prop. 29, Cor. 30, Thm 31 with proof, §4.1 to the proof of Thm 37. Theorem numbers above are those of the published version; arXiv v1 numbers them 30 and 36 |
| [Hop24] Hopkins, *Order polynomial product formulas and poset dynamics*, in *Open Problems in Algebraic Combinatorics*, Proc. Sympos. Pure Math. 110, AMS 2024, 135–157 | arXiv:2006.01568v6 | §1.1; §2 opening paragraph (the disjoint-union sentence); §4.3–4.4 (Thms 4.5–4.8) |
| [BER] Berget–Eu–Reiner, *Constructions for cyclic sieving phenomena*, SIAM J. Discrete Math. 25 (2011) 1297–1314 | arXiv:1004.0747v2 | Props. 15–17 and their proofs (words, tensor and symmetric powers). The constructions act on letter values and positions by a product C × C, or on multisets; none twists a component action by the rotation, as P1 does |
| [Sag] Sagan, *The cyclic sieving phenomenon: a survey*, Surveys in Combinatorics 2011, LMS Lecture Note Ser. 392, CUP 2011, 183–234 | arXiv:1008.0790 | §7 (promotion on rectangular SYT); §11 (constructions, Thm 11.1 after [BER]). Grep: "disjoint", "union", "product of", "promotion" |
| [AA19] Alexandersson–Amini, *The cone of cyclic sieving phenomena*, Discrete Math. 342 (2019) 1581–1601 | arXiv:1804.01447 | §6 (the product of universal CSP matrices, Prop. 6.8: C_m × C_n acting on X × Y). Not a twisted action |
| Ayyer–Klee–Schilling, *Combinatorial Markov chains on linear extensions*, J. Algebraic Combin. 39 (2014) 853–881 | arXiv:1205.7074v3 | §2.2. Prop. 2.2: the braid relations for the τ_j hold on L(P) iff P is a disjoint union of chains. Nothing on promotion orbits of disjoint unions |
| Bayer et al., *Promotion, tangled labelings, and sorting generating functions* | arXiv:2411.12034v1 | Lemma 2.20 (a conjecture on tangled labelings passes to P_1 ⊔ P_2). Different question |
| Defant, *Toric promotion* | arXiv:2112.06843 | Abstract, §1. Toric promotion on labelings of a graph; orbit sizes for forests. Different operator and set |
| Defant–Madhukara–Thomas, *Permutoric promotion* | arXiv:2305.19961 | Grep "linear extension", "disjoint union": no disjoint-union statement |

### 0.2 Web searches

- promotion linear extensions disjoint union of posets cyclic sieving
  q-multinomial (extended)
- "promotion" "disjoint union" linear extensions poset orbit structure
  shuffle arXiv
- promotion linear extensions "disjoint union" poset "promotion acts"
  components independently lemma (extended)
- cyclic sieving promotion skew standard Young tableaux disconnected shape
  disjoint union of rectangles (extended) — this found [AKL21]
- number of promotion orbits linear extensions upper bound disconnected
  poset cyclic rotation word classes
- Berget Eu Reiner "Constructions for cyclic sieving phenomena";
  Alexandersson Amini "The cone of cyclic sieving phenomena"; Sagan "The
  cyclic sieving phenomenon: a survey"; Bernstein–Striker–Vorland
  "P-strict promotion"
- Crossref metadata queries for [RSW], [Rh], [SW12], [AKL21], [Hop24],
  [Sag], [BER]

**Positive controls for the negative greps.**
- [St09] arXiv v2: "disjoint" finds the hook shapes of §4, so the grep sees
  the text. The m + n passage is found by the same grep in the published
  PDF (p. 8). So its absence from v2 is real.
- [AKL21]: "disjoint" finds Thms 31 and 37, so a disjoint-union statement
  is found when present.
- [Sag]: "promotion" finds §7, and "construct" finds the [BER]
  constructions of §11. No hit concerns disjoint unions of posets.
- [BER]: "multinomial" finds Prop. 17, the RSW Prop. 4.4 input that [LE]
  also uses.

### 0.3 Bibliographic check

| Tag in [LE] | As given in [LE] | Checked against | Result |
|---|---|---|---|
| [St09] | R. P. Stanley, *Promotion and evacuation*, Electron. J. Combin. 16(2) (2009) R9 | published PDF: "the electronic journal of combinatorics 16(2) (2009), #R9", submitted 22 Jul 2008, published 27 Apr 2009; DOI 10.37236/75 (journal BibTeX) | **Correct.** The published version (24 pp.) is longer than arXiv v2 and adds the m + n passage (p. 8) and a section on growth diagrams (§5) |
| [Rh] | B. Rhoades, *Cyclic sieving, promotion, and representation theory*, JCTA 117 (2010) 38–76 | Crossref: J. Combin. Theory Ser. A 117(1), 38–76, Jan. 2010, DOI 10.1016/j.jcta.2009.03.017 | **Correct.** An FPSAC 2008 extended abstract with the same title exists (DMTCS Proc. AJ, DOI 10.46298/dmtcs.3600); [LE] cites the journal paper |
| [RSW] | V. Reiner, D. Stanton, D. White, *The cyclic sieving phenomenon*, JCTA 108 (2004) 17–50 | Crossref: J. Combin. Theory Ser. A 108(1), 17–50, Oct. 2004, DOI 10.1016/j.jcta.2004.04.009 | **Correct** |

### 0.4 Not read

- Bernstein–Striker–Vorland, *P-strict promotion and B-bounded rowmotion*
  (Combin. Theory 2021) and *P-strict promotion and q-partition rowmotion:
  the graded case* (Eur. J. Combin. 115 (2024)). Found by title only. They
  define promotion on P-strict labelings of P × [ℓ]; a disjoint-union
  statement there was not checked.
- Fontaine–Kamnitzer, *Cyclic sieving, rotation, and geometric
  representation theory*, Selecta Math. 20 (2014) 609–625, the rectangular SSYT case
  that [AKL21, Thm 37] generalises. Not opened.
- Pon–Wang, Petersen–Pylyavskyy–Rhoades, Purbhoo: CSPs for connected
  shapes only, as summarised in [Sag] §7 and [Hop24] §4.4. Not opened.

## 1. Lemma P and its corollaries

**[LE]'s statement.** Let A be a union of components and B its complement.
Then ∂(w) has pattern rot_1(p), and only the part containing w_1 is
promoted. P1: ∂^d acts as (p; x_i) ↦ (rot_d p; ∂_{T_i}^{a_i} x_i), with a_i
the number of i's among p_1, …, p_d. P2: at a cut k, ∂^k(w) is the rotation
wγ^k with its prefix part replaced by ∂_A^{|A|} of it.

**Mechanism: Stanley [St09, §2].** In the proof of Thm 2.1 Stanley shows
∂ = δ = τ_1 τ_2 ⋯ τ_{p−1} on words (with τ_i as in [LE] §0) and describes
δ: "Let j be the least integer such that j > 1 and u_1 < u_j. Since f is a
linear extension, the elements u_2, …, u_{j−1} are incomparable with u_1.
Move u_1 so it is between u_{j−1} and u_j. … Now let k be the least integer
such that k > j and u_j < u_k. Move u_j … Continue in this way." He
attributes the word approach to Haiman (Lemma 2.7) and Malvenuto–
Reutenauer. The "carried letter" of [LE]'s proof is u_1, then u_j, then
u_k, …; each is comparable to the previous one, so all lie in the component
of u_1, and every other letter moves one place left. That is Lemma P.

**Two chains.** [St09, p. 8] (published version): "Here we will show a
connection with the case P = m × n … and promotion on m + n (where +
denotes disjoint union). … We can write w ∈ L(m + n) as a sequence
(a_m, …, a_1, b_n, …, b_1) of m 1's and n 2's in some order. … It can be
checked that Φ(w∂) = Φ(w)ψ. Hence ψ on m × n has the same cycle type as ∂
on m + n, which is relatively easy to analyze. We omit the details here."
The rotation of the 1/2-word is not stated. [SW12, §3.1]: "L([n] ⊕ [k]) is
also in equivariant bijection with the set ([n+k] choose k) under the cycle
(1, 2, …, n + k)", and Thm 6.1 makes the binary word explicit.

**k chains.** [AKL21, §4]: SM(ν, n) is the set of fillings of a disjoint
union of rows of lengths nν_j with content n^m, and M_{ij} is the number of
entries j in row i. For n = 1 these are the linear extensions of
⊔_j C_{ν_j}, and column j of M has its single 1 in the row (component)
holding j. The proof of Thm 31 begins: "∂ acting on T ∈ SM(ν, n) simply
corresponds to cyclic rotation of the columns one step left in M(T)." For
n = 1 that is Lemma P for k chains (and P1 for chains, where each
∂_{T_i} = id).

**Rectangles.** [AKL21, before and in the proof of Thm 37]: "since
promotion acts independently on each rectangle", and the fixed points of
∂^{jd} are counted as a sum over the distributions of the content among the
rectangles of products of fixed-point counts on each rectangle. That is the
product formula [LE] derives from P1, in the SSYT setting, asserted
without proof.

**General P.** Not found. The closest statement is [Hop24, §2]: "All the
properties of posets we are interested in decompose in a natural way over
disjoint unions, so we will only consider connected posets." It gives no
formula for promotion on P ⊔ Q.

**Verdict: PARTLY KNOWN.** Known for chains and rectangles, with Stanley's
mechanism. The general lemma and P1, P2 were not found.

## 2. Theorem R and Proposition O

The cyclic classes of [LE] are the sets {wγ^k : k a cut of w}. Rotation at
a cut is defined by the components of P, and it is the action that the
poset Lie theory of [Thm] is built on. No source read considers it on
linear extensions. Related but different:
- Defant's toric promotion (arXiv:2112.06843) acts on all labelings of a
  graph, with the cyclic move τ_n; its orbits for forests have size n − 1.
  It is not promotion on Lin P, and its classes are not cut rotations.
- [SW12] and [St09, p. 8] relate promotion on two chains to rowmotion on
  m × n, not to rotation classes.

No bound of the number of promotion orbits on Lin P in terms of the
components was found. For two chains the orbits are the necklaces of
binary words ([SW12]), which gives the orbit count, but no source states a
bound of the form of Proposition O.

The hypothesis of Theorem R, ∂_T^{|T|} = id, holds for rectangles
([St09, Thm 4.1(a)], due to Schützenberger), shifted double staircases and
shifted trapezoids ([St09, Thm 4.1(c, d)], Haiman), and all minuscule
posets ([Hop24, Thm 4.5]). So Theorem R applies to any disjoint union of
these.

**Verdicts: Theorem R NOT FOUND. Proposition O NOT FOUND.**

## 3. Theorem U

**Statement in [LE].** If (Lin T_i, ⟨∂_{T_i}⟩, X_i(q)) is a CSP for each
component, then (Lin P, ⟨∂⟩, [n; m]_q ∏ X_i(q)) is a CSP.

**Chains.** For P = ⊔ C_{m_i}, every Lin T_i is a point and X_i = 1. By
Lemma P (k chains, [AKL21] above), (Lin P, ∂) is (Pat(m), rotation), and
the CSP with the q-multinomial is [RSW, Prop. 4.4] with a = 1, the input
[LE] already cites. [AKL21, Thm 31] (n = 1) is the same CSP with
K_{λ/μ,1^m}(q).

**Rectangles.** [AKL21, Thm 37]: "Let γ = (γ_1, …, γ_m) be a composition
of size a_1b_1 + … + a_rb_r, satisfying rot_m^d(γ) = γ. Then there exists
some E = E(a^b, γ) ∈ N such that (SSYT(a^b, γ), ⟨∂^d⟩, q^E K_{a^b,γ}(q)) is
a CSP-triple." For γ = (1^n) every d satisfies rot_n^d(γ) = γ; with d = 1
the group is ⟨∂⟩ of order n acting on the SYT of the disjoint union of
rectangles, which are the linear extensions of the disjoint union of the
rectangle posets. This is [LE]'s rectangle example. A CSP polynomial is
determined modulo q^n − 1 by its values at the n-th roots of unity, so
q^E K_{a^b,(1^n)}(q) ≡ [n; m]_q ∏_i (q-hook of a_i^{b_i}) modulo q^n − 1.
(This congruence is derived here, not stated in [AKL21].) The proof of
[AKL21, Thm 37] has the same structure as [LE]'s: fixed points factor over
the content distribution, and each factor is the rectangle case
(Fontaine–Kamnitzer's theorem, [AKL21] Thm 34, combined with the ribbon-tableau evaluation [AKL21] Thm 33).

**General components.** Not found. [Hop24, §1.1] conjectures that
e(P; q) sieves promotion whenever promotion "has good behavior", and §2
sets disjoint unions aside as decomposing naturally. Since
Ω_{P⊔Q}(m) = Ω_P(m)Ω_Q(m), the e(P; q) of a disjoint union is the
q-multinomial times the product of the e(T_i; q), so Theorem U is the
statement that this heuristic is compatible with disjoint unions. That
consequence is ours; [Hop24] does not state it. Neither [BER] nor [AA19]
nor [Sag] §11 has a construction that twists the component actions by the
rotation of the pattern, which is what P1 describes: [BER] Prop. 16 uses a
product C × C acting on letter values and on positions separately, and
[AA19] Prop. 6.8 uses C_m × C_n on X × Y.

**Verdict: PARTLY KNOWN.** Chains: KNOWN ([RSW] Prop. 4.4; [AKL21]
Thm 31). Rectangles: KNOWN ([AKL21] Thm 37). General components: NOT FOUND,
treated as evident in [Hop24] §2.

**Not checked.** The second sentence of Theorem U ("if every X_i is the
shifted maj polynomial, then so is X", the MacMahon–Stanley factorisation
over disjoint unions) is outside the four targets and was not searched;
[AudLE §7] re-derived it via Garsia–Gessel.
