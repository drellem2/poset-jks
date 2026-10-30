**Overall verdict: no cited statement is misstated. Every input the main theorem uses either MATCHES an openly available source that was read, or has a NOT ACCESSIBLE primary source and was confirmed in an open secondary source. Three citation pointers are slightly imprecise (§6). None of them changes a hypothesis or a conclusion.**

# Citation check for the poset JKS theorem

This note checks the external results cited in `notes/poset_jks_theorem.tex`
against the sources. Earlier audits checked the arguments; this one checks the
inputs those arguments rely on. It covers:

- the three inputs of the main theorem (Jenča–Sarkoci, P. Hall, the Hopf trace formula);
- Crapo (Proof II), Weisner, Ree/Reutenauer, and Cartier–Milnor–Moore/PBW for species;
- the Wachs 1998 statements that Theorem S(c) needs for n ≥ 7, through Prop. Φ.

These are the items in the write-up's open-problems list "Items the audits
list as UNCHECKED".

Verdicts:
- **MATCHES**: I read the source text myself. The number is right, the
  statement is the one the write-up uses, and the write-up's use satisfies
  its hypotheses.
- **MISSTATED**: the number, the statement or a hypothesis is wrong.
- **NOT ACCESSIBLE**: I could not read the primary source (paywall, or
  bot-blocked open archive). Where an open secondary source states the
  result, I say what it says, but the verdict stays NOT ACCESSIBLE.

Sources actually read (all downloaded and read for this check):

| Source | Version read | URL |
|---|---|---|
| Jenča–Sarkoci | arXiv:1112.5782**v2** (1 Apr 2015, 14 pp.); also **v1** (25 Dec 2011) for comparison | https://arxiv.org/abs/1112.5782 |
| Stanley, EC1, 2nd ed. | author's online version "of 15 July 2011" | https://math.mit.edu/~rstan/ec/ec1.pdf |
| Wachs 1998 | preprint `homlie.ps`, "Dec. 31, 1994 (revised Jan. 1996)"; pages 7, 10, 16–18 read as rendered images | https://www.math.miami.edu/~wachs/papers/homlie.ps |
| Wachs, *Poset topology: tools and applications* (IAS/Park City 2004 notes) | `toolnotes.pdf` | https://www.math.miami.edu/~wachs/papers/toolnotes.pdf |
| Aguiar–Mahajan, *Monoidal Functors, Species and Hopf Algebras* | authors' PDF `a.pdf` | https://pi.math.cornell.edu/~maguiar/a.pdf |
| Aguiar–Mahajan, *Topics in Hyperplane Arrangements* | "Author's preliminary version" `surv-226.pdf` | https://pi.math.cornell.edu/~maguiar/surv-226.pdf |
| Bibliographic metadata (volume, pages, year) | Crossref API | https://api.crossref.org |

Not readable: ScienceDirect, which serves the JCTA 2014, JCT 1966 and Discrete
Math. 1998 journal texts, returned HTTP 403 (Cloudflare) to both `curl` and a
web fetch, even though the articles are in Elsevier's open archive. Munkres,
Reutenauer, Ree (Annals/JSTOR) and the print editions of EC1 and
*Topics* are paywalled.

## 1. Summary table

| # | Cited as | Where used | Verdict | One-line reason |
|---|---|---|---|---|
| A | Jenča–Sarkoci Thm 4.5 (arXiv v2): n ≥ 3 ⇒ Δ(proper part of OP(P)) ≃ ⋁^{e_C(P)} S^{n−3}, no connectivity | input (A); Lemmas homchar, small; Thm S(c) | **MATCHES** (arXiv v2) | Read verbatim. The only hypothesis is "finite, n ≥ 3". O(P), Ô(P) and e_C are the write-up's OP(P), proper part and e_C. |
| A′ | "order congruences = acyclic-quotient partitions (their Thm 3.3, after Czédli–Lenkehegyi)" | input (A) | **MATCHES**, pointer imprecise | The acyclic-quotient condition is literally their **Def. 3.1(ii)** (after Körtesi–Radeleczki–Szilágyi). Thm 3.3 (Czédli–Lenkehegyi) adds the equivalent "kernel of an order-preserving map". See §2.2. |
| A″ | JCTA 122 (2014) 28–38 vs arXiv v2 numbering | bibliography | metadata **MATCHES**; journal numbering **NOT ACCESSIBLE** | Crossref confirms vol. 122, pp. 28–38, Feb 2014, doi 10.1016/j.jcta.2013.09.010. The journal text was blocked. arXiv **v1 numbers differently** (main result = "Theorem 5"), so the "v2 numbering" qualifier in the write-up is needed. |
| B | P. Hall, EC1 2nd ed. Prop. 3.8.5 | input (B); Lemmas homchar, small | **MATCHES** (2011 online version), pointer imprecise | 3.8.5 is the chain-count form μ = c₀ − c₁ + c₂ − ⋯. The χ̃ form the write-up states is **Prop. 3.8.6** ("Proposition 3.8.5, restated"). Print-edition numbering NOT ACCESSIBLE. |
| C | Hopf trace formula, Munkres Thm 22.1 | input (C); Lemma homchar | **NOT ACCESSIBLE** (Munkres) | Paywalled. The statement as used, augmented and with reduced homology, is Wachs, *Poset topology* **Thm 2.3.9**, which I read. That reference is open and could replace or supplement Munkres. |
| D | Crapo complementation theorem, Crapo, J. Combin. Theory 1 (1966) 126–131 | Proof II only | **NOT ACCESSIBLE** (primary) | Blocked. EC1 Exercise 3.92 states it in the form [AudChar II1] uses, and its solution attributes it to "Crapo, J. Combinatorial Theory 1 (1966), 126–131 (**Thm. 3**)". Metadata confirmed by Crossref. |
| E | Weisner, EC1 Cor. 3.9.3 | Lemma weisner (Proof I) | **MATCHES** (dual form; not load-bearing) | EC1 states the meet form Σ_{t∧a=0̂} μ(t,1̂) = 0 for a ≠ 1̂. The write-up uses the dual join form and proves it in full (Lemma weisner). I re-checked that proof. |
| F | Ree, Ann. of Math. 68 (1958) 210–220; Reutenauer *Free Lie Algebras* Thm 3.1: Lie_n^⊥ = Sh_n | Prop. Φ; Cor. klyachko | **NOT ACCESSIBLE** | Both paywalled. Crossref confirms Ree: Annals vol. 68, first page 210, Sept. 1958 (end page not given). The open *Topics* Lemmas 10.7–10.8 give the arrangement form of the Ree criterion (secondary only). |
| G | Wachs 1998, Lemma 3.1, Thms 4.2–4.3 (preprint numbering), Prop. 2.3 normalisation of ρ_σ | Prop. Φ ⇒ Thm S(c),(d) for n ≥ 7 | **MATCHES** (preprint); journal **NOT ACCESSIBLE** | All four read verbatim. The dualisation to Prop. Φ was re-derived here from the statements and checked numerically for n ≤ 7 (§4). Discrete Math. 193 (1998) 287–319 confirmed by Crossref. |
| H | Cartier–Milnor–Moore and PBW for species, Aguiar–Mahajan *Monoidal Functors* Ch. 11 | Remark "Why a plethystic logarithm" (global section only) | **MATCHES** (chapter-level citation) | Both are in §11.9.3 (pp. 395–396): CMM is eq. (11.40); PBW is the sentence after Cor. 11.46. Neither is a numbered theorem in AM, which attribute them to Stover and Joyal (primaries not read). |

The main theorem (Theorem thm:main, Proof I) rests on A, A′, B, C and E.
A, A′, B and E MATCH. C is NOT ACCESSIBLE in the cited book but is confirmed
in an open source. Proof II adds D, which is NOT ACCESSIBLE. Theorem S(c),(d)
for n ≥ 7 adds F and G. G MATCHES; F is NOT ACCESSIBLE.

## 2. Jenča–Sarkoci (input A)

### 2.1 Theorem 4.5

arXiv v2, p. 8, verbatim:

> **Theorem 4.5 (Main result).** Let P be a finite poset with n elements, n ≥ 3.
> Then ∆(Ô(P)) is homotopy equivalent to a wedge of e_C(P) spheres of dimension
> n − 3.

- **Hypotheses.** Only "finite, n ≥ 3". Connectivity is not assumed; the
  connected case is the separate Cor. 4.12, which gives e(P) spheres. So
  the write-up's "it need not be connected" is correct.
- **Ô(P).** p. 2: "If P is a poset, then P̂ denotes the same poset minus upper
  or lower bounds". O(P) has bottom = singletons and top = one block (p. 5),
  so Ô(P) is the proper part. This is the write-up's \widehat{OP(P)}.
- **e_C(P).** Def. 4.1: f ∼ g iff ⊕_f = ⊕_g, and e_C(P) is the number of ∼-classes. The text
  notes: "f ∼ g if and only if there are words w, w′ over P such that f = ww′
  and g = w′w". In the write-up, a cyclic class is a coset wC_n meeting
  Lin(P). Two linear extensions lie in the same coset iff one is a rotation
  of the other, which is exactly ∼. So the two definitions give the same
  count.
- **How the write-up uses it.**
  - Lemma homchar applies it to P with n ≥ 3.
  - Lemma small applies it to Q = P|_{B₀} only when |Q| ≥ 3. The cases
    |Q| ≤ 2 are computed by hand.
  - Thm S(c) uses dim H_P = e_C(P) for n ≥ 3.
  - All three use only the homological consequence: reduced homology over ℂ
    is concentrated in degree n − 3, with dimension e_C. That follows from
    the homotopy equivalence.

  All hypotheses are satisfied. **MATCHES.**

### 2.2 Order congruences = acyclic-quotient partitions

The write-up's convention (§sec:setup) is that π is order-preserving iff the
quotient digraph P/π is acyclic.

- **Jenča–Sarkoci Def. 3.1** (credited to [10] Körtesi–Radeleczki–Szilágyi):
  - (i) a ρ-sequence is x₀, …, x_n with each step either (x_{i−1}, x_i) ∈ ρ
    or x_{i−1} < x_i;
  - (ii) ρ is an order-congruence if every ρ-cycle lies in one ρ-class;
  - (iii) π is order-preserving if π = P/ρ for an order congruence ρ.
- **Equivalence with the write-up.** A ρ-cycle that meets two classes
  projects to a closed walk in the quotient digraph with at least one
  non-loop arc, so it contains a directed cycle. Conversely, a directed cycle
  in the quotient lifts to such a ρ-cycle. So Def. 3.1(ii) is literally
  "the quotient digraph is acyclic", and O(P) = OP(P).
- **Jenča–Sarkoci Thm 3.3** (credited to [3] Czédli–Lenkehegyi): for an
  equivalence ρ, the following are equivalent: (i) ρ is an order-congruence;
  (ii) ρ = Ker f for some order-preserving f: P → Q; (iii) ≤ extends to a
  quasiorder θ with ρ = θ ∩ θ⁻¹. The write-up's Lemma D uses (ii) ⇒ (i).
  Lemma D also proves that direction directly.
- **Lattice structure.** p. 5 states that O(P) is a lattice, ranked by
  |P| − |π|, with meet = partition meet. This agrees with Lemma lattice(i),
  which the write-up proves itself.

**Verdict:** MATCHES. One pointer is imprecise. The write-up attributes the
acyclic-quotient identification to "their Thm 3.3, after Czédli–Lenkehegyi",
but the identification is their Def. 3.1, with Thm 3.3 adding the
kernel-of-isotone-map form. Suggested wording: "their Def. 3.1 (after
Körtesi–Radeleczki–Szilágyi); equivalently, kernels of order-preserving maps
(their Thm 3.3, after Czédli–Lenkehegyi)". This is not a mathematical error.

### 2.3 Numbering and journal

- **Version numbering.** v1 numbers results flat: Def. 2 = order
  congruence, Theorem 3 = Czédli–Lenkehegyi, Theorem 4 = the recurrence,
  Def. 3 = cyclic classes, Theorem 5 = main result. v2 uses section-wise
  numbering (3.1, 3.3, 3.8, 4.1, 4.5). So the write-up's "arXiv v2
  numbering" qualifier is necessary and correct. The v1 statement of the
  main result has the same hypotheses.
- **Journal.** Crossref gives J. Combin. Theory Ser. A **122** (2014),
  **28–38**, Feb 2014, doi:10.1016/j.jcta.2013.09.010. This matches the
  bibliography. The journal text was blocked (HTTP 403), so whether the
  journal's theorem numbers equal v2's is **NOT ACCESSIBLE**. v2 thanks the
  referees and was posted after publication, so it is probably the
  accepted version. That is an inference, not a check.

## 3. Hall, Hopf trace, Weisner, Crapo (inputs B, C; Lemma weisner; Proof II)

### 3.1 P. Hall: EC1 Prop. 3.8.5

EC1 (online 2nd ed., version of 15 July 2011), p. 306, verbatim:

> **3.8.5 Proposition (Philip Hall's theorem).** Let P be a finite poset, and let
> P̂ denote P with a 0̂ and 1̂ adjoined. Let c_i be the number of chains
> 0̂ = t₀ < t₁ < ⋯ < t_i = 1̂ of length i between 0̂ and 1̂. (Thus c₀ = 0 and
> c₁ = 1.) Then μ_P̂(0̂, 1̂) = c₀ − c₁ + c₂ − c₃ + ⋯ .

p. 307: **3.8.6 Proposition (Proposition 3.8.5, restated).** Let P be a
finite poset. Then μ_P̂(0̂, 1̂) = χ̃(∆(P)). Here χ̃ counts the empty face in
degree −1 (eq. (3.22)).

- **How the write-up uses it.** It states: for a finite bounded poset L,
  μ_L(0̂, 1̂) = χ̃(Δ(L̄)). This is 3.8.6 with P = L̄ and L = P̂.
- **Hypothesis 0̂ ≠ 1̂.** P̂ always has 0̂ ≠ 1̂, so the cited result needs it.
  It holds in both applications:
  - Lemma homchar: L^g contains the distinct elements 0̂ and 1̂ of OP(P),
    n ≥ 3.
  - Lemma small: |Q| ≥ 3. The one-element case |Q| = 1 is computed by hand
    and does not invoke Hall.
  - The write-up does not need P = ∅ (L a 2-element chain). There 3.8.6
    gives χ̃({∅}) = −1 = μ, which is consistent.

**Verdict:** MATCHES. The pointer would be exact as "Prop. 3.8.5 (in the
form of Prop. 3.8.6)". The CUP 2012 print numbering is NOT ACCESSIBLE; only
the author's 2011 online version was read.

### 3.2 Hopf trace formula: Munkres Thm 22.1

Munkres, *Elements of Algebraic Topology*, is paywalled, so Thm 22.1 is
**NOT ACCESSIBLE** and the number is unverified. (Jenča–Sarkoci cite the
1996 Westview printing, [9], but only for topology background.)

Open substitute, read: Wachs, *Poset topology: tools and applications*, §2.3,
**Theorem 2.3.9 (Hopf trace formula)**: for any G-simplicial complex ∆ (G
finite, acting on vertices and taking faces to faces),
Σ_{i=−1}^{dim ∆} (−1)^i C_i(∆; ℂ) ≅_G Σ_{i=−1}^{dim ∆} (−1)^i H̃_i(∆; ℂ)
as virtual G-modules.

Taking characters at g gives exactly the write-up's statement for the
augmented complex and reduced homology. Lemma homchar applies it to
G = ⟨g⟩ ⊆ Aut(P) acting on the order complex of the proper part of OP(P),
which is a G-simplicial complex.

The write-up's step "tr(g | C_i) counts the g-fixed i-chains" also holds.
In an order complex, a chain mapped to itself is fixed pointwise, so it
contributes +1 and not ±1.

**Verdict:** NOT ACCESSIBLE for the cited Munkres number. The statement
used is correct per Wachs Thm 2.3.9. Suggest citing Wachs, *Poset
topology*, Thm 2.3.9 alongside or instead of Munkres.

### 3.3 Weisner: EC1 Cor. 3.9.3

EC1, p. 314, verbatim:

> **3.9.3 Corollary (Weisner's theorem).** Let L be a finite lattice with at
> least two elements, and let 1̂ ≠ a ∈ L. Then Σ_{t : t∧a=0̂} μ(t, 1̂) = 0.

The write-up's Lemma weisner is the order dual:

- statement: in a finite lattice M with a ≠ 0̂, Σ_{x : x∨a=1̂} μ(0̂, x) = 0;
- obtained by applying 3.9.3 to M^op, using μ_{M^op}(t, 1̂) = μ_M(0̂, t).

The write-up does not rely on the citation: Lemma weisner has a complete
proof, which I re-checked.

- δ(s, 1̂) = Σ_{y ≥ s} μ(y, 1̂).
- Swapping sums gives Σ_{y ≥ a} μ(y, 1̂) δ(0̂, y).
- This vanishes because y ≥ a ≠ 0̂.

**Hypotheses as used.** M = L^g, a = O_g ≠ 0̂ because g ≠ 1. The join is
that of L^g, which Lemma lattice(iii) identifies with the partition join.

**Verdict:** MATCHES (dual form). The open-problems entry "Weisner (EC1
Cor. 3.9.3)" is the right number for the meet form.

### 3.4 Crapo's complementation theorem (Proof II only)

The primary source (J. Combin. Theory 1 (1966) 126–131; Crossref confirms
vol. 1, pp. 126–131, June 1966, doi 10.1016/S0021-9800(66)80009-1) was
blocked: **NOT ACCESSIBLE**.

Secondary source, read: EC1 **Exercise 3.92**. "Assume that L is a finite
lattice and fix t ∈ L. Show that μ(0̂, 1̂) = Σ_{u,v} μ(0̂, u) ζ(u, v) μ(v, 1̂),
where u, v range over all pairs of complements of t."

- The solution (p. 489) says: "This result is known as the 'Crapo
  complementation theorem.' See H. H. Crapo, J. Combinatorial Theory 1
  (1966), 126–131 (Thm. 3)."
- This is the form [AudChar II1] records (x ≤ y, both in z^⊥). The only
  hypothesis is that L is a finite lattice, and L^g is one.
- The write-up's "theorem number not checked" stands for the primary
  source. Per Stanley, the number is **Thm. 3**.

Proof II is not needed for the main theorem.

## 4. Wachs 1998 and Ree: what Theorem S(c) needs for n ≥ 7 (Prop. Φ)

### 4.1 Statements read (preprint, rendered pages)

- **Prop. 2.3 (Splitting basis), p. 7.** {ρ_σ : σ ∈ S_n, σ(n) = n} is a
  basis for H(Π_n), with dual basis {m̄_σ : σ(n) = n} for H*(Π_n).
  - m_σ is the maximal chain whose k-block partition has the k − 1
    singleton blocks {σ(1)}, …, {σ(k−1)} and the block {σ(k), …, σ(n)}.
  - "we choose ρ_σ to be the fundamental cycle of ∆(Π_σ) in which m̄_σ has
    coefficient 1."
  - This is the write-up's normalisation in §sec:basis: the chain
    w₁|⋯|w_{k−1}|rest has coefficient +1. **MATCHES.**
- **Lemma 3.1, p. 10.** For α, β ∈ S_n,
  ⟨ρ_α, m̄_β⟩ = sgn*(α⁻¹β) if α⁻¹β ∈ Γ_n, and 0 otherwise.
  - Γ_n is the set of minmax permutations, which avoid 213 and 231.
  - sgn*(σ) = (−1)^{inv(σ(1)⋯σ(n−1))}.
  - **MATCHES.**
- **Thm 4.2, pp. 16–17.** The matrix of σ on Lie_n in the right comb basis
  r_{σ₁}, …, r_{σ_{(n−1)!}} (the σ_j with σ_j(n) = n) has entries
  B_{i,j}(σ) = (−1)^{des(σ_i⁻¹σσ_j)} if σ_i⁻¹σσ_j ∈ Γ_n, and 0 otherwise.
  Its proof contains **(4-4)**: ⟨r_α, ε⟩ = (−1)^{des α} χ(α ∈ Γ_n).
  **MATCHES.**
- **Thm 4.3 (comb correspondence), p. 18.** r_w ↦ sgn(w) m̄_w, from the
  right comb basis of Lie_n to the signed dual splitting basis of H*(Π_n),
  determines an S_n-isomorphism Lie_n → H*(Π_n) ⊗ sgn. Its proof contains
  the identity sgn*(α) = (−1)^{des α} sgn(α) for α ∈ Γ_n. **MATCHES.**

These are cohomology and Lie statements, as the write-up says. They are
the preprint's numbers, and the write-up states that it uses preprint
numbering. For the journal, Crossref confirms Discrete Math. 193 (1998)
287–319, doi 10.1016/S0012-365X(98)00147-2, but the text was blocked, so
journal numbering is **NOT ACCESSIBLE**.

### 4.2 Do these statements give Prop. Φ?

This was re-derived here from the statements alone.

1. Let F: Lie_n → H*(Π_n) ⊗ sgn be Thm 4.3's isomorphism.
2. Take its transpose F^T: H(Π_n) ⊗ sgn → Lie_n*. It is S_n-equivariant
   because both pairings are S_n-invariant.
3. On the basis r_w (w(n) = n), F^T(ρ_σ ⊗ 1) is the functional
   r_w ↦ sgn(w) ⟨ρ_σ, m̄_w⟩ = sgn(w) sgn*(σ⁻¹w) [σ⁻¹w ∈ Γ_n], by Lemma 3.1.
4. The functional pairing with sgn(σ)σ gives:
   - r_w ↦ sgn(σ) · (coefficient of the word σ in r_w)
   - = sgn(σ) ⟨r_{σ⁻¹w}, ε⟩
   - = sgn(σ) (−1)^{des(σ⁻¹w)} [σ⁻¹w ∈ Γ_n], by (4-4).
5. By the sgn* identity, sgn(w) sgn*(α) = sgn(w) sgn(α) (−1)^{des α}
   = sgn(σ) (−1)^{des α} for α = σ⁻¹w ∈ Γ_n. So the two functionals agree
   on a basis of Lie_n.
6. Ree's theorem gives Lie_n^⊥ = Sh_n, so Lie_n* = ℂ[S_n]/Sh_n and
   F^T(ρ_σ ⊗ 1) = sgn(σ)σ + Sh_n for **every** σ ∈ S_n. (Lemma 3.1 holds for
   all α, β, so σ(n) = n is not needed.)
7. F^T is a linear isomorphism defined on all of H ⊗ sgn. So the map is
   well defined (Φ(⇐)) and injective (Φ(⇒)).

Two inputs are not theorem statements but lines inside Wachs's proofs:
(4-4), and the sgn* identity. Both are elementary. The script in
"Reproduce" checks the following, for **n ≤ 7**:

- (4-4) for every α;
- the sgn* identity for every minmax α;
- the resulting pairing identity ⟨r_w, sgn(σ)σ⟩ = sgn(w) sgn*(σ⁻¹w)[σ⁻¹w ∈ Γ_n]
  for all σ and all w with w(n) = n.

Output: all True for n = 2, …, 7.

Positive control: dropping the sgn(σ) twist makes the pairing check print
False for every n = 2, …, 5. The instrument is not vacuous.

**Verdict for the Wachs inputs (G):** MATCHES (preprint), and they give
Prop. Φ as the write-up says, **given Ree**.

### 4.3 Ree / Reutenauer Thm 3.1 (F)

Neither source is accessible: Ann. of Math. 68 (1958) is on JSTOR, and
Reutenauer, *Free Lie Algebras*, OUP 1993, is a paywalled book. **NOT
ACCESSIBLE**, so "Reutenauer Thm 3.1" stays unverified.

- **Crossref.** Confirms Ree, "Lie Elements and an Algebra Associated With
  Shuffles", Ann. of Math. 68, first page 210, Sept. 1958. The end page
  220 was not confirmed.
- **Open secondary source, read.** Aguiar–Mahajan, *Topics* (preliminary
  version), Lemmas 10.7–10.8 ("the Ree criterion"): z ∈ Lie[A] iff the
  coefficient sum over every non-singleton combinatorial top-lune
  vanishes. Lemma 10.10 states that Lie[A] and the decomposable part
  Lie[A]^⊥ are orthogonal. This is the arrangement version; for the braid
  arrangement it specialises to Lie_n ⊥ Sh_n. It is secondary support
  only.
- **Within the repository.** The write-up's natural-isomorphism table says
  [AudNat] checks "comb pairing = Sh_n without Ree" computationally. That
  is evidence for small n only.

Theorem S(c),(d) for n ≥ 7 therefore rests on two cited inputs: Wachs
(checked here) and Ree (not accessible). The main theorem (Theorem thm:main)
does **not** use Ree or Wachs.

## 5. Cartier–Milnor–Moore and PBW for species (H)

The write-up's Remark "Why a plethystic logarithm" cites "Aguiar–Mahajan,
*Monoidal Functors, Species and Hopf Algebras*, Ch. 11; theorem numbers not
re-checked". In the authors' PDF, §11.9.3, pp. 395–396:

- **CMM for species.** "The adjointness between U and P is part of the
  Cartier–Milnor–Moore theorem for species and can be found in Stover
  [Proposition 7.10 and Theorem 8.4]. It says that U and P define an
  adjoint equivalence, independent of the field characteristic. In
  particular, for any Lie monoid g and any connected cocommutative Hopf
  monoid h, we have (11.40) P(U(g)) = g and U(P(h)) = h."
- **PBW for species.** "There is also an analogue of the
  Poincaré–Birkhoff–Witt theorem for species which can be found in Joyal
  [Section 4.2, Theorem 2] and Stover [Theorem 11.3]. It says that
  U(g) = S(g) as comonoids for any Lie monoid g."

**How the write-up uses them.** 𝐐 is a connected cocommutative Hopf monoid.
CMM and PBW then give 𝐐 ≅ U(P𝐐) ≅ S(P𝐐) as species. S(q) = E ∘ q, so the
cycle index of 𝐐 is the plethystic exponential of ch P(𝐐), and
ch Prim(𝐐) = Log A(p₁). The hypotheses (connected, cocommutative, vector
species over ℂ) match the statements read.

**Verdict:** MATCHES at chapter level. AM state both results as
attributions (to Stover and Joyal), not numbered theorems, so there is no
AM theorem number to cite. The precise pointers are eq. (11.40) and the
paragraph after Cor. 11.46 in §11.9.3. The primaries (Stover, Joyal) were
not read, and the CRM Monograph print pagination is NOT ACCESSIBLE. This
remark is outside the main theorem.

## 6. Recommended wording fixes (for the write-up maintainer; not applied here)

None of these is a mathematical error. All three are optional.

1. Input (A): replace "(their Thm 3.3, after Czédli–Lenkehegyi)" with
   "(their Def. 3.1, after Körtesi–Radeleczki–Szilágyi; equivalently kernels
   of order-preserving maps, their Thm 3.3, after Czédli–Lenkehegyi)".
2. Input (B): "EC1, 2nd ed., Prop. 3.8.5" → "Prop. 3.8.5, in the form of
   Prop. 3.8.6", and drop "number not re-checked".
3. Input (C): add "Wachs, *Poset topology: tools and applications*, Thm 2.3.9"
   as an open reference. Munkres Thm 22.1 remains unverified.

Further updates to the open-problems item "Items the audits list as
UNCHECKED":

- Hall, Weisner, the Wachs 1998 preprint numbers, J–S v2 numbering and AM
  Ch. 11 are now checked.
- Crapo (Thm 3 per Stanley), Munkres 22.1, Reutenauer 3.1 and all journal or
  print numberings remain NOT ACCESSIBLE.

## 7. Out of scope

This check does not cover:

- Klyachko, Stanley 1982, Hanlon 1981 and Joyal 1986. They are used only to
  identify the antichain case with classical JKS, not as inputs to the
  theorem.
- Björner–Walker, which the write-up says is not needed.
- The *Topics* numbering items (Ex. 10.9, Thm 14.32, …) of [AudLit §5].

## Reproduce

Fetch the sources:

```
mkdir src && cd src
curl -sLO https://arxiv.org/pdf/1112.5782v2 ; curl -sLO https://arxiv.org/pdf/1112.5782v1
curl -sLO https://math.mit.edu/~rstan/ec/ec1.pdf
curl -sLO https://www.math.miami.edu/~wachs/papers/homlie.ps
curl -sLO https://www.math.miami.edu/~wachs/papers/toolnotes.pdf
curl -sLO https://pi.math.cornell.edu/~maguiar/a.pdf
curl -sLO https://pi.math.cornell.edu/~maguiar/surv-226.pdf
for f in *.pdf 1112.5782v*; do pdftotext -layout "$f"; done
# Wachs preprint uses bitmap fonts; render pages 6-19 to read the formulas:
gs -q -dNOPAUSE -dBATCH -sDEVICE=pnggray -r110 -dFirstPage=6 -dLastPage=19 -sOutputFile=wp-%02d.png homlie.ps
grep -n -E '3\.8\.5|3\.8\.6|3\.9\.3' ec1.txt          # Hall, Weisner
grep -n -E '^ *92\.' ec1.txt                           # Crapo (Ex. 3.92 + solution)
grep -n 'Hopf trace formula' toolnotes.txt             # Wachs Thm 2.3.9
grep -n -E 'Cartier|Poincar' a.txt                     # AM §11.9.3
curl -s https://api.crossref.org/works/10.1016/j.jcta.2013.09.010   # J-S metadata
```

Wachs identities check (n ≤ 7, about 1 min). Output: every line all `True`.
The positive control (remove the factor `sgn(s)*` in the `okphi` line) makes
`dual pairing` print `False`.

```python
from itertools import permutations
from collections import defaultdict
def comb(word):                      # right comb [w1,[w2,[...,[w_{n-1},w_n]]]]
    if len(word)==1: return {tuple(word):1}
    rest=comb(word[1:]); out=defaultdict(int); a=word[0]
    for u,c in rest.items(): out[(a,)+u]+=c; out[u+(a,)]-=c
    return out
def inv(w): return sum(1 for i in range(len(w)) for j in range(i+1,len(w)) if w[i]>w[j])
def des(w): return sum(1 for i in range(len(w)-1) if w[i]>w[i+1])
def sgn(w): return (-1)**inv(w)
def minmax(a): return all(a[i]<min(a[i+1:]) or a[i]>max(a[i+1:]) for i in range(len(a)-1))
def sgnstar(a): return (-1)**inv(a[:-1])
def mul(p,q): return tuple(p[q[i]-1] for i in range(len(q)))
def invp(p):
    r=[0]*len(p)
    for i,x in enumerate(p): r[x-1]=i+1
    return tuple(r)
for n in range(2,8):
    perms=list(permutations(range(1,n+1))); idw=tuple(range(1,n+1))
    combs={a:comb(a) for a in perms}
    ok44=all(combs[a].get(idw,0)==((-1)**des(a) if minmax(a) else 0) for a in perms)
    oksg=all(sgnstar(a)==(-1)**des(a)*sgn(a) for a in perms if minmax(a))
    okphi=True
    for w in perms:
        if w[-1]!=n: continue
        for s in perms:
            a=mul(invp(s),w)
            okphi&= sgn(s)*combs[w].get(s,0) == (sgn(w)*sgnstar(a) if minmax(a) else 0)
    print(n, "(4-4):",ok44, " sgn* identity:",oksg, " dual pairing:",okphi)
```
