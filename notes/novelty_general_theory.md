# Prior art for the new claims of the general-theory note

**Verdict: no claim was found stated in the literature. But Theorem 2 is a
specialization of Zaslavsky's 1977 dissection theorem. Lemma 0.2 and the
"F(V) does not see H_P" observation are already in Aguiar–Mahajan and Brown
(2000). Margolis–Saliola–Steinberg's Cohen–Macaulay theorem does not cover
Λ(V). So Theorem 1, Prop. 3 (as a combination), Conjecture G\* and
Theorems 6–8 remain NOT FOUND.**

Work item: mg-95686. This checks the new claims of `notes/general_theory.md`
("[GT]"), merged in df0b9c1, against the two sources [GT] flagged as unread
and the related literature. It does not repeat the searches of
`notes/novelty_search_2.md` ("[Nov2]", §0).

Verdicts:
- **KNOWN**: the statement is in the source, with the exact reference.
- **PARTLY KNOWN**: a special case, or the statement up to a short
  computation, is in the source.
- **NOT FOUND**: not in the sources listed in §0, which were opened and
  read. This is the result of a search, not a proof of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is never counted
  as a negative.

## Summary

| Claim of [GT] | Verdict | Closest prior art |
|---|---|---|
| Lemma 0.2 (a cone section is a ball or a sphere) | **KNOWN** | Aguiar–Mahajan, *Topics*, Prop. 2.26–2.27, eq. (2.12) |
| Theorem 1 (cone wedge theorem) | **NOT FOUND** | MSS Thm 1.1(3)/7.14 does not apply (§2.2). Braid case = Jenča–Sarkoci. Full case = Folkman. |
| Theorem 2 (cone Zaslavsky with lineality) | **PARTLY KNOWN**: a few-line specialization of Zaslavsky 1977 Thm 1.2 | Zaslavsky 1977 (as quoted by Deshpande); MSS Lemma 9.1 (same Euler-characteristic argument) |
| Prop. 3(a) (lunes in V = Lie_L(Γ_V)^⊥) | **PARTLY KNOWN**: the adjoint formula is AM (10.4) | AM *Topics* (10.4), Lemma 10.7 |
| Prop. 3(b) (bottom multiplicity of Σ_L = m(V); q ≤ m) | **PARTLY KNOWN**: the multiplicity formula is Brown's Thm 1. The identification with m(V) and q ≤ m were not found. | Brown 2000, Thm 1 eq. (8) and Thm 2 |
| Prop. 3, "correction to [Cone, §6]" (F(V) has no bottom multiplicity) | **KNOWN** | Brown 2000, §4.2, Thm 2 |
| Conjecture G\* | **NOT FOUND**. The case V = all chambers is KNOWN, including the det twist. | AM *Topics* Thm 14.32 (orientation space E^o[A]) |
| Theorems 6–8 (Q′, Prim_P = Lie(P), filtration, local PBW) | **NOT FOUND** | Malvenuto–Reutenauer 2011 (different coproduct) |
| §3 OM conjecture; §4 Varchenko–Gelfand route | Not claims; context only (§5) | Dorpalen-Barry et al. work with open cones and L^int(K) only |

**For the publication decision.** Theorem 1 and Conjecture G\* are the
parts that carry novelty, as far as this search reaches. A write-up should
do four things:
- present Theorem 2 as an instance of Zaslavsky's fundamental theorem of
  dissection theory;
- cite Aguiar–Mahajan for Lemma 0.2;
- cite Brown 2000, Thm 2, for the face semigroup of a closed convex set of
  chambers, its support lattice Λ(V), and the vanishing of its bottom
  multiplicity;
- not say that Margolis–Saliola–Steinberg covers the closed cone (§2.2).

## 0. Sources

### 0.1 Read: full text grepped, and the cited sections read

| Source | How it was obtained | What was read |
|---|---|---|
| Margolis–Saliola–Steinberg, *Cell complexes, poset topology and the representation theory of algebras arising in algebraic combinatorics and discrete geometry*, arXiv:1508.05446v2 ("MSS") | arXiv PDF, pdftotext | Thm 1.1; §2.4 (T-convex sets); §2.5 (strong elimination systems, COMs, Prop. 2.12–2.13); §3.4 (Prop. 3.16, def. of CW LRB, Prop. 3.21); §7 statement list; §9 (Lemma 9.1, Cor. 9.2, Thm 9.3, Thm 9.7). Grep: "wedge", "lineality", "T-convex", "Cohen-Macaulay", "Möbius", "closed convex". |
| Brown, *Semigroups, rings, and Markov chains*, J. Theoret. Probab. 13 (2000), arXiv:math/0006145 | arXiv PDF | §3 Thm 1 and Examples 1–3; §4.1–4.2 in full (Thm 2) |
| Aguiar–Mahajan, *Topics in Hyperplane Arrangements* (AMS Surveys 226), authors' preliminary version, pi.math.cornell.edu/~maguiar/surv-226.pdf ("AM") | PDF | §2.3 in full; §3.3.4–3.3.6; Ch. 2 and 3 notes; §7.9.8; §9.2; Lemma 10.7, Ex. 10.9, (10.4); §11.7.1; §14.4 up to Thm 14.32. Grep: "b(V)" (36 hits, all read in context), "Zaslavsky", "homotopy", "wedge of spheres", "Cohen-Macaulay", "orientation space". |
| Dorpalen-Barry–Proudfoot–Wang, *Equivariant cohomology and conditional oriented matroids*, arXiv:2208.04855 | arXiv PDF | §1 in full; Remark 4.4; grep |
| Dorpalen-Barry, *The Varchenko–Gel'fand ring of a cone*, arXiv:2104.02740 | arXiv PDF | §1 in full; §3 opening; grep |
| Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional oriented matroids*, arXiv:2507.06365 | arXiv PDF | abstract; grep |
| Dorpalen-Barry–Stump, *Shi arrangements restricted to Weyl cones*, arXiv:2204.05829 | arXiv PDF | abstract; grep |
| Dorpalen-Barry et al., arXiv:2301.05904 (Poincaré-extended ab-index) and arXiv:2512.10077 (cleanliness and the Varchenko–Gelfand algebra) | arXiv PDF | grep only ("cone", "lineality", "closed cone", "wedge of spheres") |
| Dorpalen-Barry–Kim–Reiner, arXiv:1906.00036 | arXiv PDF | grep (already read in [GT] §1.2) |
| Bandelt–Chepoi–Knauer, *COMs: complexes of oriented matroids*, arXiv:1507.06111 | arXiv PDF | grep: "Möbius", "wedge", "homotopy", "lattice of flats", "intersection lattice", "Zaslavsky", "T-convex", "lineality", "contractible"; Prop. 15 |
| Deshpande, *On a generalization of Zaslavsky's theorem for hyperplane arrangements*, arXiv:1111.1251 | arXiv PDF | §3 in full, including the statements of Zaslavsky 1977 Thm 1.2 and Cor. 2.2 that it quotes |
| Malvenuto–Reutenauer, *A self-dual Hopf algebra on double partially ordered sets*, arXiv:0905.3508 | arXiv PDF | abstract, §1; grep "linear extension", "primitive", "Lie" |
| Sanchez, *Poset Hopf monoids*, arXiv:2005.13707 | arXiv PDF | abstract; grep "linear extension", "component", "primitive" |
| Barnabei–Brini, *Dissections of convex sets and homotopy types of posets*, SLC B11c (1984) | SLC scan | the one-page abstract only (that is all the SLC scan contains) |

The arXiv API was positive-controlled before use: `au:Saliola` returns 5
entries. `au:"Dorpalen-Barry"` lists 15 papers; the cone-related ones are in
the table.

### 0.2 Web searches (new against [Nov2] §0.3)

- Zaslavsky "A combinatorial analysis of topological dissections" Advances
  1977 pdf
- poset of flats spanned by faces of a closed polyhedral cone hyperplane
  arrangement homotopy "wedge of spheres" lineality space (extended)
- Hopf monoid posets with linear extensions coproduct restriction to unions
  of connected components primitive elements Lie(P) Klyachko (extended)
- "order-preserving partitions" OR "order congruences" lattice
  generalization hyperplane arrangement cone convex set of chambers homotopy

None of them returned a statement of Theorem 1, Theorem 2 or Theorems 6–8.
The hits were Jenča–Sarkoci, Reading (shards), Sanchez, Aguiar–Mahajan
surveys and convex-cone background.

### 0.3 NOT ACCESSIBLE

- **Zaslavsky, *A combinatorial analysis of topological dissections*, Adv.
  Math. 25 (1977) 267–285**, doi:10.1016/0001-8708(77)90076-7. OpenAlex
  marks it bronze open access, but ScienceDirect returned 403 to both curl
  and WebFetch. Its Thm 1.2 and Cor. 2.2 are used below **as quoted by
  Deshpande** (arXiv:1111.1251, §3), not from the original.
- **Zaslavsky, *Counting the faces of cut-up spaces*, Bull. AMS 81 (1975)**:
  ams.org returned 403.
- **Barnabei–Brini, Adv. Math. 58 (1985) 109–118** (full paper). Only the
  SLC abstract was read. According to that abstract, it computes homotopy
  types of the poset of *regions and faces* of a dissected convex set. That
  poset is not the support lattice Λ(V).
- **Dorpalen-Barry, PhD thesis *Cones of hyperplane arrangements* (2021)**:
  not opened. Its cone chapter appears as arXiv:2104.02740, which was read.
- Still unread from [Nov2]: Baclawski–Björner 1981. It is not needed for the
  claims checked here.

## 1. Lemma 0.2 and the Euler identity: KNOWN

AM Prop. 2.26: "The intersection of any cone V of the arrangement with the
unit sphere is either a topological ball or sphere. The latter happens iff V
is a flat." Prop. 2.27 restates this in the spherical model. Eq. (2.12) gives
the corresponding Euler-characteristic identity:
- Σ_{F ∈ Cl(V)} (−1)^{rk F} = (−1)^{dim V − dim O} if V is a flat;
- the sum is 0 otherwise.

Lemma 0.2 of [GT] is Prop. 2.26 applied to the closed cone |V| ∩ Y. [GT]
proves it from scratch and should cite AM.

AM also has the flats and localizations of a cone that [GT] uses:
- the **base** b(V) is AM's name for the lineality space. This is why the
  grep for "lineality" in [Nov2] §4.1 found nothing;
- the **case** c(V) is the span;
- Lemma 3.2 and Exercise 3.30 identify lunes with base X with faces of the
  arrangement over X. This is the localization of [GT] Lemma 0.1(c), in
  AM's language.

## 2. Theorem 1 (cone wedge theorem): NOT FOUND

### 2.1 What would have covered it

The obvious candidate was MSS Theorem 1.1(3) / Theorem 7.14: "Let B be a
connected CW left regular band. Then each open interval of Λ(B) is a
Cohen-Macaulay poset." Λ(B) is the support semilattice. If F(V), the faces
of A contained in the closed cone |V|, were a CW LRB, then:
- its support semilattice would be exactly Λ(V);
- CM of Λ̄(V), together with the simple-connectivity argument of [GT]
  Step 5, would give most of Theorem 1.

### 2.2 Why MSS does not cover it

- **MSS's cone is the open cone.** MSS §2.4 defines the face semigroup of a
  T-convex set of topes as L⁺(A) = ∩_{e∈A} L⁺(e), the covectors with x_e = +
  on A. They note explicitly: "there is a slight difference in that Brown
  looks at the closure of the convex set of chambers, while we look at the
  interior." Prop. 2.13 shows that this interior object is a COM, and
  Prop. 3.16(3) shows that COMs are CW LRBs.
- **The open cone has the wrong support lattice.** The support semilattice
  of the open-cone COM is the set of flats meeting the open cone. That is
  Zaslavsky's L^int(K), and its intervals are intervals of L(A), which are
  geometric lattices and already CM by Folkman. Applied to the open cone,
  MSS Thm 9.3 gives the L^int count #V = Σ_{X ∈ L^int} |μ(X, ⊤)| (Zaslavsky's
  Example A). It does not give Theorem 2 of [GT].
- **The closed cone is not CW in MSS's sense.** The following argument is
  ours, from MSS's definitions.
  - MSS order an LRB by y ≤ x iff xy = y, so B_{≤x} = xB (proof of
    Prop. 3.16). A CW LRB needs every B_{<x} to be a sphere.
  - In F(V), B_{<x} is the set of faces of |V| strictly above x in the face
    order. That is the link of x inside the cell complex |V| ∩ S.
  - For a face x on the boundary of |V| (not in lin V), this link is a ball,
    not a sphere.
  - So F(V) is a CW LRB only when V is a flat.
- **F(V) is not a COM either.** It fails face symmetry: take x_e = 0 and
  y_e = s_e with e a wall; then (x ∘ −y)_e = −s_e. It does satisfy strong
  elimination, so it is one of MSS's "realizable strong elimination
  systems" (§2.5, with C = |V| closed convex). MSS prove only connectedness
  for those (Prop. 3.21), not CW.
- MSS list no other CW LRB whose support semilattice is Λ(V). Positive
  control: the same greps find MSS's remark about Brown's closure, so the
  closed cone is visible to the instrument.

### 2.3 Other sources

- **AM.** "homotopy" and "wedge of spheres" occur only in:
  - the descent and lune identities of Ch. 7 (relative pairs (X, A), with A
    homotopic to a wedge of spheres; §7.9.8, Example 7.89);
  - Folkman's theorem for L(A) (Prop. 14.25).

  Neither is about Λ(V).
- **Bandelt–Chepoi–Knauer.** They prove COMs are contractible (Prop. 15).
  The text has no Möbius function, lattice of flats or wedge.
- **Barnabei–Brini, from the abstract.** They give homotopy types for the
  region-and-face poset of a dissected convex set, a different poset.
- **The Dorpalen-Barry papers** have no lineality, closed-cone lattice or
  homotopy statement. All of them work with an open convex K and
  L^int(K).

**Verdict: NOT FOUND.** Two notes for a write-up:
- the method, the poset fiber theorem applied to the support map, is the
  same as MSS Lemma 9.1, Euler characteristic of the fibers of a cellular
  support map, lifted from Euler characteristics to homotopy;
- the full case (Folkman) and the braid case (Jenča–Sarkoci) are known, as
  [GT] says.

## 3. Theorem 2 (cone Zaslavsky with lineality): PARTLY KNOWN

**The cited theorem.** We use Zaslavsky 1977 Thm 1.2, the "fundamental
theorem of dissection theory". The original was NOT ACCESSIBLE (§0.3); the
statement is as quoted in Deshpande, arXiv:1111.1251, Thm 3.9. Let a space T
be dissected by finitely many subspaces, with complementary components C_j.
Let L be the intersection poset, under reverse inclusion with T at the
bottom. If the combinatorial Euler characteristic κ is a valuation on the
generated lattice, then

  Σ_j κ(C_j) = Σ_{Y ∈ L} μ(T, Y) κ(Y).

Deshpande proves the same thing by Möbius inversion of indicator functions:
eq. (3.1) and Thm 3.6. That proof works for any intersection-closed family
of closed unions of cells.

**Derivation of [GT] Theorem 2 (our computation).**
- *Set-up.* Take T = |V| ∩ S, dissected by the hyperplanes of A. The
  intersections are the sets Y ∩ |V| ∩ S. As [GT] Lemma 0.1(a) shows, they
  are indexed by Y ∈ Λ(V), and Y ∩ |V| determines its span. So L ≅ Λ(V)
  reversed, and μ_L(T, Y ∩ |V| ∩ S) = μ_{Λ(V)}(Y, R^d).
- *The values of κ.*
  - Each C_j is an open (d − 1)-cell, so κ(C_j) = (−1)^{d−1}.
  - By AM Prop. 2.26, κ(Y ∩ |V| ∩ S) is 1 for a ball (Y ⊄ lin V).
  - It is 1 + (−1)^{dim Y − 1} for a sphere (0 ≠ Y ⊆ lin V).
  - It is 0 for Y = 0.
- *The sum.* Use Σ_{Y ≥ 0} μ(Y, R^d) = 0. The right-hand side becomes
  −Σ_{Y ⊆ lin V} (−1)^{dim Y} μ(Y, R^d). Multiplying by (−1)^{d−1} gives

    #V = Σ_{Y ⊆ lin V} (−1)^{d − dim Y} μ_{Λ(V)}(Y, R^d),

  which is [GT] Theorem 2.
- *Caveat.* With Zaslavsky's own convention, L consists of *connected
  components* of intersections, and Y ∩ S = S^0 has two components when
  dim Y = 1. Deshpande's Möbius-inversion form avoids this, and it is
  exactly the proof [GT] gives.

**Related.**
- MSS Lemma 9.1 is the same argument for acyclic fibers.
- MSS Thm 9.3 and Brown 2000 eq. (12) (citing Zaslavsky 1977 Thm 3.2 and
  p. 275) give the open-cone count.

**Verdict: PARTLY KNOWN.** The formula in terms of Λ(V) and lin V was not
found written down. However, it is a specialization of Zaslavsky 1977
Thm 1.2 by a short computation, with the κ-values supplied by AM Prop. 2.26.
[GT] §1.2 calls it "elementary, and may be folklore". A write-up should
cite Zaslavsky 1977 Thm 1.2 and present Theorem 2 as an instance.

## 4. Proposition 3: PARTLY KNOWN; the "correction" is KNOWN

**Brown 2000 §4.2 treats exactly [GT]'s F(V).**
- Brown's semigroup is G = {G ∈ F : σ_i(G) ≥ 0, i ∈ J}, the faces of the
  closed convex set of chambers D.
- His M is the set of supports of faces in G. That is Λ(V).
- His M_0 ⊆ M is the set of flats that meet the open cone.
- **Thm 2 (Brown):** the random walk on D driven by weights on G has
  eigenvalue λ_X for each X ∈ M_0, with multiplicity |μ(X, V)|. In the
  proof he gets m_X = 0 for X ∈ M ∖ M_0.
- Brown's multiplicities m_X are defined by eq. (7), Σ_{Y ≥ X} m_Y = c_X.
  That is the same recursion that the composition multiplicities of the
  characters χ_X in kD satisfy, by taking traces. So, in our reading (not a
  sentence of Brown's), the multiplicity of the simple kG-module of
  X ∈ Λ(V) in kD is |μ(X, ⊤)| on M_0 and 0 off it.
- The bottom flat 0 lies in M_0 only when the open cone contains the origin,
  i.e. V is all chambers. So for proper V the bottom multiplicity of F(V)
  is 0.

That is the observation of [Cone, §6], "LRB theory of F(P) does not see
H_P", which [GT] §1.4 corrects. **That observation is KNOWN (Brown 2000,
Thm 2).**

**Prop. 3(b).**
- The formula [Γ_V : S_X] = Σ_{Y ≥ X} μ(X, Y) c_Y, for any LRB with identity
  acting on its chambers, is Brown's Thm 1, eq. (8). [GT] attributes the
  simple modules to Brown, and the formula is in the same theorem.
- What we did not find is:
  - the choice of the sub-LRB Σ_L (the faces in the lineality space);
  - the identity [Γ_V : S_0]_{Σ_L} = m(V), which needs Theorem 2;
  - the inequality q(V) ≤ m(V).

**Prop. 3(a).** The adjoint of C ↦ HC sends D to Σ_{C : HC = D} C. This is
AM (10.4), M_D · H_H = Σ_{C:HC=D} M_C, which AM use to prove the Ree
criterion (Lemma 10.7). The restriction to lunes inside V, through [Cone]
Lemma L, was not found.

**Prop. 3(c).** It uses Saliola's idempotent, as [GT] says. Nothing
cone-specific was found.

**Verdict: PARTLY KNOWN.** The ingredients are Brown 2000 Thms 1–2, AM
(10.4) and Saliola. The combination (Σ_L, m(V), q ≤ m) was not found. The
"correction" paragraph of [GT] §1.4 should cite Brown Thm 2 for the vanishing
on F(V).

## 5. Conjecture G\*: NOT FOUND (the full-arrangement case is KNOWN)

- **V = all chambers.** AM Thm 14.32: the map H^{r−2}(Π[A]) ⊗ E^o[A] →
  Lie[A] of (14.22) is a natural isomorphism, where E^o[A] is the
  one-dimensional orientation space (Lemma 14.23). Since Lie[A] = Lune^⊥,
  this is the V = all case of G\*, with E^o in the role of [GT]'s det. So
  the det twist is known at V = all, through the orientation space.
  - We did not find a sentence in AM saying that a reflection group acts on
    E^o[A] by the determinant.
- **No other case found.** No source states G\* for a proper cone, or a
  numerical identity dim(Lie[A]|_V) = (−1)^d μ(Λ(V)). Sources checked:
  - AM: Ex. 10.9, which characterizes Lie elements by zero sums over
    non-singleton top-cones, and §11.7, the extension problem; neither is
    about cones in this sense;
  - MSS;
  - Brown;
  - the Dorpalen-Barry papers.
- **No VG-ring connection.** The Varchenko–Gelfand route ([GT] §4) does not
  touch it.
  - Dorpalen-Barry (2104.02740, Thm 1) shows that the associated graded VG
    ring of an *open* cone has Hilbert series Poin(K, t), computed on
    L^int(K).
  - Dorpalen-Barry–Proudfoot–Wang (2208.04855, Thm 1.1) identify it with
    H\*(M_3(A, K)).
  - Both are about L^int(K), not Λ(V). Neither mentions a group action on
    top homology or a Lie module.

**Verdict: NOT FOUND**, beyond the V = all case. The pointed case reduces to
the valuation argument of [Nov2] §4.3, as [GT] says. The braid case is this
project's Theorem S.

## 6. Theorems 6–8 (Hopf monoid Q′): NOT FOUND

- **Malvenuto–Reutenauer.** Their abstract: the coproduct is "a natural
  decomposition of a poset into order ideals". Special double posets are
  Stanley's labelled posets. This confirms [GT]'s description: it is the
  down-set coproduct, not restriction to unions of components.
- **Sanchez.** Primitives of the poset-type Hopf monoids treated there
  (graphs, set partitions, hypergraphs, simplicial complexes) are indexed by
  indecomposables (connected objects). There are no linear extensions.
- **Search.** The extended search (§0.2) found no Hopf monoid of pairs
  (P, ℓ) with the union-of-components coproduct, and no P-graded Lie
  structure with components Lie(P).

**Verdict: NOT FOUND**, with the caveats of [GT] §2.3: the tools are
standard, and only one more search was made. Aguiar–Mahajan, *Monoidal
Functors, Species and Hopf Algebras* (the book), was not grepped for a
cocommutative poset Hopf monoid with this coproduct. That is the one obvious
remaining place to check.

## 7. Defects found in `notes/general_theory.md` (for the PM; not edited here)

1. **§1.2, "Prior art", Theorem 2** says "not found … may be folklore". It
   should say that Theorem 2 is an instance of Zaslavsky 1977 Thm 1.2 (§3
   above), and that the proof is the Möbius-inversion form of it (Deshpande
   Thm 3.6; MSS Lemma 9.1).
2. **§1.2, MSS sentence**, "the face monoid of a cone is a CW LRB". MSS's
   CW object is the *open*-cone COM (the T-convex set's interior,
   Prop. 2.13 and 3.16(3)). The closed-cone face monoid F(V) is not a COM
   and not CW by MSS's definition (§2.2). The sentence should be corrected,
   and MSS cited as covering only L^int-type support lattices.
3. **§0, Lemma 0.2** is AM *Topics* Prop. 2.26–2.27, and the Euler identity
   in the proof of Theorem 2 is AM (2.12). Both should be cited.
4. **§1.4, "Correction to [Cone, §6]"**: the vanishing of the bottom
   multiplicity of F(V) on Γ_V is Brown 2000, §4.2 Thm 2. Cite it. Brown's
   M is exactly Λ(V).
5. **§1.5, Φ_A citation.** AM Thm 14.32 is stated cohomologically:
   H^{r−2}(Π[A]) ⊗ E^o[A] ≅ Lie[A]. The property Φ_A(ρ_C) = ±C that [GT]
   uses is not stated in that form in the passage read. It has to be
   derived by dualizing, from the unbracketing formula (14.20c). [GT]
   already marks this citation "not re-checked"; the gap is now located.
6. **§1.5, the det twist.** For V = all chambers the twist is AM's
   orientation space E^o[A] (Thm 14.32). The "(new)" label should apply
   only to the computations on proper cones.
7. **§4, Dorpalen-Barry and Proudfoot–Wang.** Now read: both treat open
   cones and L^int(K). Neither gives a model of H̃(Λ̄(V)). The "not read"
   flag in §4 and §6 can be replaced by this.
