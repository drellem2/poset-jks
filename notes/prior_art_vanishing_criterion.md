# Prior art for the vanishing criterion (Formula Z, Theorem S, the ±S_n rule)

This note checks three claims of `notes/vanishing_criterion.md` ("[VC]")
against the literature:
- **Formula Z** ([VC] §2): χ_V(g) = Σ_{X ∈ Z\*(V,g)} μ_{L(A)^g}(0, X) ·
  m_X(V), a sum over the g-stable flats X ⊆ lin V with X ∩ Fix g = 0 and
  X + Fix g in no hyperplane;
- **Theorem S** ([VC] §3): χ_V(g) ≠ 0 for some g-stable top-cone V iff some
  X ∈ Z\*(g) has μ_{L(A)^g}(0, X) ≠ 0, realized by a top-lune;
- **Theorem A for −w** ([VC] §4, (A−)): for w ∈ S_n (n ≥ 3) acting on the
  braid arrangement, −w is nonzero on some cone iff the cycle lengths of w
  lie in {m, 2m} for one odd squarefree m.

Notation is that of [VC]. Throughout, χ_V(g) = (−1)^d det(g) μ(Λ(V)^g),
and "all chambers" means V = the whole space, L = R^d.

Verdicts:
- **KNOWN**: stated in a source read here, with the exact reference.
- **SPECIAL CASE KNOWN**: a narrower case is in a source read here.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is never counted
  as evidence either way. A statement about it that comes from another
  paper is marked "(secondary, via …)".

## Verdict

| Claim of [VC] | Verdict | Closest prior art (read) |
|---|---|---|
| **Formula Z**, braid arrangement, g = w ∈ S_n, V = all chambers | **SPECIAL CASE KNOWN** (in substance). Z\*(w) is the set of complements of Hanlon's *hinge* (the cycle partition) in Π_n^w. Hanlon counts j^{m−1} of them, each with [c, 1̂] ≅ the divisor lattice of j. So each term is μ(j), the multiplicity is (m − 1)!, and the sum is his value of μ(Π_n^w). Hanlon states the count and the value, not the sum over complements as an identity. | Hanlon 1981, §5 Lemmas 5–6 and Thm 4 (§2.1). The term-by-term match is checked in §2.1 for every w with 2 ≤ n ≤ 8 |
| **Formula Z**, any A and g, V = all chambers | **NOT FOUND** as an expansion. The left side is known: χ_all(g) = det(g) · tr(g \| A^d(A)), and tr(g \| A^p) is given by a sum over L(A)^g (Orlik–Solomon 1980, Thm 4.8). No source read expands it over flats transverse to Fix g. When Fix g is a flat, Z\*(g) is the set of complements of Fix g in L(A)^g. Crapo's complementation theorem and Stanley's modular factorization also sum over complements, but with other weights (§2.2) | Orlik–Solomon 1980 Thm 4.8; Crapo (via Stanley 1982 and Hanlon 1981) |
| **Formula Z**, proper cones (L ≠ R^d) | **NOT FOUND** | — (as for CF in [NovFP]) |
| **Theorem S** (some-cone criterion) | **NOT FOUND**. Two all-chambers facts are known. (a) For w ∈ S_n: μ(Π_n^w) ≠ 0 iff all cycles have one length o with μ(o) ≠ 0 (Stanley 1982, Lemma 7.1, from Hanlon Thm 4). (b) For Fix g = 0 ([VC] S2), all chambers is the only candidate cone, and its value is the top Orlik–Solomon trace (OS 1980, Thm 4.8). That every *other* cone vanishes when the transverse μ's vanish, and the top-lune witness, were not found | Stanley 1982 §7; Hanlon 1981; OS 1980 Thm 4.8; for g ∈ W: Bishop–Douglass–Pfeiffer–Röhrle Thm 1 (a different, all-chambers-only support condition, §3) |
| **Theorem A (A−)**, −w ∈ ±S_n, cycle lengths in {m, 2m}, m odd squarefree | **NOT FOUND**. Only the all-chambers part is known: L(A)^{−w} = L(A)^w gives χ_all(−w) = (−1)^{n−1} χ_all(w), so −w is nonzero on all chambers iff w is (Stanley 1982, Lemma 7.1). (A−) is strictly larger. For n ≤ 7 there are 9 classes −w, all with cycle lengths {1, 2}, that are nonzero on some cone but zero on all chambers, for example −(2,1) (§4). No source read treats −w on cones, and none states a {m, 2m} rule | Hanlon 1981; Stanley 1982; Sundaram 2018/2020 (Lie_n^{(2)}, Lie_n^S); type-B Lie: Aguiar–Mahajan *Topics* §14.9 and Notes (Bergeron; Gottlieb–Wachs). These concern the B_n arrangement, a different arrangement (§4) |
| Theorem A (A+), w ∈ S_n | not a claim of [VC]: [VC] calls it "the known rule" | all-chambers half: Stanley 1982 Lemma 7.1; per-cone half: [Thm, eq. closed], whose prior art is checked in [Nov2] |

**Bottom line.** Formula Z, Theorem S and the (A−) rule were not found in
the sources read. A write-up should cite three things:
- Hanlon 1981 §5 for the braid / g ∈ S_n / all-chambers instance of
  Formula Z. There Z\*(w) is the set of complements of the hinge, and the
  terms are Hanlon's.
- Orlik–Solomon 1980 Thm 4.8 for the all-chambers value of χ, which gives
  the all-chambers half of S2.
- Stanley 1982 Lemma 7.1 (Hanlon Thm 4) for the all-chambers half of (A±).

The new content is:
- the restriction to flats transverse to Fix g, for every cone;
- the positivity m_X ≥ 1;
- the some-cone criterion with its top-lune witness;
- the −w rule, which is not visible on all chambers.

## 0. Sources

### 0.1 Read

Full text: PDFs converted with `pdftotext -layout` and grepped. The listed
sections were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981) 319–341 | msp.org PDF `pjm-v96-n2-p04-s.pdf` | Abstract; §1; Lemmas 1–4; §5 (hinge h, Lemmas 5–6); Thm 4 and its proof; Thm 4A. Grep: "complement", "hinge", "Weisner", "cone", "signed", "hyperoctahedral", "anti" |
| Stanley, *Some aspects of groups acting on finite posets*, JCTA 32 (1982) 132–161 | author's PDF `pubfiles/50.pdf` | §1 (eq. (4)); §7 in full (Lemmas 7.1–7.2, Thm 7.3, Cors. 7.4–7.6). Grep: "fixed", "complement", "hyperoctahedral", "Dowling", "anti" |
| Orlik–Solomon, *Combinatorics and topology of complements of hyperplanes*, Invent. Math. 56 (1980) 167–189 | sites.math.washington.edu (course copy) | Introduction (trace discussion); Thm 4.8 and its proof |
| Douglass–Pfeiffer–Röhrle, *Cohomology of Coxeter arrangements and Solomon's descent algebra*, arXiv:1101.2075 ("DPR") | arXiv PDF | §1 (the history of Lehrer 1987, Lehrer–Solomon 1986, Blair–Lehrer 2001, Felder–Veselov, Bergeron, Douglass); §2.5, Conjecture 2.1. Grep: "Lie", "vanish", "support", "regular element", "Coxeter element", "character" |
| Bishop–Douglass–Pfeiffer–Röhrle, *Computations for Coxeter arrangements and Solomon's descent algebra III*, arXiv:1403.6227 ("BDPR") | arXiv PDF | Abstract; §2 through Thm 1 (top component of A(W_L)). Grep: "top", "cuspidal" |
| Felder–Veselov, *Coxeter group actions on the complement of hyperplanes and special involutions*, arXiv:math/0311190v2 | arXiv PDF | Introduction; Prop. 1 (Lefschetz on M_G with the action twisted by conjugation); Props. 2–4; Prop. 11 and the paragraph after it |
| Sundaram, *On a curious variant of the S_n-module Lie_n*, arXiv:2005.01896 (Algebraic Combin. 3 (2020)) | arXiv PDF | Abstract; §1; Definition 2.1 and the facts after it; Thm 3.6; Prop. 3.7; Thm 3.8. Grep: "vanish", "support", "same length", "odd" |
| Sundaram, *Variations on the S_n-module Lie_n*, arXiv:1803.09368v3 | arXiv PDF | Abstract; §1. Grep: "vanish", "supported", "equal length", "cone", "hyperplane" |
| Sundaram, *Prime power variations of higher Lie_n modules*, arXiv:2107.06389 | arXiv PDF | Grep as for 1803.09368 |
| Aguiar–Mahajan, *Topics in Hyperplane Arrangements* (AMS Surveys 226), authors' preliminary version `surv-226.pdf` ("AM") | PDF | Introduction paragraph "Lie elements and JKS" (top-lune criterion); §14.9.7 (Thms 14.79–14.80, type B Lie); Notes to Ch. 14 (the Hanlon/Stanley/Lehrer–Solomon paragraph and the "Type B" paragraph); App. C.4.6. Grep: "character of", "vanish", "Lie" near "cone"/"lune", "finite group", "group action" |
| *Cohomology of the hyperplane complement of a quaternionic reflection group*, arXiv:2510.18607 | arXiv PDF | §2.10 only (it restates the graded-trace formula of Orlik–Terao Ch. 6, as a positive control for the OS Thm 4.8 reading) |
| Adin–Athanasiadis–Elizalde–Roichman, *Character formulas and descents for the hyperoctahedral group*, arXiv:1504.01283 | arXiv PDF | Abstract and grep "Lie", "vanish". Its type-B Lie characters are B_n-characters of the B_n arrangement |
| Berget (type-B analogue of the Lie representation), DMTCS FPSAC proceedings, dmtcs.episciences.org/6327 | PDF | Introduction (the pointer to Bergeron) |

Only §2.10 of arXiv:2510.18607 was used, as a cross-check.

### 0.2 Web searches

- Lehrer Solomon action of symmetric group on cohomology of complement of
  reflecting hyperplanes induced from centralizers
- Sundaram "variant of Lie_n" character vanishes cycles odd length
- type B Lie representation character hyperoctahedral group vanishing
  Bergeron Reiner signed permutation
- Lehrer equivariant Orlik-Solomon algebra character of element Möbius
  function fixed lattice "fixed points" hyperplane arrangement
- Lehrer "A vanishing theorem for hyperplane cohomology" Bull. Austral.
  Math. Soc. 1996 abstract (extended)
- Orlik Solomon "Unitary reflection groups and cohomology" trace of g on
  Orlik-Solomon algebra sum over g-stable flats Möbius
- Bergeron "hyperoctahedral analogue of the free Lie algebra" character
  dimension
- Lehrer "Poincaré polynomials for unitary reflection groups" regular
  element equivariant Poincaré polynomial product formula exponents
- permutation "cycles of length m and 2m" m odd character vanishes
  symmetric group Lie representation sign twisted (extended)
- braid arrangement S_n x Z/2 action negation -1 Lie representation cones
  posets anti-automorphism character Whitney homology
- Douglass Pfeiffer Röhrle "Lie character" OR "Lie representation" finite
  Coxeter group top component Orlik-Solomon induced from Coxeter element
  centralizer

None returned a formula over flats transverse to Fix g, a some-cone
criterion, or a {m, 2m} cycle rule. The {m, 2m} search returned only
textbook pages on cycle types.

**Positive controls for the negative greps.**
- Hanlon: "complement" (11 hits) finds Lemma 6 and the c(f) construction,
  which are used in §2.1, and "hinge" finds its definition. "Weisner",
  "cone", "signed" and "hyperoctahedral" have no hits. The one hit for
  "anti" is in the journal's back matter.
- Sundaram 1803.09368: "vanish" finds the sentence "their characters
  vanish unless the conjugacy class has all cycles of equal length" (§1),
  so the instrument finds support statements when they exist. No hit
  mentions −1 acting on the arrangement, cones, or cycle lengths {m, 2m}.
- AM: "top-lune criterion" finds the introduction and §10.1.3. "Character
  of" has 283 hits. Those near "Lie" are the Ch. 14 notes (classical
  Lie_n) and the type-B paragraph.

### 0.3 NOT ACCESSIBLE

- **Lehrer–Solomon, *On the action of the symmetric group on the cohomology
  of the complement of its reflecting hyperplanes*, J. Algebra 104 (1986)
  410–424.** Not opened. Content (secondary, via DPR §1 and AM Ch. 14 notes):
  - H^p(M) for W = S_n is a sum of representations induced from linear
    characters of centralizers.
  - Their Cor. 4.6 gives the character used for AM Thm 14.58.
  - All of this is about the whole complexified complement (all chambers)
    and g ∈ S_n.
- **Lehrer, *On the Poincaré series associated with Coxeter group actions
  on complements of hyperplanes*, J. London Math. Soc. (2) 36 (1987)
  275–294**, and **Lehrer, *On hyperoctahedral hyperplane complements*,
  Proc. Symp. Pure Math. 47 (1987) 219–234.** Not opened. Content
  (secondary, via DPR §1 and Felder–Veselov): equivariant Poincaré
  polynomials P_W(g, t) of the whole complement.
- **Lehrer, *A vanishing theorem for hyperplane cohomology*, Bull. Austral.
  Math. Soc. 53 (1996) 361–368.** The Cambridge PDF returned HTTP 403.
  - Abstract (secondary, via search snippet): a representation of the
    symmetry group whose pointwise isotropy groups satisfy a vanishing
    condition does not occur in the Orlik–Solomon algebra.
  - Felder–Veselov (after Prop. 11) cite it for "the alternating
    representation never appears in H^\*(M_G)".
  - This is a vanishing of multiplicities in the whole algebra. It is not
    a vanishing of a character value at an element, and it does not
    concern cones.
- **Lehrer, *Poincaré polynomials for unitary reflection groups*, Invent.
  Math. 120 (1995) 411–425**, and **Blair–Lehrer, *Cohomology actions and
  centralisers in unitary reflection groups*, Proc. LMS (2001).** Not
  opened. Content (secondary, via DPR §1 and the Blair–Lehrer abstract):
  - P_W(g, t) = Σ_{x ∈ Z_W(g)} f_g(x)(−t)^{codim Fix x}, a sum over the
    centralizer, not over flats;
  - the formula covers linear maps normalizing W, so in type A it covers
    −w.
  - Again this is the whole complement only.
- **N. Bergeron, *A hyperoctahedral analogue of the free Lie algebra*,
  JCTA 58 (1991) 256–278**, and **F. Bergeron–N. Bergeron, *Orthogonal
  idempotents in the descent algebra of B_n and applications*, JPAA (1992).**
  Not opened. Content (secondary, via AM Ch. 14 notes, "Type B", and DPR §1):
  - Bergeron's construction gives W(B_n) acting on the B_n arrangement
    (H^\*(M_{B_n}) ⊗ sign).
  - "His Theorem 4.1 is equivalent to our Theorem 14.77."
- **Reiner.** No paper of Reiner's on the vanishing of type-B Lie
  characters was found by the searches of §0.2. Reiner's signed-poset and
  type-B P-partition papers were not opened.
- **Crapo, *The Möbius function of a lattice*, JCT 1 (1966).** Not opened.
  The complementation theorem is used as stated by Stanley 1982 (§7 Remark)
  and [VC] §6.

---

## 1. What is being compared

For V = all chambers, χ_all(g) = (−1)^d det(g) μ(L(A)^g). Orlik–Solomon
1980, Thm 4.8, reads:

> Let L be a finite geometric lattice of rank ℓ. Let G be a group which
> acts as an automorphism group of L. If g ∈ G let L^g = {x ∈ L | gx = x}
> and let μ_g be the Möbius function of the poset L^g. Then
> Σ_p tr(g | A_p) t^p = Σ_{x ∈ L^g} μ_g(x)(−t)^{r(x)}.

At the top degree p = r = d (A essential), this gives
tr(g | A_d) = (−1)^d μ(L(A)^g). Hence χ_all(g) = det(g) · tr(g | A_d(A)).
This is the "full Lie character" of [VC] up to the det twist. arXiv:2510.18607
§2.10 restates the same formula with a citation to Orlik–Terao Ch. 6. That
is the positive control for this reading.

So for V = all chambers, the *value* of χ is classical. The claims of [VC]
are not about the value. They are about:
- (Z) an expansion of that value over the transverse flats Z\*(V, g),
  with positive multiplicities and for every cone;
- (S) a criterion over all cones;
- (A−) the explicit answer for −w in type A.

Every source below was read with these three questions in mind.

## 2. Formula Z

### 2.1 The braid arrangement, w ∈ S_n, all chambers: Hanlon's hinge (SPECIAL CASE KNOWN)

Hanlon 1981 §5 works with σ having m cycles of squarefree length j (Lemma 4
reduces to this). He defines:

> Let h be the partition in L which puts each cycle in a block by itself …
> We call h the hinge.

His results on the hinge:
- **Lemma 6.** "In the lattice 𝓜, h has j^{m−1} complements". Each
  complement c satisfies (c) [c, 1] ≅ D_j, the divisor lattice of j. The
  proof constructs c(f) and notes that "c(f) is a complement to h in Π(N),
  hence … in L".
- **Theorem 4.** μ_𝓜(0̂, 1̂) = μ(j)((−1)^{m−1}(m − 1)!) j^{m−1}.

Stanley 1982, Lemma 7.1, quotes the value for L = Π_n^π, with the remark
that it transfers from 𝓜 to L.

Translate to [VC]. The flats of the braid arrangement are ordered by
inclusion, which is the reverse of refinement. So:
- the bottom flat 0 is Hanlon's 1̂;
- U = Fix w = X_cyc is the flat of the hinge h;
- μ_{L(A)^w}(0, X_π) = μ_{Π^w}(π, 1̂).

For w ∈ S_n, [VC] §4 shows Z\*(w) = {w-stable π : π ∨ cyc = 1̂,
π ∧ cyc = 0̂}. These are exactly the complements of h in Π_n^w. For
V = all chambers:
- Z\*(V, w) = Z\*(w), the complements of the hinge;
- each term is μ(π, 1̂) = μ(o), Hanlon's μ(D_j) = μ(j) with j = o;
- each multiplicity m_X(all) is (m − 1)!. A_X|_U is the braid arrangement
  on the m cycles, whose bottom multiplicity is |μ(Π_m)|.

So Formula Z on all chambers reads

  μ(Π_n^w) = (−1)^{m−1} (m − 1)! · Σ_{c complement of h} μ_{Π^w}(c, 1̂),

term for term Hanlon's count (j^{m−1} complements, each with μ(j)) times
μ([h, 1̂]) = μ(Π_m). Hanlon gives the value and the count. He does not
write the sum over complements as an identity, and his proof goes through
supersolvability and a Birkhoff-polynomial factorization, not through a
transversality argument. Hence "in substance".

COMPUTED (`compute/prior_art_vanishing_criterion.py`, part (H)), for every
cycle type with 2 ≤ n ≤ 8 (65 types):
- the displayed identity holds;
- when all cycles have one length o, there are exactly o^{r−1} complements,
  each with μ(c, 1̂) = μ(o);
- otherwise every complement has μ = 0.

Negative control: replacing "complement" by "π ∨ cyc = 1̂" alone (that is,
dropping X ∩ U = 0) breaks the identity on 56 of the 65 types. It still
holds on 9 types: the identity w = 1^n (n = 2, …, 8), where U = R^{n−1}
leaves no other X, and w = (4), (8), where every term has μ = 0.

This special case does not reach −w. There U = Fix(−w) is not the hinge
flat, Z\*(−w) is a different set, and the sum can cancel ([VC] §5,
−(2,1)).

### 2.2 General A, all chambers: Crapo and Stanley expand over complements, with other weights (NOT FOUND)

When U = Fix g is itself a flat, Z\*(g) is the set of complements of U in
L(A)^g:
- X ∩ U = 0 is X ∧ U = 0̂;
- "X + U in no hyperplane" is X ∨ U = 1̂.

Two classical expansions sum over complements:
- **Crapo's complementation theorem**: μ(0̂, 1̂) = Σ μ(0̂, x) ζ(x, y)
  μ(y, 1̂), over pairs x ≤ y of complements of a fixed element. It is cited
  in Stanley 1982 §7 Remark (for "μ(0̂, 1̂) = 0 unless 0̂ is a meet of
  coatoms") and used in [VC] §6 (CR).
- **Stanley's modular factorization**, used by Hanlon in the proof of
  Thm 4. It sums over the b with b ∧ h = 0̂.

Formula Z has the weight m_X(V) ≥ 1, the bottom multiplicity of a cone of
an arrangement in U. Crapo's weights are μ(y, 1̂) summed over complements
y ≥ x. In general U is not a flat, and then Z\*(g) is strictly larger than
the set of complements of the flat spanned by U. No source read contains an
expansion with these index sets and weights, for all chambers or for a cone.
Whether Formula Z on all chambers, when U is a flat, can be derived from
Crapo's theorem was **not checked**. It would need m_X(all) = ± Σ_{y ≥ X,
y a complement} μ(y, 1̂).

### 2.3 Proper cones (NOT FOUND)

For proper cones, [NovFP] already found no source with any formula for
χ_V(g) (EZ, CF, Cor. V). The present searches add:
- Lehrer, Lehrer–Solomon, Blair–Lehrer and Felder–Veselov concern the
  whole complexified complement;
- AM treat Lie elements of the whole arrangement (Lie[A] = P(Γ[A])), with
  no group action on cones;
- Sundaram's modules are S_n-modules with no arrangement-cone structure.

## 3. Theorem S (NOT FOUND)

No source read states a criterion for "nonzero on some cone", for any
arrangement. What is known is the all-chambers value and some support
results for it:
- **Type A, w ∈ S_n.** Stanley 1982, Lemma 7.1: μ(Π_n^π) = (−1)^{d−1}
  μ(n/d)(d − 1)!(n/d)^{d−1} "if π is a product of d cycles of length n/d,
  = 0 otherwise". This gives the all-chambers half of (A+). The other
  half, that no proper cone is nonzero when all chambers is zero, is
  [Thm, eq. closed] with [VC] §4, and is not in Stanley or Hanlon.
- **Fix g = 0 ([VC] S2).** χ_all(g) = det(g) tr(g | A_d), given by OS 1980
  Thm 4.8. The new part of S2 is that every other g-stable cone has
  χ_V(g) = 0.
- **g ∈ W, all chambers.** BDPR Thm 1 with L = S (α_S = 1) states, for W
  of rank ≤ 8:
  > ρ̃_S = Σ_{w ∈ C_S} Ind_{C_W(w)}^{W} φ_w = ε ω̃_S,

  where ω̃_S is the character of the top Orlik–Solomon component and C_S
  runs over the cuspidal classes. So tr(g | A_d) ≠ 0 forces g to centralize
  a cuspidal element of W. DPR Thm 6.3 proves this for S_n.

  This is a necessary condition on all chambers only. It is a different
  kind of statement from Theorem S: it is a condition on the centralizer,
  not on transverse flats, and it is not stated as an equivalence.
- **Top-lunes.** AM's top-lune criterion (Introduction; §10.1.3) says that
  a Lie element sums to zero on every top-lune with more than one chamber.
  Theorem S's witness cone V♯ is a top-lune. AM use no group action, so
  this is a shared object, not prior art for S.
- **Lemma F**, an input, is KNOWN (folklore; Kamiya–Takemura–Terao
  Prop. 2.7), as recorded in [NovFP] §1.2.

## 4. Theorem A for −w (NOT FOUND)

**What is known reduces to all chambers.** −1 fixes every subspace, so
L(A)^{−w} = L(A)^w and det(−w) = (−1)^{n−1} det(w) on R^n_0. Hence
χ_all(−w) = (−1)^{n−1} χ_all(w). By Stanley 1982 Lemma 7.1, this is
nonzero iff all cycles of w have one length o with μ(o) ≠ 0. The (A−) rule
is strictly larger.

COMPUTED (`compute/prior_art_vanishing_criterion.py`, part (D)): Theorem S
at −w is evaluated from the definition of Z\*(−w) in [VC] §4, with each
μ(0, X_π) computed by recursion in Π^w (not from Hanlon's formula). It
matches (A−) on all 41 classes with 3 ≤ n ≤ 7. Nine of these classes are
nonzero on some cone but zero on all chambers: −w for w = (2,1), (2,1,1),
(2,2,1), (2,1,1,1), (2,2,1,1), (2,1⁴), (2,2,2,1), (2,2,1,1,1), (2,1⁵).
All of them have cycle lengths {1, 2} (m = 1). The first class with m ≥ 3
and mixed lengths is −(6,3) at n = 9, which [VC] §4 checks.

**Sources that could have contained it, and what they contain:**
- *Hanlon 1981; Stanley 1982.* Only σ ∈ S_n acting on Π_n, and only the
  fixed lattice's μ. The transversality conditions of Z\*(−w) (odd orbit
  lengths, no tight pairs) do not occur. Grep "signed" and
  "hyperoctahedral" in Hanlon: no hits. In Stanley the hyperoctahedral
  group appears only acting on the face lattice of the cross-polytope (§6),
  which is unrelated.
- *Sundaram 2018, 2020, 2021.*
  - Lie_n^{(2)} = Ind_{C_n}^{S_n}(exp(2πi/n · 2^{k_n})) (Definition 2.1).
    It equals Lie_n for n odd and sgn ⊗ Lie_n for n ≡ 2 (mod 4).
  - Its character, like those of the Lie_n^S, is supported on classes with
    all cycles of one length (1803.09368 §1).
  - These are S_n-modules. Negation of the braid arrangement plays no
    role, and no {m, 2m} support occurs.
- *Lehrer 1995 / Blair–Lehrer 2001* (NOT ACCESSIBLE). They cover maps
  normalizing W, hence −w, but only for the whole complement. On all
  chambers −w carries no new information (above).
- *Type B.* AM §14.9.7 (Thms 14.79–14.80) and the Ch. 14 notes (Bergeron
  1991, Gottlieb–Wachs) describe the type-B Lie and Whitney-homology
  modules of the **B_n arrangement** as S^±_n-modules. The element −w lies
  in S^±_n, but its character on those modules is a trace on the type-B
  arrangement. χ_V(−w) of [VC] is a trace on cones of the **A_{n−1}**
  arrangement, which only ±S_n preserves.
  - No source read states a support or vanishing rule for type-B Lie
    characters at elements of ±S_n.
  - Adin–Athanasiadis–Elizalde–Roichman give type-B Lie character formulas
    as B_n-characters, from the abstract and grep only.
  - Bergeron 1991 was not accessible (§0.3).
  - So whether some type-B Lie character has support {−w : lengths in
    {m, 2m}} on ±S_n is **not checked**. It would be a coincidence of
    supports, not a statement about cones of A_{n−1}.
- *Felder–Veselov* compose g with complex conjugation and apply Lefschetz
  to the complexified complement. Their fixed sets, U ⊕ iE for an
  involution, are close in spirit to [VC] S3, but they compute total
  cohomology, not the top degree on a cone.

**A reformulation that may help a later search.** Theorem A states both
signs as "⟨g⟩ acts freely on {±e_1, …, ±e_n} and μ(ord g) ≠ 0". For +w this
is the familiar support of Lie_n, Z/o acting freely on [n]. For −w it is
the same condition on the 2n signed vectors. No source read states the
condition in this form.

## 5. Corrections to [VC]

- [VC] §9 says that the character formulas of Lehrer and Orlik–Solomon "may
  overlap with the full-cone case of (Z) and with S2". Checked:
  - OS 1980 Thm 4.8 gives the all-chambers value χ_all(g) = det(g)
    tr(g | A_d) = (−1)^d det(g) μ(L(A)^g). That is the definition side of
    (Z), not the expansion. It does give the all-chambers half of S2.
  - The braid / g ∈ S_n case of (Z) on all chambers is Hanlon's hinge
    computation (§2.1). [VC] §2 "Checks" already notes Z\*(C_P, g) =
    F(P, g). [Nov2] identified F(P, g) with Hanlon's complements c(f). The
    citation belongs in [VC] §2.
  - The Lehrer papers themselves remain NOT ACCESSIBLE.
- [VC] Verdict row A credits μ(Π_n^σ) to "([FPM] (ii); Hanlon)". Stanley
  1982 Lemma 7.1 is the place where it is stated for the full fixed lattice
  L = Π_n^π. Hanlon's Thm 4 is stated for 𝓜 (Stanley's Remark after
  Lemma 7.1). A write-up should cite both.
- No claim of [VC] was found to be wrong or already published in the
  stated generality.

## Reproduce

Literature: the PDFs of §0.1 were fetched with `curl`, converted with
`pdftotext -layout`, and searched with `grep -n -i -E` for the patterns
listed there. The URLs are:
- Hanlon: `https://msp.org/pjm/1981/96-2/pjm-v96-n2-p04-s.pdf`
- Stanley: `https://math.mit.edu/~rstan/pubs/pubfiles/50.pdf`
- Orlik–Solomon: `https://sites.math.washington.edu/~billey/classes/561.fall.2019/past.articles/orlik.solomon.1980.pdf`
- AM: `https://pi.math.cornell.edu/~maguiar/surv-226.pdf`
- arXiv: 1101.2075, 1403.6227, math/0311190v2, 2005.01896, 1803.09368,
  2107.06389, 1504.01283, 2510.18607

Computation, from `compute/` (plain Python 3, no third-party packages):

    python3 prior_art_vanishing_criterion.py > output/prior_art_vanishing_criterion.txt   # ~12 s, ALL CHECKS PASSED, exit 0
    python3 prior_art_vanishing_criterion.py --quick                                        # n <= 6, < 1 s
    python3 -m unittest test_prior_art_vanishing_criterion                                  # < 1 s, positive and negative controls

The archived output is `compute/output/prior_art_vanishing_criterion.txt`.

References: [VC] = `notes/vanishing_criterion.md`; [NovFP] =
`notes/novelty_fixed_point_formula.md`; [Nov2] =
`notes/novelty_search_2.md`; [Thm] = `notes/poset_jks_theorem.tex`;
[FPM] = `notes/fixed_point_mobius_identity.md`.
