# Audit of `notes/conjecture_cr_v.md`

**Verdict: REFUTATION HOLDS.** The rank-4 counterexample to Conjecture CR_V
is correct. I rebuilt it from the definitions, by hand and with my own
code. All four of (a)–(d) hold, and χ_V(g) = 0 comes out the same by four
independent routes. Theorems P, Q and 3, Lemmas F, K and R3, Proposition Ln
and the claim about Knop's lemma all hold as stated. I re-derived every
proof and found no gap. The remarks in §6 below are wording points; none
changes a statement.

The note is cited as [CRV]. Its references [PCV], [VC], [GT], [FP] and
[PAP] are as in [CRV]. I used [VC] and [FP] only for the definitions and
for statements already audited there: the definition of χ_V(g), Formula Z,
Theorem CF and the identities (2.1)–(2.2) of [FP]. I used [GT] §0 for
top-cones, Λ(V), Lemma 0.1 and m(V), and [PAP] §3.2 only for the 8-element
lattice. This audit imports nothing from `compute/`. All code is in
`compute/audit_conjecture_cr_v.py` ("[Aud]") with tests in
`compute/test_audit_conjecture_cr_v.py`. I did not read
`compute/conjecture_cr_v.py` or its output, and I wrote this verdict before
reading any other review of [CRV].

## Per-claim table

| # | Claim of [CRV] | Verdict | How checked |
|---|---|---|---|
| CX-a | V = {x_4 ≤ x_1 + 3x_2 ≤ −x_4} is a top-cone of the 12-hyperplane C_6 × C_4 arrangement, and g = diag(−1, −1, 1, 1) ∈ Stab(V) | **HOLDS** | by hand (§1.1); [Aud] finds V among the 37,867 top-cones, with S_max(V) exactly the two defining hyperplanes, and checks gA = A, gV = V and g ∈ C_6 × C_4 |
| CX-b | Λ(V)^g is a 9-element lattice, every element complemented | **HOLDS.** The lattice and a complement for each element are listed in §1.2 | by hand (every g-stable subspace classified); [Aud] by brute force on the poset |
| CX-c | Λ(V)^g is not modular | **HOLDS** (witness c ≤ D, y = L) | by hand; [Aud] tests all triples |
| CX-d | χ_V(g) = 0 | **HOLDS, four ways**: the definition (μ(M) = 0); Formula Z (1·1 + (−1)·1); Theorem CF of [FP] (2 − 2 − 1 + 1); and the trace of g on H̃_2 of the order complex of the proper part of the full Λ(V) (dimension 72 = m(V), trace 0). The g-fixed faces and their signs give (2.1) on all 9 flats of M and (2.2) with #V^g = 2 | §1.3; by hand for the first three |
| CX-36 | The C_6 × C_4 arrangement has 36 counterexample pairs, three families of 12; the Formula Z terms are (1, 1), (−1, 1) for |M| = 9 and (1, 2), (−1, 2) for |M| = 10, 11 | **HOLDS.** Exactly 36, in exactly these families, with these terms; all non-modular. The row counts 38,400 pairs, 60 zeros, 60 not Cor. V and 38,376 complemented are reproduced | [R4] |
| Q | Theorem Q: if L + U lies in a hyperplane, then cl(L + U) and cl(U) are uncomplemented elements of M | **HOLDS** | re-derived (§2); every such pair of the sweeps |
| P | Theorem P: for pointed V, χ = 0 iff U lies in a hyperplane, and then cl(U) is uncomplemented; otherwise χ = #V^g ≥ 1 | **HOLDS** | re-derived (§2); every pointed pair of the sweeps |
| CorV | The Cor. V zeros of [VC] are Crapo zeros, in every rank | **HOLDS** (this is Q) | as Q |
| F | Lemma F | **HOLDS** | re-derived (§3); checked in the form used: every Y ∈ M with Y ⊄ L contains a nonzero g-fixed face of V whose span lies in cl(U) |
| K | Lemma K, for every W ∈ M containing U | **HOLDS** | re-derived (§3); checked for **every** such W, not only W = cl(U) |
| Ln | Proposition Ln (i)–(iv), including χ = c_0 − c_L and the trace criterion for c_0 = c_L | **HOLDS** | re-derived (§3); every dim L = 1 pair; c_X counted as the number of chambers of {H ∩ U : H ⊇ X} in \|V\| ∩ U, and the trace criterion decided by exact feasibility |
| R3 | Lemma R3 (μ(L(A)^g) = 0 iff an uncomplemented element, rank 3), with the table of case (c) | **HOLDS** | re-derived row by row (§3); every group element of every rank-3 family (§7); every row's μ formula checked against (e, e′, a, p, λ) computed from the arrangement |
| 3 | Theorem 3: CR_V for d ≤ 3 | **HOLDS** | re-derived case by case (§4); COMPUTED on 37,707 rank ≤ 3 pairs (all 30 families, §7), 0 failures |
| Mod | "Complemented non-modular Λ(V)^g with μ ≠ 0 are common, e.g. 186 of the 266 nonvanishing pairs of A_3"; Knop's Lemma A.2 does not reach CR_V | **HOLDS, with exactly the stated scope.** A_3 (±S_4, class representatives, every g-stable cone): 300 pairs, 266 nonzero, all 266 complemented, 186 of them non-modular. B_3: 998 complemented, 862 non-modular, as in the note's table. Knop's lemma is about modular lattices, and the counterexample is not modular | §5 |

## 1. The counterexample

### 1.1 The data, and (a)

A has the 12 hyperplanes H_{u,w} : u_1x_1 + u_2x_2 + w_1x_3 + w_2x_4 = 0,
u ∈ {(1, 3), (2, −1), (3, 2)}, w ∈ {(±1, 0), (0, ±1)}. The matrix
R = [[1, −1], [1, 0]] has order 6, and on column vectors it permutes
(1, 3) → (−2, 1) → (−3, −2) → (−1, −3) → (2, −1) → (3, 2) → (1, 3). So
the forms ±u are one R-orbit, and the w are one orbit of the rotation by
π/2. [Aud] builds the point action of C_6 × C_4 from R and that rotation
(order 24), and checks that every element permutes the 12 hyperplanes. It
also checks that g = diag(−1, −1, 1, 1) is the element of order 2 of the
C_6 factor.

Write s = x_1 + 3x_2. V is the set of chambers with s − x_4 > 0 and
s + x_4 < 0. It is nonempty (s = 0, x_4 = −1), so it is a top-cone, and
|V| = {x_4 ≤ 0, |s| ≤ −x_4}. g maps s ↦ −s and fixes x_4, so it exchanges
the two inequalities: gV = V. No other hyperplane has V on one side
([Aud]: S_max(V) is exactly these two). So L = {s = 0, x_4 = 0} =
span{a, e_3} with a = (−3, 1, 0, 0). [Aud] counts 346 chambers, 2,037
faces and 145 flats, and |V| holds 88 chambers.

### 1.2 The lattice, (b) and (c)

The eigenspaces of g are P = span{e_1, e_2} (−1) and U = span{e_3, e_4}
(+1). Every g-stable subspace is (S ∩ P) ⊕ (S ∩ U). The normal of gH_{u,w}
is (−u, w) ∼ (u, −w), which is not ±(u, w), so **no hyperplane is
g-stable**. The 3-dimensional flats are the hyperplanes, so M has no
element of dimension 3.

- *Planes.* P is not a flat (a hyperplane containing it has u = 0), nor
  is U (w = 0). A mixed plane span{v, e_3 + te_4} with v ∈ P lies in
  H_{u,w} iff u ⊥ v and w_1 + tw_2 = 0. At most one u is ⊥ v. For t = 0
  the two hyperplanes H_{u,(0,±1)} cut out exactly span{v, e_3}. For
  t = ∞, H_{u,(±1,0)} cut out span{v, e_4}. Other t give at most a
  single hyperplane. So the stable planes that are flats are span{v_u, e_3}
  and span{v_u, e_4}, with v_u ⊥ u: v = a = (−3, 1), (1, 2) and (−2, 3).
- *Lines.* span{e_3} is the intersection of the six H_{u,(0,±1)};
  span{e_4} that of the six H_{u,(±1,0)}; span{v_u} that of the four
  H_{u,w}. No other line in U or in P is a flat.
- *Membership in Λ(V)* ([GT] Lemma 0.1(a): dim(Y ∩ |V|) = dim Y). e_3 ∈ L
  and −e_4 ∈ |V|, so both U-lines qualify. On P and on span{v, e_3} we
  have x_4 = 0, so |V| forces s = 0. That leaves only span{a} (s(a) = 0;
  s = 7 on the other two v) and span{a, e_3} = L. On span{v, e_4},
  |V| is {x_4 ≤ 0, |s(v)α| ≤ −x_4}, which is 2-dimensional for all three v.

So M = {0, a, b = ⟨e_3⟩, c = ⟨e_4⟩, L = ⟨a, e_3⟩, B = ⟨a, e_4⟩,
C = ⟨(1, 2, 0, 0), e_4⟩, D = ⟨(−2, 3, 0, 0), e_4⟩, R^4}, ordered by
a < L, B; b < L; c < B, C, D. This is the 9-element poset of [CRV] §0.2,
and [Aud] finds exactly these nine flats. It is a lattice: every pair has a
unique minimal upper bound and a unique maximal lower bound ([Aud] checks
all 81 pairs). For example a ∨ c = B and C ∧ D = c.

*Complements.* One complement per element is enough, and the list below
is a subset of the complete one in the output of [Aud]:

| x | a complement | all complements ([Aud]) |
|---|---|---|
| 0 | R^4 | R^4 |
| a | C | C, D |
| b | B | c, B, C, D |
| c | L | b, L |
| L | c | c, C, D |
| B | b | b |
| C | a | a, b, L |
| D | a | a, b, L |
| R^4 | 0 | 0 |

[CRV] lists a ↔ C, b ↔ B, c ↔ L, D ↔ a. These are all correct.

*Möbius function.* μ(a) = μ(b) = μ(c) = −1, μ(L) = μ(B) = 1,
μ(C) = μ(D) = 0, so μ(0, R^4) = −(1 − 3 + 2 + 0) = 0.

*Not modular.* c ≤ D and y = L give c ∨ (L ∧ D) = c, but
(c ∨ L) ∧ D = R^4 ∧ D = D. Deleting D gives the lattice of [PAP] §3.2:
our b, a, c, L, B, C correspond to its c, b, a, x, y, z. So D doubles the
coatom z (μ = 0). This confirms the description in [CRV].

### 1.3 χ_V(g) = 0, four ways (d)

det g = 1 and d = 4, so χ_V(g) = μ(M) = 0 **by definition**.

**Formula Z.** U lies in no hyperplane (w ≠ 0 always). The g-stable flats
inside L are 0, a, b, L. Of these, b and L meet U, and a + U lies in no
hyperplane (it would need u ⊥ a and w = 0). So Z\*(V, g) = {0, a}, with
μ_{L(A)^g}(0, ·) = 1, −1. All traces H ∩ U are the two lines x_3 = 0 and
x_4 = 0, and so are the traces of the four hyperplanes through a. The cone
|V| ∩ U is the half-plane x_4 ≤ 0. Its Λ is 0 < {x_3 = 0}, {x_4 = 0} < U,
so m = (−1)^2 · 1 = 1 in both terms. χ = 1 − 1 = 0. [Aud] reproduces the
terms (dim X, μ, m) = (0, 1, 1), (1, −1, 1).

**Theorem CF of [FP]** (fixed chambers of localizations, no Formula Z). On
𝓛^g = {0, a, b, L}, μ_{𝓛^g}(0, ·) = 1, −1, −1, 1. By Lemma F of [FP], the
g-fixed chambers of A_Y inside |V| correspond to the chambers of the traces
on U inside x_4 ≤ 0:
- Y = 0 and Y = a have both lines, so 2 chambers each;
- Y = b and Y = L have only x_4 = 0, so 1 chamber each.

χ = 2 − 2 − 1 + 1 = 0. [Aud] counts the fixed chambers of A_Y directly
from sign vectors, and also gets 0.

**From the face poset.** These routes use neither Formula Z nor the
Baclawski–Björner fixed-point theorem.
- *Homology.* [Aud] builds the order complex of the proper part of the
  whole Λ(V), which has 127 flats. It computes H̃_2 over Q as the kernel of
  the boundary map on maximal chains (dimension 72 = m(V), as Theorem 1 of
  [GT] predicts). The trace of g on it is 0, so χ = (−1)^4 det g · tr = 0.
- *Fixed faces and signs.* For each Y ∈ M, [Aud] sums
  (−1)^{dim F} det(g|_{span F}) over the g-fixed faces F of V inside Y. This
  matches [FP] (2.1) on all nine Y. With #V^g = 2, identity (2.2) reads
  2 = 0 + 1 + 0 + 1 (the X = 0, a, b, L terms), as it must.

*Positive controls for the χ code* (§7): the values of [VC] are reproduced
before the 0 above is trusted:
- the Lie_4 character 6, 0, −2, 0, 0 on all chambers of A_3;
- Lie_3 = 2, 0, −1 on A_2;
- the [VC] §5 cancellation on A_2, g = −s_12, χ = 0 with terms
  (0, 1, 1), (1, −1, 1) and two fixed chambers;
- the B_2 reflection, χ = −1;
- the B_3 Coxeter element, 0 on every stable cone;
- the [PCV] §4 pair counts of A_2, A_3, B_2, B_3 (30/24, 300/266, 45/41,
  1,106/998 pairs/nonzero).

The homology trace equals (−1)^d μ(Λ^g) on all chambers of A_3 and B_3,
for every class.

## 2. Theorems Q and P, and Cor. V

**Theorem Q.** Lemma F gives W = cl(L + U) ∈ M, and W ⊆ H ≠ R^d. W ⊇ U,
so Lemma K applies: a complement X lies in L ⊆ W and meets W in 0, so
X = 0, and then X ∨ W = W ≠ R^d. For cl(U) (⊆ H, so ≠ R^d), a complement
X ⊆ L has X + cl(U) ⊆ H. The proof is correct.

A boundary case that the note does not discuss is harmless. U = 0 would
make cl(U) = 0, which is complemented by R^d. But U = 0 forces V to be all
chambers: the average of an interior point of |V| is g-fixed, hence 0,
so 0 ∈ int |V|. Then L + U = R^d, and Q does not apply.

**Theorem P.** The case "U in a hyperplane" is Q with L = 0. In the other
case, a fixed u ∈ int|V| perturbed inside U off the proper subspaces H ∩ U
lies in a g-fixed chamber of V, so #V^g ≥ 1. With [VC] S1 (χ = #V^g), CR_V
follows for pointed cones. The proof is correct.

**Cor. V zeros in every rank** are exactly the hypothesis of Q, so they
are Crapo zeros with explicit witnesses cl(L + U) and cl(U). This is correct.

COMPUTED ([Aud]):
- Q on every pair with L + U in a hyperplane;
- P on every pointed pair (χ = #V^g counted from the chamber permutation);

both in all sweeps. The counts are in §7.

## 3. Lemmas F, K, R3 and Proposition Ln

**Lemma F.**
- (a) The relative interior R of Y ∩ |V| is nonempty (dim = dim Y),
  convex and g-stable. So the orbit average y of a point of R is in R and
  fixed. 0 ∈ R would make the cone a subspace, hence Y ⊆ L.
- (b) The face of A through y has constant signs, so it lies in |V|. Its
  span is cl(y) ⊆ Y ∩ cl(U), and cl(y) is g-stable.
- The facts about cl(U), cl(L + U) and flats inside L are as stated.

The proof is correct.

**Lemma K.** If Y ⊄ L, then 0 ≠ cl(y) ⊆ Y ∩ W, so the meet is not 0̂. If
Y ⊆ L, the meet is Y ∩ W. The join is the flat join. The proof is correct.
[Aud] checks the equivalence for *every* W ∈ M with W ⊇ cl(U), not only
W = cl(U). The right side is computed from all g-stable flats of A.

**Proposition Ln.** With dim L = 1, Z\* ⊆ {0, L} and μ(0, L) = −1. Cases
(i)–(iii) follow by reading off Z\*. In (ii), L ⊆ U would put L + U = U
in a hyperplane, so L ∩ U = 0.

For (iv), C = |V| ∩ U has lineality L ∩ U = 0, and it is full-dimensional
in U (it contains the fixed interior point of Lemma F). It is cut out by
traces of S_max hyperplanes, which contain L ⊇ X. So it is a pointed
top-cone of the essential arrangement B_X, and m_X = c_X ([GT], pointed
case).

The trace criterion holds in both directions:
- A trace h ∉ B_L meeting int_U C meets it in a relatively open subset
  of h. That subset is not covered by the finitely many B_L hyperplanes
  (each ≠ h), so h cuts an open B_L-chamber inside C.
- Conversely, a hyperplane of B_0 that cuts an open B_L-chamber in C
  meets int_U C. If it is in B_L, it cannot cut a B_L-chamber.

So c_0 = c_L iff every trace meeting int C is in B_L. The proof is correct.

Remark: when dim U = 1, every trace is {0}. Then c_0 = c_L = 1, and every
case-(iv) pair with dim U = 1 is a zero. This is consistent with Ln, and
it is the "dim U = 1" branch of Theorem 3.

[Aud] checks (i)–(iv) on every pair with dim L = 1. It computes c_0 and
c_L as chamber counts of the restricted arrangements, and decides the
trace criterion independently by exact feasibility of "t·y = 0, all S_max
constraints strict" on U. Both sides of "c_0 = c_L ⇔ criterion" agree on
every case-(iv) pair.

**Lemma R3.** Cases (a) and (b) are as stated. For case (c) I recomputed
every row:
- μ(ℓ) = μ(E′) = −1 and μ(E) = a − 1;
- μ(P) = −1 + #(lines of L(A)^g in P), where those lines are E′ (if
  e′ = 1) and P ∩ E (if it is a flat).

This gives μ(1̂) = 1 − p, 0, a − λ, a + p − λ − 1 for (e, e′) = (1, 1),
(1, 0), (0, 1), (0, 0). The witnesses are as stated:
- (1, 1), p = 1: ℓ_1 has no complement.
- (1, 0): E has no complement. Every P meets it in a flat line, and lines
  of 𝓛 lie in it.
- (0, 1), λ = a: E′ has no complement, since ℓ ∨ E′ ∈ 𝓟 for every ℓ.
- (0, 0): with λ ≤ p ≤ 1 and λ ≤ a, a + p − λ = 1 leaves exactly the three
  chains.

The proof is correct. [Aud] evaluates (e, e′, a, p, λ) from the arrangement
for every ±reflection g in every rank-3 family. It checks the predicted μ
against μ(L(A)^g), and "μ = 0 ⇔ uncomplemented" for every group element.
The rows exercised are given in §7.

## 4. Theorem 3

- *d ≤ 2.* Length ≤ 2; μ = k − 1; uncomplemented iff k = 1. (For d = 1,
  M = {0, R} and μ = −1.)
- *d = 3, dim L = 0, 3.* By P and R3.
- *d = 3, dim L = 2.* A subspace meets a closed half-space in itself or in
  a half-space of itself, so Λ(V) = L(A) ([Aud] checks this on every such
  pair). Then R3 applies.
- *d = 3, dim L = 1.* By Ln, the only zeros outside Q are those of (iv)
  with c_0 = c_L. Note U ≠ 0 there, because U lies in no hyperplane, and
  dim U ≠ 3 because L ∩ U = 0.
  - *dim U = 1.* A complement Y ≠ R^3, Y ⊄ L, contains cl(y) ⊇ U, and
    cl(U) = R^3.
  - *dim U = 2.* g is a reflection with (−1)-line L, so Y ∩ L = 0 forces
    Y ⊆ U, and Y is a flat line with ray ρ = Y ∩ |V|.
    - An interior ray gives Y = H ∩ U with H meeting int C, hence a trace
      of some H′ ⊇ L, and Y + L ⊆ H′.
    - A boundary ray lies on a facet hyperplane, which contains L.

  An open ray from 0 is either inside int_U C or inside ∂_U C, so the
  dichotomy is exhaustive. The proof is correct.

COMPUTED ([Aud], §7). Every rank ≤ 3 pair of the sweep satisfies CR_V:
37,707 pairs, 2,018 zeros, 0 counterexamples. These include 3,226 pairs with
dim L = 1 (256 under case (iv)) and 329 R3 instances. The Λ(V) = L(A) check
for dim L = 2 (620 pairs) and the Theorem 3 complement step (196 pairs) ran
on every pair, with no failure. This sweep corroborates the proof; it is not needed for it.

## 5. Knop's modular lemma

Knop's Lemma A.2, as quoted in [PAP] §3.3, needs a modular lattice. The
counterexample lattice is not modular (§1.2), so the lemma cannot reach it.
The supporting claim "complemented non-modular Λ(V)^g with μ ≠ 0 are
common" is stated in [CRV] with counts per arrangement and convention
("pairs = class representative g, every g-stable top-cone").

I reproduce the counts under that convention:
- A_3 under ±S_4: 300 pairs, 266 nonzero, 266 complemented, 186
  complemented and non-modular;
- A_2: 24 complemented, 0 non-modular;
- B_2: 41 complemented, 0 non-modular;
- B_3: 998 complemented, 862 non-modular.

The rank-2 rows have no non-modular complemented lattices, as they cannot
(length ≤ 2 lattices are modular). That is consistent with [CRV]'s table,
which lists 0 there.

The scope is stated correctly. The claim is about these enumerated pairs.
It is not a claim that non-modularity is generic in a precise sense, and
[CRV] does not claim that.

In all of my sweeps every pair with μ = 0 and complemented M was
non-modular, as Knop's lemma requires.

## 6. Remarks (no statement changes)

- **R1 (§0.4 of [CRV]).** The second-implementation cross-check is
  described there as a one-off loop, not as a script, so a reader has to
  rebuild it. [Aud] now gives a scripted independent check of all 36
  pairs: the [R4] sweep and the CX part.
- **R2 (Lemma F and Theorem Q).** Neither states the case U = 0. It cannot
  occur for a proper cone (§2). One sentence would close the reading
  question "what if cl(U) = 0̂?".
- **R3 (Ln(iv)).** When dim U = 1, every case-(iv) pair vanishes
  (c_0 = c_L = 1). This is implicit in Theorem 3's "dim U = 1" branch, and
  worth a line in Ln.
- **R4 ([VC] S2, outside the scope of this audit).** The averaging argument
  of Lemma F shows that a g with Fix g = 0 stabilizes no proper top-cone. So
  the first clause of [VC] S2 ("χ_V(g) = 0 for every V other than all
  chambers") is vacuous, though true.
- No claim of [CRV] was found to be wrong.

## 7. Data (COMPUTED, [Aud])

Rank ≤ 3: every group element (not only class representatives) and every
g-stable top-cone, on these families:
- A_2, B_2 and the 9-line D_6 arrangement in R^2;
- A_3, B_3, B_3 ∖ {z = 0}, A_3 minus a plane, and x, y, z, x + y + z;
- seven orbit arrangements under C_6 × ⟨z ↦ −z⟩, D_6 × ⟨z ↦ −z⟩,
  D_4 × ⟨z ↦ −z⟩, C_3 × ±1, D_3, C_4 × ⟨z ↦ −z⟩ and a D_6-hexagon type;
- 14 random orbit arrangements (seed 7) with ≤ 12 planes.

| family | d | n | pairs | zeros | complemented (non-modular) | P | Q | K | Ln (iv) | R3 |
|---|---|---|---|---|---|---|---|---|---|---|
| A_2, ±S_3 | 2 | 3 | 48 | 18 | 30 (0) | 24 | 6 | 65 | 12 (6) | 0 |
| B_2 | 2 | 4 | 56 | 8 | 48 (0) | 32 | 8 | 83 | 16 (0) | 0 |
| 9-line D_6 hexagon in R^2 | 2 | 9 | 228 | 36 | 192 (0) | 192 | 24 | 269 | 24 (6) | 0 |
| A_3, ±S_4 | 3 | 6 | 576 | 206 | 370 (214) | 336 | 142 | 891 | 144 (12) | 48 |
| B_3 | 3 | 9 | 1,680 | 510 | 1,170 (942) | 1,200 | 494 | 2,749 | 336 (0) | 48 |
| B_3 ∖ {z = 0} | 3 | 8 | 944 | 208 | 736 (632) | 672 | 158 | 1,279 | 208 (24) | 16 |
| A_3 minus a plane | 3 | 5 | 192 | 20 | 172 (82) | 104 | 12 | 227 | 64 (4) | 8 |
| x, y, z, x+y+z, S_3 × ±1 | 3 | 4 | 156 | 14 | 142 (94) | 72 | 0 | 198 | 48 (12) | 12 |
| C_6 × ⟨z ↦ −z⟩ | 3 | 6 | 396 | 6 | 390 (326) | 300 | 0 | 422 | 72 (6) | 12 |
| D_6 × ⟨z ↦ −z⟩ | 3 | 10 | 2,904 | 444 | 2,460 (2,324) | 2,472 | 444 | 3,865 | 336 (12) | 24 |
| D_4 × ⟨z ↦ −z⟩ | 3 | 6 | 416 | 62 | 354 (214) | 256 | 46 | 559 | 112 (12) | 16 |
| C_3 × ±1 | 3 | 6 | 258 | 0 | 258 (214) | 180 | 0 | 276 | 60 (0) | 6 |
| D_3 | 3 | 7 | 594 | 94 | 500 (452) | 450 | 94 | 721 | 108 (0) | 6 |
| C_4 × ⟨z ↦ −z⟩ | 3 | 4 | 96 | 4 | 92 (64) | 48 | 0 | 109 | 32 (4) | 8 |
| D_6-hexagon type | 3 | 13 | 7,284 | 174 | 7,110 (6,972) | 6,852 | 174 | 7,908 | 384 (0) | 12 |
| random 1 (C_3, 3 planes) | 3 | 3 | 33 | 0 | 33 (0) | 12 | 0 | 33 | 12 (0) | 3 |
| *subtotal, first run* | | | *15,861* | *1,804* | *14,057 (12,530)* | *13,202* | *1,602* | *19,654* | *1,968 (98)* | *219* |
| random 2 (C_6, 12 planes) | 3 | 12 | 6,348 | 12 | 6,336 (6,177) | 6,042 | 0 | 6,348 | 276 (12) | 6 |
| random 3 (rot6z, 6 planes) | 3 | 6 | 354 | 0 | 354 (326) | 276 | 0 | 378 | 60 (0) | 6 |
| random 4 (C_6, 6 planes) | 3 | 6 | 372 | 6 | 366 (325) | 288 | 0 | 372 | 66 (6) | 6 |
| random 5 (rot6z, 3 planes) | 3 | 3 | 36 | 0 | 36 (0) | 12 | 0 | 45 | 12 (0) | 6 |
| random 6 (D_4 × z, 6 planes) | 3 | 6 | 464 | 76 | 388 (296) | 288 | 50 | 631 | 128 (16) | 16 |
| random 7 (D_4 × z, 4 planes) | 3 | 4 | 176 | 16 | 160 (84) | 80 | 0 | 207 | 64 (20) | 16 |
| random 8 (C_3, 3 planes) | 3 | 3 | 33 | 0 | 33 (0) | 12 | 0 | 33 | 12 (0) | 3 |
| random 9 (D_6 × z, 12 planes) | 3 | 12 | 13,104 | 84 | 13,020 (11,600) | 12,624 | 0 | 13,187 | 432 (84) | 24 |
| random 10 (C_3, 6 planes) | 3 | 6 | 351 | 0 | 351 (325) | 276 | 0 | 351 | 60 (0) | 3 |
| random 11 (C_4z, 4 planes) | 3 | 4 | 80 | 4 | 76 (63) | 40 | 0 | 82 | 28 (4) | 4 |
| random 12 (C_2^3, 6 planes) | 3 | 6 | 456 | 16 | 440 (338) | 336 | 2 | 499 | 96 (16) | 8 |
| random 13 (rot6z, 3 planes) | 3 | 3 | 36 | 0 | 36 (0) | 12 | 0 | 45 | 12 (0) | 6 |
| random 14 (rot6z, 3 planes) | 3 | 3 | 36 | 0 | 36 (0) | 12 | 0 | 45 | 12 (0) | 6 |
| **total** | | | **37,707** | **2,018** | **35,689 (32,064)** | **33,500** | **1,654** | **41,877** | **3,226 (256)** | **329** |

CR_V counterexamples: 0 in every row. In every row, complemented = pairs −
zeros, as Theorem 3 predicts.

**Random families 2–14 (formerly UNRUN).** The first run was stopped after
2 h 55 min, during random family 2. Its slowness came from
`restricted_cone_data`, which rebuilt the restriction arrangement
{H ∩ U : H ⊇ X} from scratch for every pair. For g = 1 and X = 0 that
arrangement is A itself, at about 2.7 s per pair over 6,225 top-cones. The
arrangement depends only on the trace normals, not on the cone, so it is now
built once per normal list. No check changed. With the memo:
- each of families 2–14 ran as its own process (`--r3-random K`), under a
  30-minute bound, in 0–156 s;
- the 11 families other than 2 and 9 gave identical totals with and without
  the memo;
- a single uninterrupted `--r3` run of all 30 families took 336 s. Its first
  16 rows are identical to the stopped run, and its totals equal the table
  above. The R3 table rows exercised are (e, e′) = (1, 1): 38, (1, 0): 22,
  (0, 1): 37, (0, 0): 42.

Seeds and groups are in `compute/output/audit_conjecture_cr_v_r3.txt` and in
`random_rank3`. The verdict on Theorem 3 rests on the proof in §4, which this
sweep only corroborates.

Rank 4 (g ≠ 1; for g = 1, χ = m(V) ≥ 1 and M = Λ(V) is complemented by
Crapo):

| arrangement | top-cones (g = 1 pairs) | pairs g ≠ 1 | zeros | complemented | non-modular among them | CR_V counterexamples |
|---|---|---|---|---|---|---|
| C_6 × C_4, 12 hyperplanes | 37,867 | 533 | 60 | 509 | 271 | 36 |
| A_4, ±S_5 class representatives | 4,231 | 403 | 342 | 61 | 41 | 0 |

The totals 37,867 + 533 = 38,400 and 4,231 + 403 = 4,634 are the pair counts
of [CRV] §5. So are the zeros (60, 342) and the complemented counts
(37,867 + 509 = 38,376 and 4,231 + 61 = 4,292).

The 36 counterexamples are:
- 12 pairs with g = diag(−1, −1, 1, 1), |M| = 9, dim L = 2, Z-terms
  (1, 1), (−1, 1);
- 12 pairs with g = diag(1, 1, −1, −1), |M| = 10, dim L = 1, Z-terms
  (1, 2), (−1, 2);
- 12 pairs with g = diag(1, 1, −1, −1), |M| = 11, dim L = 2, Z-terms
  (1, 2), (−1, 2).

All 36 are non-modular, and CF gives 0 on each.

In rank 4, every check of P, Q, K, Ln and Formula Z passes. The checks
cover 384 + 236 pointed pairs, 268 Q pairs (A_4), 705 + 910 Lemma K
instances and 102 + 94 pairs with dim L = 1, of which 36 + 32 fall under
case (iv). Theorem CF was evaluated on every seventh
rank-4 pair.

## Reproduce

From `compute/` (plain Python 3, no packages, single process):

    python3 audit_conjecture_cr_v.py --quick   # ~3 min: controls [CTL] and the counterexample [CX]
    python3 audit_conjecture_cr_v.py --r3      # ~6 min: rank <= 3 sweep, every check of Sections 2-4
    python3 audit_conjecture_cr_v.py --r3-random K   # random family K of random_rank3(7, 14) alone, with progress lines
    python3 audit_conjecture_cr_v.py --r4      # ~5 min: C6 x C4 and A4, g != 1
    python3 -m unittest test_audit_conjecture_cr_v   # ~5 s

Each run ends with "ALL CHECKS PASSED" and exit 0. The archived outputs are
`compute/output/audit_conjecture_cr_v_quick.txt`,
`compute/output/audit_conjecture_cr_v_r3.txt` and
`compute/output/audit_conjecture_cr_v_r4.txt`.

The tests include negative controls:
- the 8-element lattice is complemented with μ = 0 and is not modular;
- M_3 is modular and N_5 is not;
- a chain has an uncomplemented element;
- a non-lattice is refused;
- Formula Z with every m_X set to 1 is wrong;
- the counterexample's g on all chambers gives χ = −2 ≠ 0.

The method differs from [CRV]'s script:
- Faces come from exact Fourier–Motzkin feasibility, hyperplane by
  hyperplane, not from compositions of cocircuits.
- Top-cones come from splitting chamber sets.
- Lattice operations come from brute force on the poset.
- χ is checked four ways: the definition, Formula Z, Theorem CF, and the
  homology trace.
