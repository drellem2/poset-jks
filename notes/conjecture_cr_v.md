# Conjecture CR_V: the Crapo converse on cone lattices

Conjecture CR_V of `notes/per_cone_vanishing.md` ("[PCV]", §4) states:

  χ_V(g) = 0  iff  Λ(V)^g has an element without a complement.

The "if" direction is Crapo's corollary (EC1 Ex. 3.92; [PCV] CO). This note
is about the converse: if every element of Λ(V)^g has a complement, then
χ_V(g) ≠ 0. That converse is false for finite lattices in general
(`notes/prior_art_per_cone_vanishing.md` ("[PAP]") §3.2: the smallest
counterexample has 8 elements). So the question is whether the geometry of
cones rules such lattices out.

**Answer: it does in rank ≤ 3, and it does not in rank 4.** §0 gives a
counterexample in R^4. Every element of Λ(V)^g is complemented, yet
χ_V(g) = 0. In rank ≤ 3, and for pointed cones in every rank, CR_V is
proven (§§1–4).

Notation is that of [PCV] and `notes/vanishing_criterion.md` ("[VC]"):
- A is a central essential arrangement in R^d.
- V is a top-cone with |V| its closure and L = lin V.
- g is a finite-order linear map with gA = A and gV = V, and U = Fix g.
- M = Λ(V)^g, the g-stable spans of faces of A in |V|, ordered by inclusion.
- χ_V(g) = (−1)^d det(g) μ(M).
- cl(S) is the smallest flat of A containing a set S.

The lattice structure is the one fixed in `notes/audit_per_cone_vanishing.md`
("[AudPCV]") F6, not the CO paragraph of the first version of [PCV].
Λ(V) is closed under the join of flats. The join in M is that join, and
the meet is the largest element of M below the intersection.

Tags: **PROVEN** (proof given here, inputs named; *not yet independently
audited*),
**COMPUTED** (by `compute/conjecture_cr_v.py`, "[CR]"), **CITED**,
**OPEN**, **REFUTED**.

## Verdict

| # | Claim | Status | Inputs |
|---|---|---|---|
| CR_V | χ_V(g) = 0 iff Λ(V)^g has an uncomplemented element | **REFUTED** (§0). A 12-hyperplane arrangement in R^4, g = diag(−1, −1, 1, 1) and a cone V with dim L = 2 give a 9-element Λ(V)^g with every element complemented and χ_V(g) = 0. Checked by hand (§0.2), by [CR] and by the independent code of `compute/audit2_vanishing_criterion.py` and `compute/per_cone_vanishing.py`. The same arrangement has 36 counterexample pairs (§5) | Formula Z of [VC] for the value 0 |
| 3 | **Theorem 3.** CR_V holds for every pair (V, g) with d ≤ 3 | **PROVEN** (§4); COMPUTED on every rank-3 pair of §5. So the counterexample of §0 has the smallest possible rank | P, Ln, R3 |
| P | Pointed V, any d: χ_V(g) = 0 iff U lies in a hyperplane, and then cl(U) has no complement. So CR_V holds for every pointed cone | **PROVEN** (§1); COMPUTED | Q, [VC] S1 |
| Q | Any d: if L + U lies in a hyperplane (the "Cor. V" zeros of [VC]), then cl(L + U) and cl(U) have no complement in M | **PROVEN** (§1); COMPUTED | K |
| F | Fixed-point lemma: every Y ∈ M with Y ⊄ L contains a nonzero y ∈ U ∩ relint(Y ∩ \|V\|), and cl(y) ∈ M, cl(y) ⊆ Y | **PROVEN** (§1) | [GT] Lemma 0.1(a) |
| K | If W ∈ M contains U, then the complements of W in M are exactly the g-stable flats X ⊆ L with X ∩ W = 0 and X + W in no hyperplane | **PROVEN** (§1); COMPUTED for W = cl(U) on every pair | F |
| Ln | dim L = 1, any d. Then χ_V(g) = 0 iff L + U lies in a hyperplane, or U lies in no hyperplane, L ∩ U = 0 and c_0 = c_L. In the second case χ_V(g) = c_0 − c_L ≥ 0, where c_X counts the chambers of {H ∩ U : H ⊇ X} in \|V\| ∩ U | **PROVEN** (§2); χ = c_0 − c_L COMPUTED on every such pair. In d = 3 a zero of the second kind makes L uncomplemented (§4). In d = 4 it does not: 12 counterexample pairs of §5 have dim L = 1 | Formula Z of [VC], [GT] (pointed m = #chambers) |
| R3 | For every central essential A in R^3 and every finite-order symmetry g, the fixed lattice L(A)^g has μ = 0 iff it has an uncomplemented element | **PROVEN** (§3), by a case analysis on the eigenvalues of g | — |
| Mod | Is Λ(V)^g modular whenever it is complemented? (If so, Knop's Lemma A.2 would settle CR_V.) | **No.** Complemented non-modular Λ(V)^g with μ ≠ 0 are common, e.g. 186 of the 266 nonvanishing pairs of A_3 (§5). The counterexample of §0 is complemented and not modular | COMPUTED |

**In one line.** The Crapo converse holds on cone lattices in rank ≤ 3, for
pointed cones, and for every zero in which L + Fix g lies in a hyperplane.
It fails in rank 4. In R^4 a Formula-Z cancellation 1 − 1 = 0 sits on a
complemented, non-modular 9-element lattice. That lattice is the 8-element
complemented lattice with μ = 0 of [PAP] §3.2, with one coatom doubled.
So an exact per-cone criterion for the vanishing of χ_V(g) cannot be
"some element has no complement".

---

## 0. The counterexample

### 0.1 The data

- **Arrangement.** A has 12 hyperplanes in R^4,

    H_{u,w} = {u_1 x_1 + u_2 x_2 + w_1 x_3 + w_2 x_4 = 0},

  with u ∈ {(1, 3), (2, −1), (3, 2)} and w ∈ {(±1, 0), (0, ±1)}. It is the
  orbit of the form (2, −1, 0, −1) under C_6 × C_4. Here C_6 rotates the
  hexagonal lattice in the (x_1, x_2)-plane and C_4 rotates the
  (x_3, x_4)-plane.
- **Symmetry.** g = diag(−1, −1, 1, 1), the rotation by π in the
  (x_1, x_2)-plane. It maps H_{u,w} to H_{−u,w} = H_{u,−w}, so gA = A.
  It has det g = 1, and U = Fix g = span{e_3, e_4}.
- **Cone.** V = {x_4 ≤ x_1 + 3x_2 ≤ −x_4}, the intersection of the
  halfspaces of H_{(1,3),(0,−1)} and H_{(1,3),(0,1)}. It is g-stable. Its
  lineality space is L = {x_1 + 3x_2 = 0, x_4 = 0} = span{a, e_3} with
  a = (−3, 1, 0, 0).
- **U.** No hyperplane contains U, since every H_{u,w} has w ≠ 0. L ∩ U =
  span{e_3}.

### 0.2 The lattice, by hand

The (−1)- and (+1)-eigenspaces of g are P = span{e_1, e_2} and U, and a
g-stable subspace is the sum of its intersections with them. A flat Y is in
Λ(V) iff Y ∩ |V| has dimension dim Y ([GT] Lemma 0.1(a)). Write
s = x_1 + 3x_2.

- *Hyperplanes.* None is g-stable, since g H_{u,w} = H_{u,−w}.
- *Lines in U.* A hyperplane contains e_3 + t e_4 iff w_1 + t w_2 = 0. So
  the flat lines in U are span{e_3} (the intersection of the four
  H_{u,(0,±1)}) and span{e_4}. Both are in Λ(V): e_3 ∈ L and −e_4 ∈ |V|.
- *Lines in P.* span{v} with v ∈ P is a flat iff v ⊥ u for some u. The
  flat is then ∩_w H_{u,w} = {u · x = 0, x_3 = x_4 = 0}. This gives three
  lines, spanned by a = (−3, 1, 0, 0), (1, 2, 0, 0) and (−2, 3, 0, 0). On
  such a line x_4 = 0, so |V| forces s = 0. Only span{a} is in Λ(V).
- *Stable planes.* P and U are not flats. No hyperplane contains them,
  since a hyperplane containing P has u = 0. A plane span{v, e_3 + t e_4}
  with v ∈ P is a flat iff v ⊥ some u and t ∈ {0, ∞}. That leaves
  span{v, e_3} and span{v, e_4} for the three v.
  - span{v, e_3} lies in {x_4 = 0}, so it meets |V| in {s = 0}. Only
    span{a, e_3} = L qualifies.
  - span{v, e_4} meets |V| in {x_4 ≤ 0, |s| ≤ −x_4}, which is
    2-dimensional for every v. All three qualify.

So M = Λ(V)^g has nine elements:
- 0;
- three lines: a = span{a}, b = span{e_3}, c = span{e_4};
- four planes: L = span{a, e_3}, B = span{a, e_4}, C = span{(1, 2, 0, 0), e_4}
  and D = span{(−2, 3, 0, 0), e_4};
- R^4.

The order is a < L, B; b < L; c < B, C, D.

              R^4
      _______/ |  \_______
     /         |   \      \
    L          B    C      D
    | \       / \   |     /
    |  \     /   \  |    /
    b    a         c
     \   |        /
          0

(L lies over b and a; B over a and c; C and D over c.)

- *Möbius function.* μ(a) = μ(b) = μ(c) = −1, μ(L) = μ(B) = 1,
  μ(C) = μ(D) = 0, so μ(0, R^4) = −(1 − 3 + 2) = 0. Hence
  χ_V(g) = (−1)^4 · det g · 0 = 0.
- *Complements.* Every element has one:
  - a ↔ C (a ∩ C = 0, and a + C is 3-dimensional, so the join is R^4);
  - b ↔ B and c ↔ L (both pairs meet in 0 and span R^4);
  - D ↔ a.
- *Not modular.* Take c ≤ D and y = L. Then c ∨ (L ∧ D) = c ∨ 0 = c,
  but (c ∨ L) ∧ D = R^4 ∧ D = D. (c + L is 3-dimensional, and M has no
  3-dimensional element.)
- *The pattern.* Deleting D leaves the 8-element lattice of [PAP] §3.2:
  - b lies under one coatom (L);
  - a lies under two (L, B);
  - c lies under two (B, C).

### 0.3 The value 0 independently of the lattice

Formula Z ([VC], audited) gives χ_V(g) = Σ_{X ∈ Z\*} μ_{L(A)^g}(0, X) m_X(V).
U lies in no hyperplane, so Z\* is the set of g-stable flats X ⊆ L with
X ∩ U = 0. These are X = 0 and X = span{a}, with μ(0, X) = 1 and −1.

- m_0 is the bottom multiplicity of |V| ∩ U = {x_4 ≤ 0} (a half-plane of U)
  for the traces of all hyperplanes. Those traces are the lines x_3 = 0
  and x_4 = 0 of U. The cone lattice is 0 < {x_3 = 0}, {x_4 = 0} < U, so
  m_0 = 1.
- m_a is the same for the traces of the hyperplanes through a, namely
  H_{(1,3),w}. These are again x_3 = 0 and x_4 = 0, so m_a = 1.

So χ_V(g) = 1 · 1 + (−1) · 1 = 0. This is a cancellation in Formula Z. In
the language of Proposition Ln: the hyperplanes not containing a add no
trace on U.

### 0.4 Checks

- [CR] part [CX] rebuilds A, g and V and compares M with the nine flats
  above. It finds μ = 0 and no uncomplemented element, and evaluates
  Formula Z with its own code (terms (1, 1) and (−1, 1)).
- The independent implementation of `compute/audit2_vanishing_criterion.py`
  (faces, Λ(V), `chi_def`, Formula Z via `GData.Z_terms`), with
  `per_cone_vanishing.lattice_info`, gives the same on all 36 failing pairs
  of the arrangement:
  - for the 12 pairs of this kind, |M| = 9, μ = 0, "has an uncomplemented
    element" = False, chi_def = 0, Formula Z = 0 (terms (−1, 1), (1, 1));
  - for the other 24 (|M| = 10 and 11), the same, with Formula Z terms
    (μ, m) = (1, 2), (−1, 2).

  This cross-check was a one-off run, not part of [CR].

### 0.5 Why rank 4

The proofs of §§1–4 break in two places. Neither is a defect of the
argument; both are features of rank 4.
- *dim L = 2 is a genuine lineality case.* In R^3 a cone with dim L = 2
  is a half-space, and then M = L(A)^g. Here V is a wedge with a
  2-dimensional edge. It meets U in a non-pointed cone whose lineality
  L ∩ U is nonzero.
- *Stable subspaces split into two planes.* In R^3, g-stable subspaces
  split along U ⊕ L, and Lemma R3 shows that two stable planes meet in a
  stable line. Here M has no 3-dimensional elements at all (no stable
  hyperplanes). Its four planes can be complementary in pairs (L ∩ C = 0),
  which is impossible for two planes in R^3.

The same arrangement also gives 12 counterexample pairs with dim L = 1
(g = diag(1, 1, −1, −1), |M| = 10) and 12 with dim L = 2 and |M| = 11
(§5). So the line-case statement that holds in R^3 (§4: a zero of
Proposition Ln(iv) makes L uncomplemented) also fails in R^4.

## 1. The fixed-point lemma, Lemma K, Theorems Q and P

**Lemma F (PROVEN).** Let Y ∈ M with Y ⊄ L.
- (a) There is a nonzero y ∈ U lying in the relative interior of Y ∩ |V|.
- (b) For such y, cl(y) ∈ M, and cl(y) ⊆ Y and cl(y) ⊆ cl(U).

Also, cl(U) ∈ M and cl(L + U) ∈ M, and every g-stable flat inside L lies in M.

*Proof.*
- (a) Y ∩ |V| is a closed convex cone. It is g-stable, and it has dimension
  dim Y ([GT] Lemma 0.1(a)). Its relative interior R is convex, nonempty
  and g-stable. For p ∈ R, the average y of the ⟨g⟩-orbit of p lies in R
  and is fixed.
- If 0 ∈ R, then the cone Y ∩ |V| is all of Y, so Y ⊆ |V| ∩ −|V| = L. This
  is excluded, so y ≠ 0.
- (b) The face of A containing y lies in |V|, because |V| is a union of
  closed faces. Its span is cl(y), the intersection of the hyperplanes
  through y. So cl(y) ∈ Λ(V).
- cl(y) is g-stable, since gy = y. It lies in the flat Y, and it lies in
  cl(U) because y ∈ U.
- For cl(U) and cl(L + U): apply (a) with Y = R^d when V ≠ all chambers.
  This gives a fixed point u ∈ int |V|. A flat containing u meets |V| in a
  set of full dimension, and cl(U), cl(L + U) are g-stable.
- When V is all chambers, M = L(A)^g.
- Flats inside L lie in Λ(V) by [GT] Lemma 0.1(b). ∎

*The meet with an element inside L.* For X ∈ M with X ⊆ L and any Y ∈ M,
X ∧ Y = X ∩ Y. Indeed X ∩ Y is a g-stable flat inside L, so it lies in M.

**Lemma K (PROVEN).** Let W ∈ M with W ⊇ U. A Y ∈ M is a complement of W
iff Y ⊆ L, Y ∩ W = 0, and Y + W lies in no hyperplane of A.

*Proof.*
- If Y ⊄ L, Lemma F gives 0 ≠ cl(y) ⊆ Y. Also cl(y) ⊆ W, since y ∈ U ⊆ W.
  So W ∧ Y ≠ 0̂.
- If Y ⊆ L, the meet is Y ∩ W.
- The join of W and Y is R^d iff no hyperplane contains W + Y. ∎

For W = cl(U), this says that the complements of cl(U) are the
X ∈ Z\*(V, g) of [VC] with X ∩ cl(U) = 0. When U is a flat, they are exactly
Z\*(V, g). In that case Crapo's theorem for the element U of M is a form of
Formula Z on any cone, extending [PCV] Theorem Cr(a) from all chambers.

**Theorem Q (PROVEN).** If L + U lies in a hyperplane of A, then
W = cl(L + U) is an element of M other than R^d with no complement in M.
So the "Cor. V" zeros of [VC] are all Crapo zeros.

*Proof.* By Lemma K, a complement X satisfies X ⊆ L ⊆ W and X ∩ W = 0, so
X = 0. Then X ∨ W = W ≠ R^d. For cl(U), which is ≠ R^d since U ⊆ L + U: by
Lemma K a complement X ⊆ L would need X + cl(U) in no hyperplane. But a
hyperplane containing L + U contains X and cl(U). ∎

**Theorem P (PROVEN).** Let V be pointed (L = 0).
- If U lies in a hyperplane, then cl(U) has no complement, and μ(M) = 0.
- If U lies in no hyperplane, then χ_V(g) = #V^g ≥ 1 ([VC] S1, audited).

So CR_V holds for every pointed cone, with the explicit obstruction cl(U).

*Proof.* The first case is Theorem Q with L = 0. The second is [VC] S1.
Directly: take a fixed u ∈ int |V| (Lemma F). Points of U near u that avoid
every H ∩ U (each a proper subspace of U) lie in a g-fixed chamber inside V. ∎

COMPUTED ([CR], parts [REP] and [CRV]):
- Theorem P on all 143,164 pointed pairs;
- Theorem Q on all 2,230 pairs with L + U in a hyperplane;
- Lemma K for W = cl(U) on every pair with cl(U) ≠ R^d. The complements
  are found in the lattice; the right side is computed from all flats.

Negative control (test): an element that does not contain U can have a
complement outside L. This happens in A_3.

## 2. Lineality of dimension one

**Proposition Ln (PROVEN; inputs Formula Z of [VC], audited, and [GT]
"pointed V: #V = m(V)").** Let dim L = 1. For a flat X ⊆ L, let c_X be
the number of chambers of the arrangement B_X = {H ∩ U : H ∈ A, H ⊇ X} of
U that lie in C = |V| ∩ U. Then:
- (i) If L + U lies in a hyperplane, then χ_V(g) = 0. This is the
  Theorem Q case.
- (ii) If U lies in a hyperplane and L + U does not, then L ∩ U = 0 and
  χ_V(g) = −m_L(V) ≠ 0.
- (iii) If U lies in no hyperplane and L ⊆ U, then χ_V(g) = m_0(V) ≥ 1.
- (iv) If U lies in no hyperplane and L ∩ U = 0, then χ_V(g) = c_0 − c_L ≥ 0.
  Moreover c_0 = c_L iff every trace H ∩ U (H ∈ A) that meets the interior
  of C in U equals a trace H′ ∩ U with H′ ∈ A, H′ ⊇ L.

*Proof.*
- Formula Z: χ_V(g) = Σ_{X ∈ Z\*} μ_{L(A)^g}(0, X) m_X(V). Here Z\* = Z\*(V, g)
  is the set of g-stable flats X ⊆ L with X ∩ U = 0 and X + U in no
  hyperplane.
- Here X ∈ {0, L}, with μ(0, 0) = 1 and μ(0, L) = −1. L is g-stable, since
  gV = V.
- 0 ∈ Z\* iff U lies in no hyperplane. L ∈ Z\* iff L ∩ U = 0 and L + U lies
  in no hyperplane.
- This gives (i)–(iii). In (ii), L ⊆ U would put L + U = U in a
  hyperplane. Also m_X ≥ 1 ([VC] Formula Z).
- (iv) L is a flat, the intersection of the facet hyperplanes of V.
  C is a cone in U with lineality L ∩ U = 0, so it is pointed. Its
  facets are traces of facet hyperplanes of V, and these contain L ⊇ X. So
  C is a top-cone of B_X, B_X is essential on U, and m_X(V) is the bottom
  multiplicity of C for B_X. For a pointed cone that is the number of
  chambers ([GT]), namely c_X.
- C is a union of closed B_L-chambers. B_L ⊆ B_0, so each chamber of
  B_L in C is cut into ≥ 1 chambers of B_0.
  Hence c_0 ≥ c_L. Equality holds iff no hyperplane h of B_0 ∖ B_L meets the
  interior of a B_L-chamber in C.
- A hyperplane h of U meeting int C in an open subset of h, with h ∉ B_L,
  meets some open B_L-chamber. Its intersection with the finitely many
  hyperplanes of B_L is nowhere dense in h. ∎

So in the line case, CR_V says this: in case (iv), if every trace meeting
int C is a trace of a hyperplane through L, then some element of M has no
complement. This is proven for d = 3 (§4), where the element is L. It is
false for d = 4 (§0.5).

COMPUTED: in case (iv), c_X is counted independently as the number of
g-fixed chambers of the localization A_X in V. This count equals
(−1)^d det(g) μ(M) on every pair of case (iv) (434 pairs, §5).

Negative control (test): c_0 alone differs from χ on some pairs of generic
4 in R^3.

## 3. Fixed lattices in rank 3

**Lemma R3 (PROVEN).** Let A be central and essential in R^3, and let g be
a finite-order linear map with gA = A. Then μ(L(A)^g) = 0 iff L(A)^g has
an element without a complement.

*Proof.* g is diagonalizable over C, with real spectrum ±1 and possibly
one conjugate pair. A g-stable subspace is a sum of its intersections with
the real isotypic components. Three cases:

*(a) g = ±1.* L(A)^g = L(A) is geometric, so μ ≠ 0 (Rota). The statement
holds, since geometric lattices are complemented.

*(b) g has non-real eigenvalues.* R^3 = E′ ⊕ E with E′ the real eigenline
and E an irreducible plane. The g-stable subspaces are 0, E′, E, R^3. So
L(A)^g is one of:
- {0, 1} (μ = −1);
- a chain 0 < x < 1 (μ = 0, x uncomplemented);
- {0, E′, E, 1} (boolean, μ = 1, complemented).

*(c) g = ±(reflection).* R^3 = E ⊕ E′ with dim E = 2, dim E′ = 1. The
g-stable subspaces are:
- 0 and R^3;
- the lines inside E, and E′;
- E, and the planes containing E′.

Write:
- 𝓛 for the lines of A inside E, a = |𝓛|;
- 𝓟 for the planes of A containing E′, p = |𝓟|;
- e = [E is a flat], e′ = [E′ is a flat].

A plane P ∈ 𝓟 contains at most one element of 𝓛, namely P ∩ E. Two planes
of 𝓟 meet in E′, so e′ = 0 forces p ≤ 1. If e = 1, every P ∩ E (P ∈ 𝓟) is
a flat, so it lies in 𝓛. Let λ be the number of P ∈ 𝓟 with P ∩ E ∈ 𝓛. The
four subcases:

| e, e′ | elements besides 0̂, 1̂ | μ(0̂, 1̂) | when μ = 0, an uncomplemented element |
|---|---|---|---|
| 1, 1 | 𝓛, E′, 𝓟, E | 1 − p | p = 1: the line ℓ_1 = P_1 ∩ E. Its candidate complements are lines in E (join ⊆ E), E′ (join P_1), P_1 and E (both contain ℓ_1) |
| 1, 0 | 𝓛, 𝓟 (p ≤ 1), E | 0 always | E: each P meets it in the line P ∩ E ∈ M, and lines of 𝓛 lie in E |
| 0, 1 | 𝓛, E′, 𝓟 | a − λ | λ = a: every ℓ ∈ 𝓛 has ℓ + E′ ∈ 𝓟, so E′ has no complement (E is not a flat) |
| 0, 0 | 𝓛, 𝓟 (p ≤ 1) | a + p − λ − 1 | a + p − λ = 1: L(A)^g is a chain 0 < ℓ < 1, 0 < P < 1 or 0 < ℓ < P < 1 |

The μ values come from μ(ℓ) = μ(E′) = −1, μ(E) = a − 1, and μ(P) = −1 +
(the number of lines of M in P). Two lines of 𝓛 join to E (if e = 1) or
to 1̂ (if e = 0). The meet of P ∈ 𝓟 and E is P ∩ E if that line is a flat,
and 0̂ otherwise. In each row, "μ = 0 ⇒ some element is uncomplemented"
is checked in the last column. ∎

*Remark.* In rank 3 two distinct stable planes of L(A)^g always meet in a
stable line. That is what rules out complemented lattices with μ = 0 here.
The 9-element lattice of §0 has two planes that meet in 0 (L ∩ C = 0),
and that needs rank 4.

## 4. Theorem 3 (rank ≤ 3)

**Theorem 3 (PROVEN).** CR_V holds for every central essential arrangement
of rank d ≤ 3, every finite-order symmetry g and every g-stable top-cone V.

*Proof.*
- *d ≤ 2.* M has length ≤ 2. A lattice 0̂ < a_1, …, a_k < 1̂ has μ = k − 1,
  and an uncomplemented element iff k = 1 ([PAP] §3.3).
- *d = 3, by dim L.*
  - **dim L = 0**: Theorem P.
  - **dim L = 3** (all chambers): M = L(A)^g, and Lemma R3 applies.
  - **dim L = 2** (|V| a closed half-space): every flat meets |V| in a set
    of its own dimension, so Λ(V) = L(A) and M = L(A)^g. Lemma R3 applies.
  - **dim L = 1**: by Proposition Ln, the only zeros not covered by
    Theorem Q are those of case (iv): U in no hyperplane, L ∩ U = 0,
    c_0 = c_L. It is shown below that then L has no complement.
- So dim U ∈ {1, 2}, since dim U = 3 would give L ⊆ U. Let Y be a
  complement of L. Then Y ≠ 0 (the join with L would be L), so Y ⊄ L.
- *dim U = 1.* By Lemma F, Y ∩ U ≠ 0, so Y ⊇ U. Y is not R^3, since its
  meet with L would be L. U is a line in no hyperplane, so it is not a flat,
  and no plane of A contains it. No such Y exists.
- *dim U = 2.* The eigenvalues are 1, 1, −1, so R^3 = U ⊕ L. A complement
  has Y ∩ L = Y ∧ L = 0 (the meet with an element inside L, §1). So
  Y = (Y ∩ U) ⊕ (Y ∩ L) = Y ∩ U, that is Y ⊆ U. U is not a flat, so Y is a
  line in U, and Y ∩ |V| is a ray ρ ⊆ C.
  - If ρ ⊆ int_U C: Y is a flat line, so Y ⊆ H for some H ∈ A. H ⊉ U, so
    H ∩ U = Y, and it meets int C. By (iv), Y = H′ ∩ U with H′ ⊇ L. Then
    Y + L ⊆ H′, and Y ∨ L ≠ R^3.
  - If ρ ⊆ ∂_U C: ∂_U C ⊆ ∂|V|, which is covered by the facet hyperplanes
    of V. All of these contain L, and one of them contains ρ, hence Y + L.
    Again Y ∨ L ≠ R^3.
- So L has no complement. ∎

COMPUTED: every rank-3 pair of §5 satisfies CR_V. That is 17,884 pairs,
including the 11,428 pairs of the rank-3 arrangements of [PCV] §4.

## 5. The search (COMPUTED)

`compute/conjecture_cr_v.py` is new code. It imports nothing from other
scripts. It works as follows:
- Faces are covectors, generated as compositions of cocircuits.
- Top-cones are all nonempty intersections of closed halfspaces of A.
- M is built from the face spans. Joins and meets are found by search in M
  itself, and μ by recursion.
- "Uncomplemented" means: no x ∈ M with x ∧ a = 0̂ and x ∨ a = 1̂.
- "Modular" means graded, with h(x) + h(y) = h(x ∧ y) + h(x ∨ y).

Pairs are (class representative g, every g-stable top-cone).

*Controls.*
- The 8-element lattice of [PAP] §3.2 is reported complemented with μ = 0.
- B_3 and M_3 are reported complemented with μ ≠ 0, and so is N_5
  (μ(N_5) = 1). Chains are not complemented.
- Non-lattices are refused (test).
- **Reproduction of [PCV] §4** (positive control): the pair counts and zero
  counts of the eleven arrangements of its table are reproduced exactly
  (16,519 pairs; part [REP]).
- Part [CX] checks §0 on its own, including Formula Z.

*Data.* Columns:
- "zeros": the pairs with χ = 0.
- "not Cor. V": the zeros with L + U in no hyperplane, the cases not settled
  by Theorem Q.
- "compl. (non-mod.)": the pairs where M is complemented, and in
  parentheses those of them where M is not modular.
- "CR_V counterexamples": the pairs with M complemented and μ = 0.

The new arrangements are fixed G-invariant arrangements, built as orbits of
one or two seed forms; they are listed in `new_families` of [CR].

| arrangement | source | d | hyperplanes | pairs | zeros | not Cor. V | compl. (non-mod.) | CR_V counterexamples |
|---|---|---|---|---|---|---|---|---|
| A2 | [PCV] | 2 | 3 | 30 | 6 | 4 | 24 (0) | 0 |
| A3 | [PCV] | 3 | 6 | 300 | 34 | 10 | 266 (186) | 0 |
| B2 | [PCV] | 2 | 4 | 45 | 4 | 0 | 41 (0) | 0 |
| B3 | [PCV] | 3 | 9 | 1,106 | 108 | 2 | 998 (862) | 0 |
| generic 4 in R^3 | [PCV] | 3 | 4 | 122 | 10 | 10 | 112 (74) | 0 |
| B3 minus {z=0} | [PCV] | 3 | 8 | 832 | 124 | 42 | 708 (614) | 0 |
| A3 minus a plane | [PCV] | 3 | 5 | 192 | 20 | 8 | 172 (82) | 0 |
| hexagon 12 | [PCV] | 3 | 12 | 3,780 | 308 | 84 | 3,472 (3,310) | 0 |
| hexagon 13 | [PCV] | 3 | 13 | 5,096 | 446 | 0 | 4,650 (4,392) | 0 |
| A4 | [PCV] | 4 | 10 | 4,634 | 342 | 74 | 4,292 (4,002) | 0 |
| generic 5 in R^4 | [PCV] | 4 | 5 | 382 | 30 | 24 | 352 (304) | 0 |
| R^3 C6 x <z->-z> | new | 3 | 6 | 396 | 6 | 6 | 390 (326) | 0 |
| R^3 D4 x <z->-z> | new | 3 | 12 | 5,634 | 46 | 26 | 5,588 (5,088) | 0 |
| R^3 D6 | new | 3 | 6 | 426 | 8 | 8 | 418 (332) | 0 |
| R^4 C5 (companion of Phi_5) x -1 | new | 4 | 5 | 240 | 0 | 0 | 240 (222) | 0 |
| R^4 C8 (companion of Phi_8) | new | 4 | 8 | 3,360 | 0 | 0 | 3,360 (3,314) | 0 |
| R^4 C3 x C3 x -1 | new | 4 | 9 | 2,898 | 0 | 0 | 2,898 (2,648) | 0 |
| R^4 C4 (cyclic coordinates) x -1 | new | 4 | 8 | 3,464 | 0 | 0 | 3,464 (3,306) | 0 |
| R^4 C12 (companion of Phi_12) | new | 4 | 12 | 35,340 | 0 | 0 | 35,340 (35,162) | 0 |
| R^4 C6 x C4 | new | 4 | 12 | 38,400 | 60 | 60 | 38,376 (37,946) | 36 |
| R^4 (C6 x C6) and the swap | new | 4 | 12 | 34,716 | 6 | 6 | 34,710 (34,438) | 0 |
| A4 minus a hyperplane | new | 4 | 9 | 3,040 | 202 | 32 | 2,838 (2,576) | 0 |
| A4 minus two hyperplanes | new | 4 | 8 | 1,688 | 254 | 76 | 1,434 (1,256) | 0 |
| D4 with W(B4) | new | 4 | 12 | 14,426 | 696 | 8 | 13,730 (13,149) | 0 |

Totals: 160,547 pairs (144,028 new), of which 142,588 are in rank 4.
There are 2,710 zeros, 480 of them not Cor. V. Every check of the proven
statements passes on every row:
- Theorem P on 143,164 pointed pairs;
- Theorem Q on 2,230 pairs;
- Lemma K;
- the formula χ = c_0 − c_L of Proposition Ln on 434 pairs.

All CR_V counterexamples lie in the C_6 × C_4 arrangement of §0. They come
in three families of 12 cones each:
- g = diag(−1, −1, 1, 1), |M| = 9 (§0);
- g = diag(1, 1, −1, −1), |M| = 10, with dim L = 1;
- g = diag(1, 1, −1, −1), |M| = 11, with dim L = 2.

All are confirmed by the second implementation (§0.4).

*Remarks on the data.*
- Most random G-invariant arrangements in R^4 have no zeros at all, since
  few of their symmetries have Fix g in a hyperplane. The zeros come from
  arrangements with many involutions: A_4 and its deletions, D_4, and
  C_6 × C_4.
- **A sharper conjecture also fails.** On the data before C_6 × C_4, every
  zero had cl(U) or an element inside L without a complement. The
  counterexamples have no uncomplemented element at all, so that sharper
  form fails too. Even the restriction to "inside L" alone fails earlier,
  on 4 pairs of generic 5 in R^4 where only cl(U) is uncomplemented (test
  `test_strict_form_of_CR_V_prime_fails`).

*Not covered.*
- The hexagon arrangements with added D_6 × ⟨z ↦ −z⟩-orbits (18–25 lines)
  were not swept. They are rank 3, so Theorem 3 covers them.
- D_4 plus a coordinate hyperplane, B_4, and A_5 on all cones were too
  large for this code. B_4 and A_5 are in [PCV] §4, by orbit
  representatives and by OP(P) with n ≤ 6.

## 6. What remains open

- **The right criterion.** CR_V is false, so the per-cone vanishing problem
  of [PCV] is again open in rank ≥ 4. The counterexample is a genuine
  cancellation in Formula Z (1 − 1), not a vanishing of the terms. What
  survives:
  - CR_V in rank ≤ 3 (Theorem 3);
  - pointed cones in every rank (Theorem P);
  - Cor. V zeros in every rank (Theorem Q);
  - the reduction of the line case to the trace condition of
    Proposition Ln(iv).
- **Type A.** Whether CR_V holds on all cones of the braid arrangement is
  OPEN. [PCV] Theorem TA settles the vanishing there, and [PCV] §3.6 gives
  the obstruction for the (TA4) zeros. For the zeros where (TA1)–(TA3)
  fail, no element was exhibited here. [PCV] found no counterexample with
  n ≤ 6.
- **Coxeter arrangements in rank 4.** No counterexample appears in A_4, or
  in D_4 with all cones. B_4, F_4 and H_4 on all cones were not swept.
- **A minimal counterexample.** It is OPEN whether a rank-4 counterexample
  with fewer than 12 hyperplanes, or with a smaller Λ(V)^g, exists.

## 7. Corrections and remarks on other notes (not applied)

- [PCV] Verdict row CR_V and §4: Conjecture CR_V is false (§0). Its
  evidence ("no counterexample on 18,750 pairs and 5,063 lattices") is
  correct as a count. It is also consistent with Theorem 3: 11,428 of the
  [PCV] pairs have rank 3, where CR_V is a theorem, and in rank 4 [PCV]
  sampled only A_4, generic 5, B_4, D_4 and F_4.
- [PCV] §5, "No proof of the converse of the Crapo obstruction is known,
  even for all chambers": all chambers is settled in rank 3 (Lemma R3), and
  pointed cones in every rank (Theorem P).
- [PCV] §4, CO: Theorem Q shows that the Cor. V zeros are Crapo zeros with
  the explicit elements cl(L + U) and cl(U). Lemma K extends [PCV]
  Theorem Cr(a) from all chambers to every cone.
- [PAP] §3.3: the lattices Λ(V)^g are in general not modular, confirmed
  with counts (§5). Knop's Lemma A.2 does not reach CR_V. [PAP] §3.2's
  8-element lattice does occur inside a cone lattice, in the form of §0.2.
- No other claim of another note was found to be wrong.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 conjecture_cr_v.py > output/conjecture_cr_v.txt   # ~45 min, ends "ALL CHECKS PASSED", exit 0
    python3 conjecture_cr_v.py --quick                         # ~90 s: [CTL], [CX], [REP] without hexagon 13 / A_4 / generic 5, and the small new families
    python3 -m unittest test_conjecture_cr_v                    # ~2 s, positive and negative controls, including the counterexample

The archived log is `compute/output/conjecture_cr_v.txt`. "ALL CHECKS
PASSED" means:
- the controls passed;
- [CX] passed;
- [REP] matches [PCV];
- Theorems P and Q, Lemma K and the formula of Proposition Ln hold on
  every row.

CR_V counterexamples are reported, not counted as failures. Each row
prints:
- the pairs, the zeros, and the zeros that are not Cor. V;
- the checks of P, Q, K and Ln;
- the CR_V failures, the CR_V′ failures and the "inside L" failures;
- the complemented pairs, split into modular and non-modular;
- the kinds of uncomplemented elements: cl(U), inside L, or other.

The second-implementation check of §0.4 is not part of the script. It is
the following loop, run once:
- build `audit2_vanishing_criterion.Arrangement(4, normals)`;
- for each failing pair, form the cone from its facet constraints with
  `mask_of_constraints`;
- compute `chi_def`, `GData(arr, g).Z_terms` and
  `per_cone_vanishing.lattice_info` on `arr.Lambda`.

References:
- [PCV] = `notes/per_cone_vanishing.md`;
- [AudPCV] = `notes/audit_per_cone_vanishing.md`;
- [PAP] = `notes/prior_art_per_cone_vanishing.md`;
- [VC] = `notes/vanishing_criterion.md`;
- [GT] = `notes/general_theory.md`;
- Crapo, *The Möbius function of a lattice*, J. Combin. Theory 1 (1966);
- Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., Ex. 3.92;
- Knop, arXiv:2209.10337, Lemma A.2;
- Rota, *On the foundations of combinatorial theory I* (1964), for
  μ ≠ 0 on geometric lattices.
