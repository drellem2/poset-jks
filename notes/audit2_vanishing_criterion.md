# Second independent audit of the vanishing criterion

**Verdict: HOLDS.** Formula Z, Theorem S (including the top-lune
realization), S1–S3, Cor. V and Theorem A of `notes/vanishing_criterion.md`
("[VC]") are correct as stated in the current version. No counterexample was
found on six arrangements that are not reflection arrangements, four of them
with symmetry groups acting by maps that are not orthogonal in the given
coordinates. Two remarks
on wording (§6) need no change to any statement.

This audit was written without reading `notes/audit_vanishing_criterion.md`
or `compute/audit_vanishing_criterion.py`, and the code imports nothing from
`compute/`. It checks the version of [VC] that already contains the fixes of
that earlier audit (the mirror hypothesis in S3 and PC(c), and the rank-0 case
of Z). §7 compares the two audits; it was written after the verdict.

Notation is that of [VC] §§1–2: U = Fix g, L = lin V, Z(V,g) and Z\*(V,g) as
there, and χ_V(g) = (−1)^d det(g) μ(Λ(V)^g).

| # | Claim of [VC] | Verdict | How checked |
|---|---|---|---|
| Z | Formula Z: χ_V(g) = Σ_{X ∈ Z\*(V,g)} μ_{L(A)^g}(0,X) m_X(V) | **HOLDS** | proof re-derived step by step (§1); exact check on every pair of 11 arrangements, 6 of them not Coxeter (§5) |
| Z.a | W″(c) applies to every localization (A_X/X, V_X, ḡ), X ∈ Z(V,g), including X = R^d | **HOLDS** | §1.1 |
| Z.b | Möbius inversion in Z(V,g), and μ_{Z(V,g)} = μ_{L(A)^g} on [0,X] | **HOLDS** | §1.2 |
| Z.c | μ_{L(A)^g}(0,X) = χ^full_{A^X}(g\|_X) | **HOLDS** | §1.3; computed on A^X as an arrangement in its own right, for every X ∈ Z\*(g) of every class |
| Z.d | m_X(V) ≥ 1, also when V and \|V\| ∩ U are not pointed | **HOLDS** | §1.4; every term computed, all ≥ 1, including non-pointed restricted cones |
| S | some cone has χ ≠ 0 iff some X ∈ Z\*(g) has μ(0,X) ≠ 0 | **HOLDS** | §2; all top-cones enumerated for every class |
| S-lune | for minimal X, every g-fixed chamber K of A_X gives a g-stable top-lune V♯ with lin V♯ = X and χ_{V♯}(g) = μ(0,X) | **HOLDS** | §2; checked for every minimal X and every K, not one K |
| S1, S2, V | pointed cones; Fix g = 0; Cor. V | **HOLDS** | §3 (short consequences of Z) |
| S3 | involutions; reflection clause with the mirror a hyperplane of A | **HOLDS** | §3; the mirror hypothesis is needed (two new examples, both directions) |
| A | ±S_n rule; (A−): cycle lengths in {m, 2m}, m odd squarefree | **HOLDS** | §4 by hand; own code for all 126 classes ±w, 3 ≤ n ≤ 8 |
| PC(a), PC(b) | per-cone necessity; equivalence for sign-coherent g | **HOLDS** | follows from Z; checked on every pair |
| PC(c) | reflections whose mirror is in A are sign-coherent | **HOLDS** | checked; fails without the mirror hypothesis, as [VC] says |
| PC′ | cancellation occurs | **HOLDS**, and is not special to type A and F_4 | cancelling pairs in 5 of the 6 non-Coxeter probes (§5) |
| CR | Crapo direction; converse CONJECTURED | "if" **HOLDS**; converse: no counterexample | §5 |

---

## 1. Formula Z

### 1.1 W″(c) on each localization

Let X ∈ Z(V,g), so X ⊆ L is a g-stable flat with X ∩ U = 0.

- *The triple is admissible.* A_X/X = {H/X : H ⊇ X} is a central arrangement
  in R^d/X, and it is essential because X = ∩_{H ⊇ X} H. V_X, the image of
  |V|, is a top-cone of it ([GT] Lemma 0.1(c): every constraint of |V|
  contains L ⊇ X). ḡ has finite order and preserves A_X/X and V_X ([FP]
  Lemma A). Nothing more is asked by W″, which is stated for every top-cone
  and every finite-order linear symmetry ([AudW] §2). The localization A_X
  is not essential in R^d, but W″ is applied to A_X/X, which is.
- *Rank.* rank(A_X/X) = d − dim X ≥ 1 unless X = R^d. X = R^d ∈ Z(V,g) forces
  U = 0 and L = R^d (V = all chambers). There the identity needed in step 5
  of [VC] is χ_{V_{R^d}} = 1 on the left, and on the right
  [R^d ∈ Z\*] m_{R^d}(V) = 1 (empty arrangement in U = 0, rank-0 convention).
  So step 5 holds at X = R^d. [VC] §2 step 1 says exactly this.
- *Lineality flats of V_X.* lin V_X = L/X, and the flats of A_X/X inside L/X
  are the Z/X with Z a flat of A, X ⊆ Z ⊆ L. Z/X is ḡ-stable iff Z is
  g-stable (Z ⊇ X). (V_X)_{Z/X} is V_Z, and the induced map is the one
  induced by g, since (R^d/X)/(Z/X) = R^d/Z.
- *Fix ḡ = (U + X)/X.* If gx − x ∈ X, the ⟨g⟩-average p of x lies in U, and
  g^k x − x = Σ_{j<k} g^j(gx − x) ∈ X, so p − x ∈ X. Correct; it uses only
  finite order and characteristic 0.
- *Index set.* For X ⊆ Z, Z ∩ (U + X) = (Z ∩ U) + X (modular law), which
  is X iff Z ∩ U ⊆ X, iff Z ∩ U ⊆ X ∩ U = 0. So the W″ sum for V_X runs over
  {Z ∈ Z(V,g) : Z ⊇ X}. Correct.
- *Right side.* Fix ḡ ⊆ H/X iff U + X ⊆ H. If X ∈ Z\*(V,g), u ↦ u + X is an
  isomorphism U → (U+X)/X. It sends H ∩ U to (H ∩ (U+X))/X for H ⊇ X (modular
  law again), so it carries {H ∩ U : H ⊇ X} onto the restriction of A_X/X to
  Fix ḡ. It carries |V| ∩ U onto V_X ∩ Fix ḡ, because |V| + X = |V|. So the
  right side is m_X(V). Correct.

### 1.2 Möbius inversion

Step 5 gives Σ_{Z ∈ Z(V,g), Z ⊇ X} χ_{V_Z}(ḡ) = ψ(X) for **every** X in the
finite poset P = Z(V,g), with the sum over the up-set of X in P. That is the
hypothesis of Möbius inversion from above, and it gives
χ_{V_X}(ḡ) = Σ_{Z ⊇ X} μ_P(X,Z) ψ(Z); at X = 0 this is (Z) with μ_P.
P is a down-set of L(A)^g (Y ⊆ X ∈ P, Y g-stable ⇒ Y ⊆ L and Y ∩ U = 0),
so μ_P(0,X) = μ_{L(A)^g}(0,X). Correct.

### 1.3 μ(0,X) as a full Lie character

The flats of A contained in X are exactly the flats of A^X = {H ∩ X : H ⊉ X}:
a flat Y ⊆ X of A equals X ∩ ∩_{H ⊇ Y, H ⊉ X} H, and conversely an
intersection of some H ∩ X is an intersection of hyperplanes of A (X is one).
A^X is essential in X since A is. g-stability is the same on both sides. So
[0,X]_{L(A)^g} = L(A^X)^{g|X}, and χ^full_{A^X}(g|_X) =
(−1)^{dim X} det(g|_X) μ. Since X ∩ U = 0, g|_X has no eigenvalue 1, so
det(g|_X) = (−1)^{#eigenvalues −1} = (−1)^{dim X} (non-real eigenvalues come
in conjugate pairs with product 1). Correct. COMPUTED: for every class of
every arrangement in §5 and every X ∈ Z\*(g), the code builds A^X as an
arrangement in coordinates of X, computes g|_X, checks it has no fixed
vector, and computes χ^full from the face poset of A^X. It equals
μ_{L(A)^g}(0,X) every time.

### 1.4 m_X(V) ≥ 1 for non-pointed V

m_X(V) = m(V_X^U), the bottom multiplicity of the top-cone |V| ∩ U of the
arrangement B = {H ∩ U : H ⊇ X} in U.

- B is a set of hyperplanes of U (no H ⊇ X contains U, as X ∈ Z\*) and is
  essential (∩ = X ∩ U = 0).
- |V| ∩ U is cut out by hyperplanes of B, since every constraint of |V|
  contains L ⊇ X. Several constraints may restrict to one hyperplane of B;
  they ask for the same side, since |V| ∩ U is full-dimensional in U (average
  an interior point of |V| over ⟨g⟩). The code asserts this consistency.
- If dim U = 0 then X = R^d and m = 1 by convention. If dim U = 1, m = 1.
  If dim U ≥ 2, [AudW] §2 proves m ≥ 1 for **every** top-cone of an essential
  arrangement (a chamber cycle is a nonzero top cycle of a complex with no
  higher simplices), pointed or not. Nothing in that argument uses
  pointedness, and V_X^U is a top-cone of the essential arrangement B.

So m_X(V) ≥ 1, as claimed. COMPUTED: every m_X(V) occurring in the checks
of §5 is ≥ 1, including the terms whose restricted cone |V| ∩ U is not
pointed (counts in §5).

## 2. Theorem S and the top-lune

(i) ⇒ (ii) is immediate from (Z). For (ii) ⇒ (i), let X be minimal among the
X ∈ Z\*(g) with μ(0,X) ≠ 0.

- *K exists.* No H ∈ A_X contains U (X + U lies in no hyperplane). Lemma F
  of [FP] holds for any central arrangement, essential or not, so it applies
  to A_X with h = g: the g-fixed chambers of A_X are in bijection with the
  chambers of A_X|_U, which exist.
- *V♯ = {C : C_e = K_e, H_e ⊇ X}* is a top-cone, g-stable since gK = K.
  |V♯| = closure(K) ⊇ X. A hyperplane H ⊉ X meets X in a proper subspace, so
  X ⊆ |V♯| has points strictly on both sides of H, and V♯ is not on one side
  of H. Hence S_max(V♯) = A_X and lin V♯ = ∩_{H ⊇ X} H = X.
- *Evaluation.* Z\*(V♯,g) = {X′ ∈ Z\*(g) : X′ ⊆ X}. Every X′ ⊊ X there has
  μ(0,X′) = 0 by minimality, so χ_{V♯}(g) = μ(0,X) m_X(V♯).
- *m_X(V♯) = 1.* |V♯| ∩ U = {u ∈ U : K_e α_e(u) ≥ 0, H_e ⊇ X}. It contains
  K ∩ U, a chamber of A_X|_U (Lemma F), which is open in U and has the same
  sign vector, so |V♯| ∩ U is the closure of that chamber. A closed chamber of
  an essential arrangement of rank k ≥ 1 is a pointed polyhedral cone; its
  support lattice is its face lattice (F ↦ span F is injective on faces of
  a chamber), the face lattice of a (k−1)-polytope with ∅ adjoined, whose
  Möbius number is (−1)^k. So m = 1. (k = 0 is X = R^d, m = 1.)

So χ_{V♯}(g) = μ(0,X) ≠ 0. The proof is correct, and it gives the stronger
statement that **every** g-fixed chamber K of A_X works, which the code
checks. Minimality is needed: the tests find X ∈ Z\*(g) with μ ≠ 0 but a
smaller X′ with μ ≠ 0, whose top-lune has χ ≠ μ(0,X) (on A_3 and on
B_3 ∖ {z = 0}). This is the same phenomenon as [VC]'s H_3 control.

## 3. S1, S2, S3, Cor. V

- **S1.** L = 0 ⇒ Z\*(V,g) ⊆ {0}, and the 0-term is [U in no hyperplane]
  m(V^U). That this equals #V^g is [FP] Cor. P (for pointed V^U Lemma F gives
  #V^g = number of chambers of V^U = m(V^U)). Holds.
- **S2.** U = 0 ⇒ X + U = X in no hyperplane only for X = R^d. Holds.
- **S3.** For g² = 1 and X g-stable, X = (X ∩ U) ⊕ (X ∩ E), so X ∩ U = 0
  forces X ⊆ E, and then g|_X = −1, [0,X]^g = L(A^X), a geometric lattice,
  μ ≠ 0 with sign (−1)^{dim X} (Rota). So the criterion is "some flat X ⊆ E
  with X + U in no hyperplane". Holds. Reflection clause: if g is a
  reflection (dim U = d − 1) and U is a hyperplane of A, then X = 0 is
  excluded (U lies in the hyperplane U), and the only nonzero subspace of the
  line E is E itself, with E + U = R^d. So: nonzero on some cone iff E is a
  flat. Holds. COMPUTED: the involution criterion agrees with Theorem S for
  every involution class of every arrangement in §5, and every X ∈ Z\*(g) of
  an involution has μ ≠ 0.

  *The mirror hypothesis is needed, in both directions.* Besides [VC]'s
  examples, the probes give:
  - generic 4 planes in R^3 (normals e_1, e_2, e_3, e_1+e_2+e_3): a
    reflection whose mirror is not in A, with E **not** a flat, is nonzero on
    some cone (the clause would say zero);
  - the same arrangement, B_3 ∖ {z = 0}, and the 12-line hexagon arrangement
    each have a reflection with mirror not in A, E a flat, nonzero, but **not**
    sign-coherent (so PC(c) needs the hypothesis too). In B_3 ∖ {z = 0} this
    is the reflection z ↦ −z in the deleted plane.
- **Cor. V.** If H ⊇ L + U, then H ⊇ X + U for every X ⊆ L, so Z\*(V,g) = ∅.
  Holds. The converse sentence "χ_V(g) ≠ 0 forces L + U in no hyperplane" is
  the contrapositive. "On pointed cones every zero is of this kind" holds by
  S1, since there χ = [U in no hyperplane] m(V^U) and L + U = U.

## 4. Theorem A

### 4.1 By hand

Setup: g = εw on R^n_0, (gx)_{w(i)} = ε x_i. Flats X_π; X_π ⊆ X_ρ iff π is
coarser than ρ. [0, X_π] in L(A)^g is the set of w-stable coarsenings of π
ordered by reverse refinement, i.e. the dual of the w̄-fixed sublattice of
Π(blocks of π); μ of a dual is the same, so μ(0, X_π) = μ(Π_b^{w̄}).
Hanlon's formula (H) is as stated in [VC] (checked against a direct Möbius
recursion for every permutation of b ≤ 6 points by the tests, and for every
w̄ occurring with n ≤ 8 by the main script).

*(A−).* U = {x : x_{w(i)} = −x_i} (automatically sum-zero). On an odd cycle
x_{w^k(i)} = (−1)^k x_i forces x = 0; on an even cycle x alternates with one
free parameter. So H_ij ⊇ U iff both i, j are in odd cycles, or i, j lie in one
even cycle at even distance (different even cycles have independent
parameters; an odd and an even point are separated by the free parameter).
X_π ∩ U: f on blocks with f(w̄B) = −f(B), zero iff every w̄-orbit is odd.
X_π + U ⊆ H_ij iff i, j share a block and form a tight pair. All as in [VC].

Necessity: all w̄-orbits have one odd length ℓ with μ(ℓ) ≠ 0; ℓ | k for
each cycle length k (w^k i = i forces w̄^k B = B), and w^{jℓ}(i) ∈ B for all
j. k odd: B contains k/ℓ points of odd cycles, so k = ℓ. k even: k/ℓ is
even; if k/ℓ ≥ 4, then i and w^{2ℓ}(i) are distinct points of B at even
distance 2ℓ, a tight pair; so k = 2ℓ. Sufficiency: singletons on odd cycles
and antipodal pairs {i, w^m(i)} on the 2m-cycles; all w̄-orbits have length
m, no block holds a tight pair, and (H) gives μ ≠ 0. Correct.

Free-action form: g^j e_i = ε^j e_{w^j i}, so Stab(e_i) = lcm(2,k)Z for
ε = −1 (k the cycle length), and ⟨g⟩ (of order lcm(2, ord w) for n ≥ 3)
acts freely iff all lcm(2,k) are equal to one N. If 4 | N then μ(N) = 0;
otherwise N = 2m, m odd, and k ∈ {m, 2m}, with μ(2m) ≠ 0 iff m squarefree.
So the two forms agree. (The claim ord(−w) = lcm(2, ord w) needs that no
permutation acts as −1 on R^n_0 for n ≥ 3: −1 would have to swap 1 and 2
and also 1 and 3.)

Small n by hand from (A−): n = 3: −(1³), −(2,1), −(3) nonzero (all of them).
n = 4: −(3,1), −(4) zero, the other three nonzero. n = 5: −(3,2), −(3,1,1),
−(4,1) zero. n = 6: −(3,1³), −(4,1,1), −(3,2,1), −(5,1), −(4,2) zero. These
are exactly the G ∖ W rows of [VC] §7, and the code agrees.

### 4.2 By code, n ≤ 8

`theorem_A_check(n)` does not use the tight-pair description. For every
class ±w and every w-stable partition π it computes U as a nullspace in
R^n, tests X_π ∩ U = 0 by ranks, tests X_π + U against every H_ij directly,
and computes μ(0, X_π) by a direct recursion on the w̄-stable partitions of
the blocks (cross-checked with Hanlon). It then compares "some π has μ ≠ 0"
with (A+)/(A−) and with the free-action form. All three agree on all 126
classes ±w with 3 ≤ n ≤ 8 (the count [VC] §4 gives). Nonzero on some cone:
5, 5, 6, 10, 7, 7 classes for n = 3, …, 8. For n ≤ 6 the log lists them.
A negative control (test `test_even_m_is_wrong`) confirms that allowing even
m would misclassify −(4,2).

## 5. Non-Coxeter probes and data

`compute/audit2_vanishing_criterion.py` builds each arrangement from rational
normals, computes flats, all faces (as compositions of cocircuits), all
top-cones (as nonempty intersections of half-space chamber sets), and the
group G generated by the listed rational matrices (verified to permute A). For
each pair (V, g), V a W-orbit representative and g a class representative of
Stab_G(V), it computes χ_V(g) from the definition (the g-stable part of
Λ(V) = spans of faces in |V|) and the right side of (Z) from its own
definitions, with m_X(V) computed from the face poset of the restricted cone.
Per class of G it checks Theorem S against **all** top-cones, the top-lunes,
μ = χ^full, S3 and Crapo.

| arrangement | d | \|A\| | simplicial | top-cones | \|G\| | pairs | χ ≠ 0 | Cor. V zeros | zero, no nonzero μ | cancelling | classes | vanishing classes | top-lunes checked |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A_2 (G = ±S_3) | 2 | 3 | yes | 19 | 12 | 14 | 9 | 2 | 1 | 2 | 6 | 1 | 11 |
| A_3 (±S_4) | 3 | 6 | yes | 219 | 48 | 49 | 28 | 13 | 6 | 2 | 10 | 5 | 41 |
| A_4 (±S_5) | 4 | 10 | yes | 4,231 | 240 | 172 | 75 | 72 | 15 | 10 | 14 | 8 | 137 |
| B_2 | 2 | 4 | yes | 33 | 8 | 15 | 13 | 2 | 0 | 0 | 5 | 0 | 14 |
| B_3 | 3 | 9 | yes | 941 | 48 | 84 | 55 | 27 | 2 | 0 | 10 | 2 | 70 |
| generic 4 in R^3 | 3 | 4 | no | 71 | 48 | 31 | 26 | 0 | 1 | **4** | 10 | 1 | 34 |
| generic 5 in R^4 | 4 | 5 | no | 231 | 240 | 60 | 46 | 2 | 3 | **9** | 14 | 2 | 68 |
| B_3 ∖ {z = 0} | 3 | 8 | yes | 635 | 16 | 119 | 78 | 27 | 5 | **9** | 10 | 4 | 61 |
| A_3 minus one plane | 3 | 5 | no | 121 | 8 | 53 | 44 | 5 | 1 | **3** | 8 | 1 | 41 |
| hexagon, 12 lines | 3 | 12 | yes | 3,283 | 24 | 294 | 207 | 68 | 7 | **12** | 12 | 6 | 113 |
| hexagon, 13 lines | 3 | 13 | yes | 4,509 | 24 | 381 | 280 | 101 | 0 | 0 | 12 | 0 | 137 |

Totals: 1,272 pairs, all satisfying (Z); 111 classes, all satisfying
Theorem S; 727 top-lunes (every minimal X, every g-fixed chamber of A_X), all
with lin = X and χ = μ(0,X); 105 flats X ∈ Z\*(g) with μ(0,X) = χ^full
computed on A^X. m_X(V) ranges over 1…35; 285 terms have a non-pointed
restricted cone |V| ∩ U, the largest m there being 35. Coxeter positive
controls: the top-cone counts and W-orbit counts of [GT]/[FP], the Lie_4
character on A_3, and the [VC] §7 counts that do not depend on the pair
convention (§6, remark 2) are reproduced; the "vanishing classes" column
matches [VC] §7 (A_2: 1, A_3: 3 + 2, A_4: 5 + 3, B_2: 0, B_3: 2).

The non-Coxeter probes:
- *generic 4 in R^3* and *generic 5 in R^4*: d+1 hyperplanes in general
  position, normals e_1, …, e_d, e_1+⋯+e_d, with G = S_{d+1} × {±1} acting by
  rational maps that are **not orthogonal** in these coordinates (a projective
  frame can be permuted arbitrarily).
- *B_3 ∖ {z = 0}*: 8 planes, simplicial, not a reflection arrangement; G of
  order 16 contains the reflection in the deleted plane z = 0.
- *A_3 minus one plane*: 5 planes, not simplicial.
- *hexagon, 12 and 13 lines*: the regular hexagon's 6 edge lines and 6
  mirrors in P^2, with and without the line at infinity; simplicial, not
  reflection arrangements (Grünbaum's A(12,1) and A(13,2) types, simpliciality
  checked by the code). They are written in hexagonal-lattice coordinates,
  so D_6 × ⟨z ↦ −z⟩ acts by rational non-orthogonal matrices.

Findings:
- (Z), Theorem S, the top-lunes, μ = χ^full, S3 and PC(a)/(b) hold on every
  pair and class.
- Cancellation (PC′) is common off the Coxeter world: generic 4 in R^3,
  generic 5 in R^4, B_3 ∖ {z = 0}, A_3 minus a plane and the 12-line hexagon
  all have cancelling pairs. [VC] does not claim otherwise (PC′ says only that
  cancellation occurs; §7's "only in type A and F_4" is about its own data).
- CR: the Crapo direction holds everywhere tested. The CONJECTURED converse
  had no counterexample: every X ∈ Z\*(g) with μ(0,X) = 0 has an
  uncomplemented element of [0,X]^g.

## 6. Remarks on wording (no statement changes)

1. [VC] §3.1 S3, reflection clause: "the roots orthogonal to α span α^⊥"
   presupposes an orthogonal reflection in the coordinates where the roots
   live. For a reflection that is not orthogonal there (as in the hexagonal
   coordinates above), the invariant form of the clause is "E = ker(g + 1) is
   a flat"; the "roots orthogonal to α" form holds after passing to a
   ⟨g⟩-invariant inner product and identifying normals with vectors through
   it. The statement "iff the line Rα is a flat" is already correct if Rα is
   read as ker(g + 1). Suggested: say "Rα = ker(s_α + 1)".
2. [VC] §7's pair counts use a different pair convention from this audit's
   (this audit: V a W-orbit representative, g a representative of a
   conjugacy class of Stab_G(V) in Stab_G(V)). The counts that do not depend
   on the convention agree: top-cones and W-orbits (A_2: 19/5, A_3: 219/16,
   A_4: 4,231/63, B_3: 941/35), the cancelling pairs (A_2: 2, A_3: 2,
   A_4: 10, B_3: 0), Cor. V zeros and "no nonzero μ" zeros (B_3: 27 and 2),
   and the number of classes vanishing on every cone. The totals of pairs
   and of nonzero pairs differ (e.g. A_2: 14 here, 19 in [VC]). Not a
   mathematical issue; [VC]'s convention is not fully specified, so its
   pair totals cannot be reproduced from the text alone.

## 7. Comparison with the first audit

Written after §§1–6. The first audit (`notes/audit_vanishing_criterion.md`)
reached the same verdict on every proven claim; its three findings (the mirror
hypothesis in S3 and in PC(c), and the rank-0 case X = R^d of Z) are already
applied in the current [VC], and this audit confirms each of them
independently (§1.1, §3). Neither audit finds a wrong formula.

What this audit adds:
- **Non-Coxeter coverage.** The first audit's non-reflection arrangements
  were coord2, tri2 and coordsum3 (= generic 4 in R^3) with orthogonal
  groups of order ≤ 12. Here: generic 4 in R^3 and generic 5 in R^4 with
  their full projective symmetry groups S_{d+1} × {±1} (orders 48 and 240,
  non-orthogonal), the simplicial non-Coxeter arrangements B_3 ∖ {z = 0} and
  the 12- and 13-line hexagon arrangements (non-orthogonal D_6 action), and
  A_3 minus a plane. Z, S, S3 and the top-lune realization hold on all.
- **μ = χ^full checked as stated.** The first audit checked the sign
  det(g|_X) = (−1)^{dim X}; here χ^full_{A^X}(g|_X) is computed from the face
  poset of A^X as an arrangement of its own, and compared with μ(0,X).
- **Every g-fixed chamber K of A_X** gives the top-lune value μ(0,X), not
  only one K.
- **Theorem A** re-checked by separate code for all 126 classes with
  n ≤ 8, and its tight-pair lemmas bypassed (Z\*(g) by ranks in R^n).
- **Cancellation (PC′) off the Coxeter world**, in rank 3 and rank 4, and
  two further examples (generic 4 in R^3) of why the reflection clauses need
  the mirror hypothesis, one in each direction.
- **Crapo** (CR): the proven direction holds and the conjectured converse has
  no counterexample on the new arrangements (the first audit did not test
  CR).

What the first audit covers and this one does not: an exhaustive (no orbit
reduction) pair set, so more pairs; the rank-1 and coord2/tri2 examples;
the ord(−w) claim at n = 2 as a negative control. Neither audit checks H_3,
F_4, D_4, or the tables of [VC] §§5, 7 beyond the counts noted in §6.

## Reproduce

From `compute/` (plain Python 3, no third-party packages; single process):

    python3 audit2_vanishing_criterion.py > output/audit2_vanishing_criterion.txt   # ~2 min, ends "ALL CHECKS PASSED", exit 0
    python3 audit2_vanishing_criterion.py --quick                                    # ~80 s: n <= 6 for Theorem A; A_4 and generic 5 in R^4 omitted
    python3 -m unittest test_audit2_vanishing_criterion                              # ~4 s, positive and negative controls

The archived log is `compute/output/audit2_vanishing_criterion.txt`.

References: [VC] = `notes/vanishing_criterion.md`; [FP] =
`notes/fixed_point_formula.md`; [GT] = `notes/general_theory.md`; [AudW] =
`notes/audit_prop_w_prime.md` (Theorem W″).
