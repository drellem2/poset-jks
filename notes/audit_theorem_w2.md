# Audit: Theorem W″ (the exact value of the Weisner sum when Fix g lies in no hyperplane)

**Verdict: HOLDS.** Every step of the proof of Theorem W″ in
`notes/audit_prop_w_prime.md` §2 ("[AudW′]") re-derives by hand. The
Galois connection is correct in both directions. Its kernel operator is
X ↦ cl(X ∩ Fix g), as claimed. Hall's theorem is applied to finite bounded
posets in both places, which is all it needs. m(V^{Fix g}) ≥ 1 holds for
every top-cone, pointed or not, given [GT] Theorem 1. No mathematical fix is
needed. Two wording-level notes are in §6.

Sources:
- [AudW′] = `notes/audit_prop_w_prime.md`, where Theorem W″ is stated and
  proved (§2);
- [GT] = `notes/general_theory.md`;
- [FP] = `notes/fixed_point_formula.md`;
- [AudFP] = `notes/audit_fixed_point_formula.md`;
- [AudA] = `notes/audit_general_theory_cones.md`;
- [AudC] = `notes/audit_theorem_c.md`.

Notation is that of [AudW′]:
- A is a finite central essential real arrangement in R^d, with d ≥ 1;
- V is a top-cone, with |V| = {x : s_e α_e(x) ≥ 0, e ∈ S_max} and lineality
  space L;
- g is a linear map of finite order with gA = A and g|V| = |V|;
- U = Fix(g), with k = dim U;
- M = Λ(V)^g;
- S(g) = Σ_{X ∈ M, X ∩ U = 0} μ_M(X, R^d).

Tags: **PROVEN** (re-derived here), **COMPUTED** (by
`compute/audit_theorem_w2.py`, written for this audit; it imports nothing
from the repository).

## The claim

**Theorem W″ ([AudW′] §2).**
- (a) If U lies in a hyperplane of A, then S(g) = 0.
- (b) If U lies in no hyperplane, then S(g) = μ_{Λ(V^U)}(0, U) = (−1)^k m(V^U)
  and m(V^U) ≥ 1. Here A^U = {H ∩ U}, and V^U is the top-cone of A^U with
  |V^U| = |V| ∩ U.
- (c) In χ-form, Σ_{X ∈ 𝓛^g, X ∩ U = 0} χ_{V_X}(ḡ) equals m(V^U) in case
  (b) and 0 in case (a).

| Step | Verdict |
|---|---|
| 1. Reduction S(g) = μ_{Q̂}(0̂, 1̂) = χ̃(Δ(Q′)) | **HOLDS** (§1) |
| 2. V^U is a top-cone of the essential arrangement A^U | **HOLDS**. One case is left implicit; it is filled in §2. |
| 3. π : X ↦ X ∩ U maps Q′ into P_U = Λ̄(V^U) | **HOLDS** (§3) |
| 4. σ : Z ↦ cl(Z) maps P_U into Q′ | **HOLDS** (§3) |
| 5. Galois connection, π∘σ = id, σ∘π ≤ id, homotopy equivalence | **HOLDS**. Both adjunction inequalities are checked (§3). |
| 6. Hall's theorem, twice | **HOLDS**. The hypotheses are only finiteness and boundedness (§1, §3). |
| 7. m(V^U) ≥ 1 through [GT] Theorem 1 and a chamber cycle | **HOLDS**, including non-pointed V^U (§4) |
| 8. χ-form (c) and the sign (−1)^d det g = (−1)^k | **HOLDS** (§5) |
| 9. Remark: #V^g = #chambers of V^U, so m(V^U) ≤ #V^g, with equality if V^U is pointed | **HOLDS** (COMPUTED; the bijection is [FP] Lemma F) |

---

## 1. Reduction to Δ(Q′) and Hall's theorem (PROVEN)

Assume U ≠ 0. This holds in case (b), since a hyperplane contains 0.

1. Put Q′ = {X ∈ M : X ≠ R^d, X ∩ U ≠ 0} and Q = Q′ ∪ {R^d}.
   - If X ⊆ Y and X ∩ U ≠ 0, then Y ∩ U ≠ 0. So Q is an up-set of M.
   - R^d ∩ U = U ≠ 0, so R^d ∈ Q.
   - The index set of S(g) is exactly M ∖ Q.
2. M has bottom 0 and top R^d, and these differ because d ≥ 1. By the
   defining recursion of μ, Σ_{X ∈ M} μ_M(X, R^d) = 0. Hence
   S(g) = −Σ_{X ∈ Q} μ_M(X, R^d).
3. Let Q̂ be the subposet {0} ∪ Q of M. It is bounded, since 0 ∉ Q
   (0 ∩ U = 0).
   - For y ∈ Q, the interval [y, R^d] of M lies in Q, because Q is an
     up-set. So μ_{Q̂}(y, R^d) = μ_M(y, R^d).
   - The recursion gives μ_{Q̂}(0, R^d) = −Σ_{y ∈ Q} μ_M(y, R^d) = S(g).
4. **Hall's theorem.** For a finite poset P with 0̂ and 1̂ adjoined,
   μ(0̂, 1̂) = χ̃(Δ(P)), with χ̃(∅) = −1. The only hypothesis is that the
   bounded poset is finite. Here P = Q′, which is finite, and 0, R^d play the
   roles of 0̂, 1̂. So S(g) = χ̃(Δ(Q′)).
   - Q′ = ∅ is allowed. Then μ = −1. This happens exactly when k = 1: a
     proper flat meeting the line U contains U, so U would lie in a
     hyperplane.

COMPUTED `[hall]`: S(g) = χ̃(Δ(Q′)) on every case-(b) pair. The chain sums
are computed directly, not through μ.

## 2. V^U is a top-cone of an essential arrangement (PROVEN)

1. No α_e vanishes on U, so each H ∩ U is a hyperplane of U. A^U has
   ∩(H ∩ U) = U ∩ ∩A = 0, so it is essential.
2. Full dimension. Average an interior point of |V| over ⟨g⟩. The result p̄
   is still interior, by convexity and g|V| = |V|, and it is g-fixed. So
   p̄ ∈ U, and a neighbourhood of p̄ in U lies in |V|.
3. |V| ∩ U = {u ∈ U : s_e α_e|_U(u) ≥ 0, e ∈ S_max}.
   - Every α_e|_U is a nonzero multiple of the form of some hyperplane of
     A^U.
   - Several e ∈ S_max can restrict to the same hyperplane K of A^U. If they
     asked for opposite sides of K, the cone would lie in K. That
     contradicts step 2.
   - So the constraints are a consistent sign assignment on a set of
     hyperplanes of A^U.
   - Its chambers form a nonempty set {C′ : C′_K = t_K} of chambers of A^U,
     that is, a top-cone in the sense of [GT] §0. Its closed support is
     exactly |V| ∩ U.

   [AudW′] does not write out the middle point. It follows from step 2, as
   shown.
4. [GT] Lemma 0.1(a) in U then gives
   Λ(V^U) = {flats Z of A^U : dim(Z ∩ |V|) = dim Z}.

COMPUTED:
- `[VUcone]`: the sign assignment is consistent on every pair.
- `[VU=]`: a chamber of A^U lies in V^U iff its interior point, lifted to
  R^d, satisfies every constraint of V strictly. V^U is computed from A^U's
  own faces, in coordinates on U.

## 3. The Galois connection (PROVEN)

Let P_U = Λ̄(V^U) be the proper part. For a subspace W, cl(W) is the
intersection of the hyperplanes of A that contain W.

**π : Q′ → P_U, π(X) = X ∩ U.**
- X = ∩_{H ⊇ X} H, so X ∩ U = ∩_{H ⊇ X}(H ∩ U) is a flat of A^U. X ≠ R^d,
  so this intersection is over at least one hyperplane.
- X ∩ U ≠ 0, by the definition of Q′.
- X ∩ U ≠ U. Otherwise U ⊆ X ⊆ H for some H, against case (b).
- X ∩ U ∈ Λ(V^U):
  - X ∩ |V| has dimension dim X and is g-stable.
  - Its relative-interior average p̄ lies in U, and a neighbourhood of p̄ in
    X lies in |V|.
  - Intersecting with U, a neighbourhood of p̄ in X ∩ U lies in |V| ∩ U. So
    dim(X ∩ U ∩ |V|) = dim(X ∩ U).
- π is monotone.

**σ : P_U → Q′, σ(Z) = cl(Z).**
- *cl(Z) ∩ U = Z.*
  - Write Z = U ∩ ∩_{e ∈ T} H_e. Each H_e contains Z, so
    cl(Z) ⊆ ∩_T H_e, and cl(Z) ∩ U ⊆ Z.
  - Z ⊆ cl(Z) ∩ U is clear.
- *g-stable.* g fixes Z pointwise, since Z ⊆ U. So g permutes the
  hyperplanes through Z.
- *In Λ(V).*
  - Z ∩ |V| has dimension dim Z, so its relative interior in Z is a nonempty
    open subset of Z.
  - Each hyperplane H ⊉ Z meets Z in a proper subspace, and there are
    finitely many. So some p in that relative interior avoids all of them.
  - The face F of A through p has zero set exactly {H : H ⊇ Z}, so
    span F = cl(Z).
  - |V| is an intersection of closed half-spaces of A, so it is a union of
    faces. Hence F ⊆ |V|, and cl(Z) = span F ∈ Λ(V).
- *Proper and meets U.* Z ≠ U is a flat of A^U, so Z ⊆ H ∩ U for some H.
  Then cl(Z) ⊆ H ≠ R^d. Also cl(Z) ∩ U = Z ≠ 0.
- σ is monotone.

**Adjunction.** For X ∈ Q′ and Z ∈ P_U, we show Z ≤ π(X) ⇔ σ(Z) ≤ X.
- (⇒) If Z ⊆ X ∩ U, then Z ⊆ X. X is a flat of A, so it is an intersection
  of hyperplanes containing Z, and cl(Z) ⊆ X.
- (⇐) If cl(Z) ⊆ X, then Z = cl(Z) ∩ U ⊆ X ∩ U.

So σ is the left adjoint of π. Then π∘σ = id, which is the identity
cl(Z) ∩ U = Z, and σ∘π ≤ id.

The composite c(X) = σπ(X) = cl(X ∩ U) is a **kernel (interior)
operator** on Q′:
- it is monotone;
- c(X) ≤ X;
- it is idempotent: c(c(X)) = cl(cl(X ∩ U) ∩ U) = cl(X ∩ U).

Its image {X ∈ Q′ : X = cl(X ∩ U)} is isomorphic to P_U via π. This is
what [AudW′] calls the closure. It is a closure in A, cl(·), and a kernel
operator on Q′.

**Homotopy equivalence.** A monotone pair with πσ = id and σπ ≤ id gives
Δ(π)Δ(σ) = id. Quillen's order-homotopy lemma (f ≤ g ⇒ Δ(f) ≃ Δ(g); proved
at chain level in [AudC] §B.2) gives Δ(σ)Δ(π) ≃ id. So
Δ(Q′) ≃ Δ(P_U), and χ̃(Δ(Q′)) = χ̃(Δ(P_U)).

Hall's theorem on the finite bounded poset Λ(V^U), with proper part P_U,
gives χ̃(Δ(P_U)) = μ_{Λ(V^U)}(0, U). This is (−1)^k m(V^U) by the
definition of m ([GT] §0). That proves the formula in (b).

COMPUTED, on every case-(b) pair, with Q′ and P_U enumerated
independently:
- `[pi]`: X ∩ U is a flat of A^U and lies in P_U;
- `[sigma]`: cl(Z) ∈ Q′, where the g-stability, the membership in Λ(V), the
  properness and the meeting with U are all re-checked;
- `[adj]`: Z ≤ π(X) ⇔ σ(Z) ≤ X for every pair (X, Z);
- `[pisig]` and `[sigpi]`;
- `[cl]`: σπ(X) = cl(X ∩ U), and it is idempotent;
- `[hall]`: χ̃(Δ(Q′)) = χ̃(Δ(P_U)) = S(g).

Negative control `neg:noclose`: σ′(Z) = Z, with the closure dropped, is
**not** a flat of A on many Z. So the closure is needed.

## 4. m(V^U) ≥ 1, including non-pointed cones (PROVEN)

Write W′ = V^U. W′ is a top-cone of an essential arrangement of rank k. It
need not be pointed: its lineality space is L ∩ U, which is often ≠ 0.

- *k = 1.* A^U is {0} in the line U. Λ(W′) = {0, U}, so m = 1. This
  includes W′ = U, which is non-pointed.
- *k ≥ 2.* [GT] Theorem 1 applies to **every** top-cone of an essential
  arrangement, pointed or not. It is proved for non-pointed V in [GT] §1.1,
  with the lineality space handled by the sphere fibers of Step 2. So
  Δ(P_U) ≃ ⋁^{m(W′)} S^{k−2}, and m(W′) = rank H̃_{k−2}(Δ(P_U)).
- *A nonzero class.*
  - Pick any chamber C of W′. Since A^U is essential, C is a pointed
    polyhedral cone.
  - F ↦ span F is an order isomorphism from the proper faces of C onto
    Λ̄(C) ⊆ P_U, because a face of a pointed cone is C ∩ span F.
  - So Δ(Λ̄(C)) is the barycentric subdivision of ∂C ∩ S ≅ S^{k−2}, and its
    fundamental class ρ_C ([AudC] §B.1) is a (k − 2)-cycle in Δ(P_U).
  - It is nonzero: its coefficients are ±1 on distinct chains.
  - Δ(P_U) has no (k − 1)-simplices, because proper flats have dimension
    1, …, k − 1. So there are no boundaries in degree k − 2, and [ρ_C] ≠ 0.
  - Hence m(W′) ≥ 1.

**Non-pointed W′ is where the earlier argument could have failed, and it does
not.** The argument never uses a property of W′ beyond Theorem 1. The
chamber C is always pointed, even when W′ is not.

The same argument with g = 1 gives **m(V) ≥ 1 for every top-cone V**
([AudW′] §2 remark). Two extreme non-pointed cases are classical:
- V = all chambers gives m = |μ(L(A))| (Folkman);
- V = a half-space gives Λ(V) = L(A), and again m = |μ(L(A))| ≥ 1.

**Dependence.** Theorem 1 is used essentially. Without the vanishing of
H̃_{<k−2}, the Euler characteristic alone would not bound m below. Theorem 1
is PROVEN in [GT] given the poset fiber theorem, or [AudA] Prop. A in its
place, and the cell facts.

COMPUTED:
- `[homol]`: the reduced Betti numbers of Δ(P_U) over Q are exactly
  {k − 2 : m(V^U)} on every case-(b) pair. This is computed from ranks of
  the boundary maps (F_p ranks, exact here by §7), so it checks Theorem 1
  for each V^U, not only its Euler characteristic.
- `[m(V)]`: m(V) ≥ 1, with homology concentrated in degree d − 2, for
  every top-cone of every test arrangement, pointed or not.
- `[rho]`: for a chamber C of V^U, ρ_C has ∂ρ_C = 0 (reduced complex), lives
  in Δ(P_U), and has one nonzero coefficient per complete flag, on distinct
  chains.
- Negative control `neg:rho+1`: with all signs +1, the chain is not a
  cycle.

## 5. The χ-form and the sign (PROVEN)

- *Sign.* A real matrix of finite order is diagonalizable over C with
  eigenvalues on the unit circle. Write r for the multiplicity of −1 and c
  for the number of conjugate pairs. Then d = k + r + 2c and
  det g = (−1)^r = (−1)^{d−k}. So (−1)^d det g = (−1)^k.
- *Terms.* Let X ∈ M with X ∩ U = 0.
  - By [FP] Lemma B(b), X ⊆ L. The reason is that p̄ ∈ X ∩ U = 0 is
    relatively interior in X ∩ |V|, so X ∩ |V| = X.
  - det(g|_X) = (−1)^{dim X}, by the sign rule applied to g|_X, which has no
    fixed vector.
  - By [FP] Lemma A, μ_M(X, R^d) = μ(Λ(V_X)^ḡ) = (−1)^{codim X} det(ḡ) χ_{V_X}(ḡ).
    Since det g = det(g|_X) det ḡ, this equals (−1)^d det(g) χ_{V_X}(ḡ).
- *Conclusion.* Σ χ_{V_X}(ḡ) = (−1)^d det(g) S(g) = (−1)^k S(g). This is
  m(V^U) in case (b) and 0 in case (a).

COMPUTED:
- `[sgn]`: the sign identity, with det computed exactly.
- `[Lb]`: X ∩ U = 0 implies X ⊆ L.
- `[chi]`: each χ_{V_X}(ḡ) is computed in its own quotient arrangement
  A_X/X, in coordinates on R^d/X, with ḡ solved from q g = ḡ q. It does
  **not** go through the interval [X, R^d] of M, so Lemma A is tested rather
  than used. The sum equals m(V^U), or 0, on every pair.

## 6. Notes on the write-up (not mathematical fixes)

1. The header of Theorem W″ lists as inputs "[GT] Lemma 0.1, [GT] Theorem 1,
   P. Hall's theorem, Quillen's order-homotopy lemma". Part (c) also uses
   [FP] Lemma A, [FP] Lemma B(b) and the sign rule [AudFP] §A.1(i). The
   proof of (c) cites them, but the header does not. Part (b) uses the
   averaging argument of [FP] Lemma B(a), as fixed in [AudFP] §C.1.
2. In "V^U is a top-cone of A^U", the case where two hyperplanes of S_max
   restrict to the same hyperplane of A^U is left implicit. It is settled by
   full-dimensionality (§2 step 3).

Neither changes a statement. Per the standing constraints, no existing note
was edited.

## 7. Computations (COMPUTED)

`compute/audit_theorem_w2.py`, plain Python 3, exact `Fraction` arithmetic,
with no floating point. It imports nothing from the repository. The one
exception to rational arithmetic is the Betti numbers, which use ranks over
F_p with p = 2^31 − 1. This is rigorous here:
- rank over F_p ≤ rank over Q, so each F_p-Betti number bounds the
  Q-Betti number from above;
- both have the same alternating sum, χ̃;
- so whenever the F_p answer is concentrated in a single degree, as every
  checked case is, the Q answer is identical.

The method differs from the earlier audits:
- The faces of A are found flat by flat. For each flat Y, the chambers of
  the restriction A^Y are enumerated by sign vectors, extended one
  hyperplane at a time. Each candidate is kept iff its strict system is
  feasible by exact **Fourier–Motzkin elimination**. Earlier audits used
  covector closure of cocircuits.
- Top-cones are all distinct chamber sets reachable by successive
  one-hyperplane restrictions. One cone is taken per G-orbit, and every
  g ∈ Stab_G(V) is tested.
- A^U and V^U are built in coordinates on U from their own faces. Each
  χ_{V_X}(ḡ) is built in its own quotient arrangement.
- Homology is computed over F_p, which is exact for the concentrated
  answers checked, by the argument above.

**Arrangements.** None was used by the earlier audits of Prop. W, Prop. W′
or G\*. Those used A_3, B_3, A_4, D_4, F_4, B_5, D_5, tetra7 and hex7.

| name | d | hyperplanes | G | notes |
|---|---|---|---|---|
| coord3 | 3 | x_i = 0 | signed permutations, 48 | the reflection group is only Z_2^3; permutations lie outside it |
| G2 | 2 | a, b, a−b, a+b, 2a−b, a−2b (hexagonal-lattice basis) | dihedral, 12 | control: every g ≠ 1 has Fix in a hyperplane or Fix = 0 |
| A2xA1 | 3 | a, b, a−b, c | D_6 × Z_2, 24 | non-orthogonal matrices in these coordinates |
| coordsum3 | 3 | x_i, x_1+x_2+x_3 | S_3 × Z_2, 12 | not a reflection arrangement |
| cyc3 | 3 | x_i, x_i + 2x_{i+1}, x_1+x_2+x_3 | ⟨cyclic shift, −1⟩, 6 | no reflection symmetries |
| K4 | 4 | x_i, Σx_i | S_4 × Z_2, 48 | |
| cyc4 | 4 | x_i, x_i + x_{i+1} (mod 4), Σx_i | dihedral 8 × Z_2, 16 | |
| K5 | 5 | x_i, Σx_i | S_5 × Z_2, 240 | d = 5 |

**Results** (archived in `compute/output/audit_theorem_w2.txt`; every
asserted check passes; the full run takes about 4 minutes).

Per arrangement:
- "W2a" counts the pairs (V, g) with Fix(g) in a hyperplane;
- "W2b, g ≠ 1" counts the pairs with Fix(g) in no hyperplane and g ≠ 1;
- the g = 1 pairs, one per cone orbit, are counted separately.

| name | chambers | top-cones (non-pointed) | cone orbits | pairs | W2a | W2b, g = 1 | W2b, g ≠ 1, by k = dim Fix g | of which V^U non-pointed | max m(V^U), g ≠ 1 |
|---|---|---|---|---|---|---|---|---|---|
| coord3 | 8 | 27 (19) | 4 | 66 | 40 | 4 | k=1: 10, k=2: 12 | 17 | 1 |
| G2 | 12 | 73 (13) | 10 | 27 | 17 | 10 | — | — | — |
| A2xA1 | 12 | 57 (33) | 8 | 54 | 36 | 8 | k=2: 10 | 8 | 1 |
| coordsum3 | 14 | 71 (33) | 13 | 43 | 7 | 13 | k=1: 6, k=2: 17 | 10 | 2 |
| cyc3 | 38 | 505 (99) | 87 | 98 | 3 | 87 | k=1: 8 | 2 | 1 |
| K4 | 30 | 231 (131) | 21 | 180 | 30 | 21 | k=1: 18, k=2: 54, k=3: 57 | 63 | 3 |
| cyc4 | 102 | 2,809 (841) | 228 | 385 | 29 | 228 | k=1: 8, k=2: 42, k=3: 78 | 40 | 7 |
| K5 | 62 | 715 (473) | 30 | 840 | 130 | 30 | k=1: 72, k=2: 216, k=3: 253, k=4: 139 | 361 | 4 |
| **total** | | 4,488 | 401 | 1,693 | 292 | 401 | 1,000 | 501 | 7 |

The maximum of m(V^U) over all case-(b) pairs, including g = 1, is 20,
reached on cyc4.

| check | statement | checks | failures |
|---|---|---|---|
| `[W2b]` | Fix g in no hyperplane ⇒ S(g) = (−1)^k m(V^U) | 1,401 | 0 |
| `[m>=1]` | m(V^U) ≥ 1 | 1,401 | 0 |
| `[W2a]` | Fix g in a hyperplane ⇒ S(g) = 0 | 292 | 0 |
| `[hall]` | S(g) = χ̃(Δ(Q′)) = χ̃(Δ(P_U)) | 1,401 | 0 |
| `[pi]`, `[sigma]` | π and σ well defined | 1,401 each | 0 |
| `[adj]` | Z ≤ π(X) ⇔ σ(Z) ≤ X, for all pairs | 1,401 | 0 |
| `[pisig]`, `[sigpi]` | π∘σ = id, σ∘π ≤ id | 1,401 each | 0 |
| `[cl]` | σ∘π = cl(· ∩ U), idempotent | 1,401 | 0 |
| `[homol]` | H̃_*(Δ(P_U); Q) = Q^{m(V^U)} in degree k − 2 only | 1,401 | 0 |
| `[rho]` | chamber cycle of V^U: nonzero cycle on distinct chains (k ≥ 2) | 1,279 | 0 |
| `[chi]` | χ-form (c), each term in its own quotient A_X/X | 1,693 | 0 |
| `[Lb]` | X ∩ U = 0 ⇒ X ⊆ L | 1,693 | 0 |
| `[sgn]` | (−1)^d det g = (−1)^k | 1,693 | 0 |
| `[VUcone]`, `[VU=]` | V^U consistent and \|V^U\| = \|V\| ∩ U | 1,401 each | 0 |
| `[fixch]` | #V^g = #chambers(V^U) ≥ m(V^U), with equality if V^U is pointed | 1,401 | 0 |
| `[m(V)]` | m(V) ≥ 1, and homology only in degree d − 2, for every top-cone | 4,488 × 2 | 0 |
| `[G]` | each group element preserves A and has finite order | 406 | 0 |

**Positive controls** (all fire):
- the chamber counts 8, 12, 12, 14, 30, 62;
- Folkman: m(all chambers) = |μ(L(A))| on all 8 arrangements;
- `[pointed]`: m(V) = #V on all 2,846 pointed cones;
- G2 has no case-(b) pair with g ≠ 1, as expected for a rank-2 reflection
  arrangement with its full reflection group;
- the unit tests: Fourier–Motzkin rejects x > 0, −x > 0; the Betti numbers
  of the boundary of an octant are {1 : 1}.

**Negative controls** (each wrong statement must fail somewhere, and does):
- `neg:nosign`, S(g) = m(V^U) without (−1)^k: fails on 652 pairs;
- `neg:m(V)`, S(g) = (−1)^k m(V), the whole cone in place of V^U: fails on
  571 pairs;
- `neg:#Vg`, #V^g in place of m(V^U): fails on 644 pairs. That is exactly
  the number of case-(b) pairs with V^U non-pointed. So on this data
  m(V^U) = #V^g iff V^U is pointed;
- `neg:noclose`, σ(Z) = Z without closure: Z is not a flat of A in 4,653
  instances;
- `neg:rho+1`, the chamber cycle with all signs +1: not a cycle on all
  1,279;
- `neg:nohyp`, "S(g) = 0 for all g ≠ 1" (Prop. W′ without its hypothesis):
  fails on 1,000 pairs, which are all the case-(b) pairs with g ≠ 1.

## Reproduce

From `compute/` (plain Python 3; no third-party packages):

    python3 audit_theorem_w2.py > output/audit_theorem_w2.txt   # ~4 min; ends "ALL CHECKS PASSED", exit 0
    python3 audit_theorem_w2.py --quick                           # ~5 s: coord3, G2, A2xA1, coordsum3, cyc3
    python3 -m unittest test_audit_theorem_w2                     # ~1 s: FM, Betti, and theorem controls

The archived log is `compute/output/audit_theorem_w2.txt`.
