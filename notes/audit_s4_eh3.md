# Independent check of (S4) for e_H = 3 (`audit_theorem_e.md` §4.2)

This note checks one claim, adversarially: the proof proposed in
`notes/audit_theorem_e.md` §4.2 ("[Aud]", merged 003e5aa) that in Theorem S of
`notes/theorem_e_equivariant_wedge.md` ("[E-note]"), consequence (S4) holds for
e_H = 3:

> **Claim.** If e_H = dim Fix(H) = 3, then T^H ≃ ⋁^{m_H} S^1.

[E-note] lists this case as "proved in the audit, not independently checked". The
computation here is new code, `compute/audit_s4_eh3.py` ("[S4]"). It imports nothing from
the repository: not [Aud]'s `audit_theorem_e.py`, and not [E-note]'s script.

Notation is that of [E-note] §0:
- V is a pointed top-cone, and G is a finite group preserving A and |V|.
- For H ≤ G, U = Fix(H), e_H = dim U, and m_H is the number of chambers of V fixed by H.
- Q′ is the poset of faces F ≠ O of V that are not chambers. X = Δ(Q′), and
  T = Δ(Λ̄(V)).

## Verdict

| Item | Verdict |
|---|---|
| **The claim** T^H ≃ ⋁^{m_H} S^1 for e_H = 3 | **HOLDS** |
| **[Aud] §4.2's proof** | **FIXABLE.** The conclusion is right and every step is valid, but the picture is wrong. When m_H ≥ 1, X^H has **no** 2-simplices: it is already a graph, so the collapse step is vacuous. The 2-dimensional case occurs only when m_H = 0, and that case is already covered by Corollary F2. Replace the proof with the dimension argument of §1 |
| **Computation** | 0 failures in 22,215 e_H = 3 pairs: B_3, B_4, and type A with n ≤ 6 (§3). X^H is a graph in all 831 pairs with m_H ≥ 1, 43 of them with H ≠ 1. The positive control fails, as it must |

**In one line.** When m_H ≥ 1, every non-chamber H-stable face meets U = Fix(H) in a cone
of dimension 1 or 2. So Q′^H has height ≤ 2, X^H is a graph, and (S1) fixes it up to
homotopy. (S4) is then proved for every e_H, as [Aud] says. The proof is simpler than
[Aud]'s.

---

## 1. A shorter proof: X^H is a graph

**Lemma D.** Let V be pointed, H ≤ G, U = Fix(H), and suppose m_H ≥ 1. Then for every
F ∈ Q′^H we have 1 ≤ dim(F ∩ U) ≤ e_H − 1. If F < F′ in Q′^H, then
dim(F ∩ U) < dim(F′ ∩ U). Hence every chain of Q′^H has at most e_H − 1 elements, and
dim X^H ≤ e_H − 2.

*Proof.*
- **Upper bound.** F is not a chamber, so its sign vector has a zero: F ⊆ h for some
  hyperplane h ∈ A. Let C be a chamber of V fixed by H. By Lemma F(a), C ∩ U ≠ ∅. C is
  open and disjoint from h, so U ⊄ h. Hence F ∩ U ⊆ h ∩ U, which has dimension e_H − 1.
- **Lower bound.** F ∩ U ≠ ∅ by Lemma F(a). It is a cone and does not contain 0, since 0
  lies only in O ≠ F. So it contains a ray, and its dimension is ≥ 1.
- **Strictness.** By Lemma F(b), F ↦ F ∩ U is an order isomorphism onto faces of the
  arrangement A^U in U. Faces of a central arrangement that are strictly related in the
  face order have strictly smaller dimension: F ∩ U lies in the relative boundary of the
  relatively open convex cone F′ ∩ U.
- **Chains.** The dimensions along a chain are strictly increasing in {1, …, e_H − 1}. ∎

**Corollary ((S4), e_H = 3).** Let e_H = 3.
- If m_H = 0, then T^H is contractible by Corollary F2.
- If m_H ≥ 1, then X^H is a graph by Lemma D. T^H ≃ X^H by Corollary F1. By (S1),
  H̃_*(X^H) is ℤ^{m_H} in degree e_H − 2 = 1 and zero otherwise, so X^H is connected
  with b_1 = m_H.
- A connected graph with b_1 = m is homotopy equivalent to ⋁^m S^1 (contract a spanning
  tree). So T^H ≃ ⋁^{m_H} S^1. ∎

Lemma D uses only Lemma F(a), (b) and Corollary F1, all of which [Aud] audited. It is the
same dimension count that [E-note] uses for e_H ≤ 2 ("clear from dimension"), carried
one dimension further. It also sharpens two remarks:
- for e_H = 2, X^H is 0-dimensional, not "≤ 1-dimensional" as [Aud] §4.1 says (harmless);
- the hypothesis m_H ≥ 1 is needed. If U lies in a hyperplane of A, which forces
  m_H = 0, then 3-dimensional cells of A^U are non-chamber faces, and X^H can be
  2-dimensional. [S4] finds exactly this in every m_H = 0 pair (§3).

## 2. [Aud] §4.2, step by step

- **"X^H is planar."** Correct. K ∩ U ∩ {φ = 1} is a convex polygon cut into convex cells
  by A^U, and a point chosen in each cell gives a straight-line embedding of Δ(Q′^H).
- **"… a straight-line 2-dimensional subcomplex L."** This is **wrong when m_H ≥ 1**,
  the only case that needs proof.
  - A 2-simplex of Δ(Q′^H) is a 3-chain v < e < c of Q′^H, with c a 2-cell of the polygon.
  - The 2-cells of the polygon are the 3-dimensional faces of A^U in K. When m_H ≥ 1 these
    are exactly C ∩ U for the H-fixed chambers C. Those are chambers, so they are not in Q′.
  - So L is the barycentric subdivision of the 1-skeleton of the polygon's cell
    structure, and D = ∅.
  - [S4] confirms this: Q′^H has height 2 in every m_H ≥ 1 pair (§3).
- **"L collapses to a graph."** The argument is valid for any finite straight-line
  2-complex in the plane.
  - One small gap: the proof needs an edge with Ω on one side. ∂Ω ⊆ ∂D is a union of
    pieces of edges, and contains a point in the relative interior of some edge e. Near
    that point, one side of e lies in Ω. So e is in exactly one 2-simplex. (Two 2-simplices
    on the same side of e would overlap.) The whole of e need not lie in ∂Ω.
  - When m_H ≥ 1, D = ∅ and the induction starts and ends at zero 2-simplices.
  - It does real work only when m_H = 0, where Corollary F2 already gives
    contractibility.
- **"Conclusion."** Correct: connected by (S1), with H_1 = ℤ^{m_H}.

**Fix.** Replace [Aud] §4.2 by Lemma D and its Corollary. Or keep it, and add one
sentence: "when m_H ≥ 1, the 2-cells of the polygon are the H-fixed chambers, so L has no
2-simplices and is already a graph." Either way the conclusion stands, and so does the
statement in [E-note] §3.1 that (S4) holds for every e_H.

## 3. Computation

[S4] checks every pair (V, H) with e_H = 3 in these families. In each pair it computes
T^H = Δ(Λ̄(V)^H) from the H-stable flats spanned by faces of V.
- It takes the Stong core (removing beat points preserves the homotopy type).
- If the core still has 3-element chains, it applies elementary simplicial collapses to
  its order complex.
- **PASS** means the result is a connected graph with b_1 = m_H, so T^H ≃ ⋁^{m_H} S^1.
- Independently, it records the maximal chain length of Q′^H, which tests Lemma D.

Faces are sign vectors of sample points on an integer grid: {−n, …, n}^n for B_n, and
{0, …, n−1}^n for the braid arrangement (all ordered set partitions). Flats are keyed by
their zero sets. e_H is computed from characters: (1/|H|) Σ_h tr(h), and on ℝ^n/ℝ1 the
trace of ±P is tr(±P) ∓ 1.

| Family | e_H = 3 pairs | m_H ≥ 1 (of which H ≠ 1) | m_H = 0 | PASS | max chain of Q′^H when m_H ≥ 1 / m_H = 0 |
|---|---|---|---|---|---|
| **[B3]** all 778 pointed top-cones of B_3 (of 940 proper), H ≤ stabilizer in W(B_3) | 778 | 778 (0) | 0 | 778 | 2 / — |
| **[B4]** all 54,448 pointed top-cones of B_4 (of 60,200 proper), H = ⟨s⟩ for each reflection s ∈ W(B_4) with sV = V | 20,960 | 0 (0) | 20,960 | 20,960 | — / 3 |
| **[A]** all 295 connected posets with 3 ≤ n ≤ 6 (3 + 10 + 44 + 238), G = full stabilizer of V in S_n × {±1}, every subgroup | 477 | 53 (43) | 424 | 477 | 2 / 3 |

So there are **0 failures in 22,215 pairs**, and **0 failures of Lemma D**.
- **Where the claim has content.** There are 831 pairs with m_H ≥ 1. In all of them Q′^H
  has height exactly 2, so X^H is a graph. This includes the 43 type-A pairs with H ≠ 1.
  These occur at n = 6, where H = ⟨−σ⟩ for a fixed-point-free involutive
  anti-automorphism σ that fixes a linear extension; e.g. the 6-chain with the reversal.
  For −σ with k 2-cycles and f fixed points, e = k, so e = 3 first occurs at n = 6.
- **Where [Aud]'s collapse step does real work.** There are 21,384 pairs with m_H = 0. In
  all of them Q′^H has height 3, so X^H is genuinely 2-dimensional, and the reflecting
  or fixed plane lies in a hyperplane of A. T^H is certified contractible in each, as
  Corollary F2 says.
- **Why B_4 has only m_H = 0.** An orthogonal H with dim Fix(H) = 3 fixes a hyperplane
  pointwise, so H = {1, s} with s the reflection in it. Every reflection of W(B_4) is in a
  hyperplane of A, which meets no chamber. [S4] therefore enumerates only these H for
  B_4, rather than all subgroups.
- **Why B_3 has only H = 1.** e_H = 3 = d forces H to act trivially.

**Controls (`[CTL]`).** Each one must fire, and each one does.
- **Positive control: (S4) must fail.** V is the non-pointed half-space {x_1 ≥ 0} of
  B_3, with H = 1 and e_H = 3. Λ̄(V) is the whole proper part of the intersection lattice
  of B_3, so T ≃ ⋁^{15} S^1, but m = 24. [S4] reports b_1 = 15 ≠ 24, so the prediction
  fails, as it must.
- **The certifier refuses a 2-sphere.** For the face poset of the octahedron boundary it
  reports "not-certified". It accepts the 2-simplex (b_1 = 0) and the crown (b_1 = 1).
- **The subgroup enumerator.** It finds S_3: 6, S_4: 30, W(B_3): 98 subgroups.
- **The dimension detector fires.** It reports height 3 on all 21,384 m_H = 0 pairs. So
  "height 2 when m_H ≥ 1" is not an artifact of the instrument.
- **Poset counts.** There are 3, 10, 44 and 238 connected posets for n = 3…6, which are
  the known values.

**Not checked.** Type A with n = 7 (the first case with H = ⟨−σ⟩, σ having one fixed
point and three 2-cycles), and B_n for n ≥ 5. These are not needed for the verdict, which
rests on the proof in §1.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process, imports nothing
from the repository):

    python3 audit_s4_eh3.py --nmax 6 > output/audit_s4_eh3.txt   # ~13 min, ends "ALL CHECKS PASS: True", exit 0
    python3 audit_s4_eh3.py --nmax 5 --skip-b4                    # ~7 s
    python3 -m unittest test_audit_s4_eh3                         # controls, 6-chain, claw

Output tags:
- `[CTL]`: controls.
- `[B3]`, `[B4]`, `[A]`: families. Each prints the pair counts, the PASS/FAIL tally, the
  histogram of max chain length of Q′^H split by m_H ≥ 1 and m_H = 0, and the number of
  failures of Lemma D.
