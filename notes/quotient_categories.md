# Quotient categories and wedges of spheres: scoping

**The idea under test.** The wedge theorems for OP(P) depend on a category with a
quotient/partition property, and that property might explain many of the wedges of
spheres that appear in combinatorics. Concretely: is there a category C with a class of
admissible quotients X → X/π, giving a lattice Q(X) for each object, whose axioms force
the proper part Q̄(X) to be a wedge of spheres, equivariantly for Aut(X), with the number
of spheres given by a natural invariant?

**Verdict: STOP** (§4). This note was audited in `notes/audit_quotient_categories.md`
([AudQC]). STOP stands; the reasons below are the corrected ones. In short:
1. **The repo's proofs have two sources of sphericity, and neither is a quotient axiom.**
   - **Convexity (R1)**, in [GT] and [TE]. These are *real-points* axioms: Hom(X, ℝ) is a
     closed polyhedral cone; quotients are cut out by flats; orbit quotients are fixed
     subspaces (§1). Any category satisfying (R1) has cone lattices as its Q(X), so that
     framework is framework (a) of `notes/general_theory.md` renamed.
   - **Complementation (C)**, in Route C (`notes/lean_js_route.md` §3). Meet-closure, a
     complement condition and the upper-interval axiom (Q2) give homology concentration
     for OP(P) with no convexity at all (§1.5). **This is the part of the quotient idea
     that does real work:** it is a genuinely non-convex, lattice-level mechanism, and the
     repo uses it. It does not reverse STOP, because (C) is Björner–Walker
     complementation, one of the three known mechanisms that the reversal test of §4
     excludes.
2. **The bare interval axioms force nothing** (§2.3).
   - Upper intervals are quotients of the quotient, and lower intervals are products over
     the fibers. With a single fiber allowed (as for Tits buildings, §2), (Q1)–(Q3) hold
     for *every* finite lattice, including the face lattice of RP², which has torsion. So
     "(Q1)–(Q3) ⇒ wedge" is **false** outright (COMPUTED in [AudQC] `[INT]`).
   - Even with partition-type data, the axioms hold for finite G-sets, where Q(G/1) is the
     subgroup lattice. That lattice is not Cohen–Macaulay in general (COMPUTED, A_4, S_4
     and A_5). Whether every such lattice is at least a non-pure wedge is Shareshian's
     conjecture, which is OPEN. A theorem deriving wedges from the partition-type axioms
     would prove it.
3. **The interval axioms are already in the literature** (§3): Schmitt's hereditary
   families, and Vallette's operadic partition posets.
   - For operadic posets, Koszulness and Cohen–Macaulayness are *equivalent* (Vallette
     2007, Thm 9). That is a reformulation of sphericity, not a source of it.
   - OP(P) is not a Vallette poset with blocks labelled by their restrictions and finite
     𝒫(2) (Proposition 3.1, PROVEN). Other labellings are OPEN.
4. **What the framework does explain** is limited to the support-map mechanism:
   - It explains OP(P) (already done in the repo).
   - It explains the d-divisible partition lattices, a known non-geometric wedge family
     (§2.2). That explanation coincides with Ehrenborg–Jung 2013.
   - It explains a family of mixed-graph lattices that interpolates between bond lattices
     and OP(P) (§2.1). That family is an instance of the cone wedge theorem.

Tags (every claim carries one):
- **PROVEN**: a proof is given here, or in the repo note cited, with its inputs named.
- **CITED**: a published result. We say whether we read it.
- **COMPUTED**: checked by `compute/quotient_categories.py` (Reproduce). The output is
  archived in `compute/output/quotient_categories.txt`.
- **OPEN**: not settled.

Abbreviations:
- [GT] = `notes/general_theory.md`. Its Theorem 1 (the cone wedge theorem) and Theorem 2
  (cone Zaslavsky) are PROVEN and audited.
- [TE] = `notes/theorem_e_equivariant_wedge.md`. Theorem E is **PROVEN, audited
  (`notes/audit_theorem_e.md`)**.
- [AudE] = `notes/audit_theorem_e.md`.
- [JSR] = `notes/lean_js_route.md` (Route C); [AudJSR] = `notes/audit_lean_js_route.md`.
- [AudQC] = `notes/audit_quotient_categories.md`, the audit of this note; its
  computations are `compute/audit_quotient_categories.py`.
- [OM] = `notes/oriented_matroid_cones.md`.
- [MO] = `notes/mo17370_wedges_of_spheres.md`.
- [PATE] = `notes/prior_art_theorem_e.md`.
- [Thm] = `notes/poset_jks_theorem.tex`.

Conventions:
- Partitions are ordered by refinement, with the finest partition 0̂ at the bottom.
- Λ(V) is ordered by inclusion of subspaces, so Λ(C_P) ≅ OP(P)^op ([GT §1.3]).
- K_X denotes a closed cone, and e(P) = |Lin P|.

---

## 1. The abstraction: what the proofs actually use

### 1.1 The objects

For a finite poset P:
- The **real points** are K_P = Hom(P, ℝ) = {x ∈ ℝ^P : a ≤ b ⇒ x_a ≤ x_b}, the closed
  order cone C̄_P.
- The **ordered quotients** are the order-preserving surjections P → [k] onto a chain.
  They are exactly the faces of K_P in the braid arrangement, and are recorded as ordered
  set partitions (B_1, …, B_k) with a ≤ b ⇒ block(a) ≤ block(b). Write O(P) for the poset
  of these faces.
- The **support map** s : O(P) → Q(P) = OP(P) forgets the order of the blocks. Its image
  is exactly OP(P) ([GT §1.3], via Prop. 2.2 of `notes/cone_lune_lie_theory.md`).

### 1.2 The axioms, each tied to the step that uses it

Read with X = P, π ∈ Q(X), and Y_π = {x constant on the blocks of π}.

| Axiom | Statement for posets | Used in | Tag |
|---|---|---|---|
| **(R1) Convex real points** | K_X is a closed polyhedral cone that is a union of faces of a real central arrangement, and π ↦ Y_π identifies Q(X)^op with Λ(K_X), the lattice of spans of faces | [GT] Thm 1, Steps 2 and 4: K_X ∩ Y ∩ S is contractible or a sphere (Lemma 0.2), and K_X ∩ S is a ball or a sphere whose top cells are the chambers | PROVEN for posets ([GT §1.3]) |
| **(R2) Quotients are slices** | Hom(X/π, ℝ) = K_X ∩ Y_π. So the fiber of s over Q_{≥π} (coarser quotients) is O(X/π) | [GT] Thm 1, Step 2. The fiber of the support map over π is the ordered companion of the quotient X/π, so the fiber condition is (R1) for X/π | PROVEN (a map P/π → ℝ is a map P → ℝ constant on blocks) |
| **(R3) Spheres come from discrete quotients** | K_{X/π} is a linear subspace iff X/π is an antichain, i.e. π is coarser than the components. Then the fiber is a sphere; otherwise it is contractible | [GT] Thm 1, Step 3 and (1.1); Thm 2 (#V = Σ_{X ⊆ lin V} m(V_X)) | PROVEN ([GT] Lemma 0.1(b),(c)) |
| **(R4) Chambers are linear extensions** | The open chambers of K_X are the injective real points up to order, i.e. Lin(P) | sphere count: m(C_P) = e(P) for connected P (pointed), and m = e_C(P) in general by Thm 2 + Lemma 1.3 of [GT] | PROVEN ([GT] Cor. 1.4) |
| **(R5) Orbit quotients are fixed subspaces** | For H ≤ Aut(P), the orbit preorder P/H is a poset, and Hom(P/H, ℝ) = K_P^H. The H-stable faces of K_P are the pullbacks of the faces of K_{P/H} | [TE] Lemma F(a)–(b), the "restriction to Fix(H)" | PROVEN below; COMPUTED `[FIX]`. Not an independent axiom: given (R1) and a linear action it is automatic ([TE] Lemma F is proved for any finite group of linear maps preserving the arrangement and the cone, and never forms an orbit quotient) |
| **(R6) Pointedness** | P connected ⇒ lin K_P = constants, so K_P is pointed after essentialization | [TE] Lemma F(c) (an H-average of a nonzero point of a pointed cone is nonzero); [GT] pointed case (m = #V) | PROVEN ([TE §2.5]) |
| **(R7) Free action on chambers** | Aut(P) acts freely on Lin(P), for every finite P (connectedness is not needed, [AudE] §3.5; it enters only through (R6)) | [TE] Thm E (free ℤG basis §2.1, contractible singular sets) | CITED in [TE] from [Thm] cor:connected; COMPUTED there |

*Proof of (R5) (PROVEN).*
- **P/H is a poset.** An automorphism preserves height (the length of the longest chain
  below an element), so each orbit has constant height. If a < b then height(a) <
  height(b), so every arc between distinct orbits strictly increases height, and the
  orbit preorder has no cycle.
- **Stable faces are pullbacks.** Let F = (B_1, …, B_k) be an H-stable face. Then h ∈ H
  permutes the blocks while preserving their order (it preserves ≤, so it maps the face's
  chain to a chain of the same face). An order-preserving bijection of a finite chain is
  the identity, so every block is H-stable, and hence a union of orbits. Then F is the
  pullback of the ordered partition (B_i/H) of P/H. That ordered partition is a face of
  K_{P/H}: if O ≤ O′ in P/H, then some a ∈ O and b ∈ O′ have a ≤ b, so
  block(O) ≤ block(O′).
- **Conversely**, the pullback of a face of K_{P/H} is H-stable and order-compatible.
- This is Lemma F(b) of [TE] in the braid case: Fix(H) = functions constant on orbits,
  and the restricted arrangement is the braid arrangement of the orbit set. ∎

COMPUTED (`[FIX]`): on all 602 pairs (P, g) with P naturally labeled, n ≤ 5, and
1 ≠ g ∈ Aut(P), the H-stable faces equal the pullbacks, and the orbit preorder was never
cyclic. Control: using the orbits of g² instead of g is rejected on all 478 pairs where
g² has more orbits.

### 1.3 What is *not* used

**PROVEN, by inspection of [GT] Thm 1, Thm 2 and [TE] §§1–2.** These proofs never use a
lattice-closure property of Q(X) inside the partition lattice. (This is a statement about
[GT] and [TE] only. Route C, [JSR] §3, does use meet-closure; see §1.5.)
- **Closure under refinement is false.** For the chain a < b < c, the one-block partition
  is acyclic, but its refinement {a, c} | {b} is not.
- **Closure under the joins of Π_n is false.** For the chain a < b < c, the partitions
  {a, b} | {c} and {a} | {b, c} are both acyclic, but their Π_n-join {a, c} | {b} is not.
- **Closure under common refinement is true** (span F + span G = span(FG) for the Tits
  product). It is not used in [GT] or [TE]. It *is* used in Route C (§1.5).
- The proofs of [GT] and [TE] use the poset Q̄(X), the support map, and the convexity of
  the fibers. The lattice structure plays no role there.

**The categorical axioms proper.** Write
- **(Q1)**: Q(X) is a finite lattice with 0̂ = id_X and 1̂ = X → pt;
- **(Q2)**: upper intervals are quotients, [π, 1̂] ≅ Q(X/π);
- **(Q3)**: lower intervals are products over the fibers, [0̂, π] ≅ ∏_B Q(X_B).

For posets, (Q2) and (Q3) hold with X_B = P|_B (PROVEN):
- (Q2): σ ≥ π is acyclic in P iff σ/π is acyclic in P/π, because P/σ = (P/π)/(σ/π).
- (Q3): if σ ≤ π and P/π is acyclic, a cycle of P/σ projects to a closed walk in P/π,
  so it stays inside one block B. Hence σ is acyclic iff each σ|_B is acyclic in P|_B.
- So every interval of OP(P) is a product of OP lattices.

(Q2) is used, through (R2). (Q3) is also used, as localization of the cone, at partitions
σ coarser than the components:
- [GT] Thm 1, Step 3 uses Lemma 0.1(c): for a flat X ⊆ lin V, [X, ℝ^d] ≅ Λ(V_X). For
  V = C_P, the interval [X, ℝ^d] is the lower interval [0̂, σ] of OP(P), and
  V_X = ∏_{B∈σ} C_{P|_B}. That is (Q3) at σ.
- [GT] Cor. 1.4 uses the same product, (C_P)_σ = ∏ C_{P|_B}, with Λ and μ multiplicative.

Both uses are derived from (R1) geometrically, so (Q3) is not an extra input there. (Q1)
is not used by [GT] or [TE]; Route C uses meet-closure (§1.5).

So the answer to "which properties of acyclic quotient do the proofs of [GT] and [TE]
use" is (R1)–(R7). Of these, only (R2) and (R5) are quotient properties, and both are
used *through* (R1): they say that the fibers of the support map, and the fixed points,
are again real-point cones of a quotient object. Two of the seven are not independent:
(R5) follows from (R1) for any linear action, and (R7) holds for every finite P (table
above). Route C uses a different set of inputs, (Q1), (Q2) and (C), in §1.5.

### 1.4 The abstract statement, and why it is a restatement

**Abstract support-map theorem (PROVEN, given [GT] Thm 1 and [TE] Thm E).** Let C be a
category with a class of quotients and a real-points functor satisfying (R1)–(R4). Then
Q̄(X) ≃ ⋁^{m(X)} S^{r−2}, with Σ_{X/π discrete} m(·) = #chambers. With (R5)–(R7) it is a
free Aut(X)-wedge.

*Proof.* (R1) makes Q(X)^op = Λ(K_X) for a top-cone K_X of an arrangement, and (R4)
identifies its chambers. This is [GT] Thm 1 and Thm 2, and [TE] Thm E (PROVEN, audited
(`notes/audit_theorem_e.md`)). ∎

The class of lattices it covers is, by (R1), exactly the class of cone lattices Λ(V). So
it adds no lattice beyond [GT] framework (a), or [OM] for oriented matroids. It is
framework (a) in categorical language. This is the first half of the STOP.

**The relaxation that does add reach.**
- Keep (R2) and the support map, but replace "K_X ∩ S is a ball or a sphere" in (R1)
  with:

  **(R1′)** the ordered companion O(X) is a Cohen–Macaulay complex (e.g. a rank-selected
  subcomplex of a Coxeter complex), and the fibers O(X/π) are contractible or spheres of
  the right dimension.
- The proof is then Quillen's fiber lemma or the Björner–Wachs–Welker fiber theorem,
  followed by the retract argument of [GT] Thm 1, Step 5.
- This is what explains the d-divisible lattices (§2.2). It is also, verbatim, the
  mechanism of Ehrenborg–Jung 2013 (§3). It is a technique, not a new framework.

### 1.5 The second mechanism: complementation (Route C)

Route C ([JSR] §3, audited HOLDS in [AudJSR]; checked over ℤ in
`notes/audit_mo17370.md` V4) proves (V): H̃_d(Δ(OP̄(P))) = 0 for d ≠ n − 3. Its inputs
are:
- **meet-closure (a strong form of (Q1)):** x ∧ π_a ∈ OP(P), where ∧ is the meet of Π_n (Lean
  `isOrderPreserving_inf`);
- **a complement condition ([JSR] Lemma M(b)):** for a minimal a and t = π_a = {a} | rest,
  the elements x ≠ 0̂ with x ∧ t = 0̂ are exactly the atoms π_ab of OP(P);
- **(Q2) at those atoms ([JSR] Lemma U):** (π_ab, 1̂) ≅ OP̄(P/π_ab).

No convexity, no cone and no arrangement appear. So the claim "only (R1) forces spheres"
is false for the repo as a whole. The abstract form is:

**Axiom (C) (complementation).** For every object X with Q̄(X) ≠ ∅ there is a t ∈ Q̄(X)
such that:
- its complements in Q(X) form an antichain;
- every complement is an atom a;
- [a, 1̂] ≅ Q(X/a) for an object X/a of the class.

**Claim (PROVEN, given Björner–Walker's homotopy complementation formula, European J.
Combin. 4 (1983), CITED from memory as in [JSR]).** In a class satisfying (Q1), (Q2) and
(C), every Q̄(X) is a wedge of spheres. The wedge is pure when all the X/a have the same
length.

*Proof.* Björner–Walker give L̄ ≃ ⋁_{a ⊥ t} Σ(Δ(0̂, a) ∗ Δ(a, 1̂)). For an atom a,
Δ(0̂, a) = ∅, so the summand is Σ Q̄(X/a). Induct on the length, with Σ∅ = S^0. ∎

**Where (C) holds.**
- **OP(P):** proved in [JSR]; COMPUTED in [AudQC] `[CMP]` on all 959 pairs (P, a minimal)
  with n ≤ 5: meet-closure, complements of π_a = the atoms π_ab, and
  |[π_ab, 1̂]| = |OP(P/π_ab)|. Control: in Π_4, t = 01|23 has the non-atom complements
  02|13 and 03|12.
- **Π_n:** by hand, t = {n} | rest.
- **Subgroup lattices, at the top level only:** [AudQC] `[CMP]` finds such a t in L(A_4),
  L(S_4) (e.g. t = A_4, whose complements are the six transposition subgroups) and L(A_5).

**This is the part of the quotient idea that does real work.** (C) is stated at the level
of the quotient lattice, uses (Q2) essentially, and gives sphericity without convexity.
**Why it does not reverse STOP:**
1. (C) is complementation, one of the three known mechanisms named in §3 (Björner–Walker,
   Kozlov, Arone–Brantner). The reversal test of §4 asks for a mechanism outside these
   three, so (C) passes the note's own test for *not* reversing.
2. Its use for OP(P) is Route C itself, already in the repo.
3. For G-sets, the induction needs (C) on every interval (H, K) of L(G), not just at the
   top. That is exactly where Shareshian's problem lives (§2.3).

Whether (C) reaches lattices where complementation is not already known to work was not
explored (OPEN).

---

## 2. Test families

| Family | Category / quotients | Verdict | Why |
|---|---|---|---|
| Π_n | sets, all quotients | **fits** | K = ℝ^n with the braid arrangement, all chambers. Folkman = [GT] Thm 1 with V = all chambers. Also OP(claw) = Π_n ([PATE §2.2]) |
| Bond lattices L(G) | graphs, contraction to connected blocks | **fits** | K = ℝ^V with the graphic arrangement A_G, all chambers (acyclic orientations) |
| Mixed graphs (§2.1) | graphs with some edges oriented; connected blocks with acyclic quotient digraph | **fits** | top-cones of A_G. Interpolates between bond lattices (no arcs) and OP(P) (complete graph, arcs = relations) |
| OP(P) | posets, acyclic quotients | **fits** (defining case) | [GT] Cor. 1.4 (Jenča–Sarkoci reproved); [TE] Thm E (PROVEN, audited (`notes/audit_theorem_e.md`)); also by complementation, Route C (§1.5) |
| Geometric lattices (Folkman) | matroids, flats | **fits with modification** | only *orientable* matroids have real points: realizable ones by [GT], all oriented matroids by [OM] Thm 1-OM. Non-orientable geometric lattices (e.g. the Fano plane, CITED as standard, not re-read) are wedges by Folkman's theorem, through semimodularity/shellability, not by this mechanism |
| Dowling lattices Q_n(G) | G-gain graphs | **fits for \|G\| ≤ 2** (types A and B, i.e. signed graphs and signed posets); **does not fit for \|G\| ≥ 3** | there is no ordered real-points functor. For cyclic G these are complex reflection arrangements, where "one side of a hyperplane" is meaningless. They are wedges because they are geometric (Folkman), which is outside the convex mechanism (CITED from memory: Dowling 1973; equivariance in Gottlieb–Wachs, not re-read) |
| d-divisible Π_n^{(d)} + 0̂ (§2.2) | sets, quotients whose fibers have sizes divisible by d (closed under composition, but no identity, so 0̂ is adjoined) | **fits with modification (R1′)** | the ordered companion is a rank-selected Coxeter complex, not a ball. Explained BY the framework: wedge PROVEN, and the count is the chamber count of the rank-selected pointed companion (COMPUTED) |
| Noncrossing NC(n) | quotients of an n-cycle by noncrossing partitions | **does not fit** (as tested) | COMPUTED: for n = 5, 6 no OP(P), P any labeled poset on [n], has NC(n)'s size, rank sizes and Möbius number. At n = 4, NC(4) = OP(P) as sets for 12 labelings of two disjoint 2-chains (a small-n coincidence: Π_4 minus one partition). Whether NC(n) is Λ(V) for a cone of a *different* arrangement is OPEN. Its wedge comes from shellability (Björner–Edelman, CITED from memory) |
| Subspace lattice / Tits building | F_q-vector spaces, all quotients | **does not fit** (no order on F_q, so no real points) | it does satisfy the interval axioms (Q2) and (Q3), with a single fiber. Solomon–Tits has the same *shape*: a contractible complex minus the open top cells opposite a chamber, Hatcher's mechanism quoted in [MO §0]. The Borel-equivariant form is Arone–Brantner Lemma 5.17 (CITED via [PATE §1.2]) |
| **Negative control**: at-most-2-to-1 quotients + 1̂ (§2.3) | sets, quotients with fibers of size ≤ 2 | **NOT a wedge of spheres** | COMPUTED: 3-torsion in H_1 for a 7-element set. Violates (Q2)/(R2): the class is not closed under composition |
| **Hardness control**: G-sets (§2.3) | G-sets, all G-quotients | **satisfies the interval axioms, not CM** | Q(G/1) = L(G). COMPUTED: A_4, S_4 and A_5 have homology below the top degree. Wedge-ness is Shareshian's conjecture, OPEN |
| **Tautological control**: intervals of any finite lattice, single fiber (§2.3) | objects [x, y], quotient by z is [z, y], fiber [x, z] | **satisfies (Q1)–(Q3), not a wedge** | the face lattice of RP² (6 vertices) has torsion (COMPUTED in [AudQC] `[INT]`) |

### 2.1 Mixed graphs (PROVEN, as an instance of [GT] Thm 1; COMPUTED)

Let G be a graph on [n] and O an acyclic orientation of some of its edges (the arcs).
Let V be the top-cone of the graphic arrangement A_G given by x_i < x_j on the arcs i → j.

**Proposition 2.1.**
- (a) Λ(V) = {π : every block induces a connected subgraph of G, and the arcs between
  distinct blocks form an acyclic digraph on the blocks}.
- (b) Δ(Λ̄(V)) ≃ ⋁^{m} S^{n−c(G)−2}, with m = m(V) ≥ 1.
- (c) Let E_0 be the set of edges whose orientation is the same in every acyclic
  orientation of G extending O. If (V(G), E_0) has the same components as G, then V is
  pointed, and m equals the number of acyclic orientations of G extending O.

*Proof.*
- (a) Flats of A_G are connected partitions. A face of V with support π is a point x,
  constant exactly on the blocks of π (generic in Y_π), with x_i ≤ x_j on the arcs. Such
  a point exists iff the arcs between distinct blocks admit a strictly increasing
  assignment of block values, i.e. iff they are acyclic. Then Lemma 0.1(a) of [GT]
  applies.
- (b) This is [GT] Thm 1, with d = n − c(G).
- (c) S_max(V) = E_0, so lin V is the flat of the components of (V(G), E_0). Pointed
  means it is the flat of the components of G (constants on components). Then [GT]
  gives m(V) = #V. ∎

**COMPUTED** (`[MIX]`): 3,902 mixed graphs (all with n ≤ 4, plus a seeded sample with
n = 5).
- Λ(V), computed geometrically from the weak orders, equals the description in (a).
- Homology is concentrated in degree n − c(G) − 2, with rank |μ| ≥ 1.
- All 2,267 pointed cases have m = #V. 1,635 non-pointed cases have m < #V.
- Control: for one edge on 3 vertices, Λ ≠ Π_3.

**Status.** Not claimed new: it is a corollary of [GT] Thm 1, and no search was made for
this family by name. It is listed because it is the natural test of whether the
"category" adds anything. It does not: the family is just more cones.

### 2.2 The d-divisible partition lattices, explained by (R1′) + (R2)

This is the known wedge family the framework explains rather than restates. The
d-divisible lattices are wedges of spheres but not geometric lattices: Wachs, EL-shelling,
CITED via Ehrenborg–Jung's introduction (read).

Let d ≥ 2, d | n, Q = Π_n^{(d)} ∖ {one block}, and S = {d, 2d, …, n − d}.

**Proposition 2.2 (PROVEN, given Quillen's fiber lemma and the shellability of rank-selected
Boolean lattices, Björner 1980 Thm 4.1; CITED via Ehrenborg–Jung §4, read).**
Δ(Q) ≃ ⋁^{β_{n−1}(S)} S^{n/d−2}, where β_{n−1}(S) is the number of permutations of
[n − 1] with descent set S.

*Proof.*
- **The object.** Take X = T, the dual claw: n above every other element. Every
  partition of T is acyclic, so OP(T) = Π_n. The faces of K_T are the ordered partitions
  with n in the last block.
- **The rank selection (R1′).** Let O′ ⊆ O(T) be the faces all of whose blocks have size
  divisible by d.
  - (B_1, …, B_k) ↦ the chain B_1 ⊂ B_1 ∪ B_2 ⊂ ⋯ of subsets of [n − 1], after
    deleting n.
  - This identifies O′ with the face poset of Δ(B_{n−1} restricted to the ranks S).
  - That complex is shellable of dimension n/d − 2. Its top homology has rank
    β_{n−1}(S): the number of top facets left over in a shelling is the number of
    permutations with descent set S. CITED, Björner 1980 and Stanley; this is
    Ehrenborg–Jung Thm 4.2.
- **The support map.** s : O′ → Q forgets the order. It is onto: order the blocks of any
  π ∈ Q so that n's block is last.
- **The fibers (R2) + (R3).** s^{−1}(Q_{≥π}) consists of the faces whose support is
  coarser than or equal to π.
  - These are the faces of K_{T/π}, rank-selection-free, because every merge of
    d-divisible blocks is d-divisible.
  - T/π is a dual claw on the blocks, with ≥ 2 elements, so K_{T/π} is pointed and not
    a subspace. Its face complex is contractible ([GT] Lemma 0.2).
- **Conclusion.** By Quillen's fiber lemma, Δ(Q) ≃ Δ(O′), which is a wedge of
  β_{n−1}(S) spheres of dimension n/d − 2. ∎

Remarks:
- The count agrees with Stanley's Möbius formula (CITED via Ehrenborg–Jung's
  introduction).
- The S_{n−1} = Aut(T) symmetry of Calderbank–Hanlon–Robinson is the automorphism group
  of the object T.

**The unpointed variant (PROVEN, same inputs plus [GT]'s retract argument).** Use all of
Π_n's companion, with no pointing.
- The fibers become spheres S^{k−2}.
- The Björner–Wachs–Welker theorem then gives Δ(rank-selected Coxeter complex) ≃
  Δ(Q) ∨ ⋁_π S^{k(π)−2} ∗ Δ(Q_{<π}), where Q_{<π} is the set of strictly *finer*
  elements of Q. This is the non-pointed [GT] Thm 1 pattern, with
  #chambers β_n(S) = m + corrections.
- **Why Q_{<π}.** BWW joins each fiber (taken below) with the part above. Here s reverses
  order from the face order to refinement, so BWW applies to s : O → Q^op, and
  (Q^op)_{>π} = Q_{<π}. The dimensions confirm it: (k−2) + (n/d − k − 1) + 1 = n/d − 2,
  the top degree. (An earlier version of this note printed Q_{>π}, which gives dimension
  2k − 4, depending on π; [AudQC] §5.2 shows it gives wrong Betti numbers, e.g.
  {0: 15, 1: 16, 2: 30} at (n, d) = (6, 2) against the true {1: 61}.)

**COMPUTED** (`[DDIV]`) for (n, d) = (4,2), (6,2), (6,3), (8,2), (9,3), (8,4):
- H̃(Δ(Q)) is concentrated in degree n/d − 2, with rank β_{n−1}(S).
- The pointed companion has the same homology.
- Every Quillen fiber is acyclic.
- The unpointed complex has rank β_n(S), and the fiber-theorem Euler identity holds.
  [AudQC] `[DDIV]` checks the corrected wedge Δ(Q) ∨ ⋁ S^{k−2} ∗ Δ(Q_{<π}) Betti number
  by Betti number: β_n(S) = 5, 61, 19, 1385, 1513, 69 in the six cases.
- Control: an unpointed fiber over a 2-block π is S^0, not acyclic.

**Status: KNOWN.** This is exactly the proof of Ehrenborg–Jung 2013, Thm 5.3
(`Π^•_c ≃ sd(Δ_c)` by Quillen, Π^{(d)}_{n} ≅ Π^•_{(d,…,d,d−1)}), read. Their
pointed set partitions are the support lattice of the dual-claw cone.
- What the framework adds is a sentence: their "pointing" is the pointedness axiom (R6).
  Their Quillen fibers are the companions of quotients (R2).
- It explains *why* the count is β_{n−1} and not β_n: the pointed cone has no lineality
  correction ([GT] Thm 2).
- That sentence is not found in Ehrenborg–Jung, which never mentions polyhedral cones.
  They do, however, realize the pointed partition lattice Π^•_n as the intersection
  lattice of the arrangement {x_i = x_j} ∪ {x_i = 0} (their Lemma 2.1). So the sentence
  is a short step from their Lemma 2.1, not a new link. It is an observation, not a
  theorem.

### 2.3 Controls

**Negative control: at-most-2-to-1 quotients (COMPUTED; matches Bouc 1992, CITED from
memory, not re-read).**
- *Definition.* Q(X) = {partitions of X with blocks of size ≤ 2} ∪ {1̂}. Its proper part
  is the face poset of the matching complex.
- *Failure of the wedge.* For |X| = 7, the proper part has reduced Betti numbers {2: 20}
  mod 2 and mod 2^31 − 1, but {1: 1, 2: 21} mod 3. So H_1 has 3-torsion, and the proper
  part is not homotopy equivalent to any wedge of spheres.
- *Instrument control.* The detector separates mod 2 from mod 3 on a 6-vertex RP^2.
- *The violated axiom* is composition closure, i.e. the upper-interval axiom (Q2), which
  is what (R2) needs. The class is closed under refinement and meets, but the composite of
  two at-most-2-to-1 maps need not be one. COMPUTED: for π = one 2-block, [π, 1̂] has 27
  elements, while the analogous lattice of X/π has 77. Without (Q2), the fiber of the
  support map over π is no longer the companion of a quotient.

**Hardness control: G-sets.** Let 𝒢 be the category of finite G-sets and all
G-equivariant quotients.
- **The interval axioms hold (PROVEN, correspondence theorem).**
  - (Q1) Q(X) is a sublattice of Π_X containing 0̂ and 1̂.
  - (Q2) [π, 1̂] ≅ Q(X/π).
  - (Q3) holds only in the orbit-twisted form: [0̂, π] ≅ ∏_{orbits of blocks} Q_{G_B}(B),
    with one block B per orbit, the fibers being G_B-sets, not G-sets. The literal
    "∏ over all blocks B" fails. So the "category" is the collection of all pairs (G, X),
    not the G-sets of one group; this is harmless for the reduction below.
  - For X = G/1, Q(X) = L(G), the subgroup lattice.
- **Not Cohen–Macaulay (COMPUTED, `[GSET]`; recomputed in [AudQC] §2.1).**
  - L(A_4): the proper part has dimension 1 but homology only H̃_0 = ℤ^4.
  - L(S_4): dimension 2, homology only H̃_1 = ℤ^12.
  - L(A_5): dimension 2, homology only H̃_1 = ℤ^60, consistent with μ(A_5) = −60 (CITED
    as Hall 1936, from memory). So L(A_5) is not CM either.
- **Wedge-ness is open.** A_4 and S_4 are solvable, so their lattices are wedges
  (Kratzer–Thévenaz, CITED from memory). In general, "every open interval in a
  subgroup lattice is a wedge of spheres" is **Shareshian's conjecture, OPEN**
  (Shareshian, *Topology of order complexes of intervals in subgroup lattices*, J.
  Algebra 268 (2003); CITED from search results, not read; a 2020 survey describes the
  case of trivial Frattini subgroup and simple composition factors as wide open).
- **Consequence.** Every open interval (H, K) of a subgroup lattice is Q̄_K(K/H) by (Q2).
  So a theorem "partition-type axioms (Q1)–(Q3) + Aut-action ⇒ wedge", applied to the
  transitive K-sets K/H, would prove Shareshian's conjecture. "⇒ wedge of
  top-dimensional spheres" is false (A_4).

**Tautological control: the bare axioms force nothing (COMPUTED in [AudQC] `[INT]`).**
Read abstractly, as in §1.3, (Q1)–(Q3) give a lattice Q(X) with no underlying set, and
§2 accepts (Q3) "with a single fiber" for Tits buildings. In that reading take any finite
lattice L:
- the objects are the intervals [x, y], with Q([x, y]) = [x, y];
- the quotient by z is [z, y], and the single fiber is [x, z].

(Q1)–(Q3) then hold tautologically. Take L = the face lattice of the 6-vertex RP² with
0̂ and 1̂ adjoined (33 elements). Its proper part has reduced Betti numbers {1: 1, 2: 1}
mod 2 and none mod 3, so it has torsion and is not a wedge of spheres.

So "(Q1)–(Q3) ⇒ wedge" is **false** outright, not merely as hard as Shareshian's
conjecture. A meaningful version must require partition-type data (Q(X) ⊆ Π_X, and (Q3)
with the fibers being the actual blocks), and for that version the G-set reduction above
is the right hardness statement. So the categorical axioms alone cannot carry the idea.
This is the second half of the STOP.

---

## 3. Prior art

**What was searched.** On 2026-10-31 we ran web searches for:
- Vallette's generalized partition posets;
- Ehrenborg–Jung's restricted partition posets;
- Batanin–Markl operadic categories with Koszul duality and partition posets;
- Kaufmann–Ward Koszul Feynman categories with posets;
- Fauvet–Foissy–Manchon finite topologies (contraction–extraction);
- Schmitt's incidence Hopf algebras (hereditary families);
- subgroup lattices that are not wedges (Shareshian);
- Gálvez-Carrillo–Kock–Tonks decomposition spaces.

**What was read.** Vallette (arXiv math/0405312v3: abstract, introduction, §§2–3,
Thm 9, the Remark after it, the §4 headings, the Hanlon–Wachs remark) and Ehrenborg–Jung
(arXiv 1312.2036: introduction, §§3–5, statements of Thms 4.2, 5.1, 5.3). Everything else
is from abstracts or search snippets and is marked so.

"Not found" means not found in these sources. It is the result of a search, not a proof
of novelty.

**Vallette 2007** (*Homology of generalized partition posets*, JPAA 208; read).
- **Setting.** A *basic-set* operad (a set operad whose composition maps are injective),
  quadratic, generated in one arity. The poset Π_𝒫(n) consists of the 𝒫-partitions:
  partitions with each block decorated by an operation.
- **Order.** λ ≤ μ when each block of λ is obtained by composing some ν ∈ 𝒫_t with the
  decorated blocks of μ that it contains. The maximal element is the partition into
  singletons, so the order is *reverse* refinement.
- **Thm 9.** 𝒫 is Koszul iff every interval [α, 1̂] is Cohen–Macaulay, and then the
  homology is the Koszul dual cooperad.
- **Examples.** Com → Π_n; Perm → pointed partitions; As → ordered partitions; t-ary Com
  → Hanlon–Wachs block sizes ≡ 1 mod t − 1; ComTrias; Dias; Trias.
- **Nature of the statement.** CM is *homological*, and the equivalence is a
  reformulation. Vallette's Remark after Thm 9 notes that a graded poset is CM iff its
  incidence algebra is Koszul (Cibils, Polo, Woodcock; CITED via Vallette).

**Fresse 2004** (*Koszul duality of operads and homology of partition posets*,
Contemp. Math. 346). CITED via Vallette's introduction, not read: the bar construction of
Com computes the homology of Π_n, and gives Lie.

**Proposition 3.1 (PROVEN). OP(P) is not a Vallette poset with blocks labelled by their
restrictions, for any operad with finite 𝒫(2).** Precisely: there is no set operad 𝒫
with 𝒫(2) finite such that, for every naturally labelled P, OP(P) is the interval
[P, 1̂] of Π_𝒫(n) with P ∈ 𝒫_n and each block B of π labelled by P|_B.
- **Vallette's order** (Vallette 2007, §3.1.2) asks, for λ ≤ μ, that each block of λ be a union of
  blocks C_{p_1}, …, C_{p_t} of μ and that *there exist* ν ∈ 𝒫_t with
  B_k = μ̃(ν × (C_{p_1}, …, C_{p_t})). So it is not enough to observe that the natural
  quotient label ν = P/π fails to determine P (e.g. P = {a < c, b} and
  P′ = {a < c, b < c} share P/π, P|_{ab} and P|_c for π = {a, b} | {c}): P and P′ could
  use different ν. (An earlier version of this proof stopped there; [AudQC] §3 noted the
  gap.)
- **The count.** Take a k-antichain B, a point c, and π = {B} | {c}. The posets Q on
  B ⊔ {c} with Q|_B an antichain and π acyclic are those with c above a nonempty subset
  of B, c below a nonempty subset of B, or c incomparable to B. (If c lay above b and
  below b′, then b < b′, contradicting that B is an antichain.) There are
  2^{k+1} − 1 of them (COMPUTED in [AudQC] `[VAL]` for k ≤ 5).
- Each such Q must equal μ̃(ν_Q × (antichain_B, id_c)) for some ν_Q ∈ 𝒫_2, and since the
  composition μ̃ is a function and the block labels are the same for all Q, different Q
  need different ν_Q. So |𝒫_2| ≥ 2^{k+1} − 1 for every k, contradicting finiteness. ∎

This rules out every finitely generated quadratic operad, which is Vallette's setting (the
posets Π_𝒫(n) are finite there, Vallette 2007, Prop. 3(1)).

**OPEN:** labellings by decorations other than restrictions (richer decorations,
Perm-style markings), and operads with infinite 𝒫(2). In both, the decorations would have
to carry the comparabilities between blocks, and nothing here rules that out.

OP(P) is instead the incidence poset of a *decomposition* (cooperad-like) structure
P ↦ Σ_π (P/π) ⊗ ⊗_B P|_B. That is the shape of contraction–extraction coproducts. For
finite topologies (= preorders) see Fauvet–Foissy–Manchon, *The Hopf algebra of finite
topologies and mould composition*, Ann. Inst. Fourier 67 (2017) (CITED from search
snippets, not read). Whether their "T-admissible" equivalences are exactly the acyclic
quotients is OPEN. No Vallette-type "Koszul ⇔ CM" theorem for such decomposition
structures was found. Whether OP(P) is a Vallette poset for some exotic labelling is
OPEN. Such a labelling could even have exactly the acyclic quotients as its underlying
partitions. It is still not interesting for this note: Thm 9 is an equivalence, so an
exotic realization would turn OP(P)'s already-known CM property into the Koszulness of
an exotic operad, and supply no source of sphericity. It would also be one operad per P
(or one operad with infinite 𝒫(2)), not a uniform framework.

**What the idea adds beyond Vallette/Fresse, and what it does not.**
- **Adds:**
  - objects that are not indexed by n alone (OP(P) depends on P);
  - a symmetry group Aut(X) of a single object, instead of S_n;
  - a *space-level* equivariant statement ([TE]; PROVEN, audited
    (`notes/audit_theorem_e.md`)), where Vallette
    identifies an S_n-module.
- **Does not add:** a reason for sphericity. In Vallette the reason is Koszulness, which
  is equivalent to CM. In the repo it is convexity (R1) or complementation (C) (§1.5).
- **The relation.** The interval axioms (Q1)–(Q3) are the common shape of both pictures.
  That shape is Schmitt's hereditary families (*Incidence Hopf algebras*, JPAA 96 (1994):
  families closed under intervals and products; CITED from search snippets, not read).
  So the idea *is* the Vallette/Schmitt picture at the level of axioms, and differs only
  in the source of sphericity, which is not categorical.

**Batanin–Markl** (*Operadic categories as a natural environment for Koszul duality*,
Compositionality 2023, and *Koszul duality for operadic categories*, arXiv 2105.05198;
abstracts only).
- Operadic categories are the categorical form of "objects with quotient maps and fibers".
  This is the closest existing formalization of a "category with a
  quotient/partition property".
- Their results concern Koszulness of operads over such categories. No poset or
  Cohen–Macaulay statement was found.
- **Kaufmann–Ward**, *Koszul Feynman categories* (Proc. AMS 2023; abstract): cubical
  Feynman categories are Koszul. No poset statement was found.
- A Vallette-type theorem for operadic categories ("Koszul over C ⇔ the quotient posets
  are CM") is the natural categorical statement. It was **not found**. Even if true, it
  would again be an equivalence, and the G-set control shows that its CM side fails in
  general.

**Gálvez-Carrillo–Kock–Tonks** (*Decomposition spaces, incidence algebras and Möbius
inversion I–III*, Adv. Math. 2018; abstracts). Decomposition spaces (unital 2-Segal
spaces) abstract incidence coalgebras and Möbius inversion. They would carry Möbius
numbers and Zaslavsky-type counts ([GT] Thm 2), not homotopy types. Not found: any
statement about sphericity of the associated posets.

**Aguiar–Mahajan.** Hopf monoids in species (CITED from memory; the repo's Hopf-monoid
analysis is [GT §2]) organize the products and coproducts. Their *Topics in Hyperplane
Arrangements* (read in [GT] and `notes/novelty_general_theory.md`) has the cone
contractibility lemma ([GT] Lemma 0.2). Neither proves sphericity from the species
structure.

**Björner–Wachs–Welker 2005** (*Poset fiber theorems*; read in [GT] and [PATE §1.3]).
This is the engine that every positive case here uses: (R2) supplies the fibers, (R1) or
(R1′) their connectivity. Any "framework" explanation of a wedge in §2 is a BWW/Quillen
argument with the fibers identified.

**Ehrenborg–Jung 2013** (*The topology of restricted partition posets*, J. Algebraic
Combin. 37; read, see §2.2). Prior art for §2.2 in full: the Quillen fiber lemma from
ordered set partitions to pointed set partitions, and the rank-selected Boolean
complex. The Möbius side of Proposition 2.2 is Stanley's (CITED via Ehrenborg–Jung).

**Arone 2015 and Arone–Brantner 2021.** CITED via [PATE §1], which read them; not re-read
here. See *A branching rule for partition complexes* (arXiv:1508.05086, Ex. 1.4,
Thm 1.2) and *The action of Young subgroups on the partition complex* (Publ. IHÉS 133,
arXiv:1801.01491, Thm 5.10, Lemma 5.17).
- **What they give.** Equivariant decompositions into wedges of induced representation
  spheres, uniformly for Π_n under Young subgroups and for Tits buildings under
  parabolics.
- **Their engine** is complementary collapse (Thm 3.14), an equivariant discrete-Morse
  collapse on a G-lattice equipped with an orthogonality fan, in the Björner–Walker
  complementation lineage.
- **Is it the quotient-category picture?** In part. It is the closest existing
  *uniform equivariant* framework, and its two main examples are the quotient lattices of
  two categories (sets and F_q-vector spaces), which is exactly the shape of the idea. Its input
  is lattice-theoretic, though: complements and an orthogonality fan in Q(X), not the
  quotient structure of a category. The two notions differ:
  - the negative control of §2.3 is closed under meets but fails (Q2);
  - conversely, complementary collapse needs complements and an orthogonality fan in the
    lattice, which (Q1)–(Q3) do not provide.
- **Overlap with this note.** Π_n (sets) is the only family where both apply ([PATE
  §2.2]). Whether Λ(V) or OP(P) admits an orthogonality fan that reproduces the chamber
  count is OPEN; [PATE §3] already lists it.
- If the equivariant side were pursued, Arone–Brantner, not Vallette, is the framework
  to compare with. That is a question about [TE] (second proof of Theorem E), not about
  quotient categories.

**Novelty, phrased as a search result.**
- Not found: an axiomatization of "categories with quotients" whose axioms force
  sphericity.
- Not found: a Vallette-type theorem for operadic categories or decomposition spaces.
- Found: every sphericity mechanism met here is one of three, none categorical:
  - Koszulness ⇔ CM (Vallette; incidence algebras);
  - convexity or shellability with fiber lemmas (Folkman, BWW, [GT], Ehrenborg–Jung);
  - complementation (Björner–Walker, Kozlov, Arone–Brantner).

---

## 4. Verdict: STOP

- **A framework that only renames known results.**
  - The repo has two sources of sphericity: convexity (R1), in [GT] and [TE], and
    complementation (C), in Route C (§1.5). Both are known mechanisms, and neither is
    supplied by the interval axioms. With (R1) the framework *is* the cone framework of
    [GT] (§1.4).
  - Axiom (C) is the part of the quotient idea that does real work: a non-convex,
    lattice-level axiom that uses (Q2) essentially. It does not reverse the verdict,
    because it is Björner–Walker complementation, which the reversal test below excludes.
  - The categorical axioms proper ((Q1)–(Q3), i.e. (R2) without (R1)) are the
    Vallette/Schmitt interval axioms (§3). Read abstractly, with a single fiber allowed,
    they hold for every finite lattice and force nothing (RP², §2.3). With partition-type
    data they cannot force wedges without settling Shareshian's conjecture, and they
    provably do not force top-dimensional wedges (§2.3).
- **Explanatory test.**
  - The only family the framework explains beyond OP(P) is d-divisible partitions (§2.2),
    and that explanation is Ehrenborg–Jung's proof.
  - Mixed graphs (§2.1) are more cones.
  - Non-orientable geometric lattices, Dowling lattices with |G| ≥ 3, NC(n) and buildings
    are outside it.
- **What to keep** (as remarks in existing notes, not as a new programme):
  - The fibers of the support map are the ordered companions of the quotients ((R2)), and
    the fixed points are the companion of the orbit quotient ((R5), PROVEN here). This is
    the one-line categorical reading of [GT] Thm 1 Step 2 and of [TE] Lemma F, and it is
    worth a sentence in [MO §4].
  - Pointing = pointedness: Ehrenborg–Jung's pointed partitions are the dual-claw cone
    (§2.2).
- **What would reverse the verdict.** A non-geometric axiom on a category of quotients
  that implies CM and is satisfied by a family not already covered by Koszulness,
  convexity or complementation. Nothing found suggests one. The nearest live questions
  belong to other notes:
  - an orthogonality fan on Λ(V) (Arone–Brantner route to Theorem E; [PATE §3]);
  - whether NC(n) is a cone lattice of some arrangement (OPEN, §2).

---

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process, imports
nothing from the repo):

    python3 quotient_categories.py > output/quotient_categories.txt   # ~3 min, ends "ALL CHECKS PASS: True", exit 0
    python3 quotient_categories.py --quick                              # ~4 s, smaller ranges
    python3 -m unittest test_quotient_categories                        # < 1 s

Output lines:
- `[CTL]`: instrument controls (B_3 = S^1, a chain, RP^2 torsion).
- `[MIX]`: §2.1.
- `[FIX]`: (R5).
- `[DDIV]`: §2.2.
- `[NEG]`: the at-most-2-to-1 control and (Q2).
- `[GSET]`: subgroup lattices.
- `[NC]`: noncrossing partitions vs OP(P).

Homology is computed as reduced Betti numbers modulo primes, not as an integral Smith
form. A difference between the mod 2 and mod 3 Betti numbers certifies torsion.
