# A homology-free proof of μ(OP(P)) = (−1)^{n−1} e_C(P)

This note gives two elementary proofs of the base-case lemma `lem:small` of
[Thm]. Neither uses topology or homology. The lemma is

  μ(OP(Q)) = (−1)^{|Q|−3} e_C(Q)   for every finite poset Q on |Q| ≥ 1 points.

Since (−1)^{|Q|−3} = (−1)^{|Q|−1}, it says the same as Theorem A below. [Thm]
proves it for |Q| ≥ 3 from Jenča–Sarkoci's homotopy type (input (A)) and
P. Hall's theorem (input (B)), and checks |Q| ≤ 2 by hand. Both proofs below
cover every n ≥ 1 at once. So `lem:small`, and with it `prop:Mside`, the
character identity (characterconj) and the closed formula (closed), no longer
need (A) or (B). They still need (C), the Hopf trace formula, only to identify
μ(OP(P)^g) with a trace on H_P. Going by the dependencies stated in [Thm], the
identity (characterconj) between Möbius values and root-of-unity sums then
needs no topology at all.

## Verdict

| Claim | Status | Inputs |
|---|---|---|
| **Theorem A.** μ(OP(P)) = (−1)^{n−1} e_C(P) for every finite poset P on n ≥ 1 points | **PROVEN** twice (Proof W, §2; Proof Z, §3), independently audited in [AudME] (both hold and are homology-free); **COMPUTED** for all 405 posets with n ≤ 6 | Proof W: dual Weisner + Lemma C; Proof Z: Lemma W + Möbius inversion + products + [GT] Lemma 1.3 |
| Lemma M (OP(P) closed under the partition meet; x ∧ π_a = 0̂ iff x ∈ {0̂} ∪ {π_ab}) | **PROVEN**; COMPUTED `[meet]` | [Thm] Lemma `lem:lattice`(i) |
| Lemma U (upper intervals: [π, 1̂] ≅ OP(P/π)) | **PROVEN**; COMPUTED `[upper]` | none |
| Lemma D (μ(OP(P)) = −Σ_b μ(OP(P/π_ab)), a minimal) | **PROVEN**; COMPUTED `[weis]` | Weisner (dual form), Lemmas M, U |
| Lemma C (e_C(P) = Σ_b e_C(P/π_ab), a minimal) | **PROVEN** here; it is Jenča–Sarkoci §4 (Lemmas 4.6, 4.8–4.11 and the first half of the proof of Thm 4.5; Lemma 4.7 is an Example; read in source); COMPUTED `[rec]` | none |
| Lemma W (Σ over P-compatible set compositions of (−1)^{#blocks} = (−1)^n [P antichain]) | **PROVEN**; COMPUTED `[W]` | none |
| Lemma F (the face identity, the braid case of [GT] Thm 2, Step "f(Y)") | **PROVEN**; COMPUTED `[faces]`, `[inv]` | Lemma W |
| Corollary (P connected: μ(OP(P)) = (−1)^{n−1} \|Lin P\|) | **PROVEN**; COMPUTED `[conn]` | Lemma F, Möbius inversion only |
| Route 1 ([GT] Thm 2 / [FP] EZ, CF at g = 1) avoids Theorem 1 but is **not** homology-free | **PROVEN** (by reading the proofs, §4) | — |
| No earlier Möbius-level (Weisner) proof was found; the cyclic-class recursion is Jenča–Sarkoci's | **CITED** / NOT FOUND (§5) | — |

Recommendation for Lean: **Proof W** (§6).

Tags: [Thm] = `notes/poset_jks_theorem.tex`; [GT] = `notes/general_theory.md`;
[FP] = `notes/fixed_point_formula.md`; [Lit] =
`notes/literature_novelty_jks_maps.md`; [JS] = Jenča–Sarkoci, *Linear
extensions and order-preserving poset partitions*, JCTA 122 (2014) 28–38,
arXiv:1112.5782v2 (arXiv numbering); [AudME] =
`notes/audit_mu_op_elementary.md` (the independent audit of this note).

## 0. Conventions

These are the conventions of [Thm, §1]. A poset P on a finite set of n ≥ 1
points. A partition π is order-preserving if the quotient digraph P/π (an
edge B → B′ between distinct blocks whenever x < y with x ∈ B, y ∈ B′) is
acyclic. OP(P) is ordered by refinement, with 0̂ the discrete partition and
1̂ the one-block partition, and μ(OP(P)) = μ(0̂, 1̂). For π ∈ OP(P), write
Q_π for the quotient poset: the transitive closure of P/π, a partial order on
the blocks of π. Write |π| for the number of blocks. e(P) = |Lin P|.
e_C(P) is the number of rotation classes wC_n that meet Lin(P). κ is the
partition of P into connected components.

For a ≠ b put π_ab for the partition whose only non-singleton block is
{a, b}, and π_a = {{a}, P ∖ {a}}. Write P/π_ab for Q_{π_ab}.

**Fact 0 (cuts; [Thm] Lemma `lem:rot`, [JS] Prop. 4.3).** If w ∈ Lin(P) and
{w_1, …, w_k} is a union of components, then the rotation w_{k+1}⋯w_n w_1⋯w_k
is in Lin(P). If P is connected, no proper rotation of a linear extension is
a linear extension, so e_C(P) = e(P).

*Proof.* There are no relations between a union of components and its
complement, which gives the first claim. For the second, if w and its
rotation by k (0 < k < n) are both linear extensions, put A = {w_1, …, w_k}
and B its complement. Then w forbids y < x for x ∈ A, y ∈ B, and the
rotation forbids x < y. So there are no relations between A and B, and P is
not connected. ∎

## 1. Lattice facts

**Lemma M (PROVEN).**
- (a) OP(P) is closed under the meet of set partitions.
- (b) If a is minimal (or maximal) and n ≥ 2, then π_a ∈ OP(P), π_a ≠ 1̂,
  and for x ∈ OP(P): x ∧ π_a = 0̂ iff x = 0̂ or x = π_ab for some b ≠ a.

*Proof.*
- (a) is [Thm] Lemma `lem:lattice`(i).
- (b) P/π_a has two vertices. If a is minimal there is no edge from P ∖ {a}
  to {a}, so it is acyclic. π_a ≠ 1̂ since n ≥ 2. The partition meet x ∧ π_a
  splits the block B of x containing a into {a} and B ∖ {a} and keeps the
  other blocks. It is discrete iff |B| ≤ 2 and every other block is a
  singleton. ∎

**Lemma U (PROVEN).** For π ∈ OP(P), σ ↦ σ/π (the partition of the blocks of
π induced by σ) is an order isomorphism [π, 1̂]_{OP(P)} → OP(Q_π). Hence
μ_{OP(P)}(π, 1̂) = μ(OP(Q_π)).

*Proof.* σ ≥ π ↦ σ/π is a bijection from the coarsenings of π onto the
partitions of the blocks of π, preserving refinement both ways. The quotient
digraph P/σ is the quotient of the digraph P/π by σ/π. Passing to the
transitive closure Q_π does not change acyclicity of the quotient: every
edge of P/π is a relation of Q_π, and every relation of Q_π is a directed
path in P/π. So a directed cycle of Q_π/(σ/π) lifts to a closed walk in
(P/π)/(σ/π) whose steps are edges or stay in one σ-block, with at least one
edge; such a walk contains a directed cycle. So σ ∈ OP(P) iff
σ/π ∈ OP(Q_π). The Möbius function of an interval is intrinsic to it. ∎

## 2. Proof W: dual Weisner plus Jenča–Sarkoci's cyclic-class recursion

**Weisner, dual form (PROVEN in [Thm] Lemma `lem:weisner`, applied to the
dual lattice; EC1 Cor. 3.9.3 states this form, as re-checked in `notes/citation_check.md` §3.3).** In a
finite lattice M and c ≠ 1̂: Σ_{x : x ∧ c = 0̂} μ(x, 1̂) = 0.

*Derivation from [Thm] Lemma `lem:weisner`.* Apply it to M^op with a = c
(c ≠ 0̂ in M^op). Joins in M^op are meets in M, and μ_{M^op}(y, x) =
μ_M(x, y). ∎

**Lemma D (PROVEN).** Let n ≥ 2 and a be minimal in P. Then

  μ(OP(P)) = − Σ_{b ≠ a, π_ab ∈ OP(P)} μ(OP(P/π_ab)).

*Proof.* OP(P) is a finite lattice by Lemma M(a) (a finite meet-semilattice
with top). Apply dual Weisner with c = π_a, which is ≠ 1̂. By Lemma M(b) the
x with x ∧ π_a = 0̂ are 0̂ and the π_ab in OP(P). So
μ(0̂, 1̂) + Σ_b μ(π_ab, 1̂) = 0. Lemma U turns μ(π_ab, 1̂) into
μ(OP(P/π_ab)). ∎

The meet here is the meet of OP(P), and Lemma M(a) says it is the partition
meet; that is what Lemma M(b) computed.

π_ab ∈ OP(P) for a minimal means: a and b are incomparable, or b covers a.

**Lemma C (PROVEN; this is [JS] §4, Lemmas 4.6, 4.8–4.11 and the first half
of the proof of Thm 4.5, read in the arXiv v2 source; Lemma 4.7 is an
Example in v2's shared numbering).** Let n ≥ 2 and a be minimal in P.
Then

  e_C(P) = Σ_{b ≠ a, π_ab ∈ OP(P)} e_C(P/π_ab).

*Proof.* Identify a rotation class with its necklace: the cyclic sequence of
its words. Let 𝒩(P) be the set of necklaces with at least one reading in
Lin(P); |𝒩(P)| = e_C(P). Define Φ on 𝒩(P): for N ∈ 𝒩(P), let b be the
successor of a in N, and let Φ(N) = (b, N′), where N′ is N with the adjacent
letters a, b replaced by one letter {a, b}.

- *Φ lands in the right set.* Pick a reading w ∈ Lin(P) of N. If a is not
  the last letter of w, then b follows a in w. If a is the last letter, then
  nothing lies above a (it is last) or below a (it is minimal), so {a} is a
  component; by Fact 0 the rotation a w_1 ⋯ w_{n−1} is in Lin(P), and in it b
  follows a. So some reading w ∈ Lin(P) has a immediately followed by b.
  Merging two adjacent letters of a linear extension gives a linear order of
  the blocks of π_ab in which every edge of P/π_ab goes forward. So P/π_ab is
  acyclic, π_ab ∈ OP(P), and the merged word is in Lin(P/π_ab). Hence
  N′ ∈ 𝒩(P/π_ab).
- *Inverse.* Given b with π_ab ∈ OP(P) and N′ ∈ 𝒩(P/π_ab), let Ψ(b, N′)
  replace the letter {a, b} by the two letters a b, in this order. Take a
  reading u ∈ Lin(P/π_ab) of N′ and expand it to a word w. Let x < y in P.
  If {x, y} ≠ {a, b}, then [x] < [y] in P/π_ab, so x precedes y in w. If
  {x, y} = {a, b}, then x = a since a is minimal, and a precedes b in w. So
  w ∈ Lin(P) and Ψ(b, N′) ∈ 𝒩(P). Its successor of a is b.
- Φ and Ψ are mutually inverse: expanding and merging the same adjacent
  pair undo each other, and the b of Φ(Ψ(b, N′)) is b. ∎

**Theorem A (PROVEN, Proof W).** For every finite poset P on n ≥ 1 points,
μ(OP(P)) = (−1)^{n−1} e_C(P).

*Proof.* Induction on n. For n = 1, OP(P) is one point, μ = 1 = e_C(P). For
n ≥ 2 pick a minimal a. The posets P/π_ab have n − 1 points. By Lemma D, the
induction hypothesis and Lemma C,

  μ(OP(P)) = − Σ_b (−1)^{n−2} e_C(P/π_ab) = (−1)^{n−1} e_C(P). ∎

*Inputs.* Lemma M, Lemma U, dual Weisner (all elementary, all in [Thm] or
proved here), Fact 0, Lemma C. No connectivity case split, no products of
lattices, no Hall, no homotopy type. n = 1 and n = 2 need no separate
treatment.

*Remark (relation to [JS]).* [JS] Thm 3.8 builds a discrete Morse matching on
Δ(Ô(P)) by induction, organised by the map c ↦ π_min ∧ π_a with the same
π_a. Its critical cells are counted by exactly the recursion of Lemma D, at
the level of sphere counts. Lemma D is the Möbius shadow of that matching,
and dual Weisner proves it in one line. [JS] §4 proves Lemma C, and the proof
above follows their map S_a (b = a ⊕_f 1 is the successor of a). What is
new here is replacing the Morse matching by Weisner, which needs nothing
topological.

## 3. Proof Z: the combinatorial cone Zaslavsky theorem

This is [GT] Theorem 2 specialised to the braid cone C_P, with its one
topological step, the Euler characteristic of |V| ∩ Y ∩ S, replaced by
Lemma W.

A **P-compatible set composition** of a finite poset Q is a surjection
F : Q → [k], for some k ≥ 0, with x < y ⇒ F(x) ≤ F(y). Its number of blocks
is k. (These are the faces of the closed order cone; see [GT, §1.3].)

**Lemma W (PROVEN).** For every finite poset Q on m ≥ 0 points,

  S(Q) := Σ_{F compatible} (−1)^{k(F)} = (−1)^m [Q is an antichain].

*Proof.* Induction on m. S(∅) = 1 (the empty map, k = 0). Let m ≥ 1, let z
be maximal in Q, put Q′ = Q ∖ z, and fix a compatible F′ : Q′ → [k′]. Let
α = max{F′(x) : x < z}, with α = 0 if nothing lies below z. The compatible F
on Q restricting to F′ (up to renumbering) are:
- z joins block j of F′, for j ∈ [max(α, 1), k′]: k′ − max(α, 1) + 1 maps,
  each with k = k′;
- z forms a new singleton block, placed at position p ∈ [α + 1, k′ + 1]:
  k′ − α + 1 maps, each with k = k′ + 1.

Nothing lies above z, so these are all the compatible F, and every
compatible F arises from exactly one F′ (remove z; renumber if its block was
{z}). The signed count over F extending F′ is
(−1)^{k′}[(k′ − max(α, 1) + 1) − (k′ − α + 1)] = −(−1)^{k′}[α = 0]. α = 0
iff z is isolated (maximal with nothing below). So S(Q) = −[z isolated] S(Q′).

If Q is an antichain, every point is isolated and S(Q) = (−1)^m. If x < y in
Q, choose z maximal with z ≥ y; then x < z, z is not isolated, and
S(Q) = 0. ∎

Lemma W is Stanley's order-polynomial reciprocity Ω(Q, −1) = (−1)^m Ω̄(Q, 1)
at x = 1 (EC1 §3.15; CITED, theorem number not re-checked), with
Ω(Q, x) = Σ_k w_k(Q) C(x, k) and w_k the number of compatible F onto [k];
Ω̄(Q, 1) is the number of strictly order-preserving maps to a one-point
chain. The proof above uses neither.

**Lemma F (PROVEN).** For every π ∈ OP(P),

  Σ_{σ ∈ OP(P), σ ≥ π} (−1)^{|σ|} e(Q_σ) = (−1)^{|π|} [π ≥ κ].

*Proof.* The pairs (σ ≥ π in OP(P), u ∈ Lin(Q_σ)) are in bijection with the
Q_π-compatible set compositions F of the blocks of π: send (σ, u) to the map
"block of π ↦ position in u of the σ-block containing it". It is compatible
because every relation of Q_π between different σ-blocks is a relation of
Q_σ. Conversely, the fibres of a compatible F form σ ≥ π, every edge of P/σ
strictly increases F, so σ ∈ OP(P), and the order of the fibres is a linear
extension of Q_σ. The number of blocks of F is |σ|. So the left side is
S(Q_π), and Lemma W gives (−1)^{|π|}[Q_π antichain]. Q_π is an antichain iff
no relation of P joins different blocks of π iff every component lies in one
block, i.e. π ≥ κ. ∎

**Proposition Z (PROVEN).** For every finite poset P on n ≥ 1 points,

  (−1)^n e(P) = Σ_{σ ≥ κ} (−1)^{|σ|} μ_{OP(P)}(0̂, σ),

and every partition σ ≥ κ is in OP(P).

*Proof.* Put h(σ) = (−1)^{|σ|} e(Q_σ) and f(π) = Σ_{σ ≥ π} h(σ) on the
finite poset OP(P). Möbius inversion gives h(π) = Σ_{σ ≥ π} μ(π, σ) f(σ).
Take π = 0̂ (Q_{0̂} = P) and use Lemma F. A partition σ ≥ κ has no edges
in P/σ. ∎

**Corollary (connected case; PROVEN).** If P is connected, then
μ(OP(P)) = (−1)^{n−1} e(P) = (−1)^{n−1} e_C(P).

*Proof.* κ = 1̂, so Proposition Z reads (−1)^n e(P) = −μ(0̂, 1̂). Fact 0. ∎

**Theorem A (PROVEN, Proof Z).** For σ ≥ κ, the lower interval
[0̂, σ] ≅ Π_{B ∈ σ} OP(P|_B), because there are no relations between blocks
of σ (as in [Thm] Lemma `lem:interval`(i)). μ is multiplicative on products
(EC1 §3.8, number not re-checked; Mathlib `mu_prod_mu`). With m(Q) = (−1)^{|Q|−1} μ(OP(Q)),
Proposition Z becomes

  e(P) = Σ_{σ ∈ Π(K)} Π_{B ∈ σ} m(P|_B),

where K is the set of components. [GT] Lemma 1.3 (PROVEN there, a Foata
bijection) is the same identity with e_C in place of m. Induction on the
number of components: the term σ = {K} is m(P) on one side and e_C(P) on the
other, every other term involves posets with fewer components. So
m(P) = e_C(P). ∎

## 4. Route 1: what the cone results actually use

- **[GT] Theorem 2 does not use Theorem 1** (the homotopy type). Its proof
  uses the regular-CW cell facts of [GT, §0], Lemma 0.2 (C ∩ S contractible
  or a sphere) and then χ(contractible) = 1, χ(S^{d−1}) = 1 + (−1)^{d−1}.
  The last step is the homotopy invariance of the Euler characteristic, i.e.
  of (cellular = singular) homology. So Route 1 is **homotopy-free but not
  homology-free**, and it needs CW complexes and contractibility, which
  Mathlib does not have.
- **[FP] EZ at g = 1** is Theorem 2 (the Hopf trace step is trivial at
  g = 1); the same inputs. **[FP] CF at g = 1** is the Möbius inversion of
  EZ, so it inherits them.
- The only place topology enters is the face sum
  f(Y) = Σ_{F ⊆ |V| ∩ Y} (−1)^{dim F} = (−1)^{dim Y}[Y ⊆ lin V]. For the
  braid cone, Y = flat of π and dim Y = |π| − 1, so this is exactly Lemma F,
  which Lemma W proves by counting. **Proof Z is Route 1 with the topology
  removed.** Specialising to C_P loses nothing: Λ(C_P) ≅ OP(P)^op
  ([GT, §1.3]) and the order complex is unchanged.
- Route 1 also yields the decomposition through lin C_P, which is where
  products and [GT] Lemma 1.3 come in for disconnected P. Proof W avoids
  both.

## 5. Prior art

- **[JS]** (read in arXiv v2): Thm 3.8 is the recursion of Lemma D for the
  number of spheres, proved by a discrete Morse matching (Forman, Kozlov's
  patchwork theorem). §4 (Lemmas 4.6, 4.8–4.11 and the first half of the
  proof of Thm 4.5) proves Lemma C by the map S_a.
  The paper never mentions the Möbius function or Weisner's theorem. So a
  combinatorial proof of the *count* recursion for e_C is known; its pairing
  with Weisner (Lemma D) was not found.
- **Schweig–Woodroofe** (arXiv:1604.03115, Thm 1.5, per [Lit, §1.1]; not
  re-read): OP(P) is comodernistic, hence CL-shellable. Shellability gives μ
  via chain counting, but the route is topological in spirit and does not
  produce e_C without further counting. Not homology-free in the sense
  wanted, and more expensive than Proof W.
- **Körtesi–Radeleczki–Szilágyi**: introduced order congruences ([JS]
  Def. 3.1 credits them). NOT CHECKED for a Möbius computation.
- **Bonnier–Oberhauser** (arXiv:1908.06496, §2, per [Lit, §1.1]): Möbius
  inversion on ordered partitions for signature cumulants. NOT RE-READ; [Lit]
  found no statement of μ(OP(P)).
- **Ehrenborg–Readdy-style chain counting**: NOT FOUND for OP(P). One web
  search ("Möbius function lattice of order-preserving partitions …") turned
  up only [JS] and generic Möbius references.
- **Lemma W** is order-polynomial reciprocity at x = 1 (Stanley; KNOWN).
- **Proof Z**'s scheme is Zaslavsky's dissection theorem made combinatorial
  for the braid cone, as [GT, §1.2] notes for Theorem 2.

## 6. Cost to formalize (relative to `lean/`)

From `lean/PLAN.md` §1: Mathlib has `IncidenceAlgebra.mu`, `mu_toDual`,
`mu_prod_mu`, `mu_mul_zeta`; Weisner is absent; `lean/` already has `OP`,
`IsOrderPreserving`, cuts, cosets, `eC`, and, in `Words.lean`, a contraction
`rc r a x` of a relation on `A ∖ {x}`. Line counts are rough guesses.

| Ingredient | Proof W | Proof Z | Notes |
|---|---|---|---|
| OP(P) meet = partition meet (Lemma M(a)) | yes | — | needed anyway for `lem:lattice`; ~100–200 |
| Lemma M(b) | yes | — | ~50 |
| Weisner, dual form | yes | — | needed anyway for `prop:Mside`; ~150–300 (via `mu_toDual` from the join form) |
| Upper interval ≅ OP(quotient), μ transported | yes (only for π_ab) | — | ~150–300; P/π_ab as a relation on `A ∖ {b}` matches the existing `rc` |
| Lemma C (necklace bijection) | yes | — | word combinatorics, reuses cuts/rotations; ~200–400 |
| Lemma W, Lemma F | — | yes | set compositions as surjections; ~300–500 |
| Möbius inversion | — | yes | from `mu_mul_zeta`; ~50–100 |
| Lower interval ≅ product, `mu_prod_mu` | — | yes | ~200–400 |
| [GT] Lemma 1.3 (Foata) | — | yes | ~400–700 |
| Topology / homology | none | none | |

Proof W is **homology-free and cheapest**, about 650–1250 lines. Most of it
(meet, Weisner, intervals) is infrastructure that `prop:Mside` needs anyway.
Its only extra content is Lemma C, which is word combinatorics of the kind
already in `Words.lean`. It also has a uniform base case n = 1. Proof Z is
homology-free but needs products and the Foata bijection. Its value is
conceptual: it is the braid case of the cone Zaslavsky theorem without
topology. Route 1 as written needs CW complexes and is the most expensive.

Lemmas C, D, W and both proofs of Theorem A have been independently audited
in [AudME], which finds that they hold and are homology-free, and that
Proof W is fit to formalize as written.

## 7. Computations

`compute/mu_op_elementary.py` (self-contained, exact integers; tests in
`compute/test_mu_op_elementary.py`; output in
`compute/output/mu_op_elementary.txt`). For every poset with n ≤ 6, one per
isomorphism class (1, 2, 5, 16, 63, 318: A000112, 405 in all):

- `[main]` μ(OP(P)) = (−1)^{n−1} e_C(P), with μ from the recursive definition
  on the lattice of acyclic-quotient partitions and e_C from rotation classes
  of linear extensions (the positive control asked for);
- `[conn]` Fact 0; `[W]` Lemma W by enumerating compatible compositions;
  `[faces]` Lemma F at every π; `[inv]` Proposition Z; `[meet]` Lemma M;
  `[weis]` Lemma D for every minimal a; `[upper]` Lemma U at every π
  (μ(OP(Q_π)) computed afresh); `[rec]` Lemma C for every minimal a,
  including that Φ is injective and lands in 𝒩(P/π_ab); `[comp]` [GT]
  Lemma 1.3.

All pass. Negative controls, each required to fail somewhere: `[neg-lin]`
(e(P) in place of e_C(P) in Theorem A) fails in 108 cases; `[neg-strict]`
(Lemma W with strict compatibility) fails in 399; `[neg-nonmin]` (Lemma C at
an element with something both above and below it) fails in 606. The test
file also mutates e_C and checks that the run reports failure.

```sh
cd compute
python3 mu_op_elementary.py            # n <= 6, about 16 s
python3 -m unittest test_mu_op_elementary
```
