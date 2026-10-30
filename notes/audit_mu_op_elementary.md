# Audit: the homology-free proofs of μ(OP(P)) = (−1)^{n−1} e_C(P)

This is an independent adversarial audit of `notes/mu_op_elementary.md`
("[ME]"). That note gives two proofs of

  **Theorem A.** μ(OP(P)) = (−1)^{n−1} e_C(P) for every finite poset P on
  n ≥ 1 points,

which is `lem:small` of `notes/poset_jks_theorem.tex` ("[Thm]"):
- **Proof W**: the dual Weisner theorem at π_a = {{a}, P ∖ a}, plus
  Jenča–Sarkoci's recursion for e_C over cyclic classes;
- **Proof Z**: cone Zaslavsky, with the topology replaced by a sign-sum lemma
  (Lemma W).

Other sources:
- [JS] is Jenča–Sarkoci, *Linear extensions and order-preserving poset
  partitions*, JCTA 122 (2014), arXiv:1112.5782v2. It was **read in the v2
  LaTeX source** for this audit.
- [GT] is `notes/general_theory.md`.

Tags: **PROVEN** means re-derived by hand here; **COMPUTED** means checked by
`compute/audit_mu_op_elementary.py`, written for this audit. That script
imports nothing from the repository, in particular not
`compute/mu_op_elementary.py`.

## Verdict

**Both proofs HOLD, and both are homology-free. Proof W is fit to formalize
as written.** In Proof W:
- π_a is in OP(P) and is a coatom;
- the orientation of dual Weisner is right;
- the e_C recursion is proved combinatorially, both in [ME] and in [JS] §4.

[JS] §4 uses its topological Theorem 3.8 only in the last line of the proof
of Thm 4.5, to identify s_O with e_C. That is the step Proof W replaces by
Weisner. No proof in [ME] has a mathematical gap. The fixes below are to
citations and status tags only.

| # | Claim of [ME] | Verdict |
|---|---|---|
| 1 | Dual Weisner: Σ_{x ∧ c = 0̂} μ(x, 1̂) = 0 for c ≠ 1̂, derived from [Thm] `lem:weisner` on M^op | **HOLDS.** §1.1. [Thm]'s proof of `lem:weisner` is three lines of incidence algebra. |
| 2 | Lemma M(a): OP(P) is closed under the partition meet, so it is a lattice whose meet is the partition meet | **HOLDS.** §1.2. COMPUTED `[Mclose]`, all pairs, n ≤ 5. |
| 3 | Lemma M(b): for a minimal, π_a ∈ OP(P), π_a ≠ 1̂, and {x : x ∧ π_a = 0̂} = {0̂} ∪ {π_ab ∈ OP(P)} | **HOLDS.** §1.2. π_a is a **coatom** of OP(P), which is the position dual Weisner needs. COMPUTED `[Mb-in]`, `[Mb-coatom]`, `[Mb]`, n ≤ 6, for every minimal and every maximal a. |
| 4 | Lemma U: [π, 1̂]_{OP(P)} ≅ OP(Q_π) | **HOLDS.** §1.3. COMPUTED `[U]` at all 39,617 pairs (P, π), n ≤ 6. Each side was computed from scratch: inside OP(P), and from the transitive closure Q_π. |
| 5 | Lemma D: μ(OP(P)) = −Σ_b μ(OP(P/π_ab)), for a minimal | **HOLDS.** §1.4. COMPUTED: `[Wdual]` (n ≤ 6, with μ(x, 1̂) taken in OP(P)) and `[D]` (all 5,928 pairs (P, a) with a minimal, n ≤ 7). |
| 6 | "π_ab ∈ OP(P) iff a ∥ b or b covers a" (a minimal) | **HOLDS.** §1.4. COMPUTED `[pab]`, n ≤ 7. |
| 7 | Lemma C: e_C(P) = Σ_b e_C(P/π_ab), by the necklace map Φ | **HOLDS.** The proof in [ME] is complete and self-contained (§1.5). COMPUTED: `[C]` (5,928 pairs, n ≤ 7), and `[Cbij]`, which checks that Φ is a bijection necklace by necklace. |
| 8 | Lemma C "is [JS] §4, Lemmas 4.6–4.11", which is combinatorial | **HOLDS.** §2. Lemmas 4.6, 4.8, 4.9, 4.10 and 4.11 (4.7 is an Example) use no topology, no Morse matching and no Thm 3.8. The recursion for e_C is stated in the proof of Thm 4.5 from Lemmas 4.10–4.11 alone. Theorem 3.8 enters only afterwards, in the sentence "By induction and Theorem 3.8, s_O(P) = e_C(P)". |
| 9 | Theorem A, Proof W (induction on n, base n = 1) | **HOLDS.** §1.6. Homology-free. |
| 10 | Lemma W: Σ_F (−1)^{k(F)} = (−1)^m [Q antichain] | **HOLDS.** The proof is re-derived in §3.1. A second proof is in §3.2: S(Q) = μ_{J(Q)}(∅, Q), the Möbius function of a distributive lattice. COMPUTED twice, both ways: `[W]` by brute force over ordered set partitions (n ≤ 6), and `[W(J)]` through J(Q) (n ≤ 7). |
| 11 | Lemma F, Prop. Z, the Corollary | **HOLD.** §3.3. COMPUTED `[F]` (39,617 pairs), `[Z]` and `[Z-op]`, n ≤ 6. |
| 12 | Theorem A, Proof Z (lower intervals are products, then [GT] Lemma 1.3, by induction on components) | **HOLDS.** §3.4. [GT] Lemma 1.3 (Foata) was read and is elementary. COMPUTED `[prod]` and `[comp]`, n ≤ 6. |
| 13 | Proof Z is homology-free | **HOLDS.** §3.5. Its inputs are counting, Möbius inversion, μ of products, and a Foata bijection. |
| 14 | Route 1 ([GT] Thm 2) is homotopy-free but not homology-free | **HOLDS** (by reading [GT] §1.2). Its proof evaluates χ(|V| ∩ Y ∩ S) as χ(point) or χ(sphere). |
| 15 | Signs and small cases: n = 1, 2, 3, disconnected P; (−1)^{n−3} = (−1)^{n−1} | **HOLD.** §4. Theorem A is false at n = 0, and both proofs use n ≥ 1. |
| 16 | Citations: "EC1 §3.15" for order-polynomial reciprocity; Mathlib has no Weisner; the line counts of §6 | **NOT CHECKED.** [ME] marks the EC1 section as not re-checked. The §6 counts are estimates. Neither affects a proof. |

Fixes:
- (a) [ME] says Lemma C is "[JS] §4, Lemmas 4.6–4.11". It is more exact to
  say: Lemmas 4.6, 4.8–4.11 and the first half of the proof of Thm 4.5. Lemma
  4.7 is an Example in v2's shared numbering.
- (b) [ME]'s verdict table tags Theorem A "not yet independently audited".
  This audit can now replace that tag. That is a change to [ME], which this
  audit does not make.

## 1. Proof W, re-derived

Convention: OP(P) is ordered by refinement, 0̂ is discrete, 1̂ is one block.

### 1.1 Dual Weisner

[Thm] `lem:weisner`: in a finite lattice M with a ≠ 0̂,
Σ_{x ∨ a = 1̂} μ(0̂, x) = 0. The proof expands δ(x ∨ a, 1̂) as
Σ_{y ≥ x ∨ a} μ(y, 1̂) and swaps the sums. It is elementary.

Apply it to M^op with a = c:
- 0̂ of M^op is 1̂ of M, so the hypothesis a ≠ 0̂ becomes c ≠ 1̂;
- the join of M^op is the meet of M, and 1̂ of M^op is 0̂ of M;
- μ_{M^op}(1̂_M, x) = μ_M(x, 1̂_M).

So Σ_{x ∧ c = 0̂} μ(x, 1̂) = 0 for every c ≠ 1̂. The sum runs over x whose
**meet** with c is the **discrete** partition, and it uses the upper values
μ(x, 1̂). That is how [ME] applies it.

Small check, on the Boolean lattice {0, a, b, 1} with c = a: the terms are
μ(0, 1) + μ(b, 1) = 1 − 1 = 0.

Negative control `[neg:Wdual-top]`: with c = 1̂ the sum is μ(0̂, 1̂). That
is nonzero on all 405 posets with n ≤ 6.

### 1.2 Lemma M: π_a and its position

**(a) Meet.** Let x, y ∈ OP(P), and suppose P/(x ∧ y) had a directed cycle.
Map the cycle to P/x. It becomes a closed walk whose steps are edges or stay
inside one block. If any step were an edge, the walk would contain a cycle
of P/x. So every step stays inside an x-block. By the same argument every
step stays inside a y-block, so every step stays inside an (x ∧ y)-block.
That contradicts the steps being edges.

So OP(P) is a meet-closed subset of Π_n containing 1̂. A finite
meet-semilattice with a top is a lattice, and its meet is the partition
meet. This matters: Weisner's index set {x ∧ c = 0̂} uses the meet of the
lattice OP(P). This is exactly [Thm] `lem:lattice`(i).

**(b) π_a.** Let a be minimal and n ≥ 2. Then P/π_a has two vertices, {a}
and P ∖ a. An edge from P ∖ a to {a} would need some y < a, and there is
none. So π_a ∈ OP(P).

π_a has two blocks, so it is a coatom of Π_n. Hence it is a coatom of
OP(P): the only partition strictly coarser than π_a is 1̂ (COMPUTED
`[Mb-coatom]`). In particular π_a ≠ 1̂, which is the one hypothesis dual
Weisner needs.

The partition meet x ∧ π_a splits the x-block B ∋ a into {a} and B ∖ a,
and keeps every other block. It is discrete iff |B| ≤ 2 and every other
block is a singleton, that is, iff x = 0̂ or x = π_ab. In the second case
x ∈ OP(P) is what puts π_ab in the sum.

Control `[pia-notOP-mid]`: if a has elements both below and above it, then
π_a ∉ OP(P). So the hypothesis "a minimal (or maximal)" is needed.

### 1.3 Lemma U

The map σ ↦ σ/π is a bijection from the coarsenings of π to the partitions
of the set of π-blocks, and it preserves refinement both ways. The digraph
P/σ is (P/π)/(σ/π).

Passing to the transitive closure Q_π does not change acyclicity:
- every edge of P/π is a relation of Q_π;
- every relation of Q_π is a directed path in P/π;
- so a cycle in Q_π/(σ/π) lifts to a closed walk in (P/π)/(σ/π) that has at
  least one edge, and such a walk contains a cycle.

Hence [π, 1̂] ≅ OP(Q_π), and μ is intrinsic to the interval. The proof only
needs π = π_ab. COMPUTED `[U]` checks every π.

### 1.4 Lemma D, and when π_ab is order-preserving

Put c = π_a in §1.1 and use §1.2(b). This gives
μ(0̂, 1̂) + Σ_{π_ab ∈ OP} μ(π_ab, 1̂) = 0. Then §1.3 turns each μ(π_ab, 1̂)
into μ(OP(P/π_ab)).

Now let a be minimal and ask when π_ab is order-preserving:
- b < a is impossible.
- If a < c < b, then {a, b} → c → {a, b} is a cycle.
- If a ∥ b, or b covers a, a cycle through {a, b} would need some c with
  c < b and (a < c or b < c). The case b < c < b is impossible, and a < c < b
  contradicts "b covers a" (and contradicts a ∥ b).

So π_ab ∈ OP(P) iff a ∥ b or b covers a (COMPUTED `[pab]`).

Negative control `[neg:D-mid]`: with a in the middle (π_a ∉ OP), the
formula of Lemma D fails on every one of the 5,299 such pairs with n ≤ 7.

### 1.5 Lemma C

The proof in [ME] §2 was checked step by step.

**Φ is well defined.** Let b be the cyclic successor of a in the necklace N.
This depends only on N.

**Φ lands in the right set.** We need a reading of N in Lin(P) in which a
is immediately followed by b.
- Take a reading w ∈ Lin(P). If a is not last in w, then b follows a.
- If a is last, then nothing lies above a (it is last), and nothing lies
  below a (it is minimal). So {a} is a component.
- By Fact 0, with the cut at k = n − 1, the rotation a w_1 ⋯ w_{n−1} is in
  Lin(P), and in it b follows a.

Merging the two adjacent letters a, b keeps the relative order of all
blocks. So every edge of P/π_ab still points forward. Hence π_ab ∈ OP(P),
and the merged word is in Lin(Q_{π_ab}).

**Ψ (expand {a, b} to a b) lands in 𝒩(P).** Let x < y in P.
- If x and y lie in different blocks, then [x] < [y] in Q_{π_ab}, so x
  precedes y.
- Otherwise {x, y} = {a, b}. Then x = a, because a is minimal, and a
  precedes b.

**Φ and Ψ are inverse.** In Φ(Ψ(b, N′)), the successor of a is b. This
includes n = 2, where N = (a b).

COMPUTED `[Cbij]`: for every poset with n ≤ 7, every minimal a and every
necklace N, Φ(N) is a necklace of P/π_b that meets Lin. Φ is injective, and
|𝒩(P)| = Σ_b |𝒩(P/π_ab)|.

Negative controls:
- `[neg:C-e]`: with e in place of e_C, the identity fails in 534 of 5,928
  cases. The smallest failure is the 2-antichain, where 2 ≠ 1.
- `[neg:C-mid]`: at a middle element, it fails in every case.

### 1.6 Theorem A, Proof W

Induct on n.

**n = 1.** OP(P) is one point, so μ = 1 = e_C(P).

**n ≥ 2.** Pick a minimal a. Each P/π_ab has n − 1 ≥ 1 points. Then

  μ(OP(P)) = −Σ_b μ(OP(P/π_ab))           (Lemma D)
           = −Σ_b (−1)^{n−2} e_C(P/π_ab)    (induction)
           = (−1)^{n−1} e_C(P)              (Lemma C).

The inputs are §1.1–1.5 and Fact 0. Fact 0 is the cut argument: a relation
between A and B would be reversed by the rotation. Nothing here is
topological.

The two recursions use **the same index set** {b : π_ab ∈ OP(P)}:
- in Lemma D, because it is the Weisner set of §1.2(b);
- in Lemma C, because Φ reaches every such b, by the surjectivity half of
  the bijection, Ψ.

This coincidence is the whole proof, and both halves are checked.

## 2. Jenča–Sarkoci §4: is the recursion homology-free?

The numbering below is from the arXiv v2 source. Theorem-like environments
share one counter per section.

| v2 number | Label | Content | Topology? |
|---|---|---|---|
| Thm 3.8 | `thm:numberofspheres` | Δ(Ô(P)) is a wedge of s_O(P) spheres, and s_O satisfies the π_ab recursion | **Yes.** Discrete Morse theory: Forman's Thm 6.3 and Kozlov's Thm 11.10. |
| Def 4.1, Prop 4.3, Cor 4.4 | `def:ce`, —, `coro:charconnected` | Cyclic classes; connected iff e = e_C | No. Words only. |
| Thm 4.5 | `thm:mainresult` | wedge of e_C(P) spheres | Its proof first derives the e_C recursion from 4.10 and 4.11, then cites 3.8. |
| Lemma 4.6 | `lemma:piab` | π_{a, a⊕_f 1} is order-preserving | No. |
| Ex 4.7 | — | example | — |
| Lemma 4.8 | `lemma:quotmap` | g is isotone iff g ∘ q is isotone | No. |
| Lemma 4.9 | `lemma:faislinear` | f_a ∈ Lin(P/π_{a, a⊕1}) | No. |
| Lemma 4.10 | `lemma:sasurjective` | S_a is surjective onto ⊔_b Lin(P/π_ab) | No. |
| Lemma 4.11 | `lemma:cycequiv` | f ∼ g iff f_a ∼ g_a | No. It contracts and expands an edge of the cycle digraph C(f, P). |

The proof of Thm 4.5 reads: "By Lemmas 4.10 and 4.11, S_a determines a
bijection … this gives us the following recurrence
e_C(P) = Σ_{π_ab order-preserving} e_C(π_ab). By induction and Theorem 3.8,
s_O(P) = e_C(P)."

So the recurrence for e_C is proved before Theorem 3.8 is invoked, and
without it. None of Lemmas 4.6–4.11 cites Theorem 3.8, Forman, Kozlov, or any
complex. The Lemmas are stated for n ≥ 2, so the recursion holds for
n ≥ 2. The proof of Thm 4.5 writes |P| > 3 only because the topological
induction starts at n = 3.

A grep of the source finds no Möbius function, Weisner or Euler
characteristic. "Homology" occurs only as a keyword and in a reference
title. This confirms [ME] §5: the pairing of the e_C recursion with Weisner
is not in [JS].

Two harmless slips in [JS] Lemma 4.11:
- the proof writes C(f_b, …) where it means C(g_a, …);
- the step "only one orientation gives an oriented cycle" is correct, since
  the other orientation splits the cycle.

[ME]'s own proof of Lemma C (§1.5) does not depend on [JS] at all. It works
with necklaces directly, so it needs neither Lemma 4.8 nor the bookkeeping
of the map f_a. **Conclusion: Proof W is homology-free whether Lemma C is
taken from [ME] or from [JS].**

[ME]'s remark that [JS] Thm 3.8 is organised by c ↦ π_min ∧ π_a, with the
same π_a, matches the source.

## 3. Proof Z, re-derived

### 3.1 Lemma W by the recursion of [ME]

Let z be maximal in Q, put Q′ = Q ∖ z, and fix a compatible F′ : Q′ ↠ [k′].
Let α = max F′ on the elements below z, with α = 0 if there are none.

- **z joins block j.** This needs j ≥ α and j ≥ 1. There are
  k′ − max(α, 1) + 1 choices. This count is 0 when k′ = 0, as it should be.
- **z forms a new block at position p.** The old blocks at positions ≥ p
  shift up by one. Every x < z keeps F(x) ≤ p iff F′(x) < p. So
  p ∈ [α + 1, k′ + 1], which gives k′ + 1 − α choices.

The signed sum is (−1)^{k′}(α − max(α, 1)) = −(−1)^{k′}[α = 0]. Also, α = 0
iff z has nothing below it, iff z is isolated (z is maximal). Restricting F
to Q′ and renumbering inverts the extension. So

  S(Q) = −[z isolated] S(Q′).

- If Q is an antichain, this gives S(Q) = (−1)^m.
- Otherwise there are x < y. Choose z ≥ y maximal; then z is not isolated,
  and S(Q) = 0. The recursion holds for *any* maximal z, so this choice is
  allowed.

### 3.2 A second proof of Lemma W

A surjection F : Q → [k] is compatible iff every D_j = F^{−1}([1, j]) is an
order ideal. So compatible F are exactly the strict chains
∅ = D_0 ⊂ D_1 ⊂ ⋯ ⊂ D_k = Q in the distributive lattice J(Q), and

  S(Q) = Σ_chains (−1)^k = μ_{J(Q)}(∅, Q)   (P. Hall's chain formula, in its
  elementary form: μ = Σ over chains of (−1)^length).

The interval [∅, Q] in J(Q) is Boolean iff Q is an antichain. Its Möbius
function is (−1)^m in that case and 0 otherwise. This is the standard
computation of μ for distributive lattices (EC1 §3.9; example number not
re-checked). That computation is itself one application of Weisner, or of
the complementation formula.

This is an independent, homology-free proof, and `[W(J)]` computes S this
way. It also gives a cheaper route for Lean, if Lemma W is ever wanted:
Mathlib's incidence algebra and order ideals are available.

### 3.3 Lemma F, Prop. Z and the Corollary

**Lemma F.** Send (σ ≥ π, u ∈ Lin(Q_σ)) to F(π-block β) = position in u of
the σ-block containing β.

- *F is compatible.* A relation of Q_π is a path in P/π. Each step of the
  path stays in one σ-block or is an edge of P/σ, and every edge of P/σ goes
  forward in u.
- *Inverse.* Let σ be given by the fibres of F. If x < y lie in different
  σ-blocks, then [x]_π < [y]_π in Q_π, so F([x]) ≤ F([y]). The blocks are
  different, so the inequality is strict. Hence P/σ is acyclic, and listing
  the fibres in order gives a linear extension of Q_σ.

The number of blocks of F is |σ|, so the left side of Lemma F is S(Q_π).
Moreover, Q_π is an antichain iff no relation of P crosses between π-blocks,
iff π ≥ κ.

Negative control `[neg:F-nokappa]`: dropping [π ≥ κ] fails in 38,665 of
39,617 cases.

**Prop. Z.** This is Möbius inversion (the "from above" form) on the finite
poset OP(P), evaluated at π = 0̂. Every σ ≥ κ is order-preserving, since
P/σ has no edges (`[Z-op]`).

**Corollary.** If P is connected, then κ = 1̂, and Prop. Z reads
(−1)^n e = −μ(0̂, 1̂). This also holds at n = 1, where 0̂ = 1̂: the sum is
−μ(0̂, 0̂) = −1 = (−1)^1 e.

### 3.4 Theorem A, Proof Z

**Lower intervals are products.** Let σ ≥ κ. A refinement τ of σ is
order-preserving iff each restriction τ|_B is order-preserving in P|_B,
because P/τ is the disjoint union of the digraphs P|_B/τ|_B. So
[0̂, σ] ≅ Π_B OP(P|_B), and μ is multiplicative (`[prod]`).

**Signs.** With m(Q) = (−1)^{|Q|−1} μ(OP(Q)),

  (−1)^{|σ|} μ(0̂, σ) = Π_B (−μ(OP(P|_B))) = Π_B (−1)^{|B|} m(P|_B) = (−1)^n Π_B m(P|_B).

So Prop. Z becomes e(P) = Σ_{σ ∈ Π(K)} Π_B m(P|_B), as [ME] says.

**[GT] Lemma 1.3** was read in [GT] §1.3. It cuts linear extensions into
irreducible pieces at the component-union cuts, and applies Foata's
transformation to the sequence of pieces. Each step is a bijection of words.
COMPUTED `[comp]`.

**Induction on |K|.** If |K| = 1, then m(P) = e(P) = e_C(P) by the
Corollary and Fact 0. In general the term σ = {K} is m(P) on one side and
e_C(P) on the other. Every other block B is a proper union of components,
so P|_B has fewer components, and m(P|_B) = e_C(P|_B) by induction.

### 3.5 Is Proof Z homology-free?

**Yes.** Its inputs are:
- Lemma W, by counting (§3.1) or by Möbius functions of distributive
  lattices (§3.2);
- the bijection of Lemma F;
- Möbius inversion;
- μ of a product;
- a word bijection ([GT] Lemma 1.3).

No complex, Euler characteristic or homotopy appears. [ME] §4 says the only
topological step of Route 1 is the face sum f(Y), and that Lemma F is that
step for the braid cone with dim Y = |π| − 1. This is right: (−1)^{dim F}
and (−1)^{|σ|} differ by the global sign −1. Proof Z is still more expensive
than Proof W, because it needs products and the Foata bijection.

## 4. Signs and small cases

- **The sign.** (−1)^{n−3} = (−1)^{n−1}, so `lem:small` and Theorem A are
  the same statement.
- **n = 0 is excluded.** μ(OP(∅)) = 1 and e_C(∅) = 1, but (−1)^{−1} = −1. So
  Theorem A is false at n = 0, as [Thm] already records. Both proofs start
  at n = 1: Proof W's base case, and the Corollary at n = 1.
- **Positive controls for the Möbius routine** (`[pos-mu]`): μ(Π_n) =
  (−1)^{n−1}(n−1)!, and OP(chain) is Boolean with μ = (−1)^{n−1}, for n ≤ 6.
  The poset generator reproduces A000112 (1, 2, 5, 16, 63, 318, 2045) for
  n ≤ 7 (`[gen]`).

All posets with n ≤ 3 (output of the script):

| n | P | μ(OP(P)) | e | e_C | components |
|---|---|---|---|---|---|
| 1 | point | 1 | 1 | 1 | 1 |
| 2 | antichain | −1 | 2 | 1 | 2 |
| 2 | chain | −1 | 1 | 1 | 1 |
| 3 | antichain | 2 | 6 | 2 | 3 |
| 3 | 2-chain + point | 2 | 3 | 2 | 2 |
| 3 | V (one below two) | 2 | 2 | 2 | 1 |
| 3 | Λ (two below one) | 2 | 2 | 2 | 1 |
| 3 | chain | 1 | 1 | 1 | 1 |

These match [JS]'s Table (2, 2, 2, 2, 1). They also match the n = 2 cases by
hand:
- the 2-chain: OP = {0̂, 1̂}, with b covering a, so Lemma D gives
  μ = −μ(point) = −1;
- the 2-antichain: OP = Π_2, μ = −1, and e_C = 1 because ab and ba are one
  rotation class.

Lemma D and Lemma C need no special case at n = 2.

**Disconnected P.**
- `[conn]`: e_C < e for every disconnected P with n ≤ 7, and e_C = e for
  every connected P.
- The negative control `[neg:A-e]` (e in place of e_C) fails in exactly the
  disconnected cases: 503 of 2,450 posets.
- Theorem A, Lemma C and Lemma D hold on all of them.
- Proof W treats disconnected P with no case split. The only place
  connectivity enters is Fact 0, when a is isolated.

## 5. Computations

`compute/audit_mu_op_elementary.py` (exact integers, no dependencies). It
covers one poset per isomorphism class, generated here as natural
labellings deduplicated by a canonical form.

- **n ≤ 6** (405 posets): every check.
- **n = 7** (all 2,045 posets): Theorem A, Lemma D, Lemma C with the
  bijection check, the π_ab criterion, Lemma W via J(Q), and Fact 0.

Here μ is computed by the defining recursion inside OP(P), enumerating
refinements block by block. e_C is the number of distinct minimal rotations
of linear extensions. e is computed both by enumeration and by a DP over
order ideals (`[e-dp]`).

| check | fails / checks |
|---|---|
| A (Theorem A), n ≤ 7 | 0 / 2450 |
| C, D (a minimal), n ≤ 7 | 0 / 5928 each |
| Cbij, n ≤ 7 | 0 / 621383 |
| pab, n ≤ 7 | 0 / 34415 |
| W(J), conn, e-dp, n ≤ 7 | 0 / 2450 each |
| Mb, Mb-in, Mb-coatom, Wdual, n ≤ 6 | 0 / 1700 each |
| Mclose, n ≤ 5 | 0 / 96448 |
| U, F, n ≤ 6 | 0 / 39617 each |
| W (brute force), Z, comp, n ≤ 6 | 0 / 405 each |
| prod, Z-op, n ≤ 6 | 0 / 952 each |
| pos-mu, gen, pia-notOP-mid | 0 / 24, 0 / 7, 0 / 5299 |
| **neg:A-e** | 503 / 2450 fail |
| **neg:C-e** | 534 / 5928 fail |
| **neg:C-mid**, **neg:D-mid** | 5299 / 5299 fail each |
| **neg:W-strict** | 399 / 405 fail |
| **neg:F-nokappa** | 38665 / 39617 fail |
| **neg:Wdual-top** | 405 / 405 fail |

Every negative control fires. The unit tests add a harness-level negative
control: replacing the necklace by the word itself, so that e_C becomes e,
makes `[A]` and `[C]` report failures.

## Reproduce

```sh
cd compute
python3 audit_mu_op_elementary.py            # n <= 6 every check, n = 7 Theorem A, C, D, W; about 3 min
python3 audit_mu_op_elementary.py --nmax 5   # about 1 s
python3 -m unittest test_audit_mu_op_elementary
```

The output of the full run is in `compute/output/audit_mu_op_elementary.txt`.
The script exits with status 0 iff every asserted check passes and every
negative control fires. [JS] v2 source: `https://arxiv.org/e-print/1112.5782v2`
(a gzipped tar archive; the text is `poset_partitions.tex`).
