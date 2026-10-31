# Audit of `notes/quotient_categories.md` (the STOP verdict)

This is an independent, adversarial audit of `notes/quotient_categories.md` ("[QC]",
merged 5fd196d). Every proof labelled PROVEN in the six items below was re-derived by hand.
Every COMPUTED claim was recomputed with new code, `compute/audit_quotient_categories.py`
("[AUD]"). It imports nothing from the repository, and in particular nothing from
`compute/quotient_categories.py`. Two primary sources were read in full text for this
audit: Vallette 2007 (arXiv math/0405312v3) and Ehrenborg–Jung 2013 (arXiv 1312.2036). For
Shareshian 2003, only the published abstract was read.

## Verdict

**Overall: STOP stands.** The reasons given for it need two corrections, and one of them
is substantive.
- The proofs in the repo do use a quotient-level axiom that is not on the (R1)–(R7) list,
  and that axiom does real work without convexity. It is the Björner–Walker
  complementation axiom (C) below, used by Route C (`notes/lean_js_route.md` §3, audited).
  So "only (R1) forces spheres" is false as written.
- STOP survives anyway. [QC]'s own reversal test (§4) asks for a mechanism other than
  Koszulness, convexity or complementation, and (C) is complementation.
- The case against the bare interval axioms (Q1)–(Q3) is stronger than [QC] says. With a
  single fiber allowed, which [QC] itself allows for Tits buildings, (Q1)–(Q3) hold for
  *every* finite lattice. So "(Q1)–(Q3) ⇒ wedge" is false outright, not merely as hard as
  Shareshian's conjecture.

| # | Claim of [QC] | Verdict | Where |
|---|---|---|---|
| 1a | §1.2–1.3: the proofs use (R1)–(R7); "(Q1) and (Q3) are not used by any proof in [GT] or [TE]" | **FIXABLE.** (Q3) is used, in the form of localization: [GT] Lemma 0.1(c) in Thm 1 Step 3, and the product (C_P)_σ = ∏ C_{P\|B} in Cor. 1.4. It is derived from (R1), so nothing breaks | §1.1 |
| 1b | §1.3: "the proofs never use a lattice-closure property … closure under common refinement … is not used either"; §1.3–§4: "only (R1) forces spheres" | **FAILS** as a claim about the repo's proofs. Route C proves homology concentration for OP(P) from meet-closure, a complement condition and (Q2), with no convexity at all. Its homotopy form is Björner–Walker. This is the steelman (axiom (C)). It does **not** reverse STOP | §1.2–1.3 |
| 1c | (R5), (R7) as independent axioms | **FIXABLE (remark).** (R5) is a consequence of (R1) for any linear action ([TE] Lemma F needs no orbit poset). (R7) holds for every P; connectedness is not needed ([AudE] §3.5) | §1.1 |
| 2a | §2.3: (Q1)–(Q3) hold for G-sets; Q(G/1) = L(G); L(A_4), L(S_4) are not CM | **HOLDS.** Recomputed: L(A_4) has H̃_0 = ℤ^4 in dimension 1, and L(S_4) has H̃_1 = ℤ^12 in dimension 2. L(A_5) (H̃_1 = ℤ^60 in dimension 2) is not CM either, which [QC] does not say. One precision: (Q3) holds only in the orbit-twisted form | §2.1 |
| 2b | "A theorem from these axioms alone would prove Shareshian's conjecture" | **HOLDS** as a reduction: every open interval (H, K) of a subgroup lattice is Q̄_K(K/H). It is **understated**: in [QC]'s own single-fiber reading, (Q1)–(Q3) hold for the face lattice of RP², so such a theorem is false | §2.2–2.3 |
| 3 | Prop. 3.1: OP(P) is not a Vallette poset with its natural labels | **HOLDS, with a gap in the proof (FIXABLE).** The proof fixes the quotient label ν = P/π, but Vallette's order only asks that *some* ν exist. A counting argument closes the gap whenever 𝒫(2) is finite. Other labellings stay OPEN. **No effect on STOP** | §3 |
| 4 | §2.2: the d-divisible explanation is Ehrenborg–Jung 2013 | **HOLDS** (read): their Ex. 3.2, Thm 4.2, Lemma 5.2 and Thm 5.3 are exactly [QC]'s steps. Small wording slip: EJ do use a hyperplane arrangement (their Lemma 2.1) | §4 |
| 5a | Prop. 2.1 (mixed graphs) | **HOLDS** | §5.1 |
| 5b | Prop. 2.2 (d-divisible, pointed) | **HOLDS** | §5.2 |
| 5c | §2.2 "unpointed variant": Δ(rank-selected) ≃ Δ(Q) ∨ ⋁_π S^{k(π)−2} ∗ Δ(Q_{>π}) | **FAILS as printed, FIXABLE.** It must be Q_{<π} (strictly finer). The printed form has the wrong dimensions and the wrong ranks (COMPUTED) | §5.2 |
| 5d | (R5) proof and `[FIX]` counts (602 pairs; control 478) | **HOLDS.** Both numbers reproduced exactly | §5.3 |
| 6 | Negative control: at-most-2-to-1 quotients, 3-torsion at n = 7; interval sizes 27 vs 77 | **HOLDS** (recomputed) | §6 |
| — | Stale status: [QC] says Theorem E is "PROVEN, audit pending" (lines 44–45, 146–147, 174, 387) | **STALE.** Theorem E is audited (`notes/audit_theorem_e.md`, folded into [TE] in f2b0ff4). Reported only; [QC] not edited | — |

Abbreviations:
- [GT] = `notes/general_theory.md`; [TE] = `notes/theorem_e_equivariant_wedge.md`.
- [JSR] = `notes/lean_js_route.md`; [AudJSR] = `notes/audit_lean_js_route.md`;
  [AudE] = `notes/audit_theorem_e.md`.
- [V] = Vallette, *Homology of generalized partition posets*, JPAA 208 (2007) 699–725.
- [EJ] = Ehrenborg–Jung, *The topology of restricted partition posets*, J. Algebraic
  Combin. 37 (2013) 643–666.
- [BW] = Björner–Walker, *A homotopy complementation formula for partially ordered sets*,
  European J. Combin. 4 (1983); cited from memory, as in [JSR].

The `[TAG]` labels are output lines of [AUD] (Reproduce).

---

## 1. Item 1: which axioms the proofs use

### 1.1 [GT] Thm 1, Thm 2, Cor. 1.4 and [TE] Lemma F, read against (R1)–(R7)

- **[GT] Thm 1.**
  - Step 2 uses (R2) together with (R1) and Lemma 0.2. [QC] has this right.
  - Step 3 uses Lemma 0.1(c): for a flat X ⊆ lin V, [X, ℝ^d] ≅ Λ(V_X). In OP order, a flat
    X ⊆ lin C_P is a partition σ coarser than the components. The interval [X, ℝ^d] is
    then the lower interval [0̂, σ] of OP(P), and V_X = ∏_{B∈σ} C_{P|_B}. That is
    **(Q3)** at σ.
  - It enters Step 3 as "Λ̄_{>Y} is the proper part of Λ(V_Y)".
- **[GT] Cor. 1.4** uses the same product explicitly: (C_P)_σ = ∏ C_{P|_B}, and Λ and μ
  are multiplicative. It also feeds the recursion that gives m = e_C.
- So the sentence "(Q1) and (Q3) are not used by any proof in [GT] or [TE]" (§1.3) is
  false. The damage is nil: the localization is proved geometrically from (R1).
  **Fix:** "(Q3) is used, at partitions coarser than the components, as localization of
  the cone; it is a consequence of (R1)."
- **[TE] Lemma F** is stated and proved for an arbitrary finite group of linear maps
  preserving A and |V|. It uses averaging (convexity), pointedness, and the restricted
  arrangement on Fix(H). It never forms an orbit quotient object.
  - (R5) is its *reading* in the braid case, not an input. Given (R1) and a linear
    action, (R5) is automatic.
  - This strengthens [QC]'s point that (R1) carries the weight.
- **(R7).** [AudE] §3.5: Aut(P) acts freely on Lin P for every finite P. In (R7),
  "P connected ⇒" is true but the hypothesis is not needed. Connectedness enters only
  through (R6).
- **Nothing else.** [TE] §2 additionally uses the G-CW structure of order complexes, the
  equivariant Whitehead theorem, Hurewicz and the chamber basis. These are generic, not
  properties of the quotients.

### 1.2 Route C uses an axiom that is not on the list

[JSR] §3 proves (V): H̃_d(Δ(OP̄(P))) = 0 for d ≠ n − 3. [AudJSR] audited it (HOLDS), and
`notes/audit_mo17370.md` V4 checked it over ℤ. Its inputs are:
- **meet-closure:** x ∧ π_a ∈ OP(P), where ∧ is the meet of Π_n (Lean
  `isOrderPreserving_inf`);
- **a complement condition (Lemma M(b)):** for a minimal a and t = π_a = {a} | rest, the
  elements x with x ∧ t = 0̂, other than 0̂ itself, are exactly the atoms π_ab of OP(P);
- **(Q2) at those atoms (Lemma U):** (π_ab, 1̂) ≅ OP̄(P/π_ab).

No convexity, no cone and no arrangement appear anywhere. [QC] §1.3 says closure under
common refinement "is not used either", and its §1 inspects only [GT] and [TE]. For the
repo as a whole, that is false.

COMPUTED (`[CMP]`), on all naturally labelled P with n ≤ 5 (every poset up to
isomorphism), 959 pairs (P, a minimal):
- OP(P) is closed under the meets of Π_n.
- The lattice complements of π_a, and also its meet-complements, are exactly the atoms
  π_ab.
- |[π_ab, 1̂]| = |OP(P/π_ab)|.
- Control, which must fail and does: in Π_4, t = 01|23 has the non-atom complements
  02|13 and 03|12.

### 1.3 The steelman: one honest non-geometric axiom that does work

**Axiom (C) (complementation).** For every object X with Q̄(X) ≠ ∅ there is a
t ∈ Q̄(X) such that:
- its complements in Q(X) form an antichain;
- every complement is an atom a;
- [a, 1̂] ≅ Q(X/a) for an object X/a of the class.

**Claim (PROVEN, given [BW]'s homotopy complementation formula, cited from memory).** In a
class satisfying (Q1), (Q2) and (C), every Q̄(X) is a wedge of spheres. The wedge is pure
when all the X/a have the same length.

*Proof.* [BW] gives L̄ ≃ ⋁_{a ⊥ t} Σ(Δ(0̂, a) ∗ Δ(a, 1̂)). For an atom, Δ(0̂, a) = ∅, so
the summand is Σ Q̄(X/a). Induct on the length, with Σ∅ = S^0. ∎

**Where it holds.**
- **OP(P):** COMPUTED, n ≤ 5, and proved in [JSR].
- **Π_n:** by hand, t = {n} | rest.
- **Subgroup lattices, at the top level:** `[CMP]` finds such a t in L(A_4) (|t| = 2, 4),
  in L(S_4) (|t| = 8, 12; e.g. t = A_4, whose complements are the six transposition
  subgroups) and in L(A_5) (|t| = 10).

**Why it does not reverse STOP.**
1. (C) is complementation, and complementation is one of the three known mechanisms that
   [QC] §3 names (Björner–Walker, Kozlov, Arone–Brantner). [QC] §4 says the verdict would
   reverse only for a mechanism outside these three.
2. Its use for OP(P) is Route C itself, which is already in the repo.
3. For G-sets the induction runs into exactly Shareshian's problem. (C) at the top of
   L(G) is not enough: one needs it for every interval (H, K), and that is where the
   non-solvable cases live. The solvable case uses complements to a chief series
   (Thévenaz, per the 2007 Woodroofe preprint arXiv 0708.3539, search snippet only).

**What [QC] should say instead of "only (R1) forces spheres".** "The repo has two
sources of sphericity: convexity (R1), in [GT] and [TE], and complementation (C), in
Route C. Both are known mechanisms, and neither is supplied by the interval axioms."

---

## 2. Item 2: G-sets and Shareshian

### 2.1 (Q1)–(Q3) for G-sets; Q(G/1) = L(G) (HOLDS)

- **(Q1), (Q2).** Meets and joins of G-invariant partitions are G-invariant, and the
  correspondence theorem gives (Q2).
- **Q(G/1) ≅ L(G).** The block of e in a left-invariant partition of G is a subgroup H,
  and the blocks are its cosets gH.
  - COMPUTED (`[GSET]`): S_3 has 6 left-invariant partitions out of Bell(6) = 203, and
    P ↦ (block of e) is an order isomorphism onto L(S_3).
  - Control: the right cosets of a non-normal C_2 are rejected.
- **(Q3), precisely.** A G-invariant refinement of π is determined by its restriction to
  one block B per orbit of blocks. That restriction is G_B-invariant. So
  [0̂, π] ≅ ∏_{orbits} Q_{G_B}(B), and the fibers are G_B-sets, not G-sets.
  - [QC] states this orbit-twisted form. It is the true one.
  - The literal "∏ over blocks B" fails for G-sets.
  - So the "category" here is the collection of all pairs (G, X), not the G-sets of one
    group. This is harmless for the reduction.
- **Homology.** COMPUTED, mod 2, 3, 5 and 2^31 − 1, all agreeing (so no small torsion):

  | G | #subgroups | μ(1̂, G) | dim Δ(L̄) | H̃ |
  |---|---|---|---|---|
  | A_4 | 10 | 4 | 1 | H̃_0 = ℤ^4 |
  | S_4 | 30 | −12 | 2 | H̃_1 = ℤ^12 |
  | A_5 | 59 | −60 | 2 | H̃_1 = ℤ^60 |

  All three have homology below the top degree, so none is Cohen–Macaulay. [QC] matches
  the first two rows and gives the A_5 row without drawing that conclusion.

### 2.2 The reduction to Shareshian (HOLDS)

**Shareshian** (J. Algebra 268 (2003) 677–686; abstract read on the publisher's profile
page): "We conjecture that the order complex of an open interval in the subgroup lattice
of a finite group has the homotopy type of a wedge of spheres." Non-pure wedges are
allowed. He proves that a minimal counterexample (H, G) has G almost simple, or G = HN
with N the unique minimal normal subgroup, non-abelian, and H ∩ N = 1.

**The reduction is exact.**
- The interval (H, K) of L(G) is the proper part of [H, K] in L(K). That is the upper
  interval at H of Q_K(K/1), i.e. Q̄_K(K/H) by (Q2).
- COMPUTED: for S_4 and every H of order 3, 4, 6 or 8, the number of G-invariant
  partitions of G/H equals #{K ≥ H}.
- So a theorem "(Q1)–(Q3) + Aut-action ⇒ Q̄(X) is a wedge", applied to the transitive
  K-sets, *is* Shareshian's conjecture for all intervals. The objects needed are the
  transitive sets K/H, so the extra generality of arbitrary G-sets is not needed.
- [QC]'s second claim, that "⇒ wedge of top-dimensional spheres" is false, is right, by
  the A_4 example.

**Status.** No resolution was found. A search turned up only partial cases, e.g.
PSL_2(4) and the R(3) example in arXiv 2004.05677, from snippets only. "OPEN" is the right
tag. [QC] marks the citation "from search results, not read". This audit read the
abstract, not the paper.

### 2.3 Stronger than Shareshian: (Q1)–(Q3) force nothing

[QC] §1.3 states (Q1)–(Q3) abstractly: Q(X) is a lattice, and there is no underlying set.
§2 (Tits building) accepts (Q2)–(Q3) "with a single fiber". In that reading, take any
finite lattice L:
- the objects are the intervals [x, y];
- Q([x, y]) = [x, y];
- the quotient by z is [z, y], and the single fiber is [x, z].

(Q1)–(Q3) then hold tautologically. Now take L = the face lattice of the 6-vertex RP²
with 0̂ and 1̂ adjoined. COMPUTED (`[INT]`): it is a lattice with 33 elements, and its
proper part has reduced Betti numbers {1: 1, 2: 1} mod 2 but none mod 3. So it has
torsion and is not a wedge of spheres.

So "(Q1)–(Q3) ⇒ wedge" is **false**, not merely Shareshian-hard. A meaningful version
must require partition-type data: Q(X) ⊆ Π_X, and (Q3) with the fibers being the actual
blocks. The G-set reduction is the right hardness statement for *that* version. This
strengthens the second half of the STOP.

---

## 3. Item 3: Proposition 3.1 against Vallette

**What [V] says (read, arXiv v3).**
- **𝒫-partitions** (§3.1.1): partitions whose blocks are decorated by elements of 𝒫(I_j).
- **Order** (§3.1.2): λ ≤ μ if each block B_k of λ is a union of blocks C_p of μ and
  "there exists an element ν in 𝒫_t such that B_k = μ̃(ν × (C_{p_1}, …, C_{p_t}))".
- With 𝒫_1 = {id}, the unique maximal element 1̂ is the partition into singletons. The
  minimal elements are 𝒫_n([n]). So [V]'s order is *reverse* refinement.
  - [QC]'s summary "a coarser element is obtained by composing" has the direction loose,
    but the content is right.
- **Basic-set** means that each map ν ↦ μ(ν(ν_1, …, ν_t)) is injective.
- **Thm 9:** for a basic-set quadratic operad generated in one arity, 𝒫̃ is Koszul iff
  every [α, 1̂], with α ∈ 𝒫_n([n]), is Cohen–Macaulay. [QC]'s statement is correct.

**The gap.** [QC]'s proof sets ν = P/π. [V]'s order only asks that *some* ν ∈ 𝒫_t exist,
so the collision "P and P′ have the same (P/π, P|_B)" is not by itself a contradiction:
P and P′ could use different ν.

**The fix (PROVEN, by counting).** Suppose OP(P) were [P, 1̂] in some Π_𝒫(n), with the
blocks labelled by their restrictions P|_B, so that P ∈ 𝒫_n. Take a k-antichain B, a
point c, and π = {B} | {c}.
- The posets Q on B ⊔ {c} with Q|_B an antichain and π acyclic are those with c above a
  subset of B, or c below a subset of B. If c lay above b and below b′, then b < b′,
  contradicting that B is an antichain. There are 2^{k+1} − 1 such Q (COMPUTED `[VAL]`
  for k ≤ 5).
- Each such Q must equal μ̃(ν_Q × (antichain_B, id_c)) for some ν_Q ∈ 𝒫_2, and different
  Q need different ν_Q.
- So |𝒫_2| ≥ 2^{k+1} − 1 for every k.

Hence no operad with finite 𝒫(2) works, in particular no finitely generated quadratic
one. That is the setting of [V], where the posets Π_𝒫(n) are finite (Prop. 3(1)).
**Fix for [QC]:** replace the ν = P/π argument by this count.

**What stays open.** Two cases remain:
- block labels that are not restrictions (richer decorations, Perm-style markings);
- operads with infinite 𝒫(2).

In both, the decorations would have to carry the comparabilities between blocks.
Nothing here rules that out, so "OP(P) is a Vallette poset for *some* labelling" is
OPEN. [QC]'s sentence "by the previous paragraph it would not be the quotient structure"
is too strong. Such a labelling could have exactly the acyclic quotients as its
underlying partitions.

**How much this weakens STOP: not at all.** Thm 9 is an equivalence. An exotic operadic
realization of OP(P) would turn OP(P)'s already-known CM property into the Koszulness of
an exotic operad. It would supply no source of sphericity. It would also be one operad
per P, or a single operad on all posets with infinite 𝒫(2), not a uniform framework.
[QC]'s judgement "not interesting" stands, with its supporting sentence weakened as
above.

---

## 4. Item 4: d-divisible = Ehrenborg–Jung (HOLDS)

Read in [EJ] (arXiv 1312.2036; journal reference J. Algebraic Combin. 37 (2013)
643–666, as recorded on arXiv):
- **Pointed set partitions** (§2): pairs (σ, Z). By Lemma 2.1, Π•_n is the intersection
  lattice of {x_i = x_j} ∪ {x_i = 0}, and Π•_n ≅ Π_{n+1}.
- **Example 3.2:** for c = (d, …, d, d−1), Π•_c ≅ Π^d_{n+1}.
- **Thm 4.2:** Δ_c = Δ(B_n(S)) is shellable, its spanning facets are the permutations
  with descent composition c, and it is a wedge of β(c) spheres of dimension k − 2.
- **The map.** φ: ordered set partitions → pointed partitions "forgets the order between
  the blocks except it keeps the last part as the pointed block".
- **Lemma 5.2:** each fiber φ^{-1}(Π•_c − 1̂)_{≥π} is a cone, hence contractible.
- **Thm 5.3:** Quillen's fiber lemma then gives Δ(Π•_c − 1̂) ≃ Δ_c.

This is [QC] §2.2 step for step:
- the dual claw T, with n in the last block, is "keep the last block pointed";
- the rank selection is the same;
- the contractible fibers are the same.

The attributions in [QC] are correct: Stanley for the Möbius function, Wachs for the EL
labelling and for vanishing below the top degree, Calderbank–Hanlon–Robinson for the
S_{n−1}-module. All three are in [EJ]'s introduction.

**One wording slip.** [QC] says EJ "never mention cones". True for polyhedral cones; EJ
say "cone" only for a simplicial cone. But EJ do realize Π•_n as an arrangement's
intersection lattice (Lemma 2.1). So [QC]'s sentence "the pointing is the pointedness
axiom (R6)" is a short step from [EJ] Lemma 2.1, not a new link. The observation stands
as an observation.

---

## 5. Item 5: Props 2.1, 2.2, the unpointed variant, and (R5)

### 5.1 Prop. 2.1, mixed graphs (HOLDS)

- **(a).** Re-derived. A point x in the relative interior of a face of V has
  span = Y_π, where π is the set of components of the equality edges. An arc between two
  blocks then has x_i < x_j strictly; otherwise its edge would merge the blocks. So the
  block digraph is acyclic. Conversely, a strictly increasing assignment exists iff the
  block digraph is acyclic.
- **(b)** is [GT] Thm 1. Λ(V) is taken over the A_G-faces inside V, so its bottom is
  always the flat of the components and its length is n − c(G), whether or not V is
  pointed.
- **(c).** S_max(V) is the set of edges whose orientation is forced. An edge is forced
  iff a directed arc path joins its ends, so the components of (V, E_0) equal those of
  (V, arcs).
- **COMPUTED (`[MIX]`).** Λ(V) was computed *from points*: every function [n] → {0,…,n−1}
  in V, recording the components of its equality edges. This is independent of the
  description in (a).
  - 4,071 cases: all n ≤ 4, plus 400 seeded n = 5 cases (my sample; [QC]'s 3,902 uses a
    different sample and enumeration, so the totals are not comparable).
  - (a) holds on every case.
  - Homology is concentrated in degree n − c(G) − 2 with rank ≥ 1.
  - All 2,294 pointed cases have m = #V. All 1,777 non-pointed cases have m < #V.
  - Controls:
    - one edge on 3 vertices gives |Λ| = 2 < 5;
    - replacing "acyclic" by "no 2-cycle" changes Λ;
    - the triangle with one arc is non-pointed, with m = 2 < #V = 3.

### 5.2 Prop. 2.2 (HOLDS) and the unpointed variant (FAILS as printed, FIXABLE)

**Prop. 2.2: re-derived.** Two silent points, neither an error:
- O′ must exclude the one-block ordered partition (the lineality face), because Q
  excludes 1̂.
- s is order-*reversing* from the face order to refinement. Quillen applies to Q^op, and
  Δ(Q) = Δ(Q^op).

COMPUTED (`[DDIV]`) for (n, d) = (4,2), (6,2), (6,3), (8,2), (9,3), (8,4):
- Δ(Q) has only H̃_{n/d−2}, of rank β_{n−1}(S), with values 2, 16, 9, 272, 477, 34.
- Δ(B_{n−1}(S)) has the same Betti numbers.
- All the pointed Quillen fibers are acyclic: 3, 30, 10, 378, 364 and 35 of them.

**The unpointed formula is wrong as printed.** [QC] has fibers s^{-1}(Q_{≥π}) and the
join with Δ(Q_{>π}).
- **The rule.** Because s reverses order, BWW ([GT]'s statement: fibers below, join with
  the part above) applied to s : O → Q^op joins each fiber with (Q^op)_{>π} = Q_{<π},
  the strictly *finer* partitions.
- **Dimensions.** With Q_{<π}: (k−2) + (n/d − k − 1) + 1 = n/d − 2, the top degree, as it
  must be. With Q_{>π}: (k−2) + (k−3) + 1 = 2k − 4, which depends on π.
- **COMPUTED.**
  - With Q_{<π}, Δ(Q) ∨ ⋁ S^{k−2} ∗ Δ(Q_{<π}) has exactly the Betti numbers of
    Δ(B_n(S)), namely β_n(S) = 5, 61, 19, 1385, 1513, 69, in all six cases.
  - With Q_{>π} it gives {0: 15, 1: 16, 2: 30} at (6,2), against the true {1: 61}, and
    it is wrong at (8,2) and (9,3) too.
- **Fix:** replace Δ(Q_{>π}) by Δ(Q_{<π}) in [QC] §2.2. [QC]'s computed "Euler identity
  holds" is consistent only with the corrected form.

### 5.3 (R5) (HOLDS)

- **The proof.** Re-derived. Height is Aut-invariant, so the orbit preorder is acyclic.
  An H-stable face satisfies (hB_1, …, hB_k) = (B_1, …, B_k) positionally, so every
  block is H-stable. The detour through "an order-preserving bijection of a chain"
  is not needed, but it is correct. The converse is clear.
- **COMPUTED (`[FIX]`):**
  - the naturally labelled posets for n = 1, …, 5 number 1, 2, 7, 40, 357;
  - on all **602** pairs (P, g ≠ 1), the H-stable faces equal the pullbacks, and no
    orbit preorder is cyclic;
  - the g² control is rejected on **478/478** pairs.

  Both of [QC]'s numbers are reproduced exactly.

---

## 6. Item 6: the negative control (HOLDS)

COMPUTED (`[NEG]`):
- **The complex.** The matching complex M_7 has f-vector (21, 105, 105).
- **Torsion.** Its reduced Betti numbers are {2: 20} mod 2 and mod 2^31 − 1, and
  {1: 1, 2: 21} mod 3. So H_1 has 3-torsion (Bouc's ℤ_3, cited from memory as in [QC]).
  The same numbers come out of the order complex of the face poset, which is the proper
  part of [QC]'s Q(7).
- **Controls.**
  - M_6 gives {1: 16} for both primes, so the detector is silent on a torsion-free case.
  - RP²_6 separates mod 2 from mod 3.
  - The 7-vertex torus agrees across primes.
- **(Q2) fails.** For π = one 2-block, |[π, 1̂]| = 26 + 1 = **27**. The 6-element
  quotient has |Q| = 76 + 1 = **77**, so (Q2) fails.

[QC]'s diagnosis is right: the class is not closed under composition. Two 2-to-1 maps can
compose to a 4-to-1 map.

---

## 7. What to change in [QC]

None of these changes the verdict.
1. §1.3, the (Q3) sentence: (Q3) is used in [GT] Thm 1 Step 3 and Cor. 1.4, as
   localization (a consequence of (R1)).
2. §1.3, "common refinement … not used": false for Route C. Add axiom (C) and the
   two-mechanism sentence of §1.3 above. In the Summary and in §4, replace "only (R1)
   forces spheres" by "(R1) or complementation (C), both known mechanisms".
3. §1.2: (R5) is a corollary of (R1) for linear actions. (R7) needs no connectedness.
4. §2.3: add that in the single-fiber reading, (Q1)–(Q3) hold for every finite lattice
   (the RP² face lattice), so the bare axioms force nothing. Note that (Q3) for G-sets is
   orbit-twisted. Add that L(A_5) is not CM either.
5. Prop. 3.1: replace the ν = P/π step by the 2^{k+1} − 1 count, and scope it to
   restriction labels with finite 𝒫(2). Soften "it would not be the quotient structure".
6. §2.2, unpointed variant: Q_{>π} → Q_{<π}. Optionally, cite [EJ] Lemma 2.1 next to the
   "pointing = pointedness" remark.
7. Status: Theorem E is PROVEN and AUDITED (`notes/audit_theorem_e.md`). Remove "audit
   pending" at lines 44–45, 146–147, 174 and 387.

## Not checked

- §2's NC(n) row, the Dowling and geometric-lattice rows, and the prior-art paragraphs on
  Batanin–Markl, Kaufmann–Ward, Gálvez-Carrillo–Kock–Tonks, Fauvet–Foissy–Manchon and
  Arone–Brantner. These were outside the six items.
- [BW]'s formula itself (cited from memory) and Kratzer–Thévenaz / Thévenaz (snippet
  only).
- Whether axiom (C) has reach beyond the lattices where complementation is already known
  to work. This was not explored.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process; imports nothing
from the repo):

    python3 audit_quotient_categories.py > output/audit_quotient_categories.txt   # ~10 s, ends "ALL CHECKS PASS: True", exit 0
    python3 audit_quotient_categories.py --quick                                  # ~2 s (no A_5, sampled [MIX], small [DDIV])
    python3 -m unittest test_audit_quotient_categories                            # < 1 s

Ranks are taken mod p (2, 3, 5 and 2^31 − 1). Different Betti numbers for different primes
certify torsion. When the Betti numbers agree for all four primes, small torsion is
excluded for those primes.
