# Literature and novelty check; Jenča–Sarkoci, explicit JKS maps, Aguiar–Mahajan

Work item: mg-92751. Subject: the reference list of
`notes/poset_jks_research_note.tex`, and the statements the note relies on:
eq. (JSdim), eq. (mainconj), eq. (restrictionlemma), and the sections
"A second formulation using Lie idempotents", "Potential proof via splitting
spheres" and "Potential proof via hyperplane-arrangement Lie theory".

Every claim is tagged PROVEN (proof given here), COMPUTED (script and command
given), CITED (exact source given) or CONJECTURED. The note's own
computational claims are not used as evidence. The independent reproduction
in `notes/reproduce_character_identity_n_le_5.md` is cited by file name where
it is used.

Notation follows the note. P is a poset on [n], O(P) = OP(P) is the lattice
of order-preserving partitions, H_P = H̃_{n−3}(Ô(P); C), and
W_P = C{Lin(P)} ⊂ C[S_n]. A word w = w_1⋯w_n is the permutation
i ↦ w_i. Left multiplication gw relabels letters. Right multiplication wσ
permutes positions, so wγ^j is w rotated left by j. ρ_w denotes the splitting
cycle of the word w (§3.1). Sh_n ⊂ C[S_n] is the span of the proper shuffles
u ш v, where u and v are nonempty words on complementary letter sets.

## Summary

1. **Novelty (CITED / searched).** SEE §1.
2. **Jenča–Sarkoci (CITED).** Their theorem is exactly what the note uses.
   Their cyclic classes are the C_n-orbits meeting Lin(P), in the note's sense.
   The only hypothesis is n ≥ 3; P need not be connected or labeled. Their
   recursion is equivariant only for Stab_{Aut P}(a), where a is a fixed
   minimal element. Every g ≠ 1 in such a stabilizer contributes 0 to the
   Lie-side character (PROVEN, §2.3). So the recursion cannot see the
   root-of-unity phases, which is the whole new content of eq. (characterconj).
3. **Explicit JKS maps.** The literature's explicit maps are Barcelo's
   (Lyndon ↔ Björner NBC basis), Wachs's comb correspondence and Wachs's
   general correspondence. The last two are Wachs 1998, Thms 4.3 and 5.4; all
   three agree. Each is stated as Lie_n → H^{n−3}(Π̄_n) ⊗ sgn, on
   *cohomology*. Dualizing gives the following, which is PROVEN from Wachs plus
   Ree and COMPUTED for n ≤ 5:

   > Φ : H̃_{n−3}(Π̄_n) ⊗ sgn → C[S_n]/Sh_n, ρ_σ ↦ sgn(σ)·σ (mod Sh_n),
   > is an S_n-isomorphism. In other words, the linear relations among the
   > splitting cycles are exactly the sign-twisted shuffle relations.

4. **eq. (restrictionlemma) is false as stated (PROVEN).** No linear map J
   whatsoever satisfies J(H_P ⊗ sgn) = W_P e_ζ for both a chain and its dual,
   for any n ≥ 3. P and P^op have the same O(P), so they have the same H_P,
   but W_P e_ζ ≠ W_{P^op} e_ζ. The same obstruction applies to the "second
   formulation" W_P κ_n with Klyachko's idempotent (COMPUTED for n = 3, 4, 5).
   **The conjecture eq. (mainconj) is untouched.** It asserts only an abstract
   isomorphism. What fails is the proposal to get it as the image of one
   fixed JKS map.
5. **Corrected restricted image identity, and a reduction (PROVEN given
   Conjecture S below).** For every w ∈ Lin(P), the splitting cycle ρ_w lies
   in H_P. Under Φ, span{ρ_w : w ∈ Lin P} goes to (W_P + Sh_n)/Sh_n.

   > **Conjecture S.** span{ρ_w : w ∈ Lin(P)} = H_P. Equivalently,
   > dim (W_P + Sh_n)/Sh_n = e_C(P).

   Conjecture S is COMPUTED for every poset with n ≤ 6 (all 318 unlabeled
   posets at n = 6). Assuming it, the following hold:
   - (a) H_P ⊗ sgn ≅ W_P/(W_P ∩ Sh_n) canonically, as Aut(P)-modules.
   - (b) For **connected** P, eq. (mainconj) holds, because both sides are the
     free module C[Lin P].
   - (c) For general P, eq. (mainconj) is equivalent to
     W_P/(W_P ∩ Sh_n) ≅ W_P/(W_P ∩ C[S_n](1 − e_ζ)) as Aut(P)-modules.
6. **Recommendation for the containment-proof item.** Use J = Φ, the dual of
   Wachs's comb correspondence, with target Lie_n^* = C[S_n]/Sh_n. If a
   subspace of C[S_n] is required, compose with right multiplication by the
   adjoint Dynkin element θ_n^*, whose kernel is exactly Sh_n. Replace the
   target statement eq. (restrictionlemma) by Conjecture S. Do not try to
   prove containment in W_P e_ζ or W_P κ_n: it is false.
7. **Aguiar–Mahajan.** SEE §4.
8. **Bibliography corrections.** See §5.

---

## 1. Novelty search

SEE AGENT

## 2. Jenča–Sarkoci

Source read: arXiv:1112.5782v2 (1 Apr 2015), the accepted version of
G. Jenča and P. Sarkoci, *Linear extensions and order-preserving poset
partitions*, J. Combin. Theory Ser. A **122** (2014) 28–38,
doi:10.1016/j.jcta.2013.09.010. Numbering is that of the arXiv version. The
published numbering was not checked against it.

### 2.1 Exact statements (CITED)

- **Definition 3.1** (after Körtesi–Radeleczki–Szilágyi). Let ρ be an
  equivalence on P. A ρ-sequence is a sequence x_0, …, x_m with
  (x_{i−1}, x_i) ∈ ρ or x_{i−1} < x_i for each i. A ρ-cycle is a ρ-sequence
  with x_0 = x_m. ρ is an *order congruence* if every ρ-cycle lies in a single
  ρ-class. Order-preserving partitions are the quotients by order
  congruences. By Thm 3.3 (Czédli–Lenkehegyi) these are exactly the kernels of
  isotone maps out of P. This agrees with the note's definition ("P/π
  acyclic"). The covering relation (p. 5) merges two blocks that are either
  incomparable or in a cover relation in P/π.
- **Theorem 3.8.** Let P be finite with n ≥ 3 elements. Then Δ(Ô(P)) is
  homotopy equivalent to a wedge of spheres of dimension n − 3. Let a be a
  minimal element and s_O(P) the number of spheres. For n > 3,
  s_O(P) = Σ_{b : π_{a,b} order-preserving} s_O(π_{a,b}), where π_{a,b} is the
  atom merging a and b, and s_O(π_{a,b}) is computed for the quotient poset
  P/π_{a,b}. The proof is a discrete Morse matching built by induction from
  Kozlov's Thm 11.10 (patchwork theorem) and Forman's theorem.
- **Definition 4.1.** For a linear extension f : P → {0, …, n−1}, let ⊕_f be
  the Z_n-action x ⊕_f k = f^{−1}(f(x) + k mod n). Then f ∼ g iff ⊕_f = ⊕_g.
  A cyclic class is a ∼-class, and e_C(P) is the number of cyclic classes. The
  paper adds: "f ∼ g iff there are words w, w′ with f = ww′ and g = w′w."
- **Prop. 4.3 / Cor. 4.4.** P is connected iff ∼ is trivial iff
  e(P) = e_C(P).
- **Theorem 4.5 (Main result).** Let P be finite with n ≥ 3 elements. Then
  Δ(Ô(P)) is homotopy equivalent to a wedge of e_C(P) spheres of dimension
  n − 3.
- **Corollary 4.12.** If P is connected, the number of spheres is e(P).

### 2.2 Does the note use it correctly? (PROVEN)

*The note's e_C(P) equals the paper's e_C(P).* A ∼-class is a set of linear
extensions that are pairwise rotations of each other (the paper's remark
after Def. 4.1). It therefore lies in a single C_n-orbit {wγ^j} of S_n.
Conversely, any two linear extensions in one C_n-orbit are rotations of each
other, so they are ∼-equivalent. So ∼-classes correspond bijectively to the
C_n-orbits that meet Lin(P), which is the note's definition.

*Hypotheses.* The only hypothesis is n ≥ 3, with P finite. Connectedness is
not assumed; it enters only in Cor. 4.12. Labeling plays no role. So
eq. (JSdim) and the note's sentence "if P is connected, then e_C(P) = |Lin(P)|"
are exactly CITED (Thm 4.5, Cor. 4.4).

*A reformulation the note can use.* A cyclic class C determines the directed
n-cycle C(f, P) on the ground set P, with edges x → x ⊕_f 1. Distinct classes
give distinct cycles. g ∈ Aut(P) fixes C iff g is an automorphism of that
directed cycle, i.e. a rotation of it. The rotation amount is the note's
r_g(C).

### 2.3 Can the recursion be made Aut(P)-equivariant?

**Lemma A (PROVEN).** If g ∈ Aut(P) fixes some cyclic class C and fixes some
point of P, then g = 1. Consequently:
- χ_{Lie(P)}(g) = 0 for every g ≠ 1 with a fixed point.
- χ_{Lie(P)}(g) ≠ 0 forces all cycles of g on [n] to have a common length
  d = n / gcd(n, r_g(C)).
- Lie(P) restricted to Stab_{Aut P}(x) is a free module, for every x ∈ P.

*Proof.* g acts on the directed n-cycle C(f, P) as rotation by r_g(C). A
rotation of an n-cycle that fixes a vertex is the identity, so g = 1. Hence
every g-fixed class requires g to be fixed-point-free. Eq. (liechar) then
gives the vanishing. A rotation by r has all orbits of size n/gcd(n, r). ∎

*Equivariance of the recursion.* Fix a minimal element a, and let
G_a = Stab_{Aut P}(a).
- On the index set: G_a permutes {b : π_{a,b} ∈ O(P)}, and g maps
  P/π_{a,b} isomorphically onto P/π_{a,gb}.
- On the bijection of Lemmas 4.10–4.11: S_a(f) is "contract the edge
  (a, a ⊕_f 1) of C(f, P)". This commutes with G_a, so S_a is G_a-equivariant
  on cyclic classes (PROVEN, by naturality of edge contraction).
- At the level of homology: the discrete Morse matching is not canonical. The
  natural homological candidate is the restriction map
  H_P → ⊕_b H̃_{n−4}(Ô(P/π_{a,b})). It takes the coefficients of the chains
  whose bottom element is π_{a,b}, using [π_{a,b}, 1̂] ≅ O(P/π_{a,b}). This
  map is G_a-equivariant, possibly up to an orientation character. That it
  is an isomorphism is CONJECTURED here, by analogy with the classical
  Res^{S_n}_{S_{n−1}} argument for Π_n. It is not proved in the paper.

**Verdict (PROVEN by Lemma A).** An equivariant J–S recursion at a minimal (or,
dually, maximal) element can at best prove the conjecture restricted to the
stabilizer G_a. By Lemma A that restriction says only "H_P is G_a-free". The
elements that carry the phases ζ^{r_g(C)} are fixed-point-free, so they lie
in no stabilizer. Proving eq. (characterconj) for them needs a different
mechanism. The "direct character identity" item should not expect the J–S
recursion alone to suffice. (Example from the note: the 3-cycle permuting
three disjoint 2-chains fixes no point.)

## 3. Explicit JKS maps

### 3.1 What the literature gives (CITED)

Sources read:
- M. L. Wachs, *On the (co)homology of the partition lattice and the free Lie
  algebra*, Discrete Math. 193 (1998) 287–319. Read from the author's preprint
  `homlie.ps` (dated "Dec. 31, 1994, revised Jan. 1996"), linked from
  https://www.math.miami.edu/~wachs/abstracts/homlie.html. **Theorem numbers
  below are the preprint's; check them against the published version before
  citing in print.**
- M. L. Wachs, *Poset topology: tools and applications*, in Geometric
  Combinatorics, IAS/Park City Math. Ser. 13, AMS 2007, 497–615 (arXiv
  math/0602226). Read from https://www.math.miami.edu/~wachs/papers/toolnotes.pdf.

Facts:
- **Splitting cycles.** For σ ∈ S_n, Π_σ is the subposet of partitions
  obtained by cutting the word σ at any set of positions. It is ≅ B_{n−1}, so
  its proper part is an (n−3)-sphere. ρ_σ is its fundamental cycle, oriented
  so that the chain m_σ (split off σ(1), then σ(2), …) has coefficient +1
  (Wachs 1998 §2, before Prop. 2.3).
  - {ρ_σ : σ(n) = n} is a basis of H̃_{n−3}(Π̄_n; Z), dual to
    {m̄_σ : σ(n) = n} (Wachs 1998 **Prop. 2.3**; Poset Topology
    **Thm 3.2.8**, attributed to Wachs, Adv. Math. 117 (1996)).
  - Pairing: ⟨ρ_σ, m̄_τ⟩ = sgn′(σ^{−1}τ) if σ^{−1}τ is a "minmax" permutation
    (avoiding 213 and 231), and 0 otherwise, where
    sgn′(α) = (−1)^{inv(α(1)⋯α(n−1))} (Wachs 1998 **Lemma 3.1**).
  - Representation matrices in the splitting basis: Wachs 1998 **Thm 3.2**.
- **Other homology bases.**
  - Björner NBC basis {ρ_T : T increasing tree}: Wachs 1998 **Prop. 2.2**;
    Poset Topology **Thm 3.2.9** (tree splitting basis) and **Thm 3.2.15**
    (Björner, general geometric lattices).
  - Caterpillar basis: Wachs 1998 **Thm 2.5**.
  - Expansion of ρ_T in splitting cycles, as a sum over the linear extensions
    ("pruning sequences") of the tree poset T: Wachs 1998 **Thm 3.3**,
    ρ_T = Σ_{σ ∈ P(T)} sgn(σ) ρ_σ. This is the one place in the classical
    literature where linear extensions of a poset index a sum of splitting
    cycles.
- **Lie side.** Lie_n is the multilinear part of the free Lie algebra inside
  C[S_n], with bracket [f, g] = fg − gf. The action is π[T, w] = [T, πw]
  (left, on letters). The right combs r_w = [w_1, [w_2, [⋯, w_n]]], for
  w(n) = n, form a basis (Wachs 1998 §4, citing Björner–Sundaram). The
  coefficient formula is ⟨r_τ, σ⟩ = (−1)^{des(σ^{−1}τ)} if σ^{−1}τ is
  minmax, and 0 otherwise (Wachs 1998 eq. (4-4) and **Thm 4.2**).
- **The maps** (all S_n-isomorphisms Lie_n → H^{n−3}(Π̄_n) ⊗ sgn; cohomology,
  maximal-chain generators):
  - **Barcelo correspondence** (Wachs 1998 **Thm 4.1**; originally Barcelo
    1990, see §3.4): Lyndon basis [A] ↦ m̄_{Φ(A)}. Here Φ is a bijection from
    Lyndon trees to increasing trees, and m_T is the dual Björner chain.
  - **Comb correspondence** (Wachs 1998 **Thm 4.3**, joint with Sundaram):
    r_w ↦ sgn(w) m̄_w for w(n) = n.
  - **General correspondence** (Wachs 1998 **Thm 5.4**):
    ψ([T, w]) = sgn(w) sgn(T) c̄(T, w), for every labeled binary tree. Here
    c(T, w) is the maximal chain that merges L(v) and R(v) at the internal
    nodes v in postorder, sgn(T) is defined recursively by
    sgn(T_1 ∧ T_2) = (−1)^{I(T_2)} sgn(T_1) sgn(T_2), and I(·) counts internal
    nodes. Cohomology presentation by these generators: **Thm 5.3** (=
    Hanlon–Wachs, Adv. Math. 113 (1995), Thm 3.11, case k = 1). The
    introduction states that all three correspondences determine the same
    isomorphism.

### 3.2 The homology-side map Φ (PROVEN from the cited facts; COMPUTED n ≤ 5)

The note wants J on *homology*, because H_P ⊂ H̃_{n−3}(Π̄_n) is a subspace of
homology (eq. homembed). Dualize ψ. Let Q ∈ Lie_n, σ ∈ S_n, and put
α = σ^{−1}τ, where τ(n) = n.

⟨ρ_σ, ψ(r_τ)⟩ = sgn(τ)·⟨ρ_σ, m̄_τ⟩ = sgn(τ) sgn′(α)·[α minmax].

Wachs's proof of Thm 4.3 gives sgn(α) = (−1)^{des α} sgn′(α) for minmax α.
Hence

⟨ρ_σ, ψ(r_τ)⟩ = sgn(σ)·(−1)^{des α}·[α minmax] = sgn(σ)·⟨r_τ, σ⟩.

By linearity in Q (the combs are a basis):

  **⟨ρ_σ, ψ(Q)⟩ = sgn(σ) · (coefficient of the word σ in Q)  for all σ ∈ S_n, Q ∈ Lie_n.**

So z ↦ ⟨z, ψ(·)⟩ is an isomorphism H̃_{n−3}(Π̄_n) → Lie_n^*, sending ρ_σ to
sgn(σ)·(coefficient of σ). Then Lie_n^* = C[S_n]/Lie_n^⊥ (σ ↦ coefficient
of σ), and by Ree's theorem Lie_n^⊥ ∩ C[S_n] = Sh_n. Ree's criterion: a
polynomial without constant term is Lie iff it is orthogonal to every proper
shuffle. Sources: R. Ree, Ann. of Math. 68 (1958) 210–220; C. Reutenauer,
*Free Lie Algebras*, Oxford 1993, Thm 3.1 (CITED from memory; the exact item
letter in Thm 3.1 was not re-checked). The result:

> **Proposition Φ.** The map Φ(ρ_σ ⊗ 1) = sgn(σ)·σ + Sh_n is a well-defined
> S_n-isomorphism H̃_{n−3}(Π̄_n) ⊗ sgn → C[S_n]/Sh_n, under the left action.
> Equivalently, Σ_σ a_σ ρ_σ = 0 iff Σ_σ a_σ sgn(σ) σ ∈ Sh_n.

Equivariance is direct. g·ρ_σ = ρ_{gσ}, because g maps Π_σ onto Π_{gσ} and
m_σ onto m_{gσ}. On H ⊗ sgn, g sends ρ_σ ⊗ 1 to sgn(g)·ρ_{gσ} ⊗ 1, and Φ
sends that to sgn(g) sgn(gσ)·gσ = sgn(σ)·gσ = g·Φ(ρ_σ ⊗ 1), using
sgn(gσ) = sgn(g) sgn(σ).

**COMPUTED** (`compute/splitting_cycles.py`, see §6), with exact integer
arithmetic for the vanishing statements:
- For n = 3, 4, 5, every proper shuffle u ш v satisfies
  Σ_{w ∈ u ш v} sgn(w) ρ_w = 0 at chain level (12, 72 and 480 shuffles).
- rank{ρ_σ} = (n−1)!, rank Sh_n = n! − (n−1)!.
- Each ρ_σ is a cycle, and g ρ_σ = ρ_{gσ} on a sample of pairs.
- Positive control (test suite): dropping the sign twist breaks the
  relation.

This verifies Proposition Φ for n ≤ 5 independently of the derivation above.

*Novelty of Proposition Φ.* We did not find "the relations among splitting
cycles are the signed shuffle relations" stated in this form. Wachs's papers
contain it implicitly (it is equivalent to Lemma 3.1 + Thm 4.2 + Thm 4.3 of
Wachs 1998). It is the homology form of the classical "Lie_n^* = words modulo
shuffles". SEE AGENT for whether the search found it.

### 3.3 eq. (restrictionlemma) is false for every J (PROVEN)

**Lemma B (PROVEN).** O(P) = O(P^op) for every poset P. Hence
H_P = H_{P^op} as subspaces of H̃_{n−3}(Π̄_n).

*Proof.* Reversing a ρ-sequence of P gives a ρ-sequence of P^op, and the
reverse of a ρ-cycle is a ρ-cycle. So Definition 3.1 of J–S is invariant under
P ↦ P^op. Equivalently, π is order-preserving iff P/π is acyclic, and this
condition is symmetric under reversal. ∎

**Proposition C (PROVEN).** Let n ≥ 3, and let C be the chain 1 < 2 < ⋯ < n.
No linear map J : H̃_{n−3}(Π̄_n) ⊗ sgn → C[S_n] satisfies eq.
(restrictionlemma) for both C and C^op.

*Proof.* Lin(C) = {12⋯n} and Lin(C^op) = {n⋯21}. By Lemma B both posets have
the same H_C = C·ρ_{12⋯n}, so eq. (restrictionlemma) would force
C·(12⋯n)e_ζ = C·(n⋯1)e_ζ. Now we_ζ is a nonzero vector supported on the
rotation orbit of w. For n ≥ 3 the word n⋯1 has n − 1 ≥ 2 descents, while
every rotation of 12⋯n has at most one descent. So the two orbits are
disjoint and the two lines differ. ∎

The same argument applies to any poset that is not self-dual compatibly with
its labeling. **COMPUTED:** W_P e_ζ = W_{P^op} e_ζ holds for only 4/5, 7/16 and
11/63 of the unlabeled posets with n = 3, 4, 5 (for a fixed labeling of each).

For the "second formulation" J(H_P ⊗ sgn) = W_P κ_n of the note: with
Klyachko's idempotent κ_n = (1/n) Σ_σ ζ^{maj σ} σ (verified to be an
idempotent lying in Lie_n), (12⋯n)κ_n and (n⋯1)κ_n are not proportional for
n = 3, 4, 5 (COMPUTED). So that formulation fails for the same reason.
dim W_P κ_n = e_C(P) does hold for every P with n ≤ 5 (COMPUTED), so the
failure is in the subspace, not the dimension.

**What a uniform J can be (PROVEN).** Suppose J is an S_n-isomorphism into a
left ideal C[S_n]a ≅ Lie_n with J(H_P ⊗ sgn) = W_P a for every chain P
(every labeling). Then J(ρ_w) = c_w·wa, and equivariance forces
c_{gw} = sgn(g)c_w. So J(Σ a_w ρ_w) = c Σ a_w sgn(w) wa, i.e.
J = c·(x ↦ xa)∘Φ. This is well defined only if Sh_n·a = 0.
- **COMPUTED:** Sh_n·e_ζ ≠ 0 and Sh_n·κ_n ≠ 0 for n = 3, 4, 5.
- For e_ζ this also follows from Prop. C, for all n ≥ 3.
- **COMPUTED:** Sh_n·θ_n^* = 0 exactly and dim C[S_n]θ_n^* = (n−1)! for
  n = 3, 4, 5, where θ_n = [⋯[[1, 2], 3], ⋯, n] is the Dynkin element and
  θ_n^* = Σ c_τ τ^{−1}.
- PROVEN in general: x ↦ xθ_n^* is the adjoint of the Dynkin operator
  x ↦ xθ_n for the form ⟨σ, τ⟩ = δ_{στ}. The Dynkin operator maps onto Lie_n
  (Dynkin–Specht–Wever), so ker(·θ_n^*) = Lie_n^⊥ = Sh_n.

### 3.4 The corrected restricted image identity

**Lemma D (PROVEN).** For w ∈ Lin(P), every partition in Π_w is
order-preserving for P. Hence ρ_w is a top cycle of Δ(Ô(P)), i.e. ρ_w ∈ H_P.

*Proof.* Cutting w into consecutive segments B_1 | ⋯ | B_k gives the kernel
of the isotone map P → [k], x ↦ (index of the segment containing x). It is
isotone because w is a linear extension. Kernels of isotone maps are order
congruences (J–S Thm 3.3). (Also COMPUTED for all w ∈ Lin(P), n ≤ 6.) ∎

**Conjecture S (CONJECTURED; COMPUTED for n ≤ 6).**
span{ρ_w : w ∈ Lin(P)} = H_P.
- By Lemma D and J–S Thm 4.5 this is equivalent to
  dim span{ρ_w : w ∈ Lin P} = e_C(P).
- By Prop. Φ it is also equivalent to dim (W_P + Sh_n)/Sh_n = e_C(P), i.e.
  dim(W_P ∩ Sh_n) = |Lin P| − e_C(P).

COMPUTED: true for all 5, 16, 63 and 318 unlabeled posets with
n = 3, 4, 5, 6.
- For n ≤ 5 it was checked at chain level: rank of the ρ_w equals e_C(P),
  and also equals dim H_P computed directly as the top cycle space of Δ(Ô(P)).
  The latter independently re-checks J–S Thm 4.5 for n ≤ 5.
- For n = 6 it was checked through the comb coordinates σ ↦ (⟨r_τ, σ⟩)_τ,
  whose kernel is exactly Sh_n (verified for n ≤ 5, and PROVEN in general
  since {r_τ} is a basis of Lie_n and Lie_n^⊥ = Sh_n).
- Rigour of the rank argument: ranks were taken mod a prime p, and
  rank_p ≤ rank_Q ≤ dim H_P = e_C(P). So rank_p = e_C(P) proves equality
  over Q.

**Consequences (PROVEN, assuming Conjecture S for the poset P):**

- (S1) *Corrected restriction identity.* Φ(H_P ⊗ sgn) = (W_P + Sh_n)/Sh_n.
  Composing with x ↦ xθ_n^*: J(H_P ⊗ sgn) = W_P θ_n^*.
- (S2) *Connected P.* {ρ_w : w ∈ Lin P} is a basis of H_P, since
  |Lin P| = e_C(P). It is permuted by Aut(P), and Aut(P) acts freely on
  Lin(P) (gw = w forces g = 1). So H_P ≅ C[Lin P] is a free Aut(P)-module.
  Likewise Lie(P) has basis {we_ζ} (distinct rotation orbits), permuted
  freely. A free module tensored with sgn is free of the same rank. Hence
  **eq. (mainconj) holds for every connected P satisfying Conjecture S**. In
  particular it holds for every connected P with n ≤ 6 (COMPUTED +
  PROVEN). This is consistent with the sibling reproduction of the character
  identity (`notes/reproduce_character_identity_n_le_5.md`), but does not
  depend on it.
- (S3) *General P.* eq. (mainconj) is equivalent to
  W_P/(W_P ∩ Sh_n) ≅ W_P/(W_P ∩ K_ζ) as Aut(P)-modules, where
  K_ζ = C[S_n](1 − e_ζ) = ker(x ↦ xe_ζ). Both sides are quotients of the same
  permutation module C[Lin P]. W_P ∩ K_ζ is spanned by the
  wγ^j − ζ^j w with w, wγ^j ∈ Lin P. W_P ∩ Sh_n contains u ш v whenever u, v
  are linear extensions of complementary unions of connected components
  (every such shuffle lies in Lin P).
- (S2′) *Connected P, without Conjecture S.* By the reasoning in (S2),
  eq. (mainconj) for connected P is equivalent to "H_P is a free
  Aut(P)-module", i.e. μ(O(P)^g) = 0 for every g ≠ 1 (Lefschetz,
  eq. homchar). By Lemma A the right-hand side of eq. (characterconj) is 0
  for these g.

### 3.5 Recommendation

For the containment-proof item:

1. Use **J = Φ**, the transpose of Wachs's comb/general correspondence
   (Wachs 1998 Thms 4.3, 5.4). It has the simplest possible formula on the
   generators that matter, ρ_σ ↦ sgn(σ)σ mod Sh_n, and its kernel
   description (the shuffles) is explicit. Barcelo's map is the same
   isomorphism (Wachs 1998, introduction), but it is written in the Björner
   NBC basis. That basis is not adapted to linear extensions: expanding
   ρ_T needs Wachs Thm 3.3.
2. Replace the goal eq. (restrictionlemma) by **Conjecture S**, which needs
   no Fourier projection at all. The note's caution that "the cyclic Fourier
   projection must be introduced after assembling the relevant top cycles"
   is borne out. The projection cannot be introduced through J at all
   (Prop. C). It has to come in as an abstract isomorphism at the end, as in
   (S2)/(S3).
3. Natural attack on Conjecture S: an induction along the J–S bijection S_a
   (contract the edge a → a ⊕_f 1). The link of ρ_w at the atom π_{a,b} is
   ±ρ_{w/ab} when a and b are adjacent in w, and 0 otherwise. Note that J–S
   use the *cyclic* successor of a. Lyndon-type triangularity gives an easy
   partial result (PROVEN, modulo the classical fact cited below): for a
   minimal a, the ρ_w with w ∈ Lin P and w_1 = a are linearly independent.
   That is e(P − a) of them, which is weaker than needed for connected P.
   *Proof.* Order the alphabet with a least. A word with distinct letters is
   Lyndon iff it begins with its least letter. The standard bracketing P_ℓ
   of a Lyndon word ℓ equals ℓ plus lexicographically larger words. (This is
   the classical triangularity of the Lyndon basis: Reutenauer, *Free Lie
   Algebras*, Ch. 5; Lothaire, *Combinatorics on Words*, Ch. 5. Theorem
   numbers not re-checked.) So the pairing matrix (⟨P_ℓ, ℓ′⟩) between Lyndon
   elements and Lyndon words is unitriangular. Hence the Lyndon words are
   independent in Lie_n^* = C[S_n]/Sh_n. Now apply Φ. ∎

## 4. Aguiar–Mahajan and cones

SEE AGENT

## 5. Bibliography corrections (proposed; the seed note is not edited)

SEE AGENT

## 6. Reproduction

Code: `compute/splitting_cycles.py` (plain Python 3; imports the poset helpers
of `compute/poset_jks_check.py`). Run from `compute/`:

    python3 splitting_cycles.py --nmax 5 --nmax-comb 6 > output/splitting_cycles.txt   # ~4 s
    python3 -m unittest test_splitting_cycles

The archived output is `compute/output/splitting_cycles.txt`. Its last line,
`ALL CHECKS PASSED`, gates the following: Proposition Φ for n ≤ 5, the
Conjecture S rank checks for n ≤ 6, dim H_P = e_C(P) for n ≤ 5, Lemma D for
n ≤ 6, and dim W_P e_ζ = e_C(P). The Lie-realization lines (e_ζ, κ_n, θ_n^*)
are reported values, not gated. Some of them are *expected* to print False
(Prop. C).
