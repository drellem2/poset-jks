# The global module HH_n, operations on Lie(P), and the plethystic logarithm

Work item: mg-266cf. The subject is research step 5 of
`notes/poset_jks_research_note.tex` and the "Still to prove" items on
naturality, the global induced-module formula eq. (globalind), and the
bracket/operad structure.

This file builds on:
- `notes/cyclic_compatible_posets_bn.md` (the "bn note");
- `notes/audit_cyclic_compatible_posets_bn.md` (the "audit"), in particular
  its §A;
- `notes/reproduce_character_identity_n_le_5.md`;
- `notes/literature_novelty_jks_maps.md` (the "literature note").

The audit's §A has not been independently checked. It is cited here as the
audit's result.

Every claim is tagged PROVEN, COMPUTED, CITED or CONJECTURED.

## Summary

1. **The character identity eq. (characterconj) holds for every finite
   poset (PROVEN, §2, given Jenča–Sarkoci).** It follows that eq. (mainconj)
   holds for every P with n ≥ 3:

       H_P ≅ sgn ⊗ Lie(P)   as Aut(P)-modules.

   There is also a closed formula for the character. For g ∈ Aut(P) of
   order o,

       (−1)^{n−3} sgn(g) μ(OP(P)^g) = Σ_{gC=C} ζ^{r_g(C)}
                                     = μ(o) · Σ_{x ∈ F(P,g)} e_C(P|_{B_0(x)}).

   Here μ(o) is the number-theoretic Möbius function. F(P,g) is the set of
   partitions of P into o unions of connected components that are permuted
   cyclically by g; it is empty unless ⟨g⟩ acts freely on the components.
   B_0(x) is any one block of x.

   The proof applies Weisner's theorem to the orbit partition O_g in the
   lattice OP(P)^g, and then counts fixed cyclic classes by cutting the
   circle into g-translates. The only external input is Jenča–Sarkoci
   Thm 4.5 (CITED in the literature note). It enters at g = 1 and in the
   Lefschetz identification eq. (homchar).

   Every step of the proof is COMPUTED separately for all 318 + 63 + 16 + 5
   + 2 + 1 posets with n ≤ 6 (949 (poset, class) pairs), and on extra
   examples at n = 7, 8. **This result goes beyond the item's scope and
   should get an independent audit before it is relied on.**
2. **Global module (Q1).**
   - (a) The only step of (globalind) that used the conjecture is
     HH_n ≅ sgn ⊗ ⊕_P Lie(P). The audit's §A shows that the rest,
     ⊕_P Lie(P) ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]), is unconditional. Item 1
     discharges that step, so (globalind) is PROVEN given Jenča–Sarkoci.
   - (b) The sign convention is: the outer twist is ⊗ sgn, i.e. ω on
     symmetric functions, giving the factor (−1)^{n−n/d} in eq. (frob). The
     note's (frob) is correct as printed, and its (plethlog) is the
     untwisted series ch(⊕_P Lie(P)).
   - (c) COMPUTED by **direct homology**, with no Lefschetz formula and no
     use of the conjecture, for n ≤ 6: the character of HH_n equals (frob)
     on every conjugacy class of S_n. The twist is invisible for n ≤ 5,
     since twisted and untwisted values coincide there. At n = 6 it is
     decisive:
     - class (6): HH_6 has −1; the untwisted formula predicts +1;
     - class (2,2,2): HH_6 has +128; the untwisted formula predicts −128.
3. **Operations (Q2).**
   - Connected posets: H_P ≅ Lie(P) ≅ C[Lin P] is a **free** Aut(P)-module
     (PROVEN). This covers every ordinal sum P ⊕ Q, every product of
     connected posets, and every substitution into a connected poset with
     at least 2 elements. The only invariant is |Lin|, and
     |Lin(P ⊕ Q)| = |Lin P|·|Lin Q|.
   - Root-of-unity phases come only from automorphisms that permute
     components freely.
   - Disjoint sums are governed by the closed formula above. One
     consequence is a Möbius formula over component partitions:
     e_C(P) = Σ_π μ_Π(π, 1̂) Π_{T∈π} |Lin(P|_T)| (PROVEN).
   - The commutator of concatenations does **not** descend to a map
     Lie(P) ⊗ Lie(Q) → Lie(P+Q) in the e_ζ model, not even for antichains
     (COMPUTED). A bracket exists in a different model; see item 4.
4. **Plethystic log (Q3), PROVEN modulo a CITED theorem.** Let 𝐐 be the
   species of pairs (P, ℓ), where P is a poset and ℓ a linear extension
   of P. It is a connected cocommutative Hopf monoid:
   - product: disjoint union of the posets and concatenation of the
     extensions;
   - coproduct: restriction.

   S_n acts freely on 𝐐[n], so the cycle index of 𝐐 is A(p_1). By
   Cartier–Milnor–Moore and PBW for species, 𝐐 ≅ E ∘ Prim(𝐐), so
   ch Prim(𝐐) = Log A(p_1) = Σ_d (μ(d)/d) log A(p_d). This is exactly
   (plethlog). Hence Prim(𝐐)[n] ≅ ⊕_P Lie(P) as S_n-modules. That is also
   COMPUTED directly for n ≤ 4, by finding the primitives and their
   character.

   This explains the shape of (plethlog): it is "primitives of a
   cocommutative Hopf monoid whose underlying species is free". Prim(𝐐)
   is a Lie monoid. The sub-Hopf monoid of antichains is 𝐋, and on it the
   bracket is the classical free Lie bracket.
   - Not achieved: the isomorphism Prim(𝐐) ≅ ⊕_P Lie(P) is not graded by
     posets. The primitives are not P-homogeneous already at n = 2. So
     this does not yet give a bracket Lie(P) ⊗ Lie(Q) → Lie(P+Q).

## 0. Reproduce

Run in `compute/`. The script is plain Python and imports
`poset_jks_check.py`.

    python3 poset_lie_structure.py > output/poset_lie_structure.txt   # all sections, ~40 s
    python3 poset_lie_structure.py --theorem 6     # §2 proof steps T1–T5, n ≤ 6 (+ n = 7, 8 examples), ~9 s
    python3 poset_lie_structure.py --homology 6    # §1 direct homology, HH_n vs (frob), ~31 s
    python3 poset_lie_structure.py --hopf 4        # §4 primitives of 𝐐
    python3 poset_lie_structure.py --bracket 5     # §3.4 e_ζ-model bracket test
    python3 -m unittest test_poset_lie_structure

The script exits with status 0 iff every check passes. The archived output
is `compute/output/poset_lie_structure.txt`.

Ranks are computed mod p = 2^31 − 1. Two facts make the exact results
rigorous:
- the mod-p kernel dimension equals e_C(P), which is the rational dimension
  by Jenča–Sarkoci, so no rank drops mod p;
- every trace is an integer of absolute value below p/2.

Positive controls (COMPUTED):
- Dropping the factor μ(o) from the closed formula makes it fail on 13 of
  the 949 pairs.
- At n = 6 the untwisted (frob) disagrees with direct homology on two
  classes (item 2(c)).
- Every (P, Q) pair in the bracket test that has something to test fails
  it.

## 1. The global module (Q1)

Notation: HH_n = ⊕_{P on [n]} H_P, V_n = ⊕_{P on [n]} Lie(P).

**1(a). Where the conjecture enters (PROVEN).**
- The audit's §A gives V_n ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]) unconditionally.
  The induction is from C_n = ⟨γ⟩, and B_n is the bn note's set: the
  posets having some rotation of 12⋯n as a linear extension.
- Relabeling makes both HH_n and V_n into S_n-modules. In both cases the
  module is induced from stabilizers:

      HH_n ≅ ⊕_{[P]} Ind_{Aut P}^{S_n} H_P,
      V_n  ≅ ⊕_{[P]} Ind_{Aut P}^{S_n} Lie(P).

  Here τ ∈ S_n carries OP(P) → OP(τP) and we_ζ ↦ (τw)e_ζ.
- Since Ind(sgn|_G ⊗ M) ≅ sgn ⊗ Ind M, eq. (mainconj) for one P in each
  orbit gives HH_n ≅ sgn ⊗ V_n. That is (globalind).
- The conjecture enters **only** at this step, and §2 proves it. So
  (globalind) is PROVEN, given Jenča–Sarkoci Thm 4.5.

**1(b). Sign convention (PROVEN; COMPUTED at n = 6).**
- ch(sgn ⊗ V) = ω ch V, and ω p_d^{n/d} = (−1)^{n−n/d} p_d^{n/d}. The bn
  note's Prop. 3 and the audit's rows 17–18 then give

      ch HH_n = (1/n) Σ_{d|n} (−1)^{n−n/d} μ(d) b_{n/d} p_d^{n/d}.

  This is the note's (frob) as printed.
- The note's (plethlog) is the generating function of ch V_n, the
  untwisted series.
- Since ω is a ring map with ω(p_d) = (−1)^{d−1} p_d, the twisted series
  is Σ_n ch HH_n = Σ_d (μ(d)/d) log A((−1)^{d−1} p_d).

**1(c). Direct numerical check (COMPUTED, `--homology 6`).**
- For every unlabeled P with 3 ≤ n ≤ 6, the script builds the order complex
  of the proper part of OP(P) and computes H_P as the kernel of the top
  boundary map. It then computes the trace of each class representative of
  Aut(P) on that kernel, and assembles the induced character of HH_n.
- Results:
  - dim H_P = e_C(P) for every P;
  - Σ_P dim H_P = 32, 786, 37464, 3183840 = (n−1)! b_n for n = 3, 4, 5, 6;
  - on every conjugacy class of S_n, the character of HH_n equals the
    twisted (frob).
- The local identity tr(g | H_P) = sgn(g) · Σ ζ^{r_g(C)} was also checked
  directly for every (P, g) with n ≤ 6. This is an independent re-check of
  the reproduction item: it uses homology, not Möbius numbers.
- Nonzero non-identity values:

  | n | class (6) | class (2,2,2) | class (3,3) | class (5) | class (2,2) | class (3) |
  |---|---|---|---|---|---|---|
  | 3 | | | | | | −1 |
  | 4 | | | | | −6 | |
  | 5 | | | | −1 | | |
  | 6 | −1 (untwisted: +1) | +128 (untwisted: −128) | −9 | | | |

## 2. The character identity for every poset

Notation:
- P is a poset on [n], and g ∈ Aut(P) has order o.
- L = OP(P), and L^g is the subposet of g-fixed partitions.
- O_g is the partition of [n] into ⟨g⟩-orbits.
- For a g-invariant set B, write P|_B for the induced subposet.

**Lemma 2.1 (PROVEN).** Let a finite group K act on a poset R by
automorphisms. Then the quotient of R by the K-orbits is acyclic.

*Proof.* Suppose the orbit quotient had a cycle X_1 → X_2 → ⋯ → X_r → X_1.
- Lift it: a_i < b_{i+1} with a_i ∈ X_i and b_{i+1} = k_i a_{i+1}, where
  k_i ∈ K.
- Applying k_1, k_1k_2, … in turn gives
  a_1 < k_1 a_2 < k_1k_2 a_3 < ⋯ < k a_1 for some k ∈ K.
- Then a_1 < k a_1 < k² a_1 < ⋯ < k^{|K|} a_1 = a_1, a contradiction. ∎

**Lemma 2.2 (PROVEN).** The following hold.
- (i) L is a lattice, and its meet is the partition meet.
- (ii) L^g is a lattice containing 0̂ and 1̂, and O_g ∈ L^g.
- (iii) For x ∈ L^g, the join x ∨ O_g in L^g is the partition join. Its
  blocks are the ⟨g⟩-orbits of blocks of x.
- (iv) x ∨ O_g = 1̂ if and only if x ∈ X(P,g). This is the set of
  partitions of [n] whose blocks are unions of connected components of P
  and are permuted transitively by g.

*Proof.*
- (i) Suppose P/(x ∧ y) had a cycle. Its image in P/x is a closed walk with
  steps "<" or "=". Acyclicity of P/x forces every step to be "=". The same
  holds in P/y, so the cycle lies in one block of x ∧ y, a contradiction.
  A finite meet-semilattice with a top element is a lattice.
- (ii) g acts on L as a lattice automorphism, so fixed points are closed
  under meet and join. O_g is order-preserving by Lemma 2.1 applied to
  K = ⟨g⟩ acting on P, and it is clearly g-fixed.
- (iii) x is g-fixed and order-preserving, so ⟨g⟩ acts on the poset P/x.
  By Lemma 2.1 the partition join x ∨_Π O_g is order-preserving, because
  it is the orbit quotient of P/x. It is also g-fixed. Every upper bound
  in L^g lies above the partition join, so the partition join is the join
  in L^g.
- (iv) Suppose x ∨ O_g = 1̂. Then ⟨g⟩ is transitive on the blocks of x. A
  transitive automorphism group of the poset P/x forces P/x to be an
  antichain, because B < g^k B gives B < g^{k|g|} B = B. So there are no
  relations between distinct blocks, and every block is a union of
  components. Conversely, every x ∈ X(P,g) is order-preserving (its
  quotient is an antichain), g-fixed, and its join with O_g is 1̂ by (iii).
  ∎

COMPUTED (T1, T2): O_g ∈ L^g; the L^g-join equals the partition join; and
{x : x ∨ O_g = 1̂} = X(P,g). These hold for all 544 non-identity pairs with
n ≤ 6.

**Lemma 2.3 (Weisner; PROVEN).** In a finite lattice M with a ≠ 0̂,

    Σ_{x : x ∨ a = 1̂} μ(0̂, x) = 0.

*Proof.* Expand δ(x ∨ a, 1̂) = Σ_{y ≥ x ∨ a} μ(y, 1̂). Then

    Σ_x μ(0̂,x) Σ_{y ≥ x, y ≥ a} μ(y,1̂) = Σ_{y ≥ a} μ(y,1̂) Σ_{x ≤ y} μ(0̂,x)
                                       = Σ_{y ≥ a} μ(y,1̂) δ(y,0̂) = 0,

since a ≠ 0̂. ∎ (This is EC1 Cor. 3.9.3 in Stanley's numbering. That
number was not re-checked; the proof above is self-contained.)

**Lemma 2.4 (PROVEN).** Let x ∈ X(P,g) have m blocks, let B_0 be one
block, and put h = g^m|_{B_0} ∈ Aut(P|_{B_0}).
- (i) The interval [0̂, x] in L^g is isomorphic to OP(P|_{B_0})^h.
- (ii) Let k = |B_0| = n/m. Then (−1)^{n−3} sgn(g) = (−1)^{k−3} sgn(h).

*Proof.*
- (i) There are no relations between blocks of x. So π ≤ x is
  order-preserving iff each restriction π|_B is, and
  [0̂, x]_L ≅ Π_B OP(P|_B). g permutes the factors cyclically, so a fixed
  point is determined by its B_0-component. That component can be any
  g^m-fixed element.
- (ii) Each cycle of g meets B_0 in exactly one cycle of h, and is m times
  as long. If h has c cycles, then sgn(g) = (−1)^{n−c} and
  sgn(h) = (−1)^{k−c}. ∎

**Proposition 2.5 (H-side formula; PROVEN given J–S).** Put
M̃(P,g) = (−1)^{n−3} sgn(g) μ(L^g). Then

    M̃(P,g) = μ(o) · Σ_{x ∈ F(P,g)} e_C(P|_{B_0(x)}),

where F(P,g) = {x ∈ X(P,g) : g^{m(x)}|_{B_0} = id}. Equivalently, F(P,g)
is the set of x with exactly o blocks such that B_0(x) contains one
component from each ⟨g⟩-orbit of components. F(P,g) is empty unless ⟨g⟩
acts freely on the set of components.

*Proof.*
- **Recursion.** If g ≠ 1, then O_g ≠ 0̂. Lemmas 2.2(iv), 2.3 and 2.4 give

      Σ_{x ∈ X(P,g)} M̃(P|_{B_0(x)}, h_x) = 0.          (W)

  If g = 1, then X(P,1) = {1̂}, and Jenča–Sarkoci gives
  M̃(P,1) = e_C(P). This is where J–S Thm 4.5 is used.
- **Möbius inversion.** Order X(P,g) by refinement. For x ∈ X(P,g), the map
  y ↦ {g^j D : D ∈ y} is a bijection from X(P|_{B_0(x)}, h_x) onto
  {z ∈ X(P,g) : z ≤ x}. It respects the pairs (block, induced
  automorphism) up to isomorphism. So (W), applied to every x, says

      Σ_{z ≤ x} f(z) = F(x),

  where f(z) = M̃(P|_{B_0(z)}, h_z) and F(x) = [h_x = 1] e_C(P|_{B_0(x)}).
  Möbius inversion on X(P,g) gives

      M̃(P,g) = f(1̂) = Σ_x μ_X(x, 1̂) F(x).
- **Which x contribute.** h_x = 1 forces g^m = 1 on all of P, so o | m.
  Disjointness of g^j B_0 for 0 < j < m forces m ≤ o. So m = o, and x ∈ F.
- **The Möbius value.** For x ∈ F, the interval [x, 1̂] in X(P,g) consists
  of the coarsenings of the free transitive Z/o-set of blocks that are
  invariant under translation. These are the coset partitions of subgroups
  of Z/o. So [x, 1̂] is the divisor lattice of o, and μ_X(x, 1̂) = μ(o). ∎

COMPUTED:
- T3: the recursion (W) holds, with μ computed directly on each restricted
  poset, for all 544 non-identity pairs with n ≤ 6.
- T4: the closed formula equals M̃(P,g) on all 949 pairs.

**Lemma 2.6 (structure of cyclic classes; PROVEN).** Let C be a cyclic class
of P, i.e. a C_n-orbit of words meeting Lin(P), and let
Cut(C) = {j : wγ^j ∈ Lin P} for a reference word w ∈ C. Then:
- (i) Distinct arcs between consecutive cuts are mutually incomparable.
  Hence each arc is a union of components.
- (ii) The word on each arc is a linear extension of the arc's subposet.
  It is irreducible: it has no split into a prefix and a suffix that are
  incomparable.
- (iii) Conversely, take a cyclic sequence of disjoint unions of components
  S_1, …, S_m covering P, each carrying an irreducible extension u_i.
  Concatenating them gives a class whose cuts are exactly the m junctions.

*Proof.* This is the bn note's Lemma 1(a), its Theorem parts (i)–(ii) and
its Lemma 4, with "arc of the fixed circle 1 → ⋯ → n" replaced by "arc of
the word w". The proofs use nothing about the labels.
- If α and β are distinct arcs starting at cuts s and s', then wγ^s puts α
  first and wγ^{s'} puts β first. So α ⊥ β.
- Irreducibility: a split α = α_1 | α_2 with α_1 ⊥ α_2 would make the
  rotation starting at α_2 a linear extension, which is a cut inside α. ∎

**Proposition 2.7 (Lie-side formula; PROVEN).** For g ∈ Aut(P) of order o,

    Σ_{C : gC = C} ζ_n^{r_g(C)} = μ(o) · Σ_{x ∈ F(P,g)} e_C(P|_{B_0(x)}).

*Proof.* Fix a reference element ρ ∈ [n]. For x ∈ F(P,g), let B_0(x) be the
block containing ρ.

Let C be g-fixed with gw = wγ^r, so g(w_i) = w_{i+r} on positions. Then
o = n/gcd(n,r). Put k = n/o = gcd(n,r).

**Step 1: from (C, s) to a partition x_s.**
- Cut(C) is invariant under +r, hence under +k.
- For s ∈ Cut(C), the arc A_s = (s, s+k] ends at the cut s+k. So A_s is a
  union of whole arcs from Lemma 2.6, hence a union of components.
- Its g-images are the arcs A_{s+jr}, and these are the o arcs A_{s+ik}.
  So x_s = {letters of A_{s+ik}} lies in F(P,g): g permutes its o blocks
  cyclically and g^o = 1.
- s and s+k give the same x_s. Distinct cosets s + ⟨k⟩ give different
  partitions, because the blocks are nonempty arcs and o ≥ 2 when g ≠ 1.
- So C has exactly |Cut(C)|/o compatible partitions x.

**Step 2: from (C, x) to data (x, u, q).**
- Let u be the word of the arc carrying B_0(x), read from its starting cut.
  Then u ∈ Lin(P|_{B_0}).
- Let q ∈ Z/o be defined by: the next arc carries g^q B_0. The arc after
  A_s is A_{s+k} = g^j A_s with jr ≡ k (mod n). So q = (r/k)^{−1}, which is
  a unit mod o.
- Conversely, given (x, u, q) with u ∈ Lin(P|_{B_0(x)}) and q a unit mod o,
  the word u · g^q u · g^{2q} u ⋯ g^{(o−1)q} u is a linear extension (by
  Lemma 4 of the bn note). g rotates it by k·q^{−1} positions, so its class
  C is g-fixed. Reading off (C, x) recovers (x, u, q).
- So the compatible pairs (C, x) are in bijection with the triples
  (x, u, q).

**Step 3: the count.**
- In the triple, the cuts of C inside one arc correspond to the cuts of the
  class C_0 of u in P|_{B_0}, by Lemma 2.6. So |Cut(C)|/o = |Cut(C_0)|.
- The phase is ζ_n^r = ω^{q^{−1}}, where ω = ζ_n^k is a primitive o-th
  root of unity.
- Therefore

      Σ_C ζ_n^{r(C)} = Σ_{(C,x)} ζ_n^{r(C)} / (|Cut C|/o)
                     = Σ_x Σ_{C_0 ∈ Cyc(P|B_0)} Σ_{u ∈ C_0 ∩ Lin} (1/|Cut C_0|) Σ_{q ∈ (Z/o)^×} ω^{q^{−1}}
                     = μ(o) Σ_x e_C(P|_{B_0(x)}).

  The last step uses the Ramanujan sum Σ_{q unit} ω^q = μ(o).

For g = 1 both sides are e_C(P). ∎

COMPUTED (T4): the closed formula equals Σ ζ^{r_g(C)}, computed by
enumerating classes, on all 949 pairs with n ≤ 6 and on the n = 7, 8
examples.

**Theorem 2.8 (PROVEN, given Jenča–Sarkoci Thm 4.5).** For every finite
poset P and every g ∈ Aut(P),

    (−1)^{n−3} μ(OP(P)^g) = sgn(g) Σ_{gC=C} ζ^{r_g(C)}.

For n ≥ 3 this is eq. (characterconj). Via eq. (homchar), it gives
eq. (mainconj): H_P ≅ sgn ⊗ Lie(P) as Aut(P)-modules.

*Proof.* Combine Propositions 2.5 and 2.7. For n ≤ 2, the g = 1 case of 2.5
is checked directly (T4 at n = 1, 2).

Eq. (homchar) is the Hopf trace formula on the order complex. g fixes a
chain iff it fixes every element of the chain, so the fixed subcomplex is
Δ of the proper part of L^g. Its reduced Euler characteristic is
μ_{L^g}(0̂, 1̂) by P. Hall's theorem. Homology is concentrated in degree
n − 3 by J–S Thm 4.5. ∎

Remarks:
- The literature note's Lemma A (fixed points kill the Lie-side character)
  is the special case "⟨g⟩ not free on components ⇒ both sides 0".
- Its proposed route through Conjecture S is not needed for (mainconj).
  Conjecture S remains open as a statement about *which* cycles span H_P.
- Theorem 2.8 does not give an explicit equivariant isomorphism. It is a
  character identity. The note's restriction lemma remains false as stated
  (literature note, §3.3).

## 3. Operations on posets (Q2)

**3.1 Connected posets are free (PROVEN).** Let P be connected with n ≥ 2.
- Every class meets Lin(P) exactly once: by Lemma 2.6(i), two cuts would
  disconnect P.
- So Lie(P) has basis {we_ζ : w ∈ Lin P}, permuted freely by Aut(P), and
  Lie(P) ≅ C[Lin P].
- By Theorem 2.8, or directly by Prop. 2.5 (F(P,g) = ∅ for g ≠ 1, since one
  component cannot be permuted freely), μ(OP(P)^g) = 0 for g ≠ 1.
- So H_P ≅ C[Lin P] ≅ sgn ⊗ C[Lin P]. This is free of rank
  |Lin P|/|Aut P|.

This covers:
- **ordinal sums** P ⊕ Q (P, Q nonempty), which are always connected, with
  |Lin(P⊕Q)| = |Lin P|·|Lin Q|. Restricted to Aut P × Aut Q,
  Lie(P⊕Q) ≅ C[Lin P] ⊗ C[Lin Q]. This is **not** Lie(P) ⊗ Lie(Q) when P or
  Q is disconnected.
- **cartesian products** of connected posets;
- **substitutions** R[Q_x] into a connected R with |R| ≥ 2. These are
  connected: elements of Q_x and Q_y with x <_R y are comparable, and every
  x has some comparable y in R.

Disconnected products and substitutions reduce to disjoint sums:
(P_1 + P_2) × Q = P_1 × Q + P_2 × Q, and the components of R[Q_x] are
those of R, substituted, except that the singleton components {x} of R
contribute the components of Q_x.

**3.2 Disjoint sums (PROVEN).** All phase information sits in Prop. 2.7.
- Two non-isomorphic connected posets: Aut(P+Q) = Aut P × Aut Q fixes both
  components. So Lie(P+Q) is free, of rank e_C(P+Q)/|Aut|.
- Here e_C(P+Q) = (C(n, p) − 1)|Lin P||Lin Q|, by 3.3.
- k copies of a connected R: g ∈ Aut(R) ≀ S_k contributes only if its
  image in S_k has cycle type (o^{k/o}) and g^o = 1. Then

      χ_{Lie(kR)}(g) = μ(o) · o^{k/o − 1} · e_C((k/o)·R).

  For R a point this is the classical value of Lie_k on the class
  (o^{k/o}), namely μ(o) o^{k/o−1} (k/o − 1)!. For example,
  χ_{Lie(2R)}(swap) = −|Lin R| for an involutive swap.

COMPUTED: the closed formula is T4, already listed.

**3.3 e_C over components (PROVEN; COMPUTED as T5).** For P with component
set K,

    e_C(P) = Σ_{π ∈ Π(K)} (−1)^{|π|−1} (|π|−1)! Π_{T∈π} |Lin(P|_T)|,
    |Lin(P)| = Σ_{π ∈ Π(K)} Π_{T∈π} e_C(P|_T).

*Proof.*
- By Lemma 2.6, classes are the cyclic sequences of irreducible pieces on
  unions of components.
- By cutting at every "component cut" (the bn note's Lemma 2, verbatim),
  linear extensions are the linear sequences of irreducible pieces.
- Take the exponential generating function, multilinear in the
  components. Sequences give 1/(1 − I), cycles give log(1/(1 − I)), and
  log ∘ exp inverts.

Example: three 2-chains give 90 − 3·6 + 2 = 74. This matches the
reproduction note's e_C. COMPUTED for all 405 posets with n ≤ 6. ∎

**3.4 No bracket in the e_ζ model (COMPUTED, `--bracket 5`).** Take the
commutator of concatenations (u, v) ↦ uv − vu, with u ∈ Lin P on
{1..p} and v ∈ Lin Q on {p+1..n}. This maps W_P ⊗ W_Q → W_{P+Q}.
- The question is whether it descends to Lie(P) ⊗ Lie(Q) → Lie(P+Q),
  where Lie(·) = W e_ζ for the appropriate n.
- Result:
  - of the 71 pairs (P, Q) with p + q ≤ 5, 51 have
    ker(W_P → Lie(P)) = 0, so there is nothing to test;
  - all 20 others **fail**, including 12 with P an antichain.
- So it fails already classically. C[S_n]e_ζ ≅ Lie_n holds only as
  abstract modules, and Klyachko's model does not carry the free Lie
  bracket.

Any bracket must come from another model. Candidates:
- the dual-Wachs model H_P ⊗ sgn ≅ (W_P + Sh_n)/Sh_n of the literature
  note, which is canonical but needs Conjecture S. Its target is the Lie
  *coalgebra* C[S_n]/Sh_n, which carries the deconcatenation cobracket. For
  w = uv ∈ Lin P, u is an extension of a down-set S and v of its
  complement. So the cobracket maps W_P into ⊕_{S ideal} W_{P|S} ⊗ W_{P|T}.
  This suggests a poset **cooperad** (CONJECTURED; not tested);
- Prim(𝐐), §4.

## 4. The plethystic logarithm (Q3)

**4.1 The Hopf monoid 𝐐 (PROVEN).** 𝐐[I] has basis the pairs (P, ℓ), where
P is a poset on I and ℓ ∈ Lin(P).
- Product: μ((P,ℓ) ⊗ (P',ℓ')) = (P + P', ℓℓ').
- Coproduct: Δ_{S,T}(P,ℓ) = (P|_S, ℓ|_S) ⊗ (P|_T, ℓ|_T).

Properties:
- Associativity and coassociativity are clear.
- Compatibility holds because restriction commutes with disjoint union:
  (P+P')|_S = P|_{S∩I} + P'|_{S∩I'}.
- 𝐐 is connected, and it is cocommutative because restriction is
  symmetric.
- 𝐐 is the sub-Hopf monoid of the Hadamard product 𝐋 × 𝐏 given by the
  compatible pairs. Here 𝐋 is linear orders with concatenation and
  restriction, and 𝐏 is posets with disjoint union and restriction.
- The forgetful map 𝐐 → 𝐋, (P,ℓ) ↦ ℓ, and the inclusion 𝐋 → 𝐐 of
  antichains are both Hopf morphisms.
- dim 𝐐[n] = n!·a_n, and S_n acts freely on the basis, since an
  automorphism fixing ℓ is trivial. So the cycle index is
  Z_𝐐 = A(p_1) = 1 + Σ a_n p_1^n.

**4.2 Primitives (PROVEN modulo CITED; COMPUTED n ≤ 4).**
- CITED: Cartier–Milnor–Moore and PBW for connected cocommutative Hopf
  monoids in species over a field of characteristic 0 give H ≅ U(Prim H)
  and U(g) ≅ E ∘ g as species. Sources: M. Aguiar and S. Mahajan,
  *Monoidal Functors, Species and Hopf Algebras*, CRM Monograph Series 29,
  AMS 2010, Ch. 11; and J. R. Stover, J. Pure Appl. Algebra 86 (1993)
  289–326. Exact theorem numbers were not re-checked.
- Hence Z_𝐐 = Exp(Z_{Prim 𝐐}), so

      Z_{Prim 𝐐} = Log A(p_1) = Σ_{d≥1} (μ(d)/d) log A(p_d).

- The right-hand side is Σ_n ch V_n by the bn note's Prop. 3, the audit's
  §A, and the bn Theorem.
- Hence **Prim(𝐐)[n] ≅ V_n = ⊕_P Lie(P)** as S_n-modules, and also
  HH_n ≅ sgn ⊗ Prim(𝐐)[n] by §1.

COMPUTED (`--hopf 4`): computing Prim(𝐐)[n] = ∩_{S,T} ker Δ_{S,T}
directly gives dimensions 1, 3, 32, 786 = (n−1)! b_n. Its S_n-character
equals the untwisted (frob) on every class, for n ≤ 4.

**4.3 What this explains, and what it does not.**
- The Witt/plethystic shape is explained by PBW. Prim of a cocommutative
  Hopf monoid with free underlying species of egf A always has cycle index
  Log A(p_1), and the classical case A = 1/(1−x) (𝐋, Prim = Lie) is the
  antichain sub-Hopf monoid.
- Prim(𝐐) is a Lie monoid under the commutator of μ. This is a genuine
  bracket Prim(𝐐)[S] ⊗ Prim(𝐐)[T] → Prim(𝐐)[S ⊔ T], and it restricts on
  antichains to the free Lie bracket.
- Combined with the bn theorem, 4.2 gives a second proof of the
  *character* identity Σ ch V_n = Log A(p_1). It does not give an
  independent proof of b_n = n[x^n] log A: §A computes ch V_n through b_n,
  so the two together are equivalent to the bn theorem.
- **Not P-graded (COMPUTED by hand at n = 2).** Prim(𝐐)[2] has basis
  - (anti, 12) − (anti, 21),
  - (1<2, 12) − (anti, 12),
  - (2<1, 21) − (anti, 21).

  The last two are not P-homogeneous. So the isomorphism with ⊕_P Lie(P)
  is only an isomorphism of S_n-modules. It does not yet produce maps
  Lie(P) ⊗ Lie(Q) → Lie(P+Q).
- Two natural refinements remain:
  - **CONJECTURED.** Some filtration of 𝐐 by the poset (for example by
    sub-orders P' ⊆ P compatible with ℓ) has associated graded primitives
    ≅ ⊕_P Lie(P), P-homogeneously. At n = 2 this is consistent with the
    "downward" filtration F_{≤P} = span{(Q, ℓ) : Q ⊆ P, ℓ ∈ Lin P}: the
    graded pieces have dimensions 1, 1, 1 (hand computation). It was not
    tested beyond n = 2.
  - **CONJECTURED (local PBW).** As Aut(P)-modules, C[Lin P] ≅ a "Sym over
    components" of the Lie(P|_T). The dimension shadow is
    |Lin P| = Σ_π Π e_C(P|_T) (3.3, PROVEN). The equivariant statement was
    not checked.

## 5. Not done / open

- An independent audit of §2. The proof is short, but it settles the
  note's main conjecture.
- An explicit, natural Aut(P)-isomorphism H_P → sgn ⊗ Lie(P). Theorem 2.8
  is a character identity only.
- A P-graded bracket or cooperad structure (§3.4, §4.3).
- Conjecture S (literature note), which is independent of Theorem 2.8.
