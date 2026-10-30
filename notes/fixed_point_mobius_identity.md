# Direct proof of the fixed-point Möbius / root-of-unity identity

Work item: mg-8878d. Subject: research step 1 of
`notes/poset_jks_research_note.tex`, i.e. eq. (characterconj):

    (-1)^{n-3} μ(OP(P)^g) = sgn(g) · Σ_{C ∈ Cyc(P), gC = C} ζ^{r_g(C)}      (g ∈ Aut(P)).

Every claim is tagged PROVEN, COMPUTED, CITED or CONJECTURED. The seed note's
computational claims are not used anywhere. Two sibling notes are used, and
their results are cited by file and section:
`notes/literature_novelty_jks_maps.md` (the literature note) and
`notes/reproduce_character_identity_n_le_5.md` (the reproduction note).

## Summary

**Theorem (PROVEN, given three classical results cited in §1).** Let P be a
finite poset on [n] with n ≥ 3. Then eq. (characterconj) holds for every
g ∈ Aut(P). More precisely, both sides are as follows.

- (a) Suppose the cycles of g on [n] do not all have the same length. Then
  μ(OP(P)^g) = 0, and no cyclic class is fixed by g. Both sides are 0.
- (b) Suppose g has cycle type d^k with d ≥ 2 and dk = n. Fix one point c₀.
  Let 𝒯 be the set of unions T of connected components of P such that
  c₀ ∈ T and P = T ⊔ gT ⊔ ⋯ ⊔ g^{d−1}T (a disjoint union). Then

      μ(OP(P)^g) = μ(d) · Σ_{T ∈ 𝒯} μ(OP(T)) = (−1)^{k−1} μ(d) · Σ_{T ∈ 𝒯} e_C(T),

  and for each r ∈ Z/n,

      #{C ∈ Cyc(P) : gC = C, r_g(C) = r} = Σ_{T ∈ 𝒯} e_C(T)   if gcd(n, r) = k,   and 0 otherwise.

  Here μ(d) is the number-theoretic Möbius function. Both sides of
  eq. (characterconj) then equal sgn(g) μ(d) Σ_{T ∈ 𝒯} e_C(T).
- (c) At g = 1 the identity is the Jenča–Sarkoci theorem.

**Corollary (PROVEN, same inputs).** eq. (mainconj) of the seed note holds
for every finite poset with n ≥ 3:

    H̃_{n−3}(Ô(P); C) ≅ sgn ⊗ Lie(P)

as Aut(P)-modules. The proof is a character computation (eq. homchar,
eq. liechar), and a finite-group representation over C is determined by its
character. **This gives an abstract isomorphism only.** It does not give the
"natural" isomorphism that the conjecture's wording asks for, and it does not
give a JKS-type map. By Prop. C of the literature note (§3.3), no single JKS
map can send H_P to W_P e_ζ for every P.

**What carries the proof.** The proof does not use the Jenča–Sarkoci recursion.
That recursion is blind to the phases (literature note §2.3, Lemma A). The
proof uses one element of the fixed lattice instead. Take z to be the
partition that merges a single ⟨g⟩-orbit. Crapo's complementation theorem
expands μ(OP(P)^g) over the complements of z, and they turn out to be very
rigid.

- In case (a), z has no complement.
- In case (b), the complements are exactly the "component transversals"
  T ∈ 𝒯. The interval below each one is OP(T). The interval above each one is
  the subgroup lattice of Z/d, which contributes μ(d).

The phase sum Σ ζ^{r_g(C)} is a Ramanujan sum c_d(1) = μ(d), times a count of
fixed classes that does not depend on the rotation.

**Consequences worth recording.**
- (i) Connected P: μ(OP(P)^g) = 0 for every g ≠ 1 (Cor. 7). By the literature
  note's (S2′), this is exactly eq. (mainconj) for connected P. Conjecture S
  is not needed.
- (ii) The antichain: this recovers μ(Π_n^g) = (−1)^{k−1} μ(d) d^{k−1} (k−1)!
  for g of type d^k, and μ(Π_n^g) = 0 for every other g ≠ 1. That is the
  classical fixed-point computation behind JKS (§6.1).
- (iii) The topological strengthening, that Ô(P)^g is contractible in case (a),
  follows from the Björner–Walker homotopy complementation formula (CITED,
  §1.4). It is not needed for the identity.

**COMPUTED.** `compute/fixed_point_mobius.py` checks every intermediate
lemma by brute force: complements computed inside the lattice, interval Möbius
numbers, and fixed classes by rotation. It does not use any step of the proof.
The run covers all 402 unlabeled posets with 3 ≤ n ≤ 6 and the
repeated-component disjoint unions at n = 7, 8, 9 (fixed-point-free
uniform classes there). No failures. See §7.

**Not proven here.**
- A natural isomorphism (see above).
- Conjecture S of the literature note (span of the splitting cycles ρ_w for
  w ∈ Lin P is all of H_P).
- Any statement about the global module H_n of eq. (globalind), beyond what
  follows from the local isomorphisms.

---

## 0. Conventions

These follow `compute/poset_jks_check.py` and the reproduction note.

- A word w = w₁⋯w_n is a permutation (position ↦ letter). wγ^j is w rotated
  left by j, i.e. (wγ^j)_i = w_{i+j}, indices mod n. g ∈ Aut(P) acts by
  relabelling letters: (gw)_i = g(w_i).
- A cyclic class C is a C_n-orbit {wγ^j} that meets Lin(P). C is g-fixed with
  rotation r = r_g(C) iff gw = wγ^r for one, equivalently every, w ∈ C. In that
  case g(w_i) = w_{i+r} for all i.
- OP(P) is ordered by refinement: 0̂ is the discrete partition and 1̂ is the
  one-block partition. L := OP(P)^g is the set of g-invariant members.
- μ(Q) means μ_Q(0̂, 1̂). For a 1-element poset, OP = {0̂ = 1̂} and μ = 1.
- "Union of components" means a union of connected components of the
  comparability graph of P.

## 1. Cited inputs

1. **Jenča–Sarkoci** (CITED; literature note §2.1, arXiv:1112.5782v2
   numbering).
   - Thm 4.5: for n ≥ 3, Δ(Ô(P)) ≃ ⋁^{e_C(P)} S^{n−3}.
   - Thm 3.3 (Czédli–Lenkehegyi): the order congruences are exactly the
     kernels of isotone maps, i.e. the partitions π with P/π acyclic.
   - The literature note §2.2 checks that their e_C is the note's e_C.
2. **P. Hall's theorem** (CITED; Stanley, *EC1*, 2nd ed., Prop. 3.8.5; the
   number is from memory and was not re-checked).
   μ_Q(0̂, 1̂) = χ̃(Δ(Q̄)) for every finite bounded poset Q, where Q̄ is the
   proper part.
3. **Hopf trace formula** (CITED; standard, e.g. Munkres, *Elements of
   Algebraic Topology*, Thm 22.1, number not re-checked).
   For a simplicial map f of a finite complex,
   Σ_i (−1)^i tr(f | C_i) = Σ_i (−1)^i tr(f | H_i).
4. **Crapo's complementation theorem** (CITED: H. H. Crapo, *The Möbius
   function of a lattice*, J. Combin. Theory 1 (1966) 126–131; the theorem
   number was not checked).
   Let L be a finite lattice, z ∈ L, and z^⊥ = {y : y ∧ z = 0̂, y ∨ z = 1̂}.
   Then

       μ(0̂, 1̂) = Σ_{x, y ∈ z^⊥, x ≤ y} μ(0̂, x) μ(y, 1̂).

   In particular μ(0̂, 1̂) = 0 if z has no complement. Every use of this
   theorem below is also checked directly by computer (§7, checks L2 and L3).
   Those checks compute μ(L) from scratch and compare it with the value the
   theorem predicts.
   - *Topological version, not used:* A. Björner and J. W. Walker, *A homotopy
     complementation formula for partially ordered sets*, European J. Combin.
     4 (1983) 11–19. If z ∈ L̄ has no complement, then L̄ is contractible.

**eq. (homchar) (PROVEN from 2 and 3).** g acts simplicially on Δ = Δ(Ô(P)).
A chain x₀ < ⋯ < x_i that g maps to itself is fixed pointwise, because g
preserves order. So g fixes each such simplex with its orientation, and
tr(g | C_i) is the number of g-fixed i-chains, i.e. the number of i-chains of
Ô(P)^g = proper part of L. With the empty simplex in degree −1, the Hopf trace
formula gives

    Σ_i (−1)^i tr(g | H̃_i(Δ)) = χ̃(Δ(L̄)) = μ_L(0̂, 1̂)

by Hall. By Thm 4.5 only i = n − 3 survives:
tr(g | H_P) = (−1)^{n−3} μ(L).

**eq. (liechar)** is PROVEN in the seed note's sense, and its convention is
checked numerically in the reproduction note. Lie(P) has the basis
{u_C e_ζ : C ∈ Cyc(P)}. g permutes it up to the scalars ζ^{r_g(C)} on fixed
classes.

## 2. The fixed lattice L = OP(P)^g

**Lemma 1 (PROVEN).** OP(P) is closed under intersection (meet in Π_n). So
OP(P) and L are finite lattices, both with meet equal to intersection.

*Proof.* Let π, σ ∈ OP(P). Suppose x₀, …, x_m = x₀ is a (π ∩ σ)-cycle: each
step is either strict (x_{i−1} < x_i) or stays inside a (π ∩ σ)-block. Then
it is a π-cycle, so by Jenča–Sarkoci Def. 3.1 it lies in one π-block. By the
same argument it lies in one σ-block. So it lies in one (π ∩ σ)-block, and
π ∩ σ is an order congruence. If π and σ are g-invariant, so is π ∩ σ. Both
lattices contain 1̂, and a finite meet-semilattice with 1̂ is a lattice. ∎

The join in L need not equal the join in Π_n. Below we only use joins in
situations where we can show that the Π_n-join is already in L. The
computation in §7 takes joins inside L itself.

**Lemma 2 (PROVEN).** Let Q be a finite poset and h ∈ Aut(Q).
- (i) Every ⟨h⟩-orbit is an antichain.
- (ii) If A ⊆ Q is an antichain, then the partition z_A whose only
  non-singleton block is A is in OP(Q).
- (iii) In particular, the partition merging one ⟨g⟩-orbit of P is in L.

*Proof.*
- (i) If x < h^i x, then x < h^i x < h^{2i} x < ⋯ < h^{oi} x = x, where o is
  the order of h. This is impossible.
- (ii) Take a z_A-cycle. Each step is either strict or a jump inside A.
  Suppose it contains a strict step. Then it contains a maximal run of strict
  steps that starts and ends in A (or a closed strict cycle, which is
  impossible). That run gives a < a′ with a, a′ ∈ A. If a = a′ this is a
  strict cycle, and if a ≠ a′ it contradicts A being an antichain. So the
  cycle has no strict steps and lies in A.
- (iii) Combine (i) and (ii); the merged partition is g-invariant because the
  block is an orbit. ∎

**Lemma 3 (PROVEN; interval structure).** Let y ∈ OP(P).
- (i) Upper interval: π ↦ π/y is an isomorphism [y, 1̂]_{OP(P)} ≅ OP(P/y).
  If y ∈ L, it restricts to [y, 1̂]_L ≅ OP(P/y)^{ḡ}, where ḡ is the
  automorphism of P/y induced by g.
- (ii) Lower interval, when y = {T, gT, …, g^{d−1}T} is a partition into d
  unions of components and g has order d on P: π ↦ π|_T is an isomorphism
  [0̂, y]_L ≅ OP(T).

*Proof.*
- (i) For π ≥ y, (P/y)/(π/y) = P/π, so the two quotients are acyclic
  together. g-invariance corresponds on both sides.
- (ii) Let π ≤ y. There are no relations between distinct blocks of y, so
  P/π is acyclic iff each restriction π|_{g^jT} is an order congruence. For
  g-invariant π, π|_{g^jT} = g^j(π|_T), so π is determined by π|_T. Conversely,
  any σ ∈ OP(T) extends to π = ⋃_j g^j σ. This is g-invariant because
  g^d = 1, and it is order-preserving by the remark just made. ∎

## 3. Unequal cycle lengths

**Proposition 4 (PROVEN).** Suppose the cycles of g ∈ Aut(P) do not all have
the same length. Then μ(L) = 0. (In particular this holds if g ≠ 1 has a
fixed point.)

*Proof.* Let c be an orbit of maximal length D. Then D ≥ 2, because the
lengths are not all equal. Let z ∈ L merge c (Lemma 2). z ≠ 0̂ since D ≥ 2,
and z ≠ 1̂ since some other orbit exists. Suppose y ∈ L is a complement of z.

1. y ∧ z = 0̂ means the D points of c lie in D distinct y-blocks
   B₁, …, B_D. g permutes the y-blocks and maps the block of x to the block
   of gx. So {B_i} is one ⟨ḡ⟩-orbit in Q := P/y, of size D.
2. By Lemma 2(i) this orbit is an antichain of Q. By Lemma 2(ii), merging it
   keeps the quotient acyclic. So the Π_n-join y ∨ z, which merges exactly
   B₁, …, B_D, is in OP(P). It is g-invariant, so y ∨_L z = y ∨_{Π_n} z.
3. y ∨ z = 1̂ therefore forces y = {B₁, …, B_D}, with g cyclically permuting
   the blocks. Then g^D fixes every block.
4. Let c′ be an orbit of length ℓ < D and x ∈ c′ ∩ B₁. The point g^j x lies
   in B_{1+j}, indices mod D. Since g^ℓ x = x, we get B_{1+ℓ} = B₁, so D | ℓ.
   This is impossible for 1 ≤ ℓ < D.

So z has no complement, and μ(L) = 0 by Crapo. ∎

**Lie side (PROVEN; this is Lemma A of the literature note §2.3, re-proved).**
If gC = C with rotation r, then g acts on the n-cycle of positions as i ↦ i + r.
All its orbits there have size n / gcd(n, r). So if g fixes any cyclic class,
all cycles of g have one common length. Under the hypothesis of Prop. 4, the
right side of eq. (characterconj) is therefore an empty sum.

## 4. Uniform cycle type d^k: the Möbius side

Let g have cycle type d^k with d ≥ 2 and n = dk, and fix a point c₀ with
orbit c. Let 𝒯 be as in the summary. For T ∈ 𝒯, write
y_T = {T, gT, …, g^{d−1}T}.
- Each g^jT meets each orbit exactly once. (g^jT are disjoint and cover P;
  if x, g^i x ∈ T with 0 < i < d, then g^i x ∈ T ∩ g^iT = ∅.) So |T| = k.
- T ↦ y_T is a bijection from 𝒯 onto these partitions, with T the block
  that contains c₀.

**Proposition 5 (PROVEN).** μ(L) = μ(d) · Σ_{T ∈ 𝒯} μ(OP(T)).

*Proof.* If k = 1, then P is a single orbit, so it is an antichain (Lemma 2),
and 𝒯 = {{c₀}}. L is the lattice of rotation-invariant partitions of Z/d.
The block H containing 0 of such a partition is a subgroup: if b ∈ H, then
H + b is the block containing b, which is H. So the partition is the coset
partition of H. Hence L ≅ (subgroups of Z/d) ≅ divisor lattice of d, and
μ(L) = μ(d) = μ(d) · μ(OP(pt)).

Now let k ≥ 2, and let z ∈ L merge c. Then z ≠ 0̂, 1̂. Steps 1–3 of the
proof of Prop. 4 apply verbatim with D = d. A complement y of z has exactly d
blocks, cyclically permuted by g, and every block meets c. Moreover
Q = P/y is a single ⟨ḡ⟩-orbit, so Q is an antichain (Lemma 2(i)). That
means there are no relations between blocks, so each block is a union of
components and y = y_T for T = (block of c₀) ∈ 𝒯.

Conversely, every y_T is in L. It is g-invariant, and P/y_T is an antichain,
hence acyclic. It is a complement of z:
- y_T ∧ z = 0̂, since each g^jT meets c once;
- y_T ∨ z ⊇ the Π_n-join, which already merges all d blocks through c.

So z^⊥ = {y_T : T ∈ 𝒯}. Two partitions into d blocks that are comparable
are equal, so z^⊥ is an antichain. Crapo's theorem then reduces to
μ(L) = Σ_T μ_L(0̂, y_T) μ_L(y_T, 1̂).

- Lemma 3(ii): μ_L(0̂, y_T) = μ(OP(T)).
- Lemma 3(i): [y_T, 1̂]_L ≅ OP(Q)^{ḡ}, where Q is an antichain of size d
  and ḡ is a d-cycle. This is the k = 1 case above, so μ_L(y_T, 1̂) = μ(d). ∎

**Closing the Möbius side.** |T| = k. By Hall + J–S Thm 4.5 (for k ≥ 3), and
directly for k = 1, 2 (OP(T) has one or two elements, and e_C(T) = 1):

    μ(OP(T)) = (−1)^{k−1} e_C(T).                                   (★)

So μ(L) = (−1)^{k−1} μ(d) Σ_{T ∈ 𝒯} e_C(T).

## 5. Uniform cycle type d^k: the Lie side

**Lemma 6a (PROVEN).** Let w ∈ Lin(P) and 0 ≤ j < n. Then wγ^j ∈ Lin(P) iff
{w₁, …, w_j} is a union of components.

*Proof.* Let A = {w₁, …, w_j}. If A is a union of components, then no
relation crosses between A and its complement, so the rotated word is a
linear extension. Conversely, suppose wγ^j ∈ Lin(P), and take a ∈ A and
b ∉ A. In w, a precedes b, so b ≮ a. In wγ^j, b precedes a, so a ≮ b. So a and
b are incomparable. ∎

**Proposition 6 (PROVEN).** For each r ∈ Z/n, let N_r be the number of
g-fixed cyclic classes C with r_g(C) = r. Then

    N_r = Σ_{T ∈ 𝒯} e_C(T)   if gcd(n, r) = k,     and N_r = 0 otherwise.

*Proof.* If gC = C with rotation r, then g has orbit size n / gcd(n, r) on
positions, and this must equal d. So gcd(n, r) = k and r = ks with
gcd(s, d) = 1. Fix such an r, and let t be the inverse of s mod d. Put
h = g^t. Then h generates ⟨g⟩, g = h^s, and h(w_i) = w_{i+k} for w ∈ C.

*The cut set is k-periodic.* For w ∈ C ∩ Lin(P), let K(w) = {j : wγ^j ∈ Lin P}.
Then |K(w)| = |C ∩ Lin P|. Since g maps Lin P to itself and
g(wγ^j) = wγ^{j+r}, the set K(w) is invariant under +r. So it is invariant
under the subgroup ⟨r⟩ = kZ/nZ. It contains 0, hence all multiples of k.

*Segment decomposition.* By Lemma 6a, each prefix {w₁, …, w_{mk}} is a union
of components, and so is each segment S_m = {w_{mk+1}, …, w_{(m+1)k}} (a
difference of nested unions of components). Moreover S_m = h^m S₀. So
T := S₀ is a union of components with P = ⊔_m h^m T = ⊔_m g^m T, i.e. T is a
"transversal" in the sense of 𝒯 but without the base-point condition. Let 𝒯*
be the set of all such T; it is the disjoint union of the g^i𝒯, so
|𝒯*| = d|𝒯|, and e_C is constant on each g-orbit. Writing u = w₁⋯w_k, we
get u ∈ Lin(T) and

    w = u · hu · h²u ⋯ h^{d−1}u.                                    (†)

*Bijection.* Consider the two sets

    X = {(C, w) : gC = C, r_g(C) = r, w ∈ C ∩ Lin P}   and
    Y = {(T, u) : T ∈ 𝒯*, u ∈ Lin(T)}.

The map (C, w) ↦ (S₀, w₁⋯w_k) is a bijection X → Y. Its inverse sends
(T, u) to (the class of w, w) with w defined by (†). That w is a linear
extension: each block h^mu is a linear extension of the union of components
h^mT. And g = h^s maps position i + mk to i + (m+s)k, so gw = wγ^{ks} = wγ^r.

*Weights.* For (C, w) ↦ (T, u):
- the rotations of u (as a word on T) that are linear extensions of T are
  the u-internal cuts j ∈ [0, k) with {u₁, …, u_j} a union of components;
- by Lemma 6a and the k-periodicity of K(w), these are exactly
  K(w) ∩ [0, k), so their number is |K(w)|/d.

Sum 1/|[u]_T ∩ Lin T| over both sides of the bijection:

    Σ_{(T,u) ∈ Y} 1/|[u]_T ∩ Lin T| = Σ_{T ∈ 𝒯*} e_C(T) = d Σ_{T ∈ 𝒯} e_C(T),
    Σ_{(C,w) ∈ X} d/|K(w)| = Σ_C |C ∩ Lin P| · d/|C ∩ Lin P| = d N_r.

So N_r = Σ_{T ∈ 𝒯} e_C(T). ∎

The count does not depend on which generator of ⟨g⟩ acts as rotation by k.
The phases therefore enter only through which rotations r occur:

    Σ_{gC=C} ζ^{r_g(C)} = (Σ_T e_C(T)) · Σ_{s ∈ (Z/d)^×} (ζ^k)^s = μ(d) Σ_{T ∈ 𝒯} e_C(T).

This uses the fact that ζ^k is a primitive d-th root of unity and the sum of
the primitive d-th roots of unity is μ(d) (Ramanujan sum c_d(1)). The value
is the same for every choice of primitive ζ, and under the convention
r ↦ −r. This matches the reproduction note's finding that both sign
conventions F0 and F1 pass.

## 6. Proof of the theorem, corollaries, special cases

**Proof of the theorem.**
- g = 1: J–S Thm 4.5 + eq. (homchar) + eq. (liechar).
- Unequal cycle lengths: Prop. 4 and the Lie-side remark after it.
- Type d^k, d ≥ 2. By eq. (homchar), Prop. 5 and (★):

      (−1)^{n−3} μ(L) = (−1)^{n−1} (−1)^{k−1} μ(d) Σ_T e_C(T) = (−1)^{n−k} μ(d) Σ_T e_C(T).

  By eq. (liechar) and Prop. 6:

      sgn(g) · Σ ζ^{r_g(C)} = (−1)^{(d−1)k} μ(d) Σ_T e_C(T) = (−1)^{n−k} μ(d) Σ_T e_C(T).

  The two sides agree. ∎

**Corollary 7 (PROVEN; connected posets).** If P is connected and g ≠ 1, then
μ(OP(P)^g) = 0. Hence eq. (mainconj) holds for connected P, and
H_P ≅ C[Lin P] ⊗ sgn ≅ C[Lin P] is a free Aut(P)-module.

*Proof.* If g has unequal cycle lengths, use Prop. 4. Otherwise g has type
d^k with d ≥ 2. Then 𝒯 = ∅, because a union of components of a connected P
is ∅ or P, and neither is a transversal when d ≥ 2. So μ(L) = 0 by Prop. 5.
(The k = 1 case cannot occur, since it forces P to be an antichain, which is
not connected for n ≥ 2.) This is the vanishing that the literature note's
(S2′) identifies as equivalent to eq. (mainconj) for connected P. ∎

### 6.1 Antichain (sanity anchor; PROVEN)

Let P be the antichain on [n], so OP(P) = Π_n. For g of type d^k, 𝒯 consists
of the transversals of the k cycles through c₀ (d^{k−1} of them). Each T is a
k-antichain with e_C(T) = (k−1)!. So

    μ(Π_n^g) = (−1)^{k−1} μ(d) d^{k−1} (k−1)!,

and μ(Π_n^g) = 0 for every g ≠ 1 that is not of uniform type. Hence
χ_{H̃(Π̄_n)}(g) = (−1)^{n−k} μ(d) d^{k−1}(k−1)!, and
sgn(g) χ = μ(d) d^{k−1}(k−1)!. This is the well-known value of χ_{Lie_n} on
the class d^k, by Klyachko's induced-character description Ind_{C_n}^{S_n} ζ
evaluated on that class (an elementary computation, CITED as classical). So
the special case reproduces the classical JKS character identity, and the
general proof restricts to the classical fixed-point computation of μ(Π_n^g).
That computation is attributed to Stanley (*Some aspects of groups acting on
finite posets*, JCTA 32 (1982)) and Hanlon (*The fixed-point partition
lattices*, Pacific J. Math. 96 (1981)); this attribution is from memory, with
exact statements not re-checked.

### 6.2 Disjoint unions of equal components (PROVEN)

Let P = Q₁ ⊔ ⋯ ⊔ Q_m, where the Q_i are isomorphic connected posets of size
ℓ, and let g ∈ Aut(P) permute the components. Write g = (σ; ψ) with σ ∈ S_m
the induced permutation of components.

In general, a σ-cycle of length e returns each of its components to itself
by g^e, which acts there as some automorphism φ of Q. The point cycles on
those components have lengths e × (cycle lengths of φ). Take the rigid case:
Q is connected with trivial automorphism group (e.g. a chain). Then
g = (σ; 1), and g has type d^k on points iff σ has type d^{m/d}. 𝒯 is then
the set of choices of one component from each σ-cycle, with c₀'s component
forced. So:

- |𝒯| = d^{m/d − 1};
- each T is a disjoint union of m/d copies of Q;
- χ_{H_P}(g) = sgn(g) μ(d) d^{m/d−1} e_C(Q^{⊔ m/d}).

*Example (the seed note's n = 6 case).* Three disjoint 2-chains, g permuting
them cyclically: d = 3, m/d = 1, T = one 2-chain, e_C = 1. So
χ_{H_P}(g) = (+1)(−1)(1) = −1. The note's claimed value −1 is thereby PROVEN.

*Equal chains, σ a single m-cycle.* Here 𝒯 is the single component of c₀,
and e_C(chain) = 1. So χ_{H_P}(g) = sgn(g) μ(m) = (−1)^{(m−1)ℓ} μ(m).

### 6.3 Ordinal sums (PROVEN)

An ordinal sum P = P₁ ⊕ P₂ with both parts nonempty is connected. So
Cor. 7 applies: χ_{H_P}(g) = 0 for g ≠ 1, and H_P is free. The same holds for
every connected family: crowns, products of chains, complete layered posets
with at least two layers, and so on.

### 6.4 Where the suggested approaches stand

- *Equivariant J–S recursion.* Not used, and it cannot see the phases
  (literature note §2.3). The proof replaces it with complementation at an
  orbit-merging element. That move is the poset analogue of a standard way to
  compute μ(Π_n^g).
- *Relating OP(P)^g to an orbit/quotient poset.* There is a partial
  classification, and it is all that is needed: the lattice is analyzed only
  around z and its complements. The orbit partition θ_g is always in L
  (Lemma 2 shows each orbit is an antichain, and the quotient P/θ_g is the
  orbit poset, which is acyclic). L itself is not described globally here.
- *Does not break anywhere.* The general argument does not fail at any step.
  The only non-elementary inputs are the three cited theorems of §1.

### 6.5 Open, and how this interacts with sibling items

- Naturality: an explicit Aut(P)-isomorphism, for example through Conjecture S
  and Φ (literature note §3.4, (S3)), is still open. The present theorem does
  imply the module statement in (S3)(c): W_P/(W_P ∩ Sh_n) ≅ W_P/(W_P ∩ K_ζ)
  for every P that satisfies Conjecture S.
- The global module eq. (globalind) needs H_n ⊗ sgn ≅ ⊕_P Lie(P) as
  S_n-modules. Given the local isomorphisms, it reduces to the induced-module
  bookkeeping of the seed note's §"A global S_n-module". That bookkeeping is
  not checked here (CONJECTURED as far as this note is concerned).

## 7. Computation

Script: `compute/fixed_point_mobius.py`. It reuses the enumeration and
exact-arithmetic helpers of `compute/poset_jks_check.py`. Run from `compute/`:

    python3 fixed_point_mobius.py --nmax 6 --large 7 8 9 > output/fixed_point_mobius.txt

The script handles one representative per conjugacy class of Aut(P). It
works by brute force and does not use any argument from §§2–6:
- complements are found by searching L, with joins computed as least upper
  bounds inside L;
- interval Möbius numbers are computed by recursion inside L;
- fixed classes are found by testing rotations.

Checks:

| check | statement | how |
|---|---|---|
| L1 | orbits are antichains; merging one orbit is in OP(P) | every orbit of every class representative |
| L2 | unequal cycle lengths: z (maximal orbit) has no complement in L; μ(L) = 0; no fixed class | direct |
| L3 | type d^k, k ≥ 2: for **every** orbit c and **every** c₀ ∈ c, z^⊥ = {y_T : T ∈ 𝒯}; μ_L(0̂, y_T) = μ(OP(T)); μ_L(y_T, 1̂) = μ(d); μ(L) = μ(d) Σ_T μ(OP(T)) | direct |
| L4 | N_r = Σ_T e_C(T) if gcd(n, r) = k, else 0 | direct |
| L5 | connected P, g ≠ 1: μ(L) = 0 | direct |
| F | full identity eq. (characterconj), exact in Z[ζ] | as in `poset_jks_check.py` |

Positive controls (the run fails if any of them never fires):
- dropping μ(d) from L3 must disagree with μ(L) somewhere;
- replacing e_C(T) by |Lin T| in L4 must disagree somewhere;
- the complement search in L3 must find nonempty z^⊥ somewhere, so that L2's
  "no complement" is not a vacuous search.

Families covered:
- all unlabeled posets with 3 ≤ n ≤ 6 (5 + 16 + 63 + 318 = 402);
- for n = 7, 8, 9, every disjoint union of connected posets of size ≤ 4 in
  which some component occurs at least twice (194 posets). These are the
  posets where the phases live. For these only the fixed-point-free uniform
  classes d^k are checked (the full OP lattice at g = 1 is too slow for the
  brute-force Möbius routine); every class is checked for n ≤ 6.

Result (COMPUTED; the archived output is `compute/output/fixed_point_mobius.txt`):

```
posets checked: 596 (all unlabeled 3 <= n <= 6, every conjugacy class of Aut(P); repeated-component disjoint unions at n in [7, 8, 9], fixed-point-free uniform classes d^k only)
  pairs: 975
  F: 975
  L2: 518
  L3: 48
  L3_with_complements: 239
  L4: 48
  L5: 365
  k1: 7
  control_no_mud_detected: 239
  control_lin_detected: 17
failures: 0
ALL CHECKS PASS
```

Runtime about 2 minutes, single core. Note: n = 7 is prime, so its only
fixed-point-free uniform class is 7^1 (antichain, k = 1); n = 8, 9 carry the
k ≥ 2 cases (types 2^4, 4^2, 3^3).

Tests: `python3 -m unittest test_fixed_point_mobius` (in `compute/`).
