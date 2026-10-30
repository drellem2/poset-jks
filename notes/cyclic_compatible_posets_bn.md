# Cyclic-compatible posets: b_n = n [x^n] log A(x)

Findings for the note's section "Witt and plethystic-logarithm pattern",
eq. (bnlog), and section "Prime-degree sanity check".

**Summary.**
- With the definition pinned down in §1, the note's values of a_n (n ≤ 8) and
  b_n (n ≤ 8) are reproduced by brute force (COMPUTED).
- The identity b_n = n[x^n] log A(x) is PROVEN (§3) by a bijection with
  "cyclic factorizations" into irreducible pieces.
- Σ_P e_C(P) = (n−1)! b_n is PROVEN (§2), so the dimension of the right-hand
  side of (globalind) is the right one.
- The C_n-action on B_n has the antichain as its only fixed point for every n,
  and #Fix(σ^k) = b_gcd(k,n). Hence b_p ≡ 1 (mod p) for p prime (PROVEN, §4).
- Assuming (globalind), eqs. (frob) and (plethlog) follow (PROVEN, §5). This
  is a deduction from (globalind), not a proof of (globalind) itself.

Every claim carries a tag: PROVEN, COMPUTED, CITED or CONJECTURED.

Reproduce all computations with

    python3 compute/cyclic_posets.py 7     # all checks, about 25 s
    python3 compute/cyclic_posets.py 8     # adds a_8, b_8 (checks 1, 3, 4 only at n=8), a few minutes

## 1. Definitions

Posets live on [n] = {1,…,n}. For c ∈ Z/n, let L_c be the rotated word

    L_c = (c+1, c+2, …, n, 1, …, c),        L_0 = 12…n.

Think of c as a *cut* on the circle 1 → 2 → … → n → 1, between c and c+1.

- a_n is the number of *naturally labeled* posets on [n], meaning posets for
  which L_0 is a linear extension (i <_P j ⇒ i < j).
  A(x) = 1 + Σ_{n≥1} a_n x^n.
- B_n is the set of labeled posets P on [n] such that **some L_c is a linear
  extension of P**. Put b_n = |B_n|.
- C(P) = { c ∈ Z/n : L_c ∈ Lin(P) }. So P ∈ B_n exactly when C(P) ≠ ∅.
- σ = (1 2 … n) acts on labeled posets by relabeling: i <_{σP} j ⇔
  σ⁻¹i <_P σ⁻¹j. A word w is an extension of P exactly when σ∘w is an
  extension of σP, and σ∘L_c = L_{c+1}. So C(σP) = C(P) + 1. In particular
  C_n = ⟨σ⟩ acts on B_n.

**COMPUTED** (`compute/cyclic_posets.py`):
- a_n = 1, 2, 7, 40, 357, 4824, 96428, 2800472 for n = 1..8. This agrees with
  OEIS A006455 (the A006455 terms are typed into the script).
- |B_n|, with B_n built explicitly as a set of posets, is
  1, 3, 16, 131, 1561, 26532, 637890 for n ≤ 7.
- For n ≤ 6 the script also enumerates *all* labeled posets on [n]. Their
  counts 1, 3, 19, 219, 4231, 130023 match A001035. It then tests the
  definition of B_n directly on each one, with the same result.
- b_8 = 21580043. At n = 8 this is computed from Lemma 1 below,
  b_n = n Σ_{P natural} 1/|C(P)|, not from an explicit set.
- All of these equal n[x^n] log A(x), computed in exact rational arithmetic,
  and they equal the note's list 1, 3, 16, 131, 1561, 26532, 637890, 21580043.

The definition "some rotation of 12…n is a linear extension" therefore
reproduces every value the note gives.

## 2. The (n−1)! b_n identity

**Proposition 1 (PROVEN).** Σ_{P labeled on [n]} e_C(P) = (n−1)! · b_n.

*Proof.* S_n acts on words by right rotation, w ↦ w∘γ, and e_C(P) counts the
orbits O of this action that meet Lin(P). Swapping the order of summation:

    Σ_P e_C(P) = Σ_O #{P : O ∩ Lin(P) ≠ ∅}.

There are n!/n = (n−1)! orbits, because the rotation action is free. Left
multiplication by τ ∈ S_n commutes with right rotation and maps Lin(P) onto
Lin(τP). It therefore permutes the orbits transitively, and
#{P : O ∩ Lin(P) ≠ ∅} is the same for every O. For the orbit
O_0 = {L_c : c ∈ Z/n} of 12…n, this count is b_n by definition. ∎

**COMPUTED** (n ≤ 6, by enumerating all labeled posets and their linear
extensions): Σ e_C = 1, 3, 32, 786, 37464, 3183840 = (n−1)! b_n.

## 3. Proof of b_n = n [x^n] log A(x)

### 3.1 Structure of C(P)

**Lemma 1 (PROVEN).** The following hold.
- (a) If c ≠ c' are both in C(P), then the arcs (c, c'] and (c', c] are
  mutually incomparable in P.
- (b) For naturally labeled P, C(P) = {0} ∪ { c ∈ [1, n−1] : no relation
  i <_P j has i ≤ c < j }.
- (c) Σ_{P∈B_n} |C(P)| = n·a_n. Hence b_n = n Σ_{P natural} 1/|C(P)|.

Here (c, c'] denotes the arc c+1, …, c' read cyclically.

*Proof.*
- (a) L_c lists (c, c'] before (c', c], and L_{c'} lists them the other way
  round. A relation between the two arcs would contradict one of the two
  extensions.
- (b) L_c with c ≠ 0 reverses exactly the pairs i ≤ c < j. In a naturally
  labeled poset every relation has the form i < j.
- (c) The pairs (P, c) with c ∈ C(P) are in bijection with pairs
  (Q natural, c ∈ Z/n), via P = σ^c Q. So there are n·a_n of them. Since
  |C(σP)| = |C(P)|, summing 1/|C(P)| over these pairs gives b_n and also
  n Σ_{Q natural} 1/|C(Q)|. ∎

### 3.2 Irreducibles and cyclic factorizations

Let Q be a poset on a set X, and fix a linear order x_1 < … < x_k of X that is
an extension of Q. Q is **reducible** (with respect to this order) if, for
some 1 ≤ j < k, the sets {x_1..x_j} and {x_{j+1}..x_k} are mutually
incomparable. Otherwise Q is **irreducible**. Let i_k be the number of
irreducible naturally labeled posets on [k], and I(x) = Σ_{k≥1} i_k x^k.

**Lemma 2 (PROVEN).** A = 1/(1 − I).

*Proof.* Let P be naturally labeled. Cut [n] at every linear cut from Lemma
1(b), and transport each block to an initial segment [k] in an
order-preserving way. This gives a sequence of naturally labeled posets
(Q_1, …, Q_m), and P is their ordered disjoint union.

Each Q_i is irreducible. Suppose a block [a, b] had an interior cut j, so
[a, j] ⊥ [j+1, b]. Take x ≤ j < y. If both lie in the block, they are
incomparable. Otherwise a linear cut a−1 or b separates them, and again they
are incomparable. So j would be a linear cut of P, which it is not.

Conversely, the ordered disjoint union of irreducibles has exactly the
junctions as its linear cuts. An interior cut would restrict to a cut of one
of the irreducible pieces. So the decomposition is a bijection between
naturally labeled posets and sequences of irreducibles, and
A = Σ_m I^m. ∎

**Definition.** A *cyclic factorization* of size n consists of:
- a nonempty set S = {s_1, …, s_m} ⊆ Z/n of cuts; and
- for each arc α = (s_t, s_{t+1}] (indices mod m; if m = 1 the arc is the
  whole circle (s_1, s_1]), an irreducible poset Q_α on α, taken with respect
  to the arc's linear order s_t+1, s_t+2, …, s_{t+1}.

Its *realization* is the labeled poset P = ⊔_α Q_α on [n]: the disjoint union
of the pieces, with no relations between different arcs.

**Lemma 3 (PROVEN).** n[x^n] log A(x) equals the number of cyclic
factorizations of size n.

*Proof.* By Lemma 2,

    log A = −log(1−I) = Σ_{m≥1} I^m / m,
    so  n[x^n] log A = Σ_m (n/m)·[x^n] I^m.

[x^n] I^m counts sequences (Q_1, …, Q_m) of irreducibles of total size n.
Given such a sequence and an offset c ∈ Z/n, lay Q_1, Q_2, … on consecutive
arcs of the circle starting just after cut c. The result is a cyclic
factorization with m cuts, and n·[x^n] I^m counts these (sequence, offset)
pairs.

Every cyclic factorization with m cuts arises from exactly m pairs: choose
which of its m cuts is the offset, and read the pieces from there. Distinct
choices give distinct offsets, so no collisions occur even when the
factorization has rotational symmetry. Dividing by m gives the count of
cyclic factorizations with m cuts. ∎

### 3.3 The bijection

**Lemma 4 (PROVEN).** Let P = ⊔_α Q_α be a disjoint union of posets on
disjoint sets. A linear order is an extension of P if and only if its
restriction to each part is an extension of that part.

This is immediate, since every relation of P lies inside one part.

**Theorem (PROVEN).** The map P ↦ (C(P), (P|_α)_α) is a bijection from B_n
onto the set of cyclic factorizations of size n. Its inverse is
realization. Consequently

    b_n = n [x^n] log A(x),   equivalently   n·a_n = Σ_{k=1}^{n} b_k a_{n−k}.

*Proof.*

**(i) The map lands in cyclic factorizations.** Let P ∈ B_n and S = C(P) ≠ ∅.

- *The arcs are mutually incomparable.* Take distinct arcs α = (s, ·] and
  α' = (s', ·]. L_s begins with α, so α precedes α' in L_s. L_{s'} begins
  with α' and reaches α later, so α' precedes α there. Hence α ⊥ α'. So P is
  the disjoint union of the restrictions P|_α.
- *Each piece is compatible with its arc order.* P|_α has the restriction of
  L_s as an extension, and that restriction is the arc order of α.
- *Each piece is irreducible.* Suppose P|_α splits at an interior point c, so
  α_1 = (s, c] and α_2 = (c, s'] are incomparable. Consider L_c:
  - every other arc appears in L_c as a contiguous block in its own arc order,
    because c is interior to α only;
  - on α, L_c reads α_2 and then α_1, which is an extension of
    P|_α = P|_{α_1} ⊔ P|_{α_2}.

  By Lemma 4, L_c ∈ Lin(P), so c ∈ C(P) = S. But c is interior to an arc of
  S, a contradiction.

**(ii) Realization lands in B_n and recovers S.** Let (S, (Q_α)) be a cyclic
factorization with realization P. For s ∈ S, the word L_s lists the arcs one
after another, each in its arc order. By Lemma 4 it is an extension, so
S ⊆ C(P) and P ∈ B_n.

Suppose some c ∉ S lies in C(P). Then c is interior to an arc α = (s, s'],
splitting it into nonempty α_1 = (s, c] and α_2 = (c, s']. (If |S| = 1,
then s' = s.) L_s puts α_1 before α_2, and L_c puts α_2 before α_1. So
α_1 ⊥ α_2, and Q_α is reducible at c, a contradiction. Hence C(P) = S, and
the pieces of P are the Q_α.

Parts (i) and (ii) show that the two maps are mutually inverse. Lemma 3
finishes the proof. The recurrence form is the coefficient of x^n in
x A'(x) = (x (log A)'(x)) · A(x). ∎

*Remark.* This is the standard "cycle of irreducibles" interpretation of
n[x^n] log(1/(1−I)), as with necklaces or Lyndon words. The poset-specific
content is the observation that the cuts at which a poset is
cyclically compatible are exactly the junctions of its cyclic factorization
(the Theorem, parts (i) and (ii)).

**COMPUTED** consistency checks:
- The recurrence n a_n = Σ b_k a_{n−k} holds with the brute-force b_n for
  n ≤ 7, and with the Lemma 1(c) value for n = 8.
- The irreducible counts implied by Lemma 2 can be read off as
  I = 1 − 1/A. They are not separately enumerated.

## 4. C_n-action on B_n and the prime-degree check

**Proposition 2 (PROVEN).** Let σ = (1 2 … n) act on B_n by relabeling. Then:
- (a) for k ∈ Z/n, #Fix(σ^k) = b_{gcd(k,n)}, with gcd(0, n) = n;
- (b) the antichain is the unique σ-fixed point;
- (c) the number of elements with trivial stabilizer is
  Σ_{d|n} μ(n/d) b_d, and it is divisible by n. For n = p prime this gives
  b_p ≡ 1 (mod p), and (b_p − 1)/p is the number of free orbits.

*Proof.* By the Theorem, B_n corresponds to cyclic factorizations, and σ acts
on them by rotating everything by 1. This is because C(σP) = C(P) + 1 and
the pieces are transported. Let g = gcd(k, n).

- (a) A factorization is fixed by σ^k exactly when it is fixed by σ^g, that
  is, when it is g-periodic. A g-periodic factorization of size n is the
  same thing as a factorization of size g: take the cut set mod g and the
  pieces on one period. Conversely, lift any size-g factorization
  periodically. So the count is b_g.
- (b) σ-fixed means 1-periodic. The only cut set is all of Z/n, every arc is
  a singleton, and P is the antichain. Directly: C(P) is a nonempty
  σ-invariant subset of Z/n, hence all of Z/n.
- (c) This is Möbius inversion of (a) over the subgroup lattice of the
  cyclic group. Elements with trivial stabilizer form free orbits of size
  n. ∎

**COMPUTED** for n ≤ 7, by applying σ^k to the explicit set B_n:
- #Fix(σ^k) = b_gcd(k,n). For example, at n = 6 the values for k = 0..5 are
  [26532, 1, 3, 16, 3, 1].
- The antichain is the only σ-fixed point.
- (b_p − 1)/p = 1, 5, 312, 91127 for p = 2, 3, 5, 7.

These match the note's multiplicities 5 (p = 3) and 312 (p = 5) in
H_p ≅ ((b_p−1)/p)·C[S_p] ⊕ (sgn⊗Lie_p). That decomposition itself is still
conditional on (globalind).

## 5. Consequences for (frob) and (plethlog), conditional on (globalind)

**Proposition 3 (PROVEN, as a deduction).** Let V_n = Ind_{C_n}^{S_n}(ζ ⊗
C[B_n]), where C_n = ⟨σ⟩ acts on C[B_n] by relabeling and ζ is a faithful
character of C_n. Then

    ch V_n = (1/n) Σ_{d|n} μ(d) b_{n/d} p_d^{n/d},
    Σ_n ch V_n = Σ_{d≥1} (μ(d)/d) log A(p_d).

Twisting by sgn multiplies the d-term by (−1)^{n−n/d}. So, *if* (globalind)
holds, eqs. (frob) and (plethlog) of the note hold, with sign convention
H_n ≅ sgn ⊗ V_n.

*Proof.*
- The character of C[B_n] at σ^k is #Fix(σ^k) = b_{n/d}, where d is the order
  of σ^k (Proposition 2(a)).
- σ^k has cycle type (d^{n/d}).
- The Frobenius formula for induced characters gives

      ch V_n = (1/n) Σ_k ζ(σ^k) b_{n/d(k)} p_{d(k)}^{n/d(k)}.

- Summing ζ(σ^k) over the k of a given order d gives the sum of the
  primitive d-th roots of unity, which is μ(d).
- For the generating function, Σ_n (1/n) Σ_{d|n} μ(d) b_{n/d} p_d^{n/d}
  = Σ_d (μ(d)/d) Σ_m (b_m/m) p_d^m, and Σ_m b_m x^m/m = log A(x) by the
  Theorem.
- The sign: ω(p_d^{n/d}) = (−1)^{(d−1)n/d} p_d^{n/d}. ∎

**CONJECTURED (not addressed here).** (globalind) itself, which identifies
the global homology module H_n with sgn ⊗ V_n. It depends on the main poset
JKS conjecture, and this item makes no progress on it. Proposition 1 shows
only that the dimensions agree, *given* Jenča–Sarkoci (CITED in the note, not
re-checked here): dim H_n = Σ_P e_C(P) = (n−1)! b_n = dim V_n.
