# Conjecture S: the splitting cycles of linear extensions span H_P

Work item: mg-3de87 (re-scoped). The target is **Conjecture S** of
`notes/literature_novelty_jks_maps.md` §3.4 (the "literature note"):

    span{ρ_w : w ∈ Lin P} = H_P := H̃_{n−3}(Δ(ÔP(P)); C).

This replaces the original target eq. (restrictionlemma), which is false for
every J (literature note §3.3, Prop. C).

Every claim below is tagged PROVEN, COMPUTED, CITED or CONJECTURED.

## Summary

1. **Conjecture S holds for every finite poset P (PROVEN, §5, given the
   CITED inputs of §1).** More precisely, fix any connected component P_1 of
   P. Let B_P be the set of linear extensions whose *first block* contains
   P_1 (§3). Then {ρ_w : w ∈ B_P} is a basis of H_P, and |B_P| = e_C(P).
2. **The algebraic core (PROVEN, elementary, §4).** B_P is linearly
   independent modulo the span Sh_n of proper shuffles. In particular, for
   connected P, **no nonzero linear combination of linear extensions of P is
   a sum of proper shuffles.** This is exactly the connected-case statement
   requested in the ticket.
3. **The relations (PROVEN, §5).** W_P ∩ Sh_n = R_P, where W_P = C{Lin P}
   and R_P is spanned by the shuffle sets s ш t, with s, t linear extensions
   of complementary unions of components. Also dim(W_P ∩ Sh_n) =
   |Lin P| − e_C(P). As Aut(P)-modules, H_P ⊗ sgn ≅ C[Lin P]/R_P.
4. **The main conjecture eq. (mainconj) for connected P (PROVEN, §6).** It
   follows as in the literature note's (S2). This proof is independent of the
   character-identity proof in `notes/global_module_operations_plethlog.md`.
5. **The key tool** is the contraction operator E_{a,x}, which deletes x
   when it is adjacent to a, with a sign recording the side. It maps
   shuffles to shuffles (Lemma 1), because it is the adjoint of the Lie
   substitution a ↦ [x, a]. Induction along such contractions, followed by
   "adjacent swaps connect Lin P", proves everything.
6. **COMPUTED (§8).**
   - Every statement in items 2–3 holds for all 2045 unlabeled posets with
     n ≤ 7.
   - Lemma 1 holds for n ≤ 7.
   - The chain-level independence of {ρ_w : w ∈ B_P} holds for n ≤ 5.
     This check does not go through Prop. Φ.

The sphere-by-sphere caution in the ticket is moot. No Fourier projection
appears anywhere: the cyclic structure enters only through the count
|B_P| = e_C(P).

## 1. Setup and inputs

Notation:
- Words are on a finite alphabet A with |A| = n and have distinct letters.
  C[S_A] denotes the span of the n! words on A.
- Sh_A ⊂ C[S_A] is the span of the proper shuffles u ш v, where u and v are
  nonempty words with complementary letter sets.
- For a poset P on A:
  - W_P = C{Lin P};
  - K_P = W_P ∩ Sh_A;
  - R_P = span{s ш t : s ∈ Lin(P|_S), t ∈ Lin(P|_{A∖S}), S a nonempty proper
    union of connected components}.
- Every word of such an s ш t is a linear extension of P, so R_P ⊆ K_P.

Inputs:
- **(Φ) CITED / PROVEN in the literature note §3.2** (from Wachs 1998,
  Lemma 3.1 and Thms 4.2–4.3, and Ree's theorem; COMPUTED there for n ≤ 5).
  Σ_σ a_σ ρ_σ = 0 in H̃_{n−3}(Π̄_n) iff Σ_σ a_σ sgn(σ) σ ∈ Sh_n. The map is
  S_n-equivariant after the sign twist.
- **(D) PROVEN in the literature note §3.4 (Lemma D).** ρ_w ∈ H_P for every
  w ∈ Lin P.
- **(JS) CITED.** dim H_P = e_C(P), the number of cyclic classes (Jenča–
  Sarkoci, arXiv:1112.5782v2, Thm 4.5). A cyclic class of w is the set of
  rotations of w that lie in Lin P (literature note §2.2).
- **(Ree) CITED.** Lie_A^⊥ = Sh_A for the form ⟨u, v⟩ = δ_{uv}
  (Reutenauer, *Free Lie Algebras*, Thm 3.1). This is used only in the
  second proof of Lemma 1 and in Corollary 5.4.

§2–§5.2 use none of these inputs. They are elementary combinatorics of
words.

## 2. The contraction operator

**Definition.** Let a ≠ x be letters of A. Define the linear map
E_{a,x} : C[S_A] → C[S_{A∖x}] on words w by
- E_{a,x}(w) = +(w∖x) if x immediately precedes a in w;
- E_{a,x}(w) = −(w∖x) if x immediately follows a in w;
- E_{a,x}(w) = 0 otherwise.

Here w∖x deletes the letter x.

**Lemma 1 (PROVEN; COMPUTED n ≤ 7).** E_{a,x}(Sh_A) ⊆ Sh_{A∖x}. More
precisely, let u, v be nonempty words with complementary letter sets. Then:
- E_{a,x}(u ш v) = (u∖x) ш v if "xa" is a factor of u;
- E_{a,x}(u ш v) = −(u∖x) ш v if "ax" is a factor of u;
- the same two rules hold with u and v exchanged;
- E_{a,x}(u ш v) = 0 in all other cases.

*Proof.* Shuffles of words with distinct letters have no multiplicities.

*Case 1: a and x lie in the same factor, say u.*
- If they are not adjacent in u, some letter of u lies between them in every
  word of u ш v. So no term has them adjacent, and the image is 0.
- If u = u_1 x a u_2, delete x from the terms in which no letter of v sits
  between x and a. This is a bijection from those terms onto (u∖x) ш v. Its
  inverse inserts x just before a. Every such term contributes with sign +.
  The case "ax" is the same with sign −.
- (u∖x) ш v is a proper shuffle, since u∖x ∋ a.

*Case 2: x ∈ u and a ∈ v.* Write u = u_1 x u_2 and v = v_1 a v_2.
- In a term …xa…, the letters before x are exactly u_1 ∪ v_1. So the term
  is p x a q with p ∈ u_1 ш v_1 and q ∈ u_2 ш v_2, and every such pair (p, q)
  occurs.
- The same holds for the terms p a x q.
- Deleting x sends both families onto {p a q}, with opposite signs, so they
  cancel.
- The case a ∈ u, x ∈ v is symmetric. ∎

*Second proof, via (Ree).* Take the form ⟨w, w′⟩ = δ_{ww′}. The adjoint of
E_{a,x} is the linear map w′ ↦ w′[a→xa] − w′[a→ax], i.e. the substitution
a ↦ [x, a] applied to multilinear words. A substitution of a Lie element for
a letter is a Lie algebra morphism of free Lie algebras, so the adjoint maps
Lie_{A∖x} into Lie_A. Dualizing with (Ree), E_{a,x} maps Lie_A^⊥ = Sh_A into
Lie_{A∖x}^⊥ = Sh_{A∖x}. ∎ (The adjointness is COMPUTED as a unit test,
`test_E_is_adjoint_of_substitution`.)

## 3. Quotients, swaps and blocks

Let P be a poset on A, and suppose a, x are adjacent in some w ∈ Lin P.

**Lemma 2 (PROVEN).**
- (a) The quotient Q = P/{a, x} is a poset. Its ground set is A∖x, with a
  standing for the block {a, x}, and its order is the transitive closure of
  the images of the relations of P. For every w ∈ Lin P in which a and x
  are adjacent, w∖x ∈ Lin Q.
- (b) Let w′ ∈ Lin Q. Then w′[a→xa] ∈ Lin P unless a <_P x, and
  w′[a→ax] ∈ Lin P unless x <_P a.
- (c) The components of Q are the images of the components of P. The
  components of a and x are merged if they differ.
- (d) If P is connected, so is Q.

*Proof.*
- (a) w∖x respects the image of every relation of P. The only nontrivial
  case is a relation involving x, say y <_P x with y ≠ a. Then y precedes x
  in w, and since a and x are adjacent and y ≠ a, y also precedes a. The
  case x <_P z is symmetric. A linear order respecting all generating
  relations shows that their transitive closure is acyclic, and that w∖x is
  a linear extension of Q.
- (b) Let w′ ∈ Lin Q and expand a to xa or ax. A relation y <_P z with
  y, z ∉ {a, x} holds in Q, so it is respected. A relation y <_P x or
  y <_P a with y ∉ {a, x} gives y <_Q a, so y precedes the whole pair. The
  case x <_P z or a <_P z is the same. Only the relation between a and x
  remains, and it forbids exactly the stated order.
- (c), (d) Immediate, since the quotient map is surjective and identifies
  only a with x. ∎

For X = Σ_{w ∈ Lin P} c_w w, extend c by zero to all words. Lemma 2 then gives

    E_{a,x}(X) = Σ_{w′ ∈ Lin Q} ( c(w′[a→xa]) − c(w′[a→ax]) ) · w′ .      (★)

**Lemma 3 (PROVEN; classical).** Any two linear extensions of P are joined
by a sequence of swaps of adjacent incomparable letters, with every
intermediate word in Lin P.

*Proof.* Let w, w′ ∈ Lin P and y = w′_1, a minimal element. The letters
preceding y in w are neither above y (since w ∈ Lin P) nor below it (since y
is minimal). So y can be moved to the front by swaps of adjacent incomparable
letters. Each intermediate word is in Lin P, because only y moves and it
passes incomparable letters. Now induct on P∖y. ∎

**Blocks.** For a word w ∈ Lin P, call a prefix of w a *union-prefix* if its
letter set is a union of connected components of P. The union-prefixes are
nested. The *blocks* of w are the segments between consecutive union-prefixes,
w = b_1 b_2 ⋯ b_m. Fix a component P_1, the *base component*. Call w *good*
if b_1 ⊇ P_1, i.e. if the first block contains P_1, and let
B_P = B_{P,P_1} be the set of good words. If P is connected, then
B_P = Lin P. If P is an antichain and P_1 = {a}, then B_P is the set of words
beginning with a, i.e. the Lyndon words for an order with a least.

**Lemma 4 (PROVEN).** |B_P| = e_C(P).

*Proof.*
- A rotation w_{j+1}⋯w_n w_1⋯w_j of w ∈ Lin P lies in Lin P iff
  w_1⋯w_j is a union-prefix.
  - If the prefix is a union of components, no relation joins it to the
    rest.
  - Conversely, a comparable pair y < z with y in the prefix and z outside
    is in the correct order in w and reversed in the rotation.
- So the cyclic class of w consists of the rotations of the block sequence
  (b_1, …, b_m).
- These rotations have the same blocks. A proper prefix of a block that is a
  union of components would itself be a union-prefix of w.
- Exactly one block contains P_1, so exactly one rotation in each class is
  good. ∎

**Lemma 5 (PROVEN).** Let a, x be adjacent in some linear extension, and let
Q = P/{a, x}, with base component Q_1 the component containing the image of
P_1. If w ∈ B_P and a, x are adjacent in w, then w∖x ∈ B_Q.

*Proof.* A union-prefix of w∖x for Q pulls back to a prefix of w that does
not separate a and x. Its letter set is a union of P-components, because
Q-components pull back to unions of P-components (Lemma 2(c)). In
particular, the first block of w∖x pulls back to a nonempty union-prefix of
w. Every nonempty union-prefix of w contains b_1 ⊇ P_1. ∎

## 4. Independence

**Theorem A (PROVEN).** For every finite poset P and every choice of base
component, B_P is linearly independent modulo Sh_A.

*Proof.* Induction on n = |A|.
- For n = 1, Sh_A = 0.
- Let n ≥ 2, and let X = Σ_{w ∈ B_P} c_w w ∈ Sh_A. Extend c by zero to all
  words. Let w ∈ Lin P have adjacent letters y, z in positions i, i+1.
  Put a = z and x = y, and Q = P/{a, x} (Lemma 2(a)).
  - By Lemma 1, E_{a,x}(X) ∈ Sh_{A∖x}.
  - By (★) and Lemma 5, E_{a,x}(X) is supported on B_Q: a coefficient at
    w′ ∉ B_Q only involves words not in B_P, where c = 0.
  - The induction hypothesis for Q (with n − 1 letters) gives
    E_{a,x}(X) = 0.
- Read off the coefficient of w∖x in (★):
  - if y ∥ z, then c(w) = c(w with y, z swapped);
  - if y <_P z, then the swapped word is not in Lin P (Lemma 2(b)), so its
    coefficient is 0 and c(w) = 0.
- By Lemma 3, c is constant on Lin P. It remains to find one word where
  c vanishes.
  - If P has k ≥ 2 components, choose a component P_2 ≠ P_1. Then the word
    "a linear extension of P_2, followed by one of P∖P_2" lies in Lin P but
    not in B_P: its first block is P_2, since no proper nonempty subset of
    the connected set P_2 is a union of components. So c = 0 there.
  - If P is connected with n ≥ 2, it has a cover relation p ⋖ q. List
    ↓q∖{q} with p last (p is maximal there), then q, then the rest. This
    gives w ∈ Lin P with p immediately before q, so c(w) = 0.
- Hence c ≡ 0. ∎

**Corollary A′ (PROVEN). For connected P, the linear extensions of P are
linearly independent modulo proper shuffles:**
W_P ∩ Sh_n = 0.

*Remarks.*
- For the antichain, Theorem A is the independence of the Lyndon words
  (words beginning with a fixed letter) modulo shuffles. The proof above is
  a short self-contained proof of that classical fact, by induction through
  E. This answers the ticket's "Lyndon triangularity" route. The right
  extension of "w_1 = a" is "the first block contains P_1", not an adapted
  alphabet order.
- Compared with the suggested J–S route, E contracts an *ordinarily*
  adjacent pair and uses both orders, xa and ax. The cyclic successor of
  J–S never appears. Cyclicity enters only through Lemma 4.
- Heuristically, E_{a,x} should be the Φ-image of taking the link of a top
  cycle at the atom π_{a,x} (literature note §3.5). The signs of that
  correspondence were not checked. The proofs here do not use it.

## 5. The relations, and Conjecture S

**Lemma 6 (PROVEN). W_P = span(B_P) + R_P.**

*Proof.*
- For z ∈ Lin P, let μ(z) be the length of the longest union-prefix of z not
  containing P_1. Then μ(z) = 0 iff z is good.
- Let w ∉ B_P have blocks b_1⋯b_m, with P_1 ⊆ b_j and j ≥ 2. Put
  s = b_1⋯b_{j−1} and t = b_j⋯b_m. Then s and t are linear extensions of
  complementary nonempty unions of components, so s ш t ∈ R_P. It contains
  w = st, and μ(w) = |s|.
- Let z ∈ s ш t with z ≠ w, and let π be a union-prefix of z not
  containing P_1.
  - π ∩ (letters of t) is a union-prefix of t. Every nonempty union-prefix
    of t contains b_j ⊇ P_1, because union-prefixes of t extend s to
    union-prefixes of w, i.e. to block boundaries. So π ∩ t = ∅.
  - Hence π is a prefix of s. If |π| = |s|, then z begins with s, so
    z = st = w.
  - Therefore μ(z) < μ(w).
- Induction on μ shows every w ∈ Lin P is congruent modulo R_P to a
  combination of good words. ∎

**Theorem B (PROVEN).**
- W_P = span(B_P) ⊕ R_P.
- K_P = W_P ∩ Sh_A = R_P.
- dim K_P = |Lin P| − e_C(P).

*Proof.*
- Let X ∈ K_P. By Lemma 6, X = b + r with b ∈ span B_P and r ∈ R_P ⊆ Sh.
  Then b ∈ Sh ∩ span B_P = 0 by Theorem A. So K_P ⊆ R_P, and R_P ⊆ K_P is
  clear.
- Directness of the sum follows from the same argument.
- The dimension follows from Lemma 4. ∎

**Theorem C (Conjecture S; PROVEN given (Φ), (D), (JS)).**
- For every finite poset P with n ≥ 3 and every base component,
  {ρ_w : w ∈ B_P} is a basis of H_P. In particular
  span{ρ_w : w ∈ Lin P} = H_P.
- The relations among the ρ_w, w ∈ Lin P, are exactly
  Σ a_w ρ_w = 0 ⇔ Σ a_w sgn(w) w ∈ R_P.

*Proof.*
- If Σ_{w ∈ B_P} a_w ρ_w = 0, then Σ a_w sgn(w) w ∈ Sh_n by (Φ), so a = 0 by
  Theorem A.
- These e_C(P) cycles (Lemma 4) lie in H_P by (D), and dim H_P = e_C(P) by
  (JS).
- The kernel statement is (Φ) combined with Theorem B. ∎

*Remark.* Without (JS), §4–§5 together with (Φ) and (D) give
dim H_P ≥ e_C(P). That is the lower half of Jenča–Sarkoci Thm 4.5, without
the discrete Morse matching. The upper bound still comes from (JS).

**Corollary 5.4 (PROVEN given (Ree)).** Restricting coefficients to Lin P
maps Lie_n onto R_P^⊥ ⊆ C^{Lin P}, a space of dimension e_C(P). For
connected P the map is onto C^{Lin P}: every function on the linear
extensions of a connected poset is the coefficient function, on Lin P, of
some Lie element. This is Theorem B dualized with Lie_n = Sh_n^⊥.

**Corollary 5.5 (PROVEN given (Φ), (D), (JS)).** As Aut(P)-modules,
H_P ⊗ sgn ≅ C[Lin P] / R_P, via ρ_w ⊗ 1 ↦ sgn(w) w.
- Aut(P) permutes Lin P by relabelling and preserves R_P.
- Equivariance is that of (Φ).

## 6. Consequences for the main conjecture

- **Connected P (PROVEN given (Φ), (D), (JS)).** By Theorem C, {ρ_w :
  w ∈ Lin P} is a basis of H_P. It is permuted by Aut(P) (g ρ_w = ρ_{gw}),
  and freely, since gw = w forces g = 1.
  - So H_P is a free C[Aut P]-module of rank |Lin P|/|Aut P|.
  - So is Lie(P) = span{w e_ζ}, whose basis {w e_ζ : w ∈ Lin P} is permuted
    freely.
  - A free module twisted by sgn is free of the same rank.
  - Hence **eq. (mainconj) holds for every connected P**, as in the
    literature note's (S2), with Conjecture S now proved.
- **General P.** Corollary 5.5 gives the explicit model
  H_P ⊗ sgn ≅ C[Lin P]/R_P. The abstract isomorphism with Lie(P) =
  C[Lin P]/(W_P ∩ K_ζ) (literature note (S3)) is the content of the
  character identity proved in `notes/global_module_operations_plethlog.md`
  (mg-266cf). That proof is not re-audited here.
  - **Not done here:** a natural or explicit isomorphism
    C[Lin P]/R_P ≅ C[Lin P]/(W_P ∩ K_ζ) ⊗ sgn for disconnected P.
  - Prop. C of the literature note shows it cannot be induced by a uniform
    map on C[S_n].

## 7. Novelty

Theorem A, Theorem B and Corollary 5.4 were not found in the sources listed
in the literature note §1. The proofs use only Lemma 1 (the transpose of a
Lie substitution) and elementary word combinatorics, so a specialist may well
know them in some form (e.g. P-partition / Malvenuto–Reutenauer folklore).
This is not a proof of novelty. Recommended expert questions are as in the
literature note §1.3.

## 8. Computations (COMPUTED)

Code: `compute/conjecture_s.py` (plain Python 3). It reuses
`poset_jks_check.py` (posets, linear extensions, cyclic classes) and
`splitting_cycles.py` (shuffles, ρ_w, rank mod p).

How Sh-membership is tested: let a be the least letter and set
L_a(u a v) = (−1)^{|u|} rev(u) ш v. The coefficient of τ in L_a(w) is the
coefficient of w in the left comb [⋯[[a, τ_1], τ_2], …]. These combs form a
basis of Lie_n, so ker L_a = Sh_n by (Ree). Check [La] below confirms this
directly for n ≤ 7.

Commands, run from `compute/`:

    python3 conjecture_s.py --nmax 6 --ne 6 --nrho 5 > output/conjecture_s.txt   # ~3 s
    python3 conjecture_s.py --nmax 7 --ne 7                                       # ~90 s
    python3 -m unittest test_conjecture_s

Both commands end with `ALL CHECKS PASSED` (exit 0). The n = 7 run is not
archived. Its `[S]` line reads:

    [S]  n=7: 2045 posets (1650 connected): rank(Lin P mod Sh) = e_C: 2045/2045;
         K_P = R_P: 2045/2045; connected K_P = 0: 1650/1650; [B] first-block basis: 2045/2045: True

What is checked:
- **[E]** Lemma 1's exact formula, for every proper shuffle and every
  ordered pair (a, x), n ≤ 7. At n = 7 that is 1 270 080 cases.
- **[La]** rank L_a = (n−1)!, and L_a kills every proper shuffle, n ≤ 7.
- **[S]** For every unlabeled poset with n ≤ 7 (1, 2, 5, 16, 63, 318, 2045
  of them for n = 1..7; the check starts at n = 2):
  - rank(Lin P mod Sh) = e_C(P) (Conjecture S via (Φ));
  - dim R_P = dim K_P;
  - K_P = 0 for connected P;
  - **[B]** |B_P| = e_C(P), and B_P is independent mod Sh, with base
    component the component of the letter 0.
- **[rho]** Chain level, without (Φ): for every poset with n ≤ 5,
  {ρ_w : w ∈ B_P} are linearly independent chains, and there are e_C(P) of
  them.

Rigour of the ranks:
- Ranks are taken modulo p = 1 000 000 021, and rank_p ≤ rank_Q.
- "B independent" and "ρ independent" are conclusions of the form
  rank_p = |B|, so they hold over Q.
- For K_P = R_P:
  dim_p R ≤ dim_Q R ≤ dim_Q K ≤ |Lin P| − rank_p, and the script checks that
  the two ends are equal.

Positive controls (`test_conjecture_s.py`):
- a sign-flipped version of Lemma 1's formula is rejected;
- a disconnected poset (two 2-chains) has K_P ≠ 0;
- the full Lin P of the 3-antichain is dependent mod Sh while its B_P is
  not;
- a good word that does not begin with a P_1-letter (2031 for 0<1, 2<3) is
  classified correctly.
