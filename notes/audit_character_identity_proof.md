# Audit of the two proofs of the character identity

Work item: mg-7219c. This is an independent adversarial audit of:
- **Proof I:** §2 of `notes/global_module_operations_plethlog.md`
  (mg-266cf), Theorem 2.8;
- **Proof II:** `notes/fixed_point_mobius_identity.md` (mg-8878d).

Both prove eq. (characterconj) of `notes/poset_jks_research_note.tex` for
every finite poset, and from it eq. (mainconj).

## Verdicts

- **Shared steps: HOLD.** The Lie-side count, the Hopf/Lefschetz step
  eq. (homchar), the use of Jenča–Sarkoci, and the sign and ζ-conventions
  were each re-derived here, and each is correct.
- **Proof I (Weisner + Möbius inversion on X(P,g)): PROOF HOLDS.**
- **Proof II (Crapo complementation at a one-orbit merge): PROOF HOLDS.**
  Crapo's theorem is cited, not proved. Its only hypothesis, that L^g is a
  finite lattice, is satisfied.

**What is proved.** Assume Jenča–Sarkoci Thm 4.5, P. Hall's theorem and the
Hopf trace formula; Proof II also assumes Crapo's complementation theorem.
Then for every finite poset P with n ≥ 3 and every g ∈ Aut(P),
eq. (characterconj) holds. As a consequence there is an **abstract**
isomorphism of Aut(P)-modules H_P ≅ sgn ⊗ Lie(P). The closed formula is
also proved:

    sgn(g)(−1)^{n−3} μ(OP(P)^g) = μ(o) Σ_{x ∈ F(P,g)} e_C(P|_{B_0(x)}).

Neither proof gives a natural or explicit isomorphism, and neither claims
to. See §5.

No error was found. Two expository slips are noted below; neither affects
the logic.

Every claim in this file is tagged PROVEN (re-derived here), COMPUTED
(script and command given), CITED, or UNCHECKED.

## 0. Reproduce

The script is `compute/audit_character_identity.py`. It is self-contained:
it imports neither `poset_lie_structure.py`, nor `fixed_point_mobius.py`,
nor `poset_jks_check.py`. Run from `compute/`:

    python3 audit_character_identity.py --nmax 6 --large 7 8 9 --homology 6 > output/audit_character_identity.txt

The script exits 0 iff every check passes.

Positive controls: each command below runs a deliberately wrong variant and
must exit 1.

    for c in no_mu_o no_sgn trace_sign no_mu_X crapo_drop lin_not_ec; do
      python3 audit_character_identity.py --nmax 5 --large --homology 5 --control $c; done

All six failed as required (COMPUTED). The variants are:
- no_mu_o: drop μ(o) from the closed formula (6 failures);
- no_sgn: drop sgn(g) from (characterconj) (1);
- trace_sign: flip the sign in (homchar) (4);
- no_mu_X: replace μ_X(x, 1̂) by 1 in Proof I's inversion (6);
- crapo_drop: drop the diagonal terms of Crapo's sum (5);
- lin_not_ec: use |Lin| in place of e_C (58).

**Main run (COMPUTED; the archived output is `compute/output/audit_character_identity.txt`):**

    posets checked: 424    (all 405 unlabeled posets with n <= 6, plus 19 families at n = 7, 8, 9)
      A: 1056  B: 1056  B_nonzero: 447  C: 632  D: 632  E: 632
      E_unequal: 593  E_nonempty: 20  F: 39  H: 402  H_trace: 543
    failures: 0
    ALL CHECKS PASS                       (single core, ~5 min)

Plus one family at n = 10, checked for every non-identity class
(`--nmax 0 --large 10 --skip-identity-large`, ~5 min, archived in
`compute/output/audit_character_identity_n10.txt`). It has 9 pairs and
0 failures.

What the letters check. Each is computed from the definitions, never from
either proof. One representative is taken per conjugacy class of Aut(P).
- **A**: eq. (characterconj), as exact integers. The Lie side is evaluated
  from the counts N_r of g-fixed classes with rotation r. The script first
  checks that N_r depends only on gcd(n, r), then sums Ramanujan sums.
- **B**: the closed formula, with F(P,g) found by enumerating all
  partitions of the set of components.
- **C**: Proof I, Lemma 2.2. O_g ∈ L^g. The join computed as a least upper
  bound *inside L^g* equals the partition join, for every x ∈ L^g, not only
  for x ∈ X. And {x : x ∨ O_g = 1̂} = X(P,g).
- **D**: Proof I, Prop. 2.5. The poset X(P,g) is built and μ_X(x, 1̂) is
  computed on it. It equals μ(o) wherever h_x = 1, and h_x = 1 forces
  m = o. For every x ∈ X, μ_{L^g}(0̂, x) is compared with μ(OP(P|B_0)^h)
  computed on the restricted poset, and the sign identity 2.4(ii) is
  checked. Finally Σ_x μ_X(x,1̂) F(x) is compared with M̃(P,g).
- **E**: Proof II. z merges one longest orbit, and z^⊥ is found by searching
  L^g with L^g-joins and meets. Crapo's double sum is compared with μ(L^g).
  If the cycle lengths are unequal, the check is z^⊥ = ∅. Otherwise the
  checks are that z^⊥ is an antichain and z^⊥ = {y_T : T ∈ 𝒯}.
- **F**: Proof II, Prop. 6: N_r = Σ_T e_C(T) if gcd(n, r) = k, and 0
  otherwise.
- **H**: an independent test of the shared Hopf step. For every poset with
  3 ≤ n ≤ 6, the script builds the order complex of the proper part of
  OP(P) and computes every boundary rank mod p = 2^31 − 1. Mod-p Betti
  numbers are ≥ the rational ones. They come out as e_C(P) in degree n − 3
  and 0 elsewhere, which also confirms J–S Thm 4.5 for n ≤ 6. **H_trace**
  then computes the trace of each class representative g on ker ∂_{n−3}
  and compares it with (−1)^{n−3} μ(OP(P)^g).

**Disconnected families at n ≥ 7 where g permutes components.** These are
chosen to differ from the authors' lists. The table shows every non-identity
class with a nonzero value; every other non-identity class gives 0 on both
sides, and all of those were checked too (COMPUTED):

| P | n | type of g | μ(L^g) | χ_{H_P}(g) | sgn(g)·χ = μ(o)Σ e_C |
|---|---|---|---|---|---|
| 4 × 2-chain | 8 | 2^4 | 10 | −10 | −10 |
| 2 × 4-chain | 8 | 2^4 | 1 | −1 | −1 |
| 2 × 3-chain + 2 points | 8 | 2^4 | 6 | −6 | −6 |
| 2 × V + 2 points | 8 | 2^4 | 12 | −12 | −12 |
| 2 × N | 8 | 2^4 | 5 | −5 | −5 |
| 2 × K_{2,2} | 8 | 2^4 | 4 | −4 | −4 |
| 2 × Y (4 elements) | 8 | 2^4 | 2 | −2 | −2 |
| 3 × 3-chain | 9 | 3^3 | −1 | −1 | −1 |
| 3 × V | 9 | 3^3 | −2 | −2 | −2 |
| 3 × Λ | 9 | 3^3 | −2 | −2 | −2 |
| 2 × 2-chain + 2 × V | 10 | 2^5 | −36 | 36 | −36 |

The zero cases cover the following situations:
- g with unequal cycle lengths (593 pairs in total);
- uniform cycle type where ⟨g⟩ is not free on the components, e.g.
  2 × K_{2,2} with g swapping the copies and twisting one of them, which
  gives type 4^2 with component orbits of size 2, and with g flipping both
  copies in place, which gives type 2^4 with every component fixed;
- mixed orbits of different sizes, e.g. 3 × 2-chain + 2 points with g of
  order 6.


## 1. Claim table

Status words: CONFIRMED (re-derived here, and checked by computation where
the table says so), BROKEN, OVERSTATED, UNCHECKED.

### 1.1 Shared steps (a flaw here would sink both proofs)

| # | Claim | Status | Reason |
|---|---|---|---|
| S1 | eq. (liechar): χ_{Lie(P)}(g) = Σ_{gC=C} ζ^{r_g(C)}, with (gw)_i = g(w_i), (wγ^r)_i = w_{i+r}, and gC = C with rotation r iff gw = wγ^r | CONFIRMED | γ e_ζ = ζ e_ζ, since γ·Σ_j ζ^{−j}γ^j = ζ Σ_j ζ^{−(j+1)}γ^{j+1}. So gw = wγ^r gives g·we_ζ = ζ^r we_ζ. The vectors w_C e_ζ, one per class, are a basis: their supports are disjoint right cosets wC_n. A non-fixed class contributes 0 to the trace. r_g(C) does not depend on the representative: for w' = wγ^j, gw' = w'γ^r. Both proofs use exactly this convention, which is the seed note's and that of `reproduce_character_identity_n_le_5.md` (F0). |
| S2 | ζ-convention does not matter | CONFIRMED | Both proofs reduce the Lie side to Σ_{s ∈ (Z/d)^×} (ζ^k)^s = μ(d), a Ramanujan sum. It is the same for every primitive ζ and for r ↦ −r. Check A evaluates the Lie side the same way, but only after checking that N_r is constant on gcd classes, so the evaluation is legitimate. |
| S3 | Rotation r forces uniform cycle type d^k with k = gcd(n, r) | CONFIRMED | g(w_i) = w_{i+r}, so the cycles of g are the orbits of i ↦ i + r on Z/n. All have size n/gcd(n, r). |
| S4 | Lie side: N_r = Σ_{T∈𝒯} e_C(T) if gcd(n, r) = k, else 0 (II Prop. 6). Equivalently Σ ζ^r = μ(o) Σ_{x∈F} e_C (I Prop. 2.7) | CONFIRMED | Re-derived both versions. (a) The cut set K(w) is invariant under +r (g preserves Lin, and g(wγ^j) = wγ^{j+r}), hence under ⟨r⟩ = kZ/nZ. (b) A rotation is a linear extension iff its prefix is a union of components (II Lemma 6a; both directions checked). (c) So w = u·hu·⋯·h^{d−1}u with h = g^{s^{−1} mod d}, and h(w_i) = w_{i+k}. (d) The map (C, w) ↦ (T, u) is a bijection X → Y with matching weights d/|K(w)| = 1/|[u] ∩ Lin T|, because cuts of u = K(w) ∩ [0, k) and K(w) is k-periodic. (e) \|𝒯*\| = d\|𝒯\|. In Proof I, the pairs (C, x) correspond bijectively to triples (x, u, q): the arc carrying g^j B_0 has word g^j u, because g is a rotation on positions. Each C has \|Cut C\|/o compatible x, since Cut is a union of ⟨k⟩-cosets of size o. The weights match the same way. COMPUTED: check F (39 classes) and check A (all 1056 pairs). |
| S5 | eq. (homchar): χ_{H_P}(g) = (−1)^{n−3} μ(OP(P)^g) | CONFIRMED | (a) g fixes a simplex (a chain) setwise only if it fixes it pointwise, since an order automorphism of a finite chain is the identity. So the trace on oriented i-chains counts the g-fixed i-chains, and these are the i-chains of the proper part of L^g (0̂, 1̂ ∈ L^g). (b) Hopf trace on the augmented complex gives χ̃(Δ(proper part of L^g)) = μ_{L^g}(0̂,1̂) by Hall. (c) H̃ is concentrated in degree n − 3 by J–S Thm 4.5. COMPUTED independently by direct homology (check H): Betti numbers, and the trace on ker ∂_{n−3}, for 543 (P, g) with 3 ≤ n ≤ 6. |
| S6 | J–S Thm 4.5: for n ≥ 3, Δ(proper part of OP(P)) ≃ ⋁^{e_C(P)} S^{n−3} | CITED, consistent | The arXiv:1112.5782v2 abstract was re-read for this audit: "wedge of spheres of dimension n−3", with the number of spheres equal to the number of cyclic extensions. Their order congruences are the partitions with acyclic quotient; this identification is taken from the literature note §2.1–2.2 and not re-read in the paper (UNCHECKED here). COMPUTED: check H confirms the homological consequence (reduced homology over Q is e_C(P)-dimensional and concentrated in degree n − 3; not the homotopy type), for the acyclic-quotient definition, for all 402 posets with 3 ≤ n ≤ 6. That is all the proofs use. |
| S7 | Where J–S enters | CONFIRMED | In both proofs it is used only as μ(OP(Q)) = (−1)^{\|Q\|−1} e_C(Q). Proof I applies it to Q = P\|_{B_0(x)} for x ∈ F; Proof II applies it to Q = T ∈ 𝒯. These are posets with fewer elements and *trivial* automorphism. It is also used at g = 1, and in S5. For \|Q\| = 1, 2 the value comes from hand computation, not J–S. Hand check: OP of a point has one element and μ = 1; OP of a 2-chain or a 2-antichain is {0̂, 1̂}, so μ = −1 and e_C = 1. Proof II states this explicitly. Proof I leaves it to "T4 at n = 1, 2" (slip (a) below). |
| S8 | Sign bookkeeping | CONFIRMED | For type d^k, sgn(g) = (−1)^{(d−1)k} = (−1)^{n−k}, and (−1)^{n−3}(−1)^{k−1} = (−1)^{n−k}. Proof I, Lemma 2.4(ii): every g-cycle meets B_0 in exactly one h-cycle and is m times as long, so g and h have the same number c of cycles. Both sides then equal (−1)^{c+1}. COMPUTED (check D, every x ∈ X). |

### 1.2 Proof I (mg-266cf §2): the steps specific to it

| # | Claim | Status | Reason |
|---|---|---|---|
| I1 | Lemma 2.1: the orbit quotient of a poset by a finite group is acyclic | CONFIRMED | The lift of a cycle gives a_1 < k a_1 < k² a_1 < ⋯ < k^{\|K\|} a_1 = a_1. |
| I2 | Lemma 2.2(i)–(ii): the meet in L is the partition meet; L, L^g are lattices; O_g ∈ L^g | CONFIRMED | A cycle of P/(x∧y) maps to a closed walk in P/x. The walk cannot cross x-blocks, or P/x would have a cycle; likewise for y. So the cycle lies in one x∧y block. L^g is closed under the L-meet and the L-join, since g is a lattice automorphism. COMPUTED (C). |
| I3 | Lemma 2.2(iii): the L^g-join of x and O_g is the partition join | CONFIRMED | The partition join of x and O_g has as blocks the ⟨g⟩-orbits of x-blocks: starting from one x-block B and adding orbits of points gives ∪_j g^j B, a union of x-blocks. Its quotient is the orbit quotient of the poset P/x, which is acyclic by I1. So the partition join lies in L^g, and every upper bound in L^g lies above it. Weisner is therefore applied with the correct join in L^g. COMPUTED (C), for every x ∈ L^g, with the L^g-join computed as a least upper bound inside L^g. |
| I4 | Lemma 2.2(iv): {x ∈ L^g : x ∨ O_g = 1̂} = X(P,g) | CONFIRMED | A group acting transitively on the poset P/x forces it to be an antichain, so each block is a union of components. The converse also holds. COMPUTED (C). |
| I5 | Lemma 2.3 (Weisner), applied in L^g with a = O_g ≠ 0̂ | CONFIRMED | The in-line proof is correct. It needs only a finite lattice and its own join, and I3 supplies the join. |
| I6 | Lemma 2.4(i): [0̂, x]_{L^g} ≅ OP(P\|_{B_0})^h with h = g^m\|_{B_0} | CONFIRMED | There are no relations between x-blocks, so [0̂, x]_L = Π_B OP(P\|_B). A g-fixed tuple is determined by its B_0 entry, which is g^m-fixed. Conversely σ extends to ∪_{j<m} g^j σ, which is consistent because g^m σ = σ. COMPUTED (D): the Möbius numbers agree for every x ∈ X(P,g), in 632 pairs. |
| I7 | The Möbius inversion identifies {z ∈ X(P,g) : z ≤ x} with X(P\|_{B_0(x)}, h_x), including the automorphism and the isomorphism type | CONFIRMED | The map is y ↦ {g^j D : D ∈ y, 0 ≤ j < m}. Its image is a partition into unions of components, g-invariant and g-transitive, and finer than x. Its inverse is z ↦ (z-blocks inside B_0). Transitivity of h on these blocks holds because the stabiliser of B_0 in ⟨g⟩ is ⟨g^m⟩. For the image z of y: m_z = m_x m_y, the block D ⊆ B_0 is a block of z, and h_z = g^{m_x m_y}\|_D = h_x^{m_y}\|_D. So the summand of (W) for (P\|_{B_0(x)}, h_x) at y equals f(z). |
| I8 | "Respects pairs up to isomorphism" suffices for f to be well defined | CONFIRMED | f(z) = M̃(P\|_B, g^{m}\|_B) depends on the choice of the z-block B only through the isomorphism class of the pair (poset, automorphism). For two blocks B and g^j B, the map g^j is an isomorphism of pairs: it conjugates g^m\|_B to g^m\|_{g^jB}. M̃ is an invariant of such isomorphism classes, because μ of the fixed lattice and sgn are. |
| I9 | Σ_{z≤x} f(z) = [h_x = 1] e_C(P\|_{B_0(x)}) | CONFIRMED | If h_x ≠ 1, this is (W) for (P\|_{B_0(x)}, h_x) via I7. (W) uses only I3–I6 and not J–S, and it is valid at any size ≥ 2. If h_x = 1, the only transitive partition is the one-block partition, so {z ≤ x} = {x}, and f(x) = M̃(Q, 1) = e_C(Q) by S7. |
| I10 | Contributing x: h_x = 1 ⟺ m = o; F(P,g) is empty unless ⟨g⟩ is free on components | CONFIRMED | The block action of ⟨g⟩ is an m-cycle, so m \| o. h_x = 1 forces g^m = 1 on all blocks, so o \| m. A component with nontrivial stabiliser g^j, 0 < j < o, would force g^j B_0 = B_0. COMPUTED (D: "h_x = 1 with m ≠ o" never occurs). |
| I11 | [x, 1̂]_X ≅ divisor lattice of o for x ∈ F, so μ_X(x, 1̂) = μ(o) | CONFIRMED | Coarsenings of x in X are the translation-invariant partitions of the regular Z/o-set of blocks. The block of 0 in such a partition is a subgroup. Transitivity is automatic. COMPUTED (D): μ_X(x, 1̂) on the poset X(P,g) equals μ(o). The control no_mu_X fails. |
| I12 | Theorem 2.8 for n ≤ 2 | CONFIRMED (trivial) | The note gives a computation; a hand check is immediate. Only n ≥ 3 matters for (mainconj). |

### 1.3 Proof II (mg-8878d): the steps specific to it

| # | Claim | Status | Reason |
|---|---|---|---|
| II1 | Crapo's complementation theorem (CITED: Crapo, J. Combin. Theory 1 (1966) 126–131) | CONFIRMED as used | Exact statement: let L be a finite lattice, z ∈ L, and z^⊥ = {y : y ∧ z = 0̂, y ∨ z = 1̂}. Then μ_L(0̂,1̂) = Σ_{x,y ∈ z^⊥, x ≤ y} μ_L(0̂,x) μ_L(y,1̂). The only hypothesis is that L is a finite lattice, with ∧ and ∨ the operations *of L*. L^g is a finite lattice (II Lemma 1, the same argument as I2). The theorem number was not checked against the paper (UNCHECKED, as the note itself says). COMPUTED (E): Crapo's sum, with z^⊥ found using the L^g operations, equals μ(L^g) in all 632 non-identity pairs. The control crapo_drop fails. |
| II2 | Lemma 2: orbits are antichains; merging an antichain A keeps the quotient acyclic | CONFIRMED | In a cycle of the quotient, a maximal strict run starts and ends in A. That gives a ≤ a′ in A with a strict step, which contradicts A being an antichain (a = a′ is impossible too, since P has no strict cycles). |
| II3 | Prop. 4: with unequal cycle lengths, the merge z of a longest orbit has no complement, so μ(L^g) = 0 | CONFIRMED | Let y be a complement. The D points of c lie in distinct y-blocks B_1, …, B_D, cyclically permuted, with g B_i = B_{i+1}. These blocks are an orbit of ḡ on the poset P/y, hence an antichain there. So the partition join y ∨_Π z, which merges B_1, …, B_D, is in L^g, and it is the L^g-join. Then y ∨ z = 1̂ forces y = {B_1, …, B_D}. A shorter cycle c′ of length ℓ, with a point x ∈ B_1, has g^ℓ x ∈ B_{1+ℓ}, so D \| ℓ, a contradiction. COMPUTED (E): z^⊥ = ∅ in all 593 unequal-length pairs, and μ = 0 there. Non-vacuity: the same search finds nonempty z^⊥ in 20 uniform pairs. |
| II4 | Prop. 5: for type d^k with k ≥ 2, z^⊥ = {y_T : T ∈ 𝒯}, and z^⊥ is an antichain | CONFIRMED | By II3, a complement has d blocks permuted cyclically, and its quotient is a single ḡ-orbit, hence an antichain, so every block is a union of components. Conversely y_T ∧ z = 0̂ because \|T ∩ c\| = 1, and the partition join of y_T and z is already 1̂. All elements of z^⊥ have exactly d blocks, so z^⊥ is an antichain, and Crapo's double sum collapses to its diagonal. COMPUTED (E). |
| II5 | Lemma 3: [0̂, y_T]_{L^g} ≅ OP(T) (no residual automorphism, since g^d = 1) and [y_T, 1̂]_{L^g} ≅ Π_d^{d-cycle} ≅ divisor lattice of d | CONFIRMED | Same argument as I6 and I11. COMPUTED (D and E use these intervals). |
| II6 | k = 1 case: L^g ≅ divisor lattice of d | CONFIRMED | P is a single orbit, hence an antichain. |
| II7 | Cor. 7: connected P and g ≠ 1 give μ(L^g) = 0 | CONFIRMED | 𝒯 = ∅. COMPUTED (A/B on all connected posets with n ≤ 6). |
| II8 | §6.2 rigid components: \|𝒯\| = d^{m/d−1}; for equal chains with σ an m-cycle, χ = (−1)^{(m−1)ℓ} μ(m) | CONFIRMED | Two independent instances in the table above: 2 × 4-chain gives −1 and 3 × 3-chain gives −1. |

### 1.4 What each note says about scope

| # | Claim | Status | Reason |
|---|---|---|---|
| R1 | (mainconj) holds for every finite P with n ≥ 3, as an abstract isomorphism of Aut(P)-modules | CONFIRMED, given J–S Thm 4.5, Hall, Hopf trace (and Crapo for Proof II) | Characters over C determine modules. |
| R2 | Either proof gives the "natural" isomorphism asked for in (mainconj) | Neither claims it | Both notes state that the isomorphism is abstract only. See §5. |
| R3 | Proof I §1(a): (globalind) PROVEN | Half CONFIRMED, half UNCHECKED | HH_n ≅ ⊕_{[P]} Ind_{Aut P}^{S_n} H_P and Ind(sgn ⊗ M) ≅ sgn ⊗ Ind M are standard, so HH_n ≅ sgn ⊗ V_n follows from R1. The other half, V_n ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]), is the earlier audit's §A. It is outside this audit (UNCHECKED here). |
| R4 | The two proofs corroborate each other | Partly | They share S1–S8 entirely. Two proofs give **no** extra confidence in those steps; that confidence comes from the re-derivation above and from checks A, F, H. They are genuinely independent only on the Möbius side (I1–I11 versus II1–II7), and both of those routes hold. |

## 2. Expository slips (no effect on validity)

- (a) Proof I, Prop. 2.5. The proof says "If g = 1 … Jenča–Sarkoci gives
  M̃(P,1) = e_C(P)". The recursion also uses this when |B_0(x)| ∈ {1, 2},
  and J–S says nothing there (Thm 4.5 is for n ≥ 3). The values are
  correct by the hand computation in S7. Proof I cites only a computer
  check ("T4 at n = 1, 2"), so the hand argument should be written in.
- (b) Proof I, Prop. 2.5, "Which x contribute". "Disjointness of g^j B_0
  for 0 < j < m forces m ≤ o" is true, but the cleaner reason is that the
  block action is a transitive cyclic action, so m | o. Combined with
  o | m this gives m = o either way.

## 3. Where the two proofs meet

Proof I's set F(P,g) is Proof II's {y_T : T ∈ 𝒯}: take the block that
contains c_0. Proof I's μ(o) is Proof II's μ(d), since a nonempty F forces
type o^{n/o}. So the closed formulas are the same formula. Proof I gets
there by a recursion that passes through every element of X(P,g). Proof II
uses only the antichain z^⊥. Check D confirms that Proof I's intermediate
quantities (μ on every [0̂, x] and μ_X(x, 1̂)) are what the proof says they
are, not only the final value.

## 4. Things looked for and not found

- **A join in L^g that differs from the partition join**, which would have
  invalidated Weisner. The L^g-join can differ from the Π_n-join in
  general. But for joins with O_g (Proof I), and with the one-orbit merge z
  against a complement (Proof II), the Π_n-join is already
  order-preserving and g-fixed. Check C tests every x ∈ L^g, not only
  x ∈ X.
- **A g whose cycle type is uniform but which fixes a component.** For
  example, 2 × K_{2,2} with the copies swapped and one twisted gives type
  4^2 with component orbits of size 2. Both proofs predict 0 (F = ∅,
  𝒯 = ∅). Computation gives 0 on both sides.
- **A sign or ζ-convention mismatch with eq. (liechar).** None (S1, S2).
  The no_sgn and trace_sign controls show that the checks are sensitive to
  such a mismatch.
- **Failure of the Hopf step through homology outside the top degree.**
  None for n ≤ 6 (check H). For n ≥ 7 this rests on J–S as cited.

## 5. Natural versus abstract isomorphism

Both proofs establish equality of characters. They therefore give an
isomorphism H_P ≅ sgn ⊗ Lie(P) of Aut(P)-modules that exists but is not
specified.

What can be said beyond that:
- (i) Choosing an isomorphism for one P in each S_n-orbit and transporting
  it by relabelling gives isomorphisms compatible with relabelling. This
  is why (globalind) follows (R3).
- (ii) Nothing more canonical follows, i.e. no isomorphism compatible with
  maps between different posets, nor one given by a formula. That would
  need an explicit equivariant map, for example a JKS-type map or the
  splitting-cycle map of the literature note's Conjecture S together with
  Φ (§3.4 there).
- (iii) The literature note's Prop. C (§3.3, not re-checked here) says that
  no single JKS map sends H_P to W_P e_ζ for every P. So a natural
  isomorphism, if one exists, must be built differently.

The character identity is the full content of "isomorphic as
Aut(P)-modules". It is silent on naturality.

