# Observation CC: every zero on a cone of the braid arrangement has a uniform witness

Observation CC (`notes/prior_art_cr_v_type_a.md` = "[PACVA]", §2.3) was
COMPUTED for n ≤ 7. Let P be a poset on [n], n ≥ 3, and let g = ετ ∈ ±S_n
with g C_P = C_P. Put M = OP(P)^τ (refinement order: 0̂ is the discrete
partition, 1̂ the one-block partition). Then

  χ_{C_P}(g) = 0  iff  (LOW) 0̂ ≠ ⋀ coatoms of M,  or  (HIGH) 1̂ ≠ ⋁ atoms of M.

Convention: if M = {0̂, 1̂}, its coatom is 0̂ and its atom is 1̂, so CC fails
there (and μ = −1).

**Answer: Observation CC holds for every finite poset (Theorem CC, PROVEN
below).** The coatom side LOW holds on every zero of rows W+1, W+2, W−1,
W−2 and W−3 of table W of `notes/cr_v_type_a.md` ("[CVA]"). The atom side
HIGH holds on every zero of row W−4. The proof gives an explicit lower bound
for ⋀ coatoms, namely the common refinement c ∧ D of two explicit
partitions, and an explicit upper bound for ⋁ atoms, the two-block partition
O | Q. Both are uncomplemented witnesses with a uniform description
(Corollary U). The case split that remains is between "c ∧ D ≠ 0̂" and row
W−4. It is not TA-CR's five-way list.

The proof does not use Theorem TA-CR. It uses:
- EC1 Cor. 3.9.5 (CITED) for "CC ⇒ μ = 0";
- the nonvanishing halves of the closed zero criteria (CITED, audited): for
  g = +w, [Thm, eq. closed]; for g = −τ, [PCV] Theorem TA;
- steps S1, S2, S4 and the averaging argument of S5 from [CVA] §1
  (PROVEN there, audited in [AudCVA]);
- two arguments from the proof of TA-CR, rows W−2 and W−3, restated in full
  here (Lemma T).

Tags:
- **PROVEN**: proof given here, with every input named. Not yet
  independently audited. The shared steps are numbered (CD, CK, A, P, Z+,
  Z−, T, B, B′, U) so that an audit can check them one by one.
- **COMPUTED**: by `compute/observation_cc.py` ("[OCC]"). It imports the
  enumeration and lattice code of `compute/cr_v_type_a.py` and, for the side
  question, the cone-lattice code of `compute/conjecture_cr_v.py`.
- **CITED**: from an audited note or the literature.
- **OPEN**.

## Verdict

| # | Claim | Status | Inputs |
|---|---|---|---|
| CC | **Theorem CC.** For every poset P on [n], n ≥ 3, and every g = ±τ preserving C_P: μ(M) = 0 iff LOW or HIGH. More precisely: (a) for g = +w, μ = 0 iff c ∧ D ≠ 0̂, and then LOW holds; (b) for g = −τ, if one of (TA1)–(TA3) fails then c ∧ D ≠ 0̂ and LOW holds; (c) for g = −τ in row W−4, HIGH holds, with ⋁ atoms ≤ O \| Q | **PROVEN** (§3). COMPUTED: exhaustive for n ≤ 8 up to isomorphism, with 0 failures (§4); plus the 13 targeted pairs with n = 8, 9, 18 of [CVA] | CD, CK, A, Z+, Z−, B; Cor. 3.9.5; [Thm], [PCV] TA (nonvanishing halves) |
| CD | **Lemma CD.** Every coatom x of M satisfies x ≥ κ or x ≥ c | **PROVEN** (§2). COMPUTED on every pair with n ≤ 8, 0 failures | S5's averaging (CITED [CVA]) |
| CK | **Lemma CK.** Every coatom x of M with x ≥ κ satisfies x ≥ D | **PROVEN** (§2) (Hanlon's Lemma 2, relative to κ). COMPUTED, n ≤ 8, 0 failures | S2 |
| A | **Proposition A.** ⋀ coatoms ≥ c ∧ D. If c ∧ D ≠ 0̂, then M has a proper element and LOW holds | **PROVEN** (§2). COMPUTED, n ≤ 8, 0 failures | CD, CK, S2, S4 |
| Z | **Proposition Z.** c ∧ D ≠ 0̂ on every zero with g = +w, and whenever g = −τ and one of (TA1)–(TA3) fails. In row W−4, c ∧ D = 0̂ | **PROVEN** (§3). COMPUTED: c ∧ D ≠ 0̂ on every zero outside W−4 and on no W−4 pair, n ≤ 8 | P, T |
| B | **Proposition B.** In row W−4 every atom of M lies below Q \| singletons or below O \| singletons, so ⋁ atoms ≤ O \| Q < 1̂ | **PROVEN** (§3). COMPUTED, n ≤ 8, 0 failures | S2 |
| U | **Corollary U.** If c ∧ D ≠ 0̂, then c ∧ D has no complement in M. In row W−4, O \| Q has no complement in M. So every zero has the witness c ∧ D or O \| Q | **PROVEN** (§3). COMPUTED, n ≤ 8, 0 failures | A, B, [PACVA] §2.2 step |
| X | **Exact form of the coatom predicate.** For g = −τ: c ∧ D ≠ 0̂ iff one of (TA1)–(TA3) fails | **PROVEN** (§3, Cor. X) | Z, A, Cor. 3.9.5, [PCV] TA |
| W | The task's question: is the TA-CR witness W ≥ ⋀ coatoms, or ≤ ⋁ atoms? | **COMPUTED** (§4, n ≤ 8): W ≥ ⋀ coatoms on every zero of rows W+1, W−2, W−3, W−4, but not on 112 W−1 zeros and 1 W+2 zero. Not used in the proof, which goes through c instead (W ≤ c for rows W+1 to W−3) | — |
| G | Side question: CC beyond type A | **COMPUTED** (§5). It fails on the rank-4 CR_V counterexample of [CRV] §0, as it must (that lattice is complemented with μ = 0). It holds on all 1,120 zeros of the 12 rank-≤3 families. In rank 4 (7 families plus A4, 438 zeros), the only zeros without CC are the 36 complemented CR_V counterexamples. On all 141,393 pairs, a zero has CC iff it has an uncomplemented element | — |
| Rk | Status changes for other notes (not applied here) | §6 | — |

**In one line.** Every coatom of OP(P)^τ is coarser than comp(P) or than
cl(Fix g) (a fixed-point averaging argument). The coatoms coarser than
comp(P) are the coatoms of a fixed-point partition lattice, which Hanlon
classified. Their common refinement therefore contains c ∧ D, and c ∧ D ≠ 0̂
on every zero except those of row W−4. There, odd points can only pair with
odd points in an atom, so all atoms lie below O | Q.

---

## 1. Notation

P is a poset on [n], n ≥ 3, and g = ετ preserves C_P (so τ ∈ Aut P if ε = +1,
τ an anti-automorphism if ε = −1; [CVA] S0). M = OP(P)^τ, ordered by
refinement. As in [CVA] §1:
- **S1** (CITED [CVA]): χ_{C_P}(g) = 0 iff μ(M) = 0.
- **S2** (PROVEN [CVA]): the meet in M is the common refinement x ∧ y; the
  join is the acyclic closure of the partition join; every τ-stable partition
  ≥ κ is acyclic, so lies in M.
- **S4** (PROVEN [CVA]): c := cl(Fix g) ∈ M, and no block of c contains a
  relation of P. For g = +w, c = cyc(w). For g = −τ, c has the block O of all
  points on odd cycles of τ (if O ≠ ∅) and, for each even cycle, its two
  parity classes.

New notation:
- κ = comp(P), the partition into connected components.
- For a block K of κ, λ_K is the length of the ⟨τ⟩-orbit of K. If i ∈ K lies
  on a τ-cycle of length ℓ_i, then λ_K | ℓ_i (τ^{ℓ_i} fixes i, so maps K to
  the component of i).
- r := rad(gcd_K λ_K), the product of the distinct primes dividing all λ_K.
  So r | λ_K | ℓ_i for every i ∈ K.
- **D** is the partition whose blocks are the sets ⋃_{a ∈ Z} τ^{ar}K, one for
  each ⟨τ^r⟩-orbit of components. D ≥ κ. D is τ-stable (τ maps the
  ⟨τ^r⟩-orbit of K to that of τK), so D ∈ M by S2.
- c ∧ D is the common refinement. It lies in M (S2).
- For −τ: O = points on odd cycles, Q = [n] ∖ O.

## 2. The coatoms

**Lemma CD (PROVEN).** Suppose M has an element other than 0̂ and 1̂. Then
every coatom x of M satisfies x ≥ κ or x ≥ c.

*Proof.* Let x be a coatom with x ≱ κ. This is the situation of [CVA] S5,
whose first four bullets use only "x ∈ M, x ≱ κ". They give:
- (S5.1) a relation i <_P j with i, j in different blocks of x, and the set R
  of y ∈ R^n_0 constant on x-blocks with y_a < y_b for every relation a <_P b
  between different x-blocks;
- (S5.2) R is nonempty and convex;
- (S5.3) R is g-stable;
- (S5.4) the ⟨g⟩-average y* of a point of R lies in R ∩ Fix g. It lies in
  C_P (relations inside an x-block hold with equality), and y*_i < y*_j.

Let ŷ be the level-set partition of y*. As in S5:
- ŷ ∈ M: τ-stable since gy* = y* and (gy)_{τ(k)} = ε y_k; acyclic since
  y* ∈ C_P, so quotient edges go from smaller to larger values.
- ŷ ≥ x, since y* is constant on x-blocks.
- ŷ ≥ c. By definition, i ~_c j iff z_i = z_j for every z ∈ Fix g, and
  y* ∈ Fix g.
- ŷ ≠ 1̂, since y*_i < y*_j.

As x is a coatom and x ≤ ŷ < 1̂, we get ŷ = x, so x ≥ c. ∎

**Lemma CK (PROVEN).** Every coatom x of M with x ≥ κ satisfies x ≥ D.

*Proof.* The ⟨τ⟩-orbits of blocks of x partition the blocks.
- *Two or more orbits.* Let U be the union of one orbit. Then
  y = {U, [n] ∖ U} is τ-stable and ≥ κ, so y ∈ M (S2). Also x ≤ y < 1̂, so
  y = x. Both blocks of x are τ-stable unions of components. Each D-block
  lies in the ⟨τ⟩-orbit of one component, so it lies in one block of x.
- *One orbit.* The blocks are B, τB, …, τ^{s−1}B with s ≥ 2 (x ≠ 1̂), and
  τ^jB = τ^{j′}B iff s | j − j′.
  - *s is a prime p.* If s = ab with 1 < a < s, merge the blocks whose index
    is congruent mod a. This gives a τ-stable partition with a blocks, ≥ x,
    ≥ κ, different from x and from 1̂, against maximality.
  - *p | λ_K for every component K.* K lies in some τ^jB (x ≥ κ). Then
    τ^{λ_K}τ^jB meets τ^jB (both contain K), so p | λ_K.
  - So p | r. For every component K ⊆ τ^jB and every a, τ^{ar}K ⊆ τ^{j+ar}B
    = τ^jB. So the D-block of K lies in τ^jB. ∎

This is Hanlon's classification of the coatoms of Π_n^σ (Hanlon 1981,
Lemma 2: two σ-stable blocks, or p cyclically permuted blocks with p a prime
dividing every cycle length; CITED via [PACVA] §3.1), applied to the
interval [κ, 1̂] of M. That interval is the fixed lattice of the action of τ
on the set partitions of the components. The proof above is self-contained.

**Proposition A (PROVEN).** If M ≠ {0̂, 1̂}, then ⋀ coatoms ≥ c ∧ D. If
c ∧ D ≠ 0̂, then M ≠ {0̂, 1̂}, and LOW holds.

*Proof.*
- *The bound.* By CD and CK, every coatom is ≥ c or ≥ D, hence ≥ c ∧ D. The
  meet in M is the common refinement (S2), so ⋀ coatoms ≥ c ∧ D.
- *M ≠ {0̂, 1̂}.* Suppose c ∧ D ≠ 0̂ and M = {0̂, 1̂}. As c, D ∈ M, we get
  c = D = 1̂.
  - D = 1̂ means a single ⟨τ^r⟩-orbit of components. A ⟨τ^r⟩-orbit lies in a
    ⟨τ⟩-orbit of λ components and has λ/r of them (r | λ). So r = 1 and
    then λ = gcd λ_K has radical 1, so λ = 1: P is connected.
  - P connected with n ≥ 2 has a relation i <_P j. By S4 no block of c holds
    a relation, so c ≠ 1̂. Contradiction.
- *LOW.* ⋀ coatoms ≥ c ∧ D ≠ 0̂. ∎

## 3. Theorem CC

**Lemma P (PROVEN).** If some point i and some integer a satisfy
τ^{ar}i ≠ i and τ^{ar}i ~_c i, then c ∧ D ≠ 0̂.

*Proof.* τ^{ar}i ∈ τ^{ar}K_i, which lies in the D-block of the component
K_i of i. So {i, τ^{ar}i} lies in one block of c and one block of D. ∎

**Proposition Z+ (PROVEN).** Let g = +w. If c ∧ D = 0̂, then every cycle of w
has length r, ord w = r is squarefree, and ⟨w⟩ acts freely on the
components. Hence (by [Thm, eq. closed], nonvanishing half, CITED)
χ_{C_P}(+w) ≠ 0. Equivalently: every zero with g = +w has c ∧ D ≠ 0̂.

*Proof.* c = cyc(w), so w^r i ~_c i for every i. By Lemma P with a = 1,
w^r i = i, so ℓ_i | r. Since r | λ_{K_i} | ℓ_i, we get ℓ_i = λ_{K_i} = r for
every i. Then o = ord w = lcm ℓ_i = r is squarefree (a radical), and every
λ_K = o, which is freeness. ∎

**Lemma T (PROVEN; the arguments of rows W−2 and W−3 of [CVA] §3).** Let
g = −τ with (TA1) holding, Λ ⊆ {m, 2m}, m odd squarefree. If (TA2) or
(TA3) fails, then κ ∧ c ≠ 0̂.

*Proof.*
- *(TA2) fails.* Some component K has λ = λ_K ∉ {m, 2m}. Since λ | o | 2m,
  and the divisors of 2m that are multiples of m are m and 2m, m ∤ λ. Take
  y ∈ K.
  - If y is odd (cycle length m), τ^λ y ∈ K is another odd point (m ∤ λ).
    Both lie in the block O of c.
  - If y lies on a 2m-cycle, τ^{2λ}y ∈ K differs from y (2m ∤ 2λ) and has
    the same parity class.
- *(TA3) fails.* Some K ∪ τ^mK holds two odd points. An odd point q ∈ τ^mK
  has τ^{−m}q = q, so q ∈ K. So K holds two odd points, both in O.

Either way some component meets a block of c in two points. ∎

**Proposition Z− (PROVEN).** Let g = −τ. If c ∧ D = 0̂, then (TA1), (TA2) and
(TA3) hold.

*Proof.*
- *Odd points.* For i ∈ O on a cycle of length ℓ, τ^r i ∈ O, so τ^r i ~_c i.
  By Lemma P (a = 1), τ^r i = i, so ℓ | r, so ℓ = r (r | ℓ).
- *Even cycles.* For i on an even cycle of length ℓ, τ^{2r}i has the same
  parity class as i. By Lemma P (a = 2), ℓ | 2r. If r is even, τ^r i also
  has the same parity class, and ℓ | r, so ℓ = r.
- *(TA1).*
  - If O ≠ ∅: every odd length equals r, so r is odd. An even length ℓ
    satisfies r | ℓ | 2r, so ℓ = 2r. So Λ ⊆ {r, 2r} with r odd squarefree.
  - If O = ∅ and r is odd: every ℓ is even with r | ℓ | 2r, so Λ = {2r}.
  - If O = ∅ and r is even: every ℓ = r, and r = 2m′ with m′ odd squarefree
    (r is a radical), so Λ = {2m′}.

  In each case Λ ⊆ {m, 2m} for an odd squarefree m.
- *(TA2), (TA3).* D ≥ κ, so c ∧ D ≥ c ∧ κ. If (TA2) or (TA3) failed,
  c ∧ κ ≠ 0̂ by Lemma T. ∎

**Proposition B (PROVEN).** Let g = −τ be in row W−4: (TA1)–(TA3) hold,
O ≠ ∅ ≠ Q, and every odd point is isolated in P. Put a = Q | singletons on O,
b = O | singletons on Q, and O | Q the two-block partition. Then a, b,
O | Q ∈ M, every atom of M is ≤ a or ≤ b, and ⋁ atoms ≤ O | Q < 1̂. So HIGH
holds.

*Proof.*
- *Membership.* O and Q are τ-stable, so a, b and O | Q are. Every relation
  of P lies inside Q. So a and O | Q have quotients without edges. The
  quotient of b on its Q-singletons is P restricted to Q, which is acyclic,
  and the block O carries no relation. So all three lie in M. Also
  a ≠ 0̂ (|Q| ≥ 2, as even cycles have length ≥ 2) and a ≠ 1̂ (O ≠ ∅), so M
  has proper elements and its atoms are proper.
- *Atoms.* Let x be an atom.
  - If x ∧ a ≠ 0̂, then x ∧ a ∈ M (S2) lies in (0̂, x], so x ∧ a = x and
    x ≤ a.
  - If x ∧ a = 0̂, every block of x has at most one point of Q. Suppose a
    block B holds q ∈ O and j ∈ Q. By (TA1), q lies on an m-cycle and j on a
    2m-cycle. So τ^mq = q, hence τ^mB = B, and τ^mj ≠ j is a second Q-point
    of B. Contradiction. So every block of x lies in O or is a Q-singleton:
    x ≤ b.
- *Join.* O | Q is an upper bound of a and b in M, so ⋁ atoms ≤ a ∨_M b ≤
  O | Q < 1̂. ∎

**Proposition B′ (PROVEN).** In row W−4, c ∧ D = 0̂.

*Proof.* The odd points are singleton components with λ = m, and every λ_K
lies in {m, 2m} (TA2). So gcd λ_K = m and r = m (squarefree by TA1).
- Two odd points q ≠ q′: the D-block of {q} is ⋃ τ^{am}{q} = {q}.
- Two points of one parity class: i and j = τ^{2b}i ≠ i on a 2m-cycle. If j
  were in τ^{am}K_i, then τ^{2b−am}i ∈ K_i, so λ_{K_i} | 2b − am, so
  m | 2b, so m | b (m odd), so 2m | 2b and j = i. Contradiction.

The blocks of c are O and the parity classes, so c ∧ D = 0̂. ∎

**Theorem CC (PROVEN).** For every poset P on [n], n ≥ 3, and every g = ετ
preserving C_P: χ_{C_P}(g) = 0 iff LOW or HIGH.

*Proof.*
- *If.* LOW or HIGH gives μ(M) = 0 by EC1 Cor. 3.9.5 (CITED), and S1.
- *Only if, g = +w.* By Z+, c ∧ D ≠ 0̂. By Proposition A, LOW.
- *Only if, g = −τ.* By [PCV] Theorem TA (nonvanishing half, CITED), one of
  (TA1)–(TA4) fails.
  - If one of (TA1)–(TA3) fails: c ∧ D ≠ 0̂ by Z−, and LOW by
    Proposition A.
  - Otherwise (TA4) fails, which is row W−4: HIGH by Proposition B. ∎

**Corollary U (PROVEN).** If c ∧ D ≠ 0̂, then c ∧ D has no complement in M.
In row W−4, O | Q has no complement in M. So every zero of χ_{C_P}(±τ) has
one of these two uncomplemented witnesses, and the "only if" of TA-CR
follows again, with a uniform witness.

*Proof.* This is the elementary step of [PACVA] §2.2, slightly extended.
- *Below ⋀ coatoms.* Let 0̂ ≠ z ≤ every coatom, and suppose y is a
  complement. Then y ≠ 1̂ (z ∧ 1̂ = z ≠ 0̂), so y ≤ some coatom C (M is
  finite). As z ≤ C, z ∨ y ≤ C < 1̂. Apply this to z = c ∧ D (Prop. A).
- *Above ⋁ atoms.* Dually, let 1̂ ≠ z ≥ every atom, and suppose y is a
  complement. Then y ≠ 0̂, so y ≥ some atom A. As A ≤ z, z ∧ y ≥ A ≠ 0̂.
  Apply this to z = O | Q (Prop. B). ∎

**Corollary X (PROVEN).** For g = +w: χ = 0 iff c ∧ D ≠ 0̂ iff some cycle of
w is longer than rad(gcd_K λ_K). For g = −τ: c ∧ D ≠ 0̂ iff one of
(TA1)–(TA3) fails.

*Proof.*
- *+w, first equivalence.* "⇒" is Z+. "⇐" is Proposition A plus
  Cor. 3.9.5.
- *+w, second equivalence.* The proof of Z+ shows that c ∧ D = 0̂ forces
  every ℓ_i = r. Conversely, if every ℓ_i = r, then w^r = id, and no pair
  {i, w^k i} with w^k i ≠ i lies in a D-block: w^k i ∈ w^{ar}K_i would give
  w^{k−ar}i ∈ K_i, so λ_{K_i} divides k − ar. Here λ_{K_i} = r (from
  r | λ_{K_i} | ℓ_i = r), so r | k and w^k i = i.
- *−τ.* "⇐" is Z−. "⇒": if (TA1)–(TA3) all hold, either (TA4) fails, and
  c ∧ D = 0̂ by B′, or (TA4) holds, χ ≠ 0 by [PCV] TA, and then c ∧ D = 0̂,
  since otherwise Proposition A and Cor. 3.9.5 would give χ = 0. ∎

**Remarks.**
- *What replaced the five-way list.* The proof of the coatom side does not
  split rows W+1, W+2, W−1, W−2, W−3. It needs one predicate, c ∧ D ≠ 0̂,
  and one arithmetic argument per sign (Z+, Z−). Lemma T is the only
  ingredient taken from TA-CR's case analysis, and it is used only through
  κ ∧ c ≤ c ∧ D.
- *The task's question* ("for each witness type, is that witness ≥ ⋀
  coatoms, or ≤ ⋁ atoms?"). The proof does not compare W with ⋀ coatoms
  directly. It goes through c: rows W+1 to W−3 have W ≤ c ([CVA] table W,
  column "kind"), and ⋀ coatoms ≥ c ∧ D. The direct comparison is COMPUTED
  in §4. W ≥ ⋀ coatoms fails on 112 W−1 zeros and 1 W+2 zero with n ≤ 8,
  so the TA-CR witnesses are not themselves uniform.
- *n ≤ 2* is outside the statement, as for TA-CR ([CVA] S0 needs n ≥ 3).
- *Both sides are needed.* LOW fails on some W−4 zeros (Prop. B′ explains
  why c ∧ D cannot help there; LOW can still hold through other coatoms), and
  HIGH fails on many W+1 zeros (§4).

## 4. Computation ([OCC], type A)

`compute/observation_cc.py` imports the enumeration of `cr_v_type_a.py`
(posets up to isomorphism, τ up to conjugation by Aut P, both signs) and its
lattice M. On every pair it checks:
- **CC**: LOW or HIGH iff μ = 0;
- **CD**, **CK**: every coatom is ≥ κ or ≥ c; every coatom ≥ κ is ≥ D;
- **A**: c ∧ D ≠ 0̂ ⇒ M has proper elements, LOW, and ⋀ coatoms ≥ c ∧ D;
- **U**: c ∧ D ≠ 0̂ ⇒ c ∧ D uncomplemented; in row W−4, O | Q
  uncomplemented;
- **ZL**: on every zero of rows W+1 to W−3, c ∧ D ≠ 0̂;
- **W4**: in row W−4, every atom ≤ a or ≤ b, ⋁ atoms ≤ O | Q, HIGH.

It also counts, for each zero, its row, which of LOW and HIGH hold, and
whether the TA-CR witness W satisfies W ≥ ⋀ coatoms and W ≤ ⋁ atoms.

**Controls ([CTL]), all passing:**
- Π_4^{(1234)} (a 3-element chain): CC holds, μ = 0. Π_4: CC fails, μ = −6.
- Injected fault: with c replaced by 0̂ in the predicate, check ZL fails on
  112 zeros with n ≤ 5 (so ZL can fire).
- Unit tests (`test_observation_cc.py`): Π_3^{(012)} = {0̂, 1̂} is not CC;
  D on two explicit examples; a W−4 pair with LOW false and HIGH true
  exists at n = 5 (so the atom side is needed, and Prop. B′ is visible).
- Reproduction: the n ≤ 7 pair, zero and side counts equal [PACVA] §2.3
  exactly (6,154 pairs, 3,519 zeros; low-only 0, 0, 4, 64, 558; high-only
  0, 0, 3, 3, 36).

**Exhaustive sweep, n = 3..8, up to isomorphism.** Every check passes on every
pair. The n = 8 sweep finished all 16,999 posets within its budget (28 min
48 s wall, 2 workers): nothing is UNRUN.

| n | posets | pairs | zeros | CC mismatches | CD / CK / A / U / ZL / W4 failures | LOW only / HIGH only / both | pairs with c ∧ D ≠ 0̂ (of them W−4) | zeros by row W+1 / W+2 / W−1 / W−2 / W−3 / W−4 |
|---|---|---|---|---|---|---|---|---|
| 3 | 5 | 14 | 5 | 0 | 0 / 0 / 0 / 0 / 0 / 0 | 0 / 0 / 5 | 3 (0) | 3 / 0 / 0 / 0 / 0 / 2 |
| 4 | 16 | 50 | 22 | 0 | 0 / 0 / 0 / 0 / 0 / 0 | 0 / 0 / 22 | 20 (0) | 15 / 1 / 3 / 0 / 1 / 2 |
| 5 | 63 | 174 | 99 | 0 | 0 / 0 / 0 / 0 / 0 / 0 | 4 / 3 / 92 | 89 (0) | 80 / 0 / 7 / 0 / 2 / 10 |
| 6 | 318 | 866 | 481 | 0 | 0 / 0 / 0 / 0 / 0 / 0 | 64 / 3 / 414 | 471 (0) | 432 / 0 / 23 / 2 / 14 / 10 |
| 7 | 2,045 | 5,050 | 2,912 | 0 | 0 / 0 / 0 / 0 / 0 / 0 | 558 / 36 / 2,318 | 2,857 (0) | 2,758 / 0 / 69 / 0 / 30 / 55 |
| 8 | 16,999 | 39,174 | 21,658 | 0 | 0 / 0 / 0 / 0 / 0 / 0 | 5,852 / 36 / 15,770 | 21,603 (0) | 21,128 / 3 / 273 / 0 / 199 / 55 |
| total | | 45,328 | 25,177 | 0 | 0 | 6,478 / 78 / 18,621 | 25,043 (0) | |

Reading the table:
- *Corollary X on the data.* In every row, the number of pairs with
  c ∧ D ≠ 0̂ is the number of zeros minus the W−4 zeros (e.g. n = 8:
  21,658 − 55 = 21,603). So the predicate never fires on a nonzero pair or on
  a W−4 pair.
- *Rows n ≤ 7* reproduce [CVA] §4 (zeros per row) and [PACVA] §2.3 (sides).
- *Every HIGH-only zero is in row W−4* (78 = 78 W−4 zeros with LOW false).
  The LOW-only zeros are in rows W+1 (6,229), W+2 (1), W−1 (48) and W−3
  (200).

**The task's question, COMPUTED (all n ≤ 8; the TA-CR witness W of [CVA]
table W against ⋀ coatoms and ⋁ atoms):**

| row | zeros | W ≥ ⋀ coatoms fails | W ≤ ⋁ atoms fails |
|---|---|---|---|
| W+1 | 24,416 | 0 | 526 |
| W+2 | 4 | 1 | 0 |
| W−1 | 375 | 112 | 4 |
| W−2 | 2 | 0 | 0 |
| W−3 | 246 | 0 | 0 |
| W−4 | 134 | 0 | 0 |

So on rows W+1, W−2, W−3 and W−4 the TA-CR witness is always ≥ ⋀ coatoms.
On W+2 and W−1 it sometimes is not. That is why the proof uses c ∧ D, not W.

**Targeted pairs ([EXTRA]).** The 13 pairs of [CVA] §4 with n = 8, 9, 18 (rows
W+2 and the "m odd, not squarefree" branch of W−1, plus nonzero controls):
every zero has LOW and c ∧ D ≠ 0̂, every nonzero pair fails CC, and all
checks pass.

**Not run.** τ = (9)(18) on 27 points (the two-length branch of W−1, first at
n = 27) is UNRUN here. Z− covers it: Λ = {9, 18}, gcd λ = 9, r = 3, and the
odd points lie on cycles of length 9 > 3.

## 5. Side question: CC beyond type A (COMPUTED only)

[OCC] part [GEN] reuses the cone lattices Λ(V)^g of `compute/conjecture_cr_v.py`
([CR]): every class representative g and every g-stable top-cone V of each
family. It tests CC directly on the lattice (coatoms, atoms, meet and join
from [CR]'s lattice routine). Controls: the 8-element complemented lattice
with μ = 0 fails CC; a 4-element chain satisfies it; B_3 fails it. On every
family, CC never holds on a nonzero pair. That is Cor. 3.9.5 on the data, a
check of the code.

| family | rank | pairs | zeros | zeros with CC | zeros without CC | of those, with an uncomplemented element |
|---|---|---|---|---|---|---|
| CR_V counterexample of [CRV] §0 (one pair of the C6 × C4 family below; not counted again in the total) | 4 | 1 | 1 | 0 | 1 | 0 |
| A2, B2 | 2 | 75 | 10 | 10 | 0 | 0 |
| A3, B3, generic 4, B3 minus {z=0}, A3 minus a plane, hexagon 12, hexagon 13, R^3 C6 × ⟨z↦−z⟩, R^3 D4 × ⟨z↦−z⟩, R^3 D6 | 3 | 17,884 | 1,110 | 1,110 | 0 | 0 |
| A4 (type A, all cones) | 4 | 4,634 | 342 | 342 | 0 | 0 |
| generic 5 in R^4; R^4 C5 × −1, C8, C3 × C3 × −1, C4 × −1, C12 | 4 | 45,684 | 30 | 30 | 0 | 0 |
| R^4 C6 × C4 (the family of the counterexample) | 4 | 38,400 | 60 | 24 | 36 | 0 |
| R^4 (C6 × C6) and the swap | 4 | 34,716 | 6 | 6 | 0 | 0 |
| total | | 141,393 | 1,558 | 1,522 | 36 | 0 |

(The five rank-4 families C5 × −1, C8, C3 × C3 × −1, C4 × −1 and C12 have
no zeros, so they say nothing about CC beyond the code check.)

Findings:
- **The rank-4 counterexample.** CC fails there (LOW and HIGH both false),
  as it must: the lattice is complemented with μ = 0, and CC would force an
  uncomplemented element (Cor. U's step).
- **Rank ≤ 3.** CC holds on all 1,120 zeros of the 12 rank-2 and rank-3 families. Since CR_V is
  a theorem in rank ≤ 3 ([CRV] Theorem 3), this is consistent with "CC iff
  CR_V obstruction" in rank ≤ 3. Whether CC holds on every rank-3 pair is
  OPEN: it is COMPUTED here, not proven.
- **Rank 4.** The only zeros without CC are the 36 CR_V counterexample pairs
  of [CRV] §5, which are complemented. On every computed family, the zeros
  with CC are exactly the zeros with an uncomplemented element (1,522 =
  1,522). So in these data, CC is as strong as "uncomplemented element" on
  cone lattices. Rival's example (EC1 Ex. 3.28) shows the two differ for
  abstract lattices. No cone lattice with an uncomplemented element and no
  CC was found.
- **Not run here (UNRUN):** the rank-4 families "A4 minus one/two
  hyperplanes" and "D4 with W(B4)" of [CR], and every rank ≥ 5 family.

## 6. Status changes for other notes (reported, not applied)

- **[PACVA] §2.3 and Verdict row "Observation CC"**: COMPUTED → PROVEN
  (Theorem CC here; awaiting independent audit). The n ≤ 7 counts are
  reproduced, and n = 8 is added.
- **[CVA] §6, "Observation CC … Whether this holds for all n is OPEN"**:
  settled by Theorem CC (PROVEN here, awaiting audit).
- **[CVA] Theorem TA-CR**: unaffected. Corollary U gives a second proof of
  its "only if" half, with the uniform witnesses c ∧ D and O | Q. It uses the
  same cited zero criteria, the same S-steps, and Lemma T, but not Lemma C
  or table W.
- No claim of another note was found to be wrong.

## 7. What remains open

- **Audit.** Every PROVEN claim here awaits an independent audit. The steps
  to check are CD, CK, A, P, Z+, T, Z−, B, B′, U, X and Theorem CC.
- **Other Coxeter types.** Lemma CD holds for any arrangement: it is [CRV]
  Lemma F. Lemma CK uses the partition structure of [κ, 1̂], and so does the
  arithmetic of Z±. For B_n and D_n, CC is OPEN. §5 records where it does
  and does not hold among the families computed.
- **Is "CC iff uncomplemented element" true for all cone lattices?** It holds
  on all 141,393 pairs of §5, and in type A it follows from Theorem CC and
  TA-CR. OPEN in general. Even in rank 3 it is only COMPUTED.
- **A zero-criterion-free proof.** Theorem CC still cites the nonvanishing
  halves of [Thm] and [PCV] TA. Corollary X shows that, for +w, the
  predicate c ∧ D ≠ 0̂ is exactly the zero set. A direct proof that
  c ∧ D = 0̂ and "not W−4" force μ ≠ 0 would make the whole statement
  self-contained. OPEN.

## Reproduce

From `compute/` (plain Python 3, no third-party packages; `--jobs` sets the
number of worker processes, the default is 1):

    python3 observation_cc.py --nmax 8 --budget 5400 --jobs 2 --no-gen > output/observation_cc.txt   # 29 min with 2 workers, ends "ALL CHECKS PASSED", exit 0
    python3 observation_cc.py --nmax 3 --gen-r4 > output/observation_cc_gen_r4.txt                    # 37 min, side question incl. rank 4
    python3 observation_cc.py --nmax 7 --no-gen                                                       # ~1 min, single process
    python3 -m unittest test_observation_cc                                                           # < 1 s

`--budget` bounds the wall time of the type-A sweep in seconds. Posets not
reached are printed as UNRUN, and the script exits 1 without printing ALL
CHECKS PASSED. The archived logs are `compute/output/observation_cc.txt`
(controls, [EXTRA], sweep n ≤ 8) and `compute/output/observation_cc_gen_r4.txt`
(controls, [EXTRA], sweep n = 3, side question).

References:
- [CVA] = `notes/cr_v_type_a.md`; [AudCVA] = `notes/audit_cr_v_type_a.md`;
- [PACVA] = `notes/prior_art_cr_v_type_a.md`;
- [PCV] = `notes/per_cone_vanishing.md` (Theorem TA);
- [CRV] = `notes/conjecture_cr_v.md`;
- [Thm] = `notes/poset_jks_theorem.tex`;
- Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., Cor. 3.9.5, Ex. 3.28;
- Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981),
  Lemma 2.
