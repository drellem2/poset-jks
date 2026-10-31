# Audit of `notes/observation_cc.md` (Theorem CC and its steps)

This is an independent, adversarial audit of `notes/observation_cc.md`
("[OCC-note]", merged 8eed58f). Every proof was re-derived line by line from
the note's statements and from the steps it cites. All computation is new
code, `compute/audit_observation_cc.py` ("[AUD]"). It imports nothing from
the repository, and in particular nothing from `compute/observation_cc.py` or
`compute/cr_v_type_a.py`.

## Verdict

| Claim | Verdict | Notes |
|---|---|---|
| **Theorem CC** (μ(M) = 0 iff LOW or HIGH, for every P on [n], n ≥ 3, and every g = ±τ preserving C_P) | **HOLDS** | The case split is exhaustive. No zero falls between the rows (§2). The cited zero criteria are used only in their nonvanishing direction, and that direction was audited (§3). Recomputed exhaustively for n ≤ 8 up to isomorphism (45,328 pairs, 25,177 zeros) with 0 failures, and the pair counts equal the note's table (§5) |
| **Lemma CD** (every coatom is ≥ κ or ≥ c) | **HOLDS** | The S5 averaging step is used correctly. It needs only x ∈ M and x ≱ κ (§1). 0 failures, n ≤ 8 |
| **Lemma CK** (every coatom ≥ κ is ≥ D) | **HOLDS** | The self-contained proof is correct. The relativisation of Hanlon's Lemma 2 to [κ, 1̂] is valid and is not needed by the proof (§1). 0 failures, n ≤ 8. A broken control (D built with r = 1) fails on 85 pairs |
| **Proposition A** (⋀ coatoms ≥ c ∧ D; if c ∧ D ≠ 0̂, then M is proper and LOW holds) | **HOLDS** | §1. 0 failures |
| **Lemma P** | **HOLDS** | §1 |
| **Proposition Z+** | **HOLDS** | §1. The nonvanishing half of [Thm, eq. closed] follows from the displayed formula in one line (§3) |
| **Lemma T** | **HOLDS** | §1 |
| **Proposition Z−** | **HOLDS** | §1. The three (TA1) subcases are exhaustive, and the m they produce is the m of (TA2) and (TA3) |
| **Proposition B** (row W−4: every atom is ≤ Q \| singletons or ≤ O \| singletons, so ⋁ atoms ≤ O \| Q) | **HOLDS** | §1. 0 failures. A broken control (Q \| singletons in place of O \| Q) fails on 79 W−4 pairs |
| **Proposition B′** (c ∧ D = 0̂ in row W−4) | **HOLDS** | §1. 0 failures (no W−4 pair has c ∧ D ≠ 0̂) |
| **Corollary U** (c ∧ D, resp. O \| Q, is uncomplemented) | **HOLDS** | The [PACVA] §2.2 step was checked against its source text. Its extension from "the meet of the coatoms" to "any z ≠ 0̂ below every coatom", and its dual, are valid (§4). Recomputed by scanning all of M for a complement: 0 failures |
| **Corollary X** | **HOLDS** | Both signs. For −τ, "⇒" uses B′ as well as the inputs listed in the verdict row (bookkeeping, R2) |
| τ = (9)(18) on 27 points (UNRUN in the note) | **HOLDS** | Checked symbolically for every poset with this τ (Z− applies because (TA1) fails), and computed for the antichain: r = 3, c ∧ D = cyc(τ⁶) ≠ 0̂, ⋀ coatoms = D = cyc(τ³) (§2.3) |
| Bookkeeping in the verdict table | **FIXABLE** (presentation only) | R1, R2 in §6. No proof is affected |

**In one line.** Theorem CC and every step it rests on (CD, CK, A, P, Z+, T,
Z−, B, B′, U, X) hold as stated. The two predicates "c ∧ D ≠ 0̂" and "row
W−4" together cover every zero, and on n ≤ 8 they are disjoint and cover
exactly the zeros. The note's computed table for n ≤ 8 is reproduced
exactly by independent code.

---

## 1. The proofs, step by step

Notation is that of [OCC-note] §1. M = OP(P)^τ is ordered by refinement. κ is
the component partition, λ_K is the length of the ⟨τ⟩-orbit of the component
K, r = rad(gcd_K λ_K), and D has one block ⋃_a τ^{ar}K per ⟨τ^r⟩-orbit of
components. Throughout, r | λ_K | ℓ_i for i ∈ K (S6 of [CVA]).

**Lemma CD.** Let x be a coatom with x ≱ κ. Then some relation i <_P j joins
two x-blocks, since otherwise every component would lie in one x-block. The
set R of S5 needs only that x is τ-stable and acyclic. Its g-stability is
exactly S5's third bullet, and its ⟨g⟩-average y* lies in R ∩ Fix g by
convexity. The level partition ŷ of y* is:
- τ-stable, since y*_{τk} = ε y*_k;
- acyclic, since y* ∈ C_P and quotient edges join different levels;
- ≥ x, since y* is constant on x-blocks;
- ≥ c, since y* ∈ Fix g, so c-equivalent points have equal y*-values;
- ≠ 1̂, since y*_i < y*_j.

Maximality gives ŷ = x. The hypothesis "M has a proper element" only ensures
that the coatoms are proper. **Correct.**

**Lemma CK.** Let x be a coatom with x ≥ κ.
- *Two or more ⟨τ⟩-orbits of blocks.* y = {U, [n] ∖ U} is τ-stable and ≥ κ,
  so acyclic, and x ≤ y < 1̂. So x = y. Each of the two blocks is τ-stable
  and a union of components, so it contains the whole ⟨τ⟩-orbit, and hence
  the D-block, of every component in it.
- *One orbit of s blocks.* If s = ab with 1 < a < s, the blocks with index
  ≡ j (mod a) merge into a τ-stable partition with a blocks. τ shifts the
  index by 1, and a | s makes the classes well defined. This partition lies
  strictly between x and 1̂, and it is ≥ κ, so it lies in M, a
  contradiction. So s = p is prime. τ^{λ_K} fixes K, so τ^{λ_K} fixes the
  block containing K, and p | λ_K. Hence p | r, and τ^{ar}K stays in the same
  block.

**Correct.** *Hanlon's Lemma 2 relative to κ.* The interval [κ, 1̂] of M is the
set of all τ-stable partitions ≥ κ, since all of them are acyclic (S2,
audited). Contracting each component to a point identifies it with Π_k^σ,
where σ is the permutation that τ induces on the k components. The cycle
lengths of σ are the λ_K. A coatom of M that is ≥ κ is a coatom of this
interval. Hanlon's two coatom types (two σ-stable blocks, or p blocks
permuted cyclically, with p prime dividing every cycle length of σ) are
therefore the two cases above, with "every cycle length of σ" read as
"every λ_K". The relativisation is valid. The proof uses only the easy
direction (every coatom has one of the two forms), and it proves that
direction itself, so the citation carries no weight.

**Proposition A.** CD and CK give every coatom ≥ c or ≥ D, hence ≥ c ∧ D. The
meet of the coatoms in M is their common refinement (S2), so it is
≥ c ∧ D. For properness: if M = {0̂, 1̂} and c ∧ D ≠ 0̂, then c = D = 1̂,
because c, D ∈ M (S4, S2) and neither is 0̂. A ⟨τ^r⟩-orbit inside a ⟨τ⟩-orbit
of λ components has λ/r of them. So D = 1̂ forces a single ⟨τ⟩-orbit with
λ/r = λ, so r = 1 = rad λ, so λ = 1, and P is connected. Then P has a
relation, which lies in no block of c (S4), so c ≠ 1̂. **Correct.**

**Lemma P.** τ^{ar}i lies in τ^{ar}K_i, which lies in the D-block of K_i. So i and
τ^{ar}i ≠ i share a block of D and, by hypothesis, a block of c. **Correct.**

**Proposition Z+.** With c = cyc(w), w^r i ~_c i, so Lemma P gives ℓ_i | r. With
r | λ_{K_i} | ℓ_i this forces ℓ_i = λ_{K_i} = r for all i. So o = r is a
radical, and every component orbit has length o, which is freeness. **Correct.**

**Lemma T.** Under (TA1), o ∈ {m, 2m}, so λ | o | 2m. The divisors of 2m that m
divides are m and 2m, so λ ∉ {m, 2m} forces m ∤ λ.
- An odd y ∈ K has τ^λ y ∈ K, odd, and different from y (m ∤ λ).
- A y on a 2m-cycle has τ^{2λ}y ∈ K, in the same parity class, and different
  from y (2m ∤ 2λ).
- (TA3) fails: an odd q ∈ τ^mK satisfies q = τ^{−m}q ∈ K, so K holds two odd
  points.

Each case puts two points of one c-block in one component. **Correct.**
(When m = 1, the (TA2) case is vacuous, since λ | 2 = 2m.)

**Proposition Z−.** Lemma P with a = 1 on odd points gives ℓ = r for every odd
length. With a = 2 on even cycles (a shift by 2r preserves the parity
class) it gives ℓ | 2r, and with a = 1 when r is even it gives ℓ = r.
The three (TA1) subcases (O ≠ ∅; O = ∅ with r odd; O = ∅ with r even)
are exhaustive. Each yields Λ ⊆ {m, 2m} with m odd and squarefree. m is
unique, since it is the odd element of Λ, or half the even one. So
Lemma T applies with the same m. Then κ ≤ D gives c ∧ κ ≤ c ∧ D.
**Correct.**

**Proposition B.** O and Q are τ-stable. Every relation lies inside Q, because
the odd points are isolated. So a = Q | singletons and O | Q have
quotients without edges, and the quotient of b = O | singletons is P|_Q
plus an isolated vertex. All three lie in M. |Q| ≥ 2 and O ≠ ∅ make a
proper, so the atoms are proper. Take an atom x.
- If x ∧ a ≠ 0̂, then x ≤ a by minimality, since x ∧ a ∈ M.
- Otherwise every block of x holds at most one Q-point. A block B holding an
  odd q (on an m-cycle by (TA1)) and some j ∈ Q (on a 2m-cycle) satisfies
  τ^mB = B, because τ^m q = q. Then τ^m j ≠ j is a second Q-point of B,
  which is impossible. So x ≤ b.

O | Q is an upper bound of a and b in M. Only (TA1) and the W−4 hypotheses
are used. **Correct.**

**Proposition B′.** The odd points are singleton components with λ = m, and
(TA2) gives every λ_K ∈ {m, 2m}. So gcd λ_K = m and r = m. Two odd points
lie in different D-blocks, since ⋃ τ^{am}{q} = {q}. For two points i ≠
j = τ^{2b}i of one parity class, j ∈ τ^{am}K_i would give
λ_{K_i} | 2b − am. Then m | 2b, so m | b, so j = i. Points of different
c-blocks need no check. **Correct.**

**Corollary X.**
- *+w.* The first equivalence is Z+ ("⇒"), and A with Cor. 3.9.5 ("⇐").
  Since r | ℓ_i always, "some cycle longer than r" is the negation of "every
  ℓ_i = r". The converse computation (λ_{K_i} = r forces r | k) is correct.
- *−τ.* "⇐" is Z−. "⇒" splits on (TA4). If (TA4) fails, B′ applies. If it
  holds, the cited nonvanishing half of [PCV] TA gives χ ≠ 0, and A with
  Cor. 3.9.5 gives c ∧ D = 0̂.

**Correct.**

## 2. The case split

### 2.1 Every zero is covered, and none falls between the rows

- *g = +w.* Z+ gives c ∧ D = 0̂ ⇒ (o squarefree and ⟨w⟩ free) ⇒ χ ≠ 0. So
  every zero has c ∧ D ≠ 0̂. There is no second case.
- *g = −τ.* A zero violates one of (TA1)–(TA4), by the nonvanishing half of
  [PCV] TA. Either one of (TA1)–(TA3) fails, and then c ∧ D ≠ 0̂ (Z−), or
  all three hold and (TA4) fails. The negation of (TA4) is "τ has odd and
  even cycles, and every odd cycle consists of isolated points". Odd cycles
  are all-isolated or all-non-isolated, since τ maps isolated points to
  isolated points. That negation is exactly Prop. B's hypothesis, i.e. row
  W−4.

The two alternatives are complementary, and no condition is left over.
Rows W+1, W+2, W−1, W−2 and W−3 never have to be distinguished: Z± handles
them all at once.

### 2.2 On the data

[AUD] computes c by exact linear algebra on Fix g, D, the rows (from
(TA1)–(TA4) and the [Thm] criterion, independently of μ), and μ. On every
pair with n ≤ 8:
- every zero has c ∧ D ≠ 0̂ or lies in W−4 (check "between", 0 failures);
- no nonzero pair has c ∧ D ≠ 0̂ ("Zfalse", 0);
- no W−4 pair has c ∧ D ≠ 0̂ ("Bprime", 0);
- every zero outside W−4 has c ∧ D ≠ 0̂ ("Zcov", 0).

So on n ≤ 8, "c ∧ D ≠ 0̂" and "W−4" partition the zero set exactly, as
Cor. X predicts.

### 2.3 The unrun case τ = (9)(18), n = 27

*Symbolically, for every poset P* with an anti-automorphism τ of cycle type
(9)(18): Λ = {9, 18}, and 9 is not squarefree, so (TA1) fails. Z− (its
contrapositive) gives c ∧ D ≠ 0̂ directly, whatever the components are.
The note's arithmetic (gcd λ = 9, r = 3) is that of the antichain. For a
general P, r ∈ {1, 3}, since λ_K | 9 for a component holding an odd
point. If r = 1, then i and τi ≠ i (i odd) witness c ∧ D ≠ 0̂ through
Lemma P. If r = 3, then i and τ³i ≠ i do. Either way Prop. A gives LOW.

*Computed, for the antichain* ([AUD] part [BIG]):
- r = 3, and c from exact linear algebra on Fix(−τ) ⊆ R^27_0 equals the
  explicit form (blocks O and the two parity classes, sizes 9, 9, 9).
- D = cyc(τ³), with blocks of sizes 3, 3, 3, 6, 6, 6.
- c ∧ D = cyc(τ⁶) ≠ 0̂. This is the same element as the [CVA] witness for this
  branch (k = 2m/p = 6). [AudCVA] §3 showed by exhaustive search that it is
  uncomplemented, which agrees with Cor. U.
- κ = 0̂, so every coatom of Π_27^τ falls under Lemma CK. The four coatoms
  listed by CK are {C₉, C₁₈} and the three 3-cyclic ones. They are τ-stable,
  and their meet is cyc(τ³) = D ≥ c ∧ D.

## 3. The cited zero criteria: direction of use

The note cites [Thm, eq. closed] and [PCV] Theorem TA. Every use was traced:

| Where | What is used | Direction |
|---|---|---|
| Z+, Thm CC (a), Cor. X (+w) | o squarefree and ⟨w⟩ free ⇒ χ ≠ 0 | nonvanishing |
| Thm CC (−τ), Cor. X (−τ, "⇒") | (TA1)–(TA4) all hold ⇒ χ ≠ 0 | nonvanishing |
| "If" of Thm CC, A ⇒ zero, Cor. X "⇐" | EC1 Cor. 3.9.5 only | — |

The vanishing halves are never used. They are reproved by Z± with A and
Cor. 3.9.5. Both nonvanishing halves were audited:
- *[Thm].* The nonvanishing half follows from eq. (closed) in one line.
  Under freeness, choosing one component per ⟨w⟩-orbit as B₀ and setting
  B_k = w^kB₀ gives an element of F(P, g). Each term e_C(P|_{B₀}) is the
  number of cyclic classes meeting Lin(P|_{B₀}) ≠ ∅, so it is ≥ 1. So the
  sum is positive, and μ(o) ≠ 0 for squarefree o. Eq. (closed) is part of
  the theorem whose two proofs are audited ([Thm], *Status*).
- *[PCV] TA.* `notes/audit_per_cone_vanishing.md`, verdict row TA: "Each
  condition re-derived as necessary, and their conjunction as sufficient
  (§4)." Sufficiency is the half used here.

[AUD] also checks both criteria in full against μ on every pair with n ≤ 8
(check "crit", 0 mismatches). That is a data check, not part of the proof.

## 4. Corollary U and the [PACVA] §2.2 step

The source (`notes/prior_art_cr_v_type_a.md` §2.2, "The elementary step") reads:
"If x := ⋀ coatoms ≠ 0̂, then x has no complement. A complement y has y ≠ 1̂,
since x ∧ 1̂ = x ≠ 0̂. So y ≤ c for some coatom c, and x ≤ c too. Then
x ∨ y ≤ c < 1̂. Dually …".

Cor. U applies it to any z ≠ 0̂ that lies below every coatom, not only to the
meet itself. The argument uses only z ≤ C for the coatom C above y, so the
extension is valid. Here z = c ∧ D lies below every coatom by Prop. A, and
M ≠ {0̂, 1̂} by Prop. A again. The dual uses z = O | Q ≠ 1̂, which lies above
every atom by Prop. B. Since y ≠ 0̂, some atom A ≤ y, and then A ≤ z ∧ y.
**Correct.**

[AUD] does not trust the argument. For every pair with c ∧ D ≠ 0̂, and for
O | Q in row W−4, it scans every y ∈ M for a complement. Meet and join in M
are decided from the definitions: y ∧_M z = 0̂ iff no x ∈ M ∖ {0̂} refines
both, and y ∨_M z = 1̂ iff no x ∈ M ∖ {1̂} is coarser than both. No
complement was found (checks "U_cD", "U_OQ", 0 failures).

## 5. Computation ([AUD])

**Model.** Posets up to isomorphism are generated by adding a maximal element
over every order ideal. The canonical form is the minimal relation mask over
all labelings that respect an invariant colour refinement. The pairs are
every automorphism (+) and anti-automorphism (−), up to conjugation by
Aut P, as in the note. M is computed from the definition: τ-stable set
partitions with an acyclic quotient (Kahn's algorithm). LOW and HIGH are
decided without any meet or join formula:
- LOW holds iff some x ≠ 0̂ in M refines the AND of the coatom pair masks;
- HIGH holds iff some x ≠ 1̂ in M is coarser than the partition join of the
  atoms.

c is computed from a basis of Fix g ∩ R^n_0 (exact rationals) and compared
with the explicit S4 form.

**Checks on every pair**:
- CC: zero iff LOW or HIGH;
- the cited criteria against μ;
- c by linear algebra against its explicit form; c, D and c ∧ D in M;
- CD, CK and Prop. A (bound, properness, LOW);
- coverage: Zcov, Zfalse, between;
- Prop. B (membership of a, b, O | Q; every atom ≤ a or ≤ b; every atom
  ≤ O | Q; HIGH) and Prop. B′;
- Cor. U (both witnesses, by full scan);
- Cor. X (both signs).

**Controls, all passing** ([CTL]):
- poset counts 1, 1, 2, 5, 16, 63, 318, 2045, 16999 (OEIS A000112);
- μ(Π_n) = (−1)^{n−1}(n−1)! for n ≤ 6;
- Π_4 = OP(antichain 4)^{id}: μ = −6, LOW and HIGH both false. This control
  *must fail* CC, and it does, consistently with μ ≠ 0;
- Π_4^{(0123)}: a 3-element chain, μ = 0, CC holds;
- Π_3^{(012)} = {0̂, 1̂}: μ = −1, neither side holds;
- the CC test on an abstract lattice where it must report a mismatch: the
  smallest bounded lattice found, 0̂ and 1̂ adjoined to a 6-element poset,
  is complemented with μ = 0, and LOW and HIGH are both false. [AUD]
  reports the mismatch;
- unit tests (`test_audit_observation_cc.py`). With HIGH stubbed to "false",
  the sweep reports exactly the three HIGH-only zeros at n = 5 as CC
  failures, so the failure path fires. A W−4 pair with HIGH true and
  c ∧ D = 0̂ is also tested.

**Broken witnesses ([NEG]; each must fail somewhere, and does), number of
pairs, n ≤ 8:**

| broken variant | pairs where it fails |
|---|---|
| κ in place of D ("c ∧ κ ≠ 0̂ on every zero outside W−4") | 716 |
| Q \| singletons in place of O \| Q ("every atom ≤ it" in W−4) | 79 |
| D with r := 1 in Lemma CK ("every coatom ≥ κ is ≥ D") | 85 |
| CC test with LOW only (HIGH dropped) | 78 |

The last count equals the number of HIGH-only zeros, all of them in W−4.

**Exhaustive sweep, n = 3..8** (`compute/output/audit_observation_cc.txt`):

| n | posets | pairs | zeros | LOW only / HIGH only / both | c^D != 0 (of them W-4) | zeros W+1 / W+2 / W-1 / W-2 / W-3 / W-4 | failures | NEG kappa / Q / r=1 / LOW-only |
|---|---|---|---|---|---|---|---|---|
| 3 | 5 | 14 | 5 | 0 / 0 / 5 | 3 (0) | 3 / 0 / 0 / 0 / 0 / 2 | 0 | 1 / 0 / 0 / 0 |
| 4 | 16 | 50 | 22 | 0 / 0 / 22 | 20 (0) | 15 / 1 / 3 / 0 / 1 / 2 | 0 | 6 / 2 / 6 / 0 |
| 5 | 63 | 174 | 99 | 4 / 3 / 92 | 89 (0) | 80 / 0 / 7 / 0 / 2 / 10 | 0 | 15 / 2 / 0 / 3 |
| 6 | 318 | 866 | 481 | 64 / 3 / 414 | 471 (0) | 432 / 0 / 23 / 2 / 14 / 10 | 0 | 38 / 10 / 20 / 3 |
| 7 | 2045 | 5050 | 2912 | 558 / 36 / 2318 | 2857 (0) | 2758 / 0 / 69 / 0 / 30 / 55 | 0 | 134 / 10 / 0 / 36 |
| 8 | 16999 | 39174 | 21658 | 5852 / 36 / 15770 | 21603 (0) | 21128 / 3 / 273 / 0 / 199 / 55 | 0 | 522 / 55 / 59 / 36 |

(failures = sum over all checks; NEG columns = pairs where each broken variant fails.)

Every column agrees with the note's §4 table: posets, pairs, zeros, the
LOW only / HIGH only / both split, the pairs with c ∧ D ≠ 0̂ (none in W−4),
and the zeros by row. Per row (all n ≤ 8, zeros only):

| row | LOW only | HIGH only | both |
|---|---|---|---|
| W+1 | 6,229 | 0 | 18,187 |
| W+2 | 1 | 0 | 3 |
| W−1 | 48 | 0 | 327 |
| W−2 | 0 | 0 | 2 |
| W−3 | 200 | 0 | 46 |
| W−4 | 0 | 78 | 56 |

This confirms the note's §4 statements. Every HIGH-only zero is in W−4
(78), and the LOW-only zeros are 6,229 in W+1, 1 in W+2, 48 in W−1 and 200
in W−3.

**Not rerun here.**
- The note's §4 table "W ≥ ⋀ coatoms / W ≤ ⋁ atoms". It is COMPUTED there
  and used by no proof.
- The 13 targeted pairs with n = 9 and 18. Those with n = 8 are inside the
  exhaustive sweep.
- §5 (beyond type A). It is COMPUTED only and is not part of Theorem CC.

## 6. Remarks (presentation only; no proof affected)

- **R1.** The verdict row "Z" includes "In row W−4, c ∧ D = 0̂", with inputs
  P, T. That statement is Proposition B′ (§3), whose inputs are (TA1) and
  (TA2). The verdict table has no row for B′, P or T, though §7 lists them
  as steps to audit.
- **R2.** The verdict row "X" lists inputs Z, A, Cor. 3.9.5 and [PCV] TA. The
  −τ "⇒" direction also uses B′ (the (TA4)-fails branch).
- **R3.** The note's check of the unrun case (§4, "Not run") does the
  arithmetic for the antichain only. For a general poset with τ of type
  (9)(18), r may be 1 instead of 3. Z− still covers it, because (TA1)
  fails (§2.3 above).

## Reproduce

From `compute/` (plain Python 3, no third-party packages; `--jobs` sets the
number of worker processes):

    python3 audit_observation_cc.py --nmax 8 --jobs 3 > output/audit_observation_cc.txt   # ~6 min with 3 workers, ends "ALL CHECKS PASSED", exit 0
    python3 audit_observation_cc.py --nmax 7 --jobs 3                                      # ~6 s
    python3 -m unittest test_audit_observation_cc                                          # < 1 s

`--budget SECONDS` bounds the sweep. If it runs out, the script prints UNRUN
and exits 1. `--skip-big` omits part [BIG].

References:
- [OCC-note] = `notes/observation_cc.md`; [CVA] = `notes/cr_v_type_a.md`;
  [AudCVA] = `notes/audit_cr_v_type_a.md`;
- [PACVA] = `notes/prior_art_cr_v_type_a.md`;
- [PCV] = `notes/per_cone_vanishing.md`, audited in
  `notes/audit_per_cone_vanishing.md`;
- [Thm] = `notes/poset_jks_theorem.tex`;
- Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., Cor. 3.9.5;
- Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981),
  Lemma 2.
