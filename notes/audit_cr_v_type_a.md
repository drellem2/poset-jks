# Audit of `notes/cr_v_type_a.md` (Theorem TA-CR, Lemmas K_A and C)

Independent, adversarial audit of `notes/cr_v_type_a.md` ("[CVA-note]",
mg-6de94, merged 5185eea). The proofs were re-derived line by line from the
note's statements. All computation is new code,
`compute/audit_cr_v_type_a.py` ("[AUD]"). It imports nothing from the
repository, and in particular nothing from `compute/cr_v_type_a.py`.

## Verdict

| Claim | Verdict | Notes |
|---|---|---|
| **Theorem TA-CR** (CR_V on every cone of the braid arrangement, explicit witnesses) | **HOLDS** | Every zero of (TA1)–(TA4) and of [Thm, eq. closed] falls in exactly one row of table W, and each row's proof is correct (§2). The converse is Crapo. Recomputed for n ≤ 7 with 0 failures (§4). The untested W−1 branch was checked on τ = (9)(18) at n = 27 and on four further instances (§3) |
| **Lemma K_A** (S5) | **HOLDS** | Proof correct (§1). Recomputed on every complement of every w ≤ cl(Fix g), n ≤ 6, and on every complement of every cl(Fix g^k), n = 7: all are ≥ κ, and the join with w is the partition join |
| **Lemma C** | **HOLDS** | Both directions correct (§1). Recomputed by brute force without posets on 3,142 triples (σ, κ, h), n ≤ 7, all σ-stable κ, 2,055 complemented. It also agrees with the lattice on every orbit partition cyc(τ^k) in the sweep |
| **S0** | **HOLDS** (modulo Whitney, CITED) | §1 |
| **S2** | **HOLDS** | Meet and join recomputed against brute-force glb/lub on all 61,545 element pairs, n ≤ 5 (§4) |
| **S4** | **HOLDS** | cl(Fix g^k) recomputed by exact linear algebra for every k ≤ 2·ord τ on every pair, n ≤ 7. It always lies in M, below cl(Fix g), with antichain blocks. The explicit form for −τ matches |
| **S5** | **HOLDS** | = Lemma K_A |
| Remark "W+1, W−2, W−3 do not occur on all chambers" (§3, *Remarks*, 2nd bullet) | **FIXABLE** (remark only) | False for W+1: on the antichain, +w is a W+1 zero whenever w has two cycle lengths (§2, R1). True for W−2 and W−3. No proof uses it |
| Side check: "5,063 lattices" vs 3,576 | **3,576 is correct** | Recounted independently (§5) |

**In one line.** Theorem TA-CR, Lemma K_A, Lemma C and steps S0, S2, S4, S5
hold as stated. The case analysis is exhaustive. Each witness is τ-stable,
acyclic and uncomplemented. The W−1 branch with Λ = {m, 2m}, m odd and not
squarefree, holds on τ = (9)(18), n = 27, by exhaustive search. One remark is
wrong as written, and nothing depends on it. The [PCV] figure 5,063 is not
supported; 3,576 is.

---

## 1. The shared steps and the two lemmas

Each item below was re-derived from scratch.

**S0.** The hyperplane permutation of g is an automorphism of M(K_n). For
n = 3, every permutation of the 3 edges comes from S_3. For n ≥ 4, K_n is
3-connected, and Whitney's 2-isomorphism theorem gives the vertex permutation
τ. Then g′ = gτ^{−1} fixes every hyperplane, so every functional e_i − e_j is
an eigenvector of g′^T. The relation (e_1 − e_2) + (e_2 − e_3) = e_1 − e_3 and
the connectivity of K_n force a single eigenvalue, which is real of finite
order, hence ±1. The decomposition g = ετ is unique for n ≥ 3, because no
permutation acts as −1 on R^n_0. Recovering P from C_P (comparable iff the
inequality holds on all of C_P) is correct. **Holds.**

**S2.**
- *Meet.* A cycle in the quotient of x ∧ y projects to closed walks in the
  acyclic quotients of x and of y. So it stays in one block of each, hence
  in one block of x ∧ y, a contradiction.
- *Join.* An acyclic coarsening must merge every strong component, and the
  condensation is acyclic, so one round of merging suffices. τ, or the
  reversal for an anti-automorphism, preserves strong components.
- *Plain join.* If x ≥ κ or y ≥ κ, every relation lies inside a block of
  x ∨ y.

[AUD] does not rely on "one round suffices": its closure iterates. It checks
the fast join and meet against the brute-force least upper and greatest lower
bounds in M. **Holds.**

**S4.**
- *Fixed point.* int C_P is nonempty, convex and h-stable, so averaging gives
  a point of Fix h ∩ int C_P.
- *Generic point.* The points of Fix h that separate every pair not
  identified on Fix h form an open dense set, so a generic interior fixed
  point exists. Its level partition is cl(Fix h). Its quotient is acyclic,
  because edges go up in value, and no block contains a relation.
- *τ-stable.* (gx)_{τi} = εx_i, and the sign cancels in x_i = x_j.
- *Explicit form for −π.* An odd cycle forces x = 0 on it. An even cycle
  carries ±a, and different even cycles carry independent parameters. Note
  that cl(Fix(+π)) = 1̂ when π is an n-cycle, because Fix = 0. This agrees
  with cyc(π) = 1̂.

**Holds.**

**S5 / Lemma K_A.**
- *The cone R.* R is nonempty: take values increasing along a topological
  order of the acyclic quotient. It is convex, and it is g-stable for both
  signs. For ε = −1 the anti-automorphism reverses the strict inequalities,
  and the sign flips them back.
- *The averaged point.* The ⟨g⟩-average y* is constant on x-blocks. It is
  constant on cl(Fix g)-blocks because y* ∈ Fix g, and hence on w-blocks. It
  satisfies y* ∈ C_P, and y*_i < y*_j for some relation that crosses
  x-blocks. Such a relation exists because some component is not inside an
  x-block, and components are connected by comparabilities.
- *Its level partition.* The level partition lies in M, is ≥ x and ≥ w, and
  is ≠ 1̂.

Also, every partition ≥ κ is acyclic, so the complements in Lemma C(i) are
exactly the τ-stable partitions ≥ κ. **Holds.**

**Lemma C.**
- *Step 1.* A ⟨σ⟩-orbit of x-blocks has a σ-stable union, and the
  H-orbits stay inside it, so x ∨ w = 1̂ forces a single orbit of blocks.
- *Step 2.* ⟨σ^ℓ⟩ ⊆ ⟨σ^s⟩ iff s | ℓ, for divisors of o.
- *Step 3.* φ = j mod gcd(s, h) is well defined and constant on the blocks
  of x and of w.
- *Step 4.* σ^j q ∈ B iff s | j, and the H-orbit of q is {σ^j q : gcd(h, ℓ) | j}.
  So x ∧ w = 0̂ gives ℓ | lcm(s, gcd(h, ℓ)). Both numbers divide ℓ, and they
  are coprime by Step 3.
- *(ii) ⇒ (i).* The disjointness of the σ^jB uses only s | λ_{K_r} and the
  fact that distinct orbit representatives give distinct κ-blocks. The meet
  and join arguments run Step 4 backwards and use gcd(h, s) = 1.

The application uses w = cyc(τ^k), which is the orbit partition of
⟨τ^{gcd(k, o)}⟩. **Holds.**

## 2. The case analysis of Theorem TA-CR

**Exhaustion.** For g = +w, the zero set is "ord w not squarefree, or ⟨w⟩
not free on components" ([Thm, eq. closed]). F(P, g) ≠ ∅ iff the action is
free: if it is free, B_j = ∪_r g^j K_r is an element of F(P, g). For g = −τ,
the zero set is "some (TA1)–(TA4) fails" ([PCV] Theorem TA). "First matching
row" assigns each zero exactly one row:
- W+1 and W+2 split the +w zeros by freeness;
- W−1 to W−4 split the −τ zeros by the first failing condition.

The table's W−1 sub-cases are themselves exhaustive:
- o odd with |Λ| ≥ 2;
- Λ ⊆ {m, 2m} for an odd m, which is then unique, and not squarefree
  because (TA1) fails;
- o even and Λ in no such set.

Both cited zero sets were reproduced on every pair with n ≤ 7 (§4,
"criterion": 0 mismatches).

**Each witness is in M** (τ-stable and acyclic). Rows W+1 to W−3 are
cl(Fix g^k) for the stated k: W+1 with k = 1, W+2 with k = o/p, W−1 with k
even, W−2 and W−3 with k = 1. So they are in M by S4. The W−4 element is
τ-stable because O is. It is acyclic because every relation lies inside Q:
odd points are isolated when (TA4) fails. [AUD] checks W ∈ M on every zero.

**Each witness is uncomplemented.**
- *W+1.* h = 1 forces all ℓ = s = o and then λ_K = o, which is freeness.
  Correct.
- *W+2.* Freeness gives every ℓ = o. With h = o/p, every cycle of w^h has
  length p, and p | h because p² | o. Correct.
- *W−1.* With k = 2m/p, h = gcd(k, o) is m/p (o = m) or 2m/p (o = 2m). In both
  cases gcd(m, h) = m/p, because p is odd. So every cycle of τ^h has length
  s = p, and p | m/p | h. With k = 2, h = gcd(2, o), and (ii) would force
  Λ = {s} (o odd) or Λ ⊆ {s, 2s} with s odd (o even). Both are excluded in
  their sub-cases. Correct. W ≤ c because Fix g ⊆ Fix g^k.
- *W−2.* λ | o | 2m and λ ∉ {m, 2m} give m ∤ λ. Then τ^λ y ≠ y on an odd
  point, and τ^{2λ} y ≠ y in the same parity class on a 2m-cycle. So
  κ ∧ c ≠ 0̂, and S5 finishes. Correct.
- *W−3.* An odd point q ∈ τ^m K satisfies τ^{−m} q = q, so q ∈ K. Correct.
- *W−4.* a ≥ κ, so the join is the partition join (S2). A complement meets
  Q exactly once in each block: a block missing Q would survive in x ∨ a,
  since a is discrete on A_0. The resulting equivariant map φ contradicts
  τ^m = id on odd points against the 2m-cycles of Q. Correct.

**Converse.** An uncomplemented element forces μ = 0 by Crapo (CITED), hence
χ = 0 by S1 (CITED, [VC]). [AUD] checks both directions directly: μ(M) = 0
iff M has an uncomplemented element, on every pair with n ≤ 7.

**Dependence on the cited theorems.** The direction "χ = 0 ⇒ uncomplemented"
uses the *nonvanishing* halves of [Thm] and Theorem TA, through exhaustion.
The note says so. Those halves are audited elsewhere. [Thm] rests on the
cited inputs (JS)–(Hopf). This audit does not re-audit them. It reproduces
both zero sets for n ≤ 7.

**R1 (FIXABLE, remark only).** §3, *Remarks*, 2nd bullet says that W+1, W−2
and W−3 do not occur on all chambers (κ = 0̂). This is false for W+1. Take
the antichain on 3 points and g = +(0 1). Here ⟨w⟩ is not free on the points.
Π_3^{(01)} is the chain 0̂ < 01|2 < 1̂, so μ = 0, and cyc(w) = 01|2 is
uncomplemented. In general, on the antichain, W+1 occurs exactly when w has
two distinct cycle lengths. Lemma C(ii) then fails with h = 1 even at κ = 0̂,
so for W+1 the obstruction does not need κ either. For W−2 and W−3 the
remark is right: for singletons, λ is a cycle length, which lies in {m, 2m},
and K ∪ τ^m K has at most one odd point. The fix is to drop W+1 from that
sentence. No proof uses the remark.

## 3. The untested W−1 branch: Λ = {m, 2m}, m odd not squarefree

**Instance.** Take n = 27, P = the antichain on [27], and τ = (a_0 … a_8)(b_0 … b_17),
so g = −τ. Then:
- Λ = {9, 18}, and (TA1) fails because 9 is not squarefree;
- m = 9, p = 3, and k = 2m/p = 6;
- h = gcd(6, 18) = 6.

τ^6 splits the 9-cycle into 3 cycles {a_i, a_{i+3}, a_{i+6}}, and the 18-cycle
into 6 cycles {b_j, b_{j+6}, b_{j+12}}. So W = cyc(τ^6) has 9 blocks of size 3.

**Symbolic check.** By Lemma C, every cycle of τ^6 has length s = 3:
9/gcd(9, 6) = 3 and 18/gcd(18, 6) = 3. But gcd(3, 6) = 3 ≠ 1, so (ii)
fails. Concretely: by Steps 1 and 4, a complement would be one orbit of 3
blocks B, τB, τ²B, each meeting every W-block once. Step 3 then needs
gcd(3, 6) = 1. This symbolic check uses Lemma C. The machine check below
does not.

**Machine check ([AUD] part [BIG]).** For the antichain, M is the set of all
τ-stable partitions, and the join is the partition join. [AUD] enumerates
*every* τ-stable partition x of [27] with x ∧ W = 0̂. It does so by
breadth-first joins of the partitions generated by single ⟨τ⟩-orbits of
pairs. Every τ-stable partition is the join of the orbit-partitions of its
pairs, and x ∧ W = 0̂ is inherited by refinements, so the pruned search is
exhaustive. There are 11 such x, and none has x ∨ W = 1̂. **W is
uncomplemented**, as the theorem says.

**Controls on the same instance.**
- *Positive control.* With k = 2, W′ = cyc(τ²) has 3 blocks of size 9, and
  Lemma C(ii) holds (s = 9, h = 2). The search finds 9 complements. So the
  search can find complements.
- *k = 2 is not enough in this branch.* For the antichain on 9 points with
  τ = (9), k = 2 gives cyc(τ²) = 1̂, which is complemented. This is the
  author's example, and it is reproduced. k = 6 gives 3 blocks, which are
  uncomplemented.
- *Further instances of the branch.* All are uncomplemented, matching
  Lemma C:
  - τ = (18), k = 6;
  - τ = (9)(9)(18) at n = 36, k = 6, with 119 candidate x;
  - τ = (25), m = 25, p = 5, k = 10.

**Why the antichain covers every poset with this τ.** Rows W+1 to W−3 have
w ≤ c. By K_A, every complement in OP(P)^τ is a τ-stable x ≥ κ with
x ∧ W = 0̂ and partition join 1̂. That is a subset of the antichain's
complements of the same W. So "uncomplemented for the antichain" implies
"uncomplemented for every P on which τ is an anti-automorphism".

## 4. Recomputation ([AUD], n ≤ 7)

**Model.** [AUD] uses its own conventions throughout:
- *Posets.* It generates posets up to isomorphism by adding a maximal
  element over an order ideal. Canonical forms come from a permutation search
  inside refined invariant classes.
- *Symmetries.* It finds Aut(P) and the anti-automorphisms by backtracking,
  and reduces τ up to conjugation by Aut(P).
- *The lattice.* M is the set of τ-stable acyclic partitions. μ is computed
  by recursion. The *full* complement relation of M is computed by direct
  search.
- *Witnesses.* They are built from the table's text, not from the author's
  code. cl(Fix h) comes from exact rational linear algebra on
  Fix h ∩ R^n_0, not from the S4 formula. The formula is checked separately.

**Controls (all pass).**
- Poset counts 1, 1, 2, 5, 16, 63, 318, 2045 (OEIS A000112).
- μ(Π_n) = (−1)^{n−1}(n−1)! for n ≤ 6.
- Π_4^{(1234)} is a 3-chain with μ = 0 and its middle element
  uncomplemented. This is the positive control for "uncomplemented".
- Π_4 is complemented with μ = −6.
- OP(3-chain) has 4 elements and μ = 1.
- The F6 join example of [AudPCV].
- The fast join and meet equal the brute-force lub and glb on 61,545 element
  pairs (n ≤ 5).

**Sweep, n = 3..7, up to isomorphism and conjugacy** (archived in
`compute/output/audit_cr_v_type_a.txt`):

| n | pairs +w | pairs −τ | zeros +w | zeros −τ | W+1 / W+2 / W−1 / W−2 / W−3 / W−4 | cl(Fix g) complemented on zeros | Lemma C lattice checks (complemented) | K_A complements checked | failures |
|---|---|---|---|---|---|---|---|---|---|
| 3 | 9 | 5 | 3 | 2 | 3 / 0 / 0 / 0 / 0 / 2 | 2 | 38 (32) | 23 (all w <= c) | 0 |
| 4 | 34 | 16 | 16 | 6 | 15 / 1 / 3 / 0 / 1 / 2 | 4 | 150 (106) | 121 (all w <= c) | 0 |
| 5 | 144 | 30 | 80 | 19 | 80 / 0 / 7 / 0 / 2 / 10 | 11 | 595 (357) | 771 (all w <= c) | 0 |
| 6 | 758 | 108 | 432 | 49 | 432 / 0 / 23 / 2 / 14 / 10 | 15 | 3028 (1766) | 8595 (all w <= c) | 0 |
| 7 | 4804 | 246 | 2758 | 154 | 2758 / 0 / 69 / 0 / 30 / 55 | 61 | 17977 (10113) | 10554 (w = cl(Fix g^k)) | 0 |

Totals: 5,749 + 405 = 6,154 pairs; 3,289 + 230 = 3,519 zeros; 0 failures. Runtime 390 s for the whole script.

Checks run on every pair, with the count of failures over all n:
- CR_V in both directions (0);
- the zero criteria of [Thm] and (TA1)–(TA4) against μ = 0 (0);
- each zero lands in a row, and no row fires on a nonzero (0);
- W ∈ M (0);
- W uncomplemented (0);
- S4 for every k ≤ 2·ord τ: in M, ≤ c, antichain blocks, cyc form for even
  powers, and the −τ formula (0);
- Lemma C against the lattice for every orbit partition cyc(τ^k) (0);
- Lemma K_A on every complement of every w ≤ c (n ≤ 6), or of every
  cl(Fix g^k) (n = 7) (0).

**Agreement with the author's numbers.** The per-n pair counts, zero counts
and row counts (W+1 / W+2 / W−1 / W−2 / W−3 / W−4) equal [CVA-note] §4 for
every n = 3..7. The totals match too: 6,154 pairs and 3,519 zeros. So does
the count of zeros on which cl(Fix g) itself is complemented: 2, 4, 11, 15,
61, total 93, of which 79 are W−4, 13 are W−1 and 1 is W+2. My Lemma C
check counts differ from the author's 4,764 because I test every k in
1..2·ord τ, repeats included. This is a difference of bookkeeping, not of
outcome.

**Positive controls that must fail (all fire).** Run on n ≤ 6:
- Witness cl(Fix g) in every row: 32 failures, all W_COMPLEMENTED. This
  confirms that the exponent k in the table matters.
- Criterion without (TA4): 24 criterion mismatches.
- Plain partition join instead of the acyclic closure: 12 CR_V failures.
- k = 2 in row W−1: this cannot fire at n ≤ 7, because no odd non-squarefree
  m fits. It fires on −(9) at n = 9 (§3).

**Lemma C without posets ([LC]).** Every cycle type σ with n ≤ 7, every
σ-stable partition κ, and every h | o: 3,142 triples. Condition (i) was
checked by direct search over σ-stable x ≥ κ, against (ii). All agree, and
2,055 are complemented.

## 5. Side check: 5,063 or 3,576?

[PCV] §4 (and [CRV] §7) cite "all 5,063 lattices OP(P)^{±τ} with n ≤ 6".
- **The archived log.** `compute/output/per_cone_vanishing.txt`, the only
  version, from commit f46fb01, prints the CR_V tallies per n. Their sums
  are 20, 96, 478 and 2,982 for n = 3..6, a total of **3,576**. Of these,
  8 + 37 + 153 + 922 = 1,120 are −τ.
- **The code.** `part_TA` in `compute/per_cone_vanishing.py` loops over
  n = 3..6, over isomorphism classes, and over every automorphism and every
  anti-automorphism without conjugacy reduction. One CR_V tally is made per
  lattice, so the log's dicts count exactly these lattices.
- **Independent recount ([AUD] part [COUNT]).** Over my own isomorphism
  classes, Σ|Aut(P)| + Σ|Anti(P)| per n is 12 + 8, 59 + 37, 325 + 153 and
  2,060 + 922. That is 20, 96, 478 and 2,982, total **3,576**.

**3,576 is correct.** I did not find a count that gives 5,063. The
candidates tried were: adding n ≤ 2 (3,586); reducing by conjugacy (the
n = 3..6 rows of §4 give 1,104); and adding the −τ "pairs" lines (4,696) or
the n = 7 involution pairs (4,665) of the same log. None gives 5,063. The figure has no support in the
committed code or log, and should be replaced by 3,576. As the author notes,
the conclusion "no counterexample" is unaffected.

## 6. Remarks (not applied)

- R1 (§2): drop W+1 from the sentence "on all chambers these rows do not
  occur".
- [PCV] row CR_V and §4, and [CRV] §7: 5,063 → 3,576 (§5).
- [CVA-note] §4 "Not run": the n = 27 branch is now COMPUTED by this audit
  (§3).
- The [CVA-note] header "*Not yet independently audited*" can point here.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 audit_cr_v_type_a.py --nmax 7 > output/audit_cr_v_type_a.txt   # ~7 min, ends "ALL CHECKS PASSED", exit 0
    python3 audit_cr_v_type_a.py --nmax 6                                  # ~20 s
    python3 -m unittest test_audit_cr_v_type_a                             # < 1 s, positive and negative controls

`--budget SECONDS` bounds the sweep. If it runs out, the script prints UNRUN
and exits 1. `--kafull-nmax` (default 6) is the largest n on which K_A is
checked for every w ≤ cl(Fix g), and not only for cl(Fix g^k). `--skip-big`
omits part [BIG].

References: [CVA-note] = `notes/cr_v_type_a.md`; [PCV] =
`notes/per_cone_vanishing.md`; [AudPCV] = `notes/audit_per_cone_vanishing.md`;
[CRV] = `notes/conjecture_cr_v.md`; [VC] = `notes/vanishing_criterion.md`;
[Thm] = `notes/poset_jks_theorem.tex`; Crapo, J. Combin. Theory 1 (1966);
Whitney, Amer. J. Math. 55 (1933).
