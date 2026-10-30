# The character identity at n = 7, and a direct equivariant-homology cross-check

Work item: mg-6bbe0 (research step 4 of `notes/poset_jks_research_note.tex`).
Subject: equation (characterconj) of the note,

    (-1)^{n-3} μ(OP(P)^g) = sgn(g) · Σ_{C ∈ Cyc(P), gC = C} ζ_n^{r_g(C)}     (g ∈ Aut(P)),

and the left side's interpretation as the character χ_{H_P}(g) of
H_P = H̃_{n-3}(Δ(proper part of OP(P))).

Every claim is tagged PROVEN, COMPUTED, CITED or CONJECTURED. Conventions
(words, γ, r_g(C), ζ) are those of `compute/poset_jks_check.py` and
`notes/reproduce_character_identity_n_le_5.md`.

## Summary

1. **n = 7, all 2045 unlabeled posets, all 4804 (P, g-class) pairs:** the
   identity holds with 0 failures (COMPUTED).
2. **But n = 7 barely tests the refinement.** Exactly one nonidentity pair has
   a nonzero character, the antichain with g a 7-cycle. That case is the
   classical Joyal–Klyachko–Stanley case. The sign factor is never tested,
   and the phase is tested only on the antichain. This follows from a general
   lemma (PROVEN, §2), not from luck. For prime n, everything the
   conjecture says beyond Jenča–Sarkoci and classical JKS is the vanishing
   statement μ(OP(P)^g) = 0 for g ≠ 1. That vanishing was checked on all
   2758 nonidentity pairs at n = 7 that are not the antichain's 7-cycle.
3. **The sign can only be tested at n even and not a power of 2** (beyond
   the antichain). So n = 8 cannot test it either. The next sizes that do are
   n = 10, 12, and 14 (PROVEN, §2).
4. **Direct homology cross-check of the left side (COMPUTED).** I wrote a
   separate program that computes trace(g | ker ∂_top) on the order complex
   without Möbius numbers or Lefschetz. It agrees with (-1)^{n-3} μ(OP(P)^g) on
   **every** (P, g-class) pair for n = 4, 5, 6 (34 + 144 + 758 pairs, plus the 26 rows
   for the named n = 6 examples), including all 8 discriminating n = 6 pairs.
   It also agrees on **all 4804 (P, g-class) pairs at n = 7** (2045 posets),
   including the one discriminating n = 7 pair.
   No counterexample appeared.

## 1. Programs and how to reproduce

All in `compute/`. Plain Python 3, no dependencies. See `compute/README.md`.

| file | role |
|---|---|
| `n7_sweep.py` | Enumerates all unlabeled posets on 7 points (extension method + a faster canonical form). Calls `poset_jks_check.analyse` (the mg-cfd00 checker) on each, tallies the controls F1–F4, and tags the named symmetric families. |
| `equivariant_homology.py` | Second, separate instrument for the left side: the trace of g on ker(∂: C_{n-3} → C_{n-4}). It has its own OP(P) enumeration (Kahn's algorithm, not DFS), its own chains, and its own linear algebra. |
| `test_n7_and_homology.py` | Tests: OEIS counts through n = 7; the fast canonical form and automorphisms against brute force (n ≤ 5); the JKS closed-form positive control; a corrupted-boundary negative control. |

Commands (run in `compute/`):

    python3 n7_sweep.py --n 7 --jobs 3 --tsv output/n7_character_table.tsv > output/n7_summary.txt
    python3 equivariant_homology.py output/character_table.tsv --select all --n 6 \
        --out output/n6_homology_all.tsv > output/n6_homology_all.txt
    python3 equivariant_homology.py output/character_table.tsv --select discriminating --n 6 \
        --with-identity --out output/n6_homology_discriminating.tsv > output/n6_homology_discriminating.txt
    python3 equivariant_homology.py output/n7_character_table.tsv --select all --n 7 \
        --out output/n7_homology_all.tsv > output/n7_homology_all.txt
    python3 -m unittest test_n7_and_homology test_poset_jks_check

Archived tables:

- `output/n7_character_table.tsv`. One row per (poset, conjugacy class of
  Aut(P)) at n = 7, 4804 rows. The columns are the same as mg-cfd00's table:
  covers, |Aut|, |OP|, |Lin|, e_C, class representative, cycle type, class
  size, sgn, #OP(P)^g, μ(OP(P)^g), #{C : gC = C}, the rotation multiset
  {r_g(C)}, LHS, RHS, and pass/fail for F0–F4. The last column is the
  symmetric family name, if any.
- `output/n7_summary.txt`. Totals, control tallies, discriminating pairs, the
  family list, and timing.
- `output/n{6,7}_homology_*.tsv/.txt`. For each pair: the number of top
  simplices, the primes used, the multiplicity N_k of each eigenvalue ω^k on
  H_{n-3}, the homology trace, the μ-side value, and agreement.

## 2. Which (P, g) can discriminate at all (PROVEN)

**Lemma 1.** Suppose g ∈ Aut(P), g ≠ 1, fixes a cyclic class C. Then g is
fixed-point-free with all cycles of one length d > 1 (cycle type d^{n/d}), and
sgn(g) = (-1)^{(d-1)n/d}. Each g-orbit is an antichain of P.

*Proof.* Take w ∈ C with gw = wγ^r. Then g = wγ^r w^{-1} is conjugate in
S_n to γ^r. Since γ is an n-cycle, γ^r has cycle type d^{n/d} with
d = n/gcd(n, r). If d = 1 then g = 1, so d > 1. A d-cycle has sign
(-1)^{d-1}, and there are n/d of them. For the last claim, suppose
a <_P g^s a. Applying g^s repeatedly gives
a < g^s a < g^{2s} a < ⋯ < g^{ds} a = a, which contradicts
antisymmetry. ∎

Consequences, with RHS(g) := sgn(g) Σ_{gC=C} ζ^{r_g(C)}:

- **(a) Phase.** For g ≠ 1 every fixed class has r_g(C) ≠ 0, because r = 0
  forces gw = w and hence g = 1. So whenever g ≠ 1 fixes a class,
  Re Σ ζ^r < #{C : gC = C}. The plain-count control F3 therefore fails
  exactly on the pairs with g ≠ 1 that fix at least one class. Those are
  exactly the pairs with g of type d^{n/d} and a fixed class.
- **(b) Sign.** The no-sign control F2 can differ from F0 only where
  sgn(g) = -1 and Σ ζ^r ≠ 0. By Lemma 1 this needs d even and n/d odd.
  - If n is odd, d is odd, so g is even and **F0 ≡ F2 identically**. The
    sign factor carries no information at odd n.
  - If n = 2^a, then n/d odd forces d = n. So g is an n-cycle and P is an
    antichain (one orbit, which is an antichain). The sign is tested only by
    classical JKS.
  - So the sign is tested on a non-antichain poset only if n is even and not
    a power of 2: n = 6, 10, 12, 14, …. Here g has n/d ≥ 3 odd cycles of
    even length d.
- **(c) Prime n.** If n is prime, then d = n, so g is an n-cycle and P is the
  antichain. Hence for every non-antichain P and every g ≠ 1 we get
  RHS(g) = 0, and the conjecture at that P says exactly μ(OP(P)^g) = 0. For
  the antichain, the identity is the classical JKS character, which is CITED
  below and also checked in the tests.
- **(d) Conjugate convention.** F1 (ζ^{-r}) is redundant whenever F0 holds:
  F0 makes Σ ζ^r a rational integer, so its complex conjugate Σ ζ^{-r} is
  the same integer. F1 can never be the only failing formula.
- **(e) Degree sign.** F4, which drops (-1)^{n-3}, is vacuous at odd n.

These facts explain the mg-cfd00 control tallies: F2 fails 0 times at
n = 3, 4, 5. They also predict the n = 7 tallies below before any
computation.

## 3. n = 7 results (COMPUTED)

Source: `output/n7_summary.txt`.

- Enumeration: 2045 unlabeled posets on 7 points, which matches OEIS A000112.
  The fast canonical form reproduces the counts 1, 2, 5, 16, 63, 318 for n ≤ 6.
  For n ≤ 6 its isomorphism classes coincide with those of the mg-cfd00
  brute-force canonical form, and the fast automorphism groups equal brute
  force for n ≤ 6 (unit test for n ≤ 5; one-off run for n = 6).
- 4804 (P, g-class) pairs, of which 2759 have g ≠ 1.
- **F0 (the note's identity) fails on 0 pairs.**
- The Jenča–Sarkoci dimension (-1)^{n-3} μ(OP(P)) = e_C(P) holds for all 2045
  posets. e_C = |Lin| holds for every connected P. 395 disconnected P have
  e_C ≠ |Lin|.
- Controls, failing pairs / posets:

  | control | n=7 |
  |---|---|
  | F1 ζ^{-r} | 0 / 0 |
  | F2 no sgn | 0 / 0 |
  | F3 plain count (phase dropped) | 1 / 1 |
  | F4 no (-1)^{n-3} | 0 / 0 |

- The only nonidentity pair with a nonzero character is the antichain with
  g = (1 2 3 4 5 6 7). There μ(Π_7^g) = -1, the six fixed classes have
  rotations {1, 2, 3, 4, 5, 6}, and both sides equal -1. This is also the only
  discriminating pair. Lemma 1(c) predicts exactly this.
- All 2758 other nonidentity pairs have μ(OP(P)^g) = 0 = RHS.

**Named symmetric families (COMPUTED).** These are all inside the 2045 and
are tagged in the table's `family` column. They include:

- unions of equal chains plus points (7 one-point chains, i.e. the antichain;
  2×2-chain+3pt; 3×2-chain+1pt; 2×3-chain+1pt);
- all 63 complete layered posets (ordinal sums of antichains, compositions
  of 7, including the claws 1+6 and 6+1 and the 7-chain);
- the crowns: crown3+1pt, and the 2+2 crown (=K_{2,2}) with 3 points;
- the products chain2×chain2+3pt and chain2×chain3+1pt;
- the Boolean square with a 3-antichain above or below it;
- the spiders with 3 arms of length 2 and with 2 arms of length 3;
- two 3-chains with a common top or a common bottom.

All of them pass F0. Except for the antichain, every one has character 0 at
every g ≠ 1, as Lemma 1(c) forces. Products like (2×2)×antichain need
n ≥ 8, and "k equal m-chains" with km = 7 exists only for the
antichain and the 7-chain, since 7 is prime. At n = 7 the large-|Aut(P)|
families therefore test only vanishing.

## 4. Direct homology cross-check of the left side (COMPUTED)

**What is computed.** H_{n-3} = ker(∂: C_{n-3} → C_{n-4}) for the order
complex of the proper part of OP(P). This is exact, with no theorem needed,
because the complex has no (n-2)-simplices: a chain in the proper part has
at most one partition of each block count 2, …, n-1. The trace of g on that
kernel is computed as follows.

- g permutes the oriented top simplices with no signs, because it preserves
  the vertex order of a chain.
- Let m = ord(g) and pick a prime p ≡ 1 (mod m), together with a primitive
  m-th root ω ∈ F_p. For each k, the ω^k-eigenspace of C_{n-3} has basis
  Σ_j ω^{-kj} g^j c over the g-orbits of top chains.
- ∂ maps this eigenspace into the ω^k-eigenspace of C_{n-4}. Its matrix there
  has entries equal to the coefficients at orbit bases. Its nullity N_k is the
  multiplicity of ω^k on H_{n-3}.
- trace = Σ_{d | m} μ_{Möbius}(d) · N_{(primitive d-th roots)}. The program
  asserts that N_k is constant on Galois orbits, i.e. on k with equal
  gcd(k, m).

**Why the mod-p answer is the characteristic-0 answer.** Each eigenspace
matrix reduces a matrix over Z[ζ_m] modulo a prime above p. Rank can only
drop under reduction, so N_k(F_p) ≥ N_k(ℂ) for every k. The program also
runs g = 1, which gives Σ_k N_k(F_p) = dim_{F_p} ker ∂ for the integer
matrix ∂. In every case checked this equals e_C(P), and by Jenča–Sarkoci
(CITED, JCTA 122 (2014); theorem number not rechecked) e_C(P) is
dim_ℂ H_{n-3} = Σ_k N_k(ℂ). Since each N_k(F_p) ≥ N_k(ℂ) and the sums are
equal, every N_k(F_p) = N_k(ℂ). So the traces are exact in characteristic 0,
conditional only on that cited dimension. Without the citation they are
values mod a prime of good reduction, which is very likely but not certain.
Every row was computed with two different primes p ≈ 10^6, p ≡ 1 mod m, and
the resulting traces were identical. The program refuses to report a trace
if the two primes disagree.

**Note on the Lefschetz route.** The μ-side uses
Σ_i (-1)^i tr(g | H̃_i) = μ(OP(P)^g) (Lefschetz/Hopf trace plus the fixed-
point subcomplex = Δ of the fixed subposet) *and* concentration of homology
in degree n-3. The homology instrument uses neither. Agreement on every pair
therefore also certifies, for these (P, g), that the lower-degree homology
contributes nothing to the alternating trace. (It does not certify that the
lower homology vanishes, only that its alternating trace is zero. The vanishing
is Jenča–Sarkoci's wedge-of-spheres theorem, CITED.)

**Controls on the instrument (COMPUTED, `test_n7_and_homology.py`).**
- *Positive control (JKS).* For the antichain at n = 3, 4, 5, 6, and every
  conjugacy class of S_n, the trace equals sgn(g) · χ_{Lie_n}(g). Here
  χ_{Lie_n}(g) = μ(d)(n/d − 1)! d^{n/d−1} if g has type d^{n/d}, and 0
  otherwise. This is CITED as the classical character of Lie_n (Klyachko
  1974; see also Stanley, "Some aspects of groups acting on finite posets",
  JCTA 32 (1982), and Hanlon 1981); the exact theorem numbers were not
  rechecked. The formula is evaluated by its own code, independent of both
  instruments.
- *Negative control.* Dropping one face map from ∂ changes the n = 5
  antichain's dimension from 24 to 50. It also changes the phase-
  discriminating value for the three 2-chains with g = (1 3 5)(2 4 6) from
  -1 to +1. So the instrument does detect a wrong boundary.
- *A control that turned out invalid, and why.* Dropping the face signs
  (-1)^i does **not** change the answer (24 at n = 5, 120 at n = 6). This
  is PROVEN to be no accident. Every face of a top chain misses exactly one
  rank i, and rescaling the face-basis element missing rank i by (-1)^i
  conjugates the signed top boundary into the unsigned one, so the kernels
  are isomorphic. It is therefore not used as a control.

**Results.**

| scope | pairs | agree | disagree | notes |
|---|---|---|---|---|
| n = 4, all | 34 | 34 | 0 | `--select all --n 4` on `output/character_table.tsv` (not archived; < 1 s) |
| n = 5, all | 144 | 144 | 0 | likewise (< 1 s) |
| n = 6, all 318 posets + named examples | 784 | 784 | 0 | `output/n6_homology_all.*`, ~20 s |
| n = 6, discriminating (F2 or F3 fails) + their g = 1 | 16 | 16 | 0 | `output/n6_homology_discriminating.*` |
| n = 7, all 2045 posets, every class (incl. g = 1) | 4804 | 4804 | 0 | `output/n7_homology_all.*`, 3 shards, ~13 min wall |

For every g = 1 row, the homology dimension equals e_C(P), at n ≤ 7. The n = 7
discriminating pair (antichain, 7-cycle) has multiplicities N_k = 102, 103, …,
103 on H_4 (dimension 720), so trace = 102 − 103 = −1. This equals the μ-side
and the RHS.

*Bug found and fixed during this work (recorded for honesty).* In the first
full run, the "second prime" was the same prime as the first for every g of
order ≥ 3, because `prime_1_mod(m, p+1)` rounded back down to p. The tables
showed this (e.g. `primes = 1000133,1000133`). The function now returns the
smallest prime ≥ start that is ≡ 1 mod m. `homology_trace` asserts that the
primes are distinct, and a unit test covers it. All archived homology
outputs were regenerated after the fix. The traces did not change. The
exactness argument above never relied on the second prime.

The 8 discriminating n = 6 pairs, with the multiplicities N_k of ω^k on
H_3 (k = 0, …, m−1). Source: `output/n6_homology_discriminating.txt`.

| poset (covers) | g | sgn | fixed classes, rotations | N_k | trace H_3 | μ-side | RHS |
|---|---|---|---|---|---|---|---|
| antichain | (12)(34)(56) | − | 8 × r=3 | 64, 56 | 8 | 8 | 8 |
| antichain | (123)(456) | + | r ∈ {2³, 4³} | 38, 41, 41 | −3 | −3 | −3 |
| antichain | (123456) | − | r ∈ {1, 5} | 20,19,22,18,22,19 | −1 | −1 | −1 |
| 1<4, 2<3 (+2 points) | (12)(34)(56) | − | 4 × r=3 | 52, 48 | 4 | 4 | 4 |
| 1<5,1<6,2<3,2<4 (two copies of "1 below 2") | (12)(35)(46) | − | 2 × r=3 | 39, 37 | 2 | 2 | 2 |
| 1<6, 2<5, 3<4 (three 2-chains) | (123)(465) | + | r ∈ {2, 4} | 24, 25, 25 | −1 | −1 | −1 |
| 1<6,2<6,3<5,4<5 (two copies of "2 below 1") | (13)(24)(56) | − | 2 × r=3 | 39, 37 | 2 | 2 | 2 |
| 1<2<6, 3<4<5 (two 3-chains) | (13)(24)(56) | − | 1 × r=3 | 10, 9 | 1 | 1 | 1 |

The six rows with sgn = − are exactly the n = 6 pairs where the sign factor
matters, i.e. where F2 fails. This matches mg-cfd00's tally of 6 pairs on
5 posets. Two of them, the antichain's 2³ and 6-cycle classes, are
classical JKS. The other four are non-antichain posets with g of type 2³,
consistent with Lemma 1(b). Each is Q ⊔ Q, with g swapping the two copies,
for Q one of the four non-antichain 3-element posets: 2-chain + point,
"1 below 2", "2 below 1", and the 3-chain. The note's own example, three disjoint 2-chains,
appears twice in mg-cfd00's table, as n6_057 and as the named example. Its
g is even, so it tests the phase but not the sign.

## 5. Runtime scaling (COMPUTED, this machine, single-threaded Python)

- **Enumeration** (fast canonical form): 0.3 s for all posets up to n = 7.
  The old brute-force canonical form over all of S_n would cost
  8! = 40320 relabelings per candidate at n = 8. The cell-refinement form only
  pays n! for the antichain-like posets.
- **Character checker** (`poset_jks_check.analyse`, both sides, including the
  explicit C[S_n] trace check): n = 6 takes ~5 s in total (mg-cfd00's figure,
  not re-measured). At n = 7 the total is 205 s CPU, 68 s wall on 3 workers.
  The median is 0.08 s per poset. The maximum is 7.5 s, for the antichain
  (|OP| = 877, 15 classes, |Aut| = 5040 automorphisms tested for class
  functions). The cost is dominated by the O(|OP|²) Möbius recursion and by
  scanning n! words for Lin(P).
  - Rough n = 8 extrapolation: |OP| ≤ B_8 = 4140, i.e. (4140/877)² ≈ 22× more
    per Möbius call, and 8× more words. There are 8.3× as many posets (16999).
    A full n = 8 sweep with this code is plausibly ~10 CPU-hours. A targeted
    run restricted to posets with a fixed-point-free automorphism of type 2⁴
    or 4² (§7) would be far cheaper. This is an estimate, not a measurement.
- **Homology instrument**: n = 6, all 784 rows, ~20 s. n = 7, all 4804 rows,
  2270 s CPU (≈ 13 min wall on 3 shards). That is at most 3.7 s per row; the
  largest complex is the n = 7 antichain with 56700 top simplices. Sparse
  elimination mod p shows little fill-in at this size. At n = 8 the antichain
  has 8!·7!/2⁷ = 1,587,600 top simplices (28× n = 7), so a targeted n = 8 run
  of this instrument on discriminating pairs only is feasible. Running it on
  all pairs is probably not worthwhile (an estimate, not measured).

## 6. What this does and does not establish

- PROVEN: Lemma 1 and consequences (a)–(e). Also the sign-insensitivity of
  the top kernel under removing face signs.
- COMPUTED: for all posets with n ≤ 7, eq. (characterconj) holds for every
  g ∈ Aut(P), with the right side from the mg-cfd00 checker. For n ≤ 6 the
  left side is now confirmed twice: once via μ and once via a direct trace
  on homology. For n = 7 the same double confirmation holds for all 4804 pairs.
- Not established: anything at n ≥ 8. Because of Lemma 1, the n = 7 sweep
  adds no test of the sign factor and only one, classical, test of the
  phase. What it does add is a large test of the vanishing μ(OP(P)^g) = 0
  for g ≠ 1 (2758 pairs).
- CONJECTURED (not part of the note): the vanishing μ(OP(P)^g) = 0 whenever
  g ≠ 1 is not of type d^{n/d} with a g-fixed linear-extension class. This is
  the RHS = 0 case of the conjecture, and it is checked through n = 7. It
  might have a direct proof by a fixed-point-free action on OP(P)^g, or by a
  closure / complementation argument. It is a natural first sub-target for
  research step 1 of the note.

## 7. Recommendation for the n = 8 item

- n = 8 (16999 posets) **cannot test the sign** beyond the antichain
  (Lemma 1(b): 8 is a power of 2). It can test the phase on non-antichain
  posets with g of type 2⁴ or 4². To reach these cheaply, restrict to posets
  admitting a fixed-point-free automorphism of type 2⁴ or 4². Every other
  g ≠ 1 needs only μ(OP(P)^g) = 0.
- The first n after 6 that tests the sign on a non-antichain is n = 10, with
  g of type 2⁵ (an odd permutation). Candidates are P = Q ⊔ Q with g the
  swap, for Q any 5-element poset (63 choices), together with the posets
  that have a fixed-point-free involution with antichain orbits. At n = 6
  the sign-discriminating non-antichain pairs were exactly Q ⊔ Q with the
  swap, for all four non-antichain 3-element Q (table in §4). This suggests
  that the 63 posets Q ⊔ Q at n = 10 are the most valuable next experiment.
  A full sweep is not needed, and those are also cheap. n = 12 (types 4³ and
  2⁶) and n = 14 come next. Whether each such pair actually has a fixed class
  (nonzero RHS) is not known in advance; that is part of the experiment.
