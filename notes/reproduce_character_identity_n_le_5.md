# Independent reproduction of the character identity for n ≤ 5 (and n = 6)

Work item: mg-cfd00. Subject: the section "Computational evidence" of
`notes/poset_jks_research_note.tex` and its equation (characterconj):

    (-1)^{n-3} μ(OP(P)^g) = sgn(g) · Σ_{C ∈ Cyc(P), gC = C} ζ^{r_g(C)}     (g ∈ Aut(P)).

Each claim below is tagged PROVEN, COMPUTED, CITED or CONJECTURED.

## How to reproduce

Code: `compute/poset_jks_check.py`, written from scratch, plain Python 3, no
dependencies. Archived output: `compute/output/summary.txt` and
`compute/output/character_table.tsv`. Both come from one command, run in
`compute/` (it takes about 5 s):

    python3 poset_jks_check.py --nmax 6 --control-counts --examples \
        --tsv output/character_table.tsv > output/summary.txt

Tests: `python3 -m unittest test_poset_jks_check` (in `compute/`).

The table has one row per (poset, conjugacy class of Aut(P)). Its columns are
the cover relations, |Aut|, |OP|, |Lin|, e_C, the class representative and
cycle type, the class size, sgn, the number of g-fixed order-preserving
partitions, μ(OP(P)^g), the number of g-fixed cyclic classes, the rotation
multiset {r_g(C)} (written `r^mult`), both sides of the identity, and one
pass/fail column for each formula F0–F4 described below.

## What the program does

- **Posets.** All unlabeled posets are generated in two independent ways:
  - (A) Extension: add a new maximal element above an order ideal, then
    deduplicate by canonical form.
  - (B) Brute force: list the naturally labeled posets, take all of their
    relabelings, and deduplicate.
- **OP(P).** These are the set partitions π for which the block digraph
  (B → B′ when x <_P y for some x ∈ B, y ∈ B′, with B ≠ B′) has no directed
  cycle. μ(OP(P)^g) = μ(0̂, 1̂) is computed on the subposet of g-fixed
  partitions with the refinement order, using the recursion
  μ(0̂, x) = −Σ_{y<x} μ(0̂, y). Since 0̂ and 1̂ are always order-preserving and
  always g-fixed, μ(0̂, 1̂) is well defined.
- **Lin(P) and Cyc(P).** A linear extension is a word w = w_1⋯w_n, which is
  the same as the permutation position ↦ label. γ = (1 2 ⋯ n) acts on positions
  by w ↦ wγ^j, which turns w_1⋯w_n into w_{1+j}⋯w_n w_1⋯w_j. Cyc(P) is the set
  of these rotation orbits that meet Lin(P). An element g ∈ Aut(P) acts by
  w ↦ gw, which relabels the letters. For a fixed class, r_g(C) is the unique
  r with gw = wγ^r.
- **Exact comparison.** The right-hand side is kept as an integer vector
  (c_r)_{r ∈ Z/n}. The identity Σ c_r ζ^r = m holds exactly iff
  Φ_n(x) divides Σ c_r x^r − m. The program checks this with integer
  polynomial division by the cyclotomic polynomial Φ_n. Floating-point
  arithmetic is never used to decide the identity.
- **Independent check of the trace formula (eq. liechar).** For every class
  representative g, the program computes left multiplication by g on the basis
  {u_C e_ζ} of Lie(P) directly in C[S_n], with
  e_ζ = (1/n) Σ_j ζ^{−j} γ^j and ζ = e^{2πi/n}. It checks two things:
  - each g-fixed basis vector is scaled by exactly ζ^{r_g(C)};
  - the trace equals Σ ζ^{r_g(C)}.
- **Class functions.** The program evaluates the right-hand side on every
  element of every conjugacy class and asserts that it is constant on each
  class. The left-hand side is a class function by PROVEN reasoning: h maps
  OP(P)^g isomorphically onto OP(P)^{hgh⁻¹}, so it is evaluated only on class
  representatives.

## Results

**Poset enumeration matches OEIS (COMPUTED).** This is a control on the
enumeration. Methods (A) and (B) agree, and the counts match the OEIS
sequences A000112, A001035 and A006455.

| n | unlabeled (A) | unlabeled (B) | labeled (B) | naturally labeled (B) |
|---|---|---|---|---|
| 1 | 1 | 1 | 1 | 1 |
| 2 | 2 | 2 | 3 | 2 |
| 3 | 5 | 5 | 19 | 7 |
| 4 | 16 | 16 | 219 | 40 |
| 5 | 63 | 63 | 4231 | 357 |
| 6 | 318 | — | — | — |

So "5 + 16 + 63 = 84 types" in the note is all unlabeled posets with
3 ≤ n ≤ 5. The naturally labeled counts 1, 2, 7, 40, 357 agree with the note's
values of a_n.

**The character identity holds for all posets with n ≤ 5 (COMPUTED).** It
holds exactly for every g in every class, with 0 failures:

- 84 posets and 187 (poset, class) pairs for n = 3, 4, 5 (9 + 34 + 144 pairs);
- the degenerate cases n = 1 and n = 2 (1 + 3 pairs) also hold.

This reproduces the note's n ≤ 5 claim.

**The note's three n = 6 examples (COMPUTED).** All three satisfy the
identity. The five-armed star was run in both orientations, center below and
center above.

| poset | \|Aut\| | \|OP\| | \|Lin\| | e_C | nontrivial nonzero values |
|---|---|---|---|---|---|
| star, 1 < 2,…,6 | 120 | 203 | 120 | 120 | none (all 0) |
| star, 2,…,6 < 1 | 120 | 203 | 120 | 120 | none (all 0) |
| {1,2,3} < {4,5,6} | 36 | 125 | 36 | 36 | none (all 0) |
| 1<2, 3<4, 5<6 | 6 | 174 | 90 | 74 | g = (1 3 5)(2 4 6): μ = +1, rotations {2, 4}, both sides −1 |

The note's claim that "an automorphism cyclically permuting the three
components gives character value −1" is reproduced. In our convention the two
fixed classes have r = 2 and r = 4 (mod 6), so the sum is
ζ_6² + ζ_6⁴ = −1. That g is even, and the left-hand side is (−1)³ · μ = −1.

For the star and for K_{3,3}, every nonidentity element has 0 on both sides.
These examples therefore test only that μ(OP(P)^g) vanishes; they do not test
the phase.

**All 318 posets with n = 6 (COMPUTED, beyond the requested scope).** The
identity holds for all 318 posets and 758 (poset, class) pairs, with 0
failures. The run cost about 5 s, which is why it was included.

**Jenča–Sarkoci dimension and connected posets (COMPUTED, n ≤ 6).**
- (−1)^{n−3} μ(OP(P)) = e_C(P) holds for every poset (eq. JSdim), with
  0 failures.
- e_C(P) = |Lin(P)| holds for every connected P, with 0 failures.
- For disconnected posets the two quantities differ in 1, 2, 6, 19 and 80
  cases for n = 2, …, 6. (For example, the three 2-chains have |Lin| = 90 and
  e_C = 74.) So connectedness is genuinely needed.
- The JS dimension formula itself is CITED: Jenča–Sarkoci, JCTA 122 (2014).
  The page and theorem number were not re-checked here.

## Positive controls: the checker can fail

On the same data the program also evaluates four other formulas, which it
reports as F1–F4. F0 is the note's formula. "Fails" below means the exact test
rejects the formula on at least one (poset, class) pair. The table lists the
number of failing pairs and, in parentheses, the number of failing posets.

| formula | n=2 | n=3 | n=4 | n=5 | n=6 |
|---|---|---|---|---|---|
| F0: sgn(g) Σ ζ^{r} (note) | 0 | 0 | 0 | 0 | 0 |
| F1: sgn(g) Σ ζ^{−r} (opposite convention) | 0 | 0 | 0 | 0 | 0 |
| F2: Σ ζ^{r} (WRONG: sign twist dropped) | 1 (1) | 0 | 0 | 0 | 6 (5) |
| F3: sgn(g) · #fixed classes (WRONG: phase dropped) | 1 (1) | 1 (1) | 3 (2) | 1 (1) | 8 (6) |
| F4: μ without (−1)^{n−3} (WRONG) | 3 (2) | 0 | 18 (16) | 0 | 326 (318) |

**Which posets discriminate the phase, i.e. where F3 fails (COMPUTED).**
- n = 3, 4, 5:
  - the antichains, with g an n-cycle, and also g = (1 2)(3 4) for n = 4;
  - the poset 1<4, 2<3 (two 2-chains) with g = (1 2)(3 4): the fixed class
    has r = 2, so the sum is ζ_4² = −1, whereas the count is 1.
- n = 6: six posets, including the three 2-chains with g = (1 3 5)(2 4 6).
- The simplest case is the antichain with n = 3 and g = (1 2 3). The fixed
  classes have r = 1 and r = 2. The phase sum is −1, which agrees with
  μ(Π_3^g) = μ({0̂, 1̂}) = −1. The plain count is 2.

**Which posets discriminate the sign twist sgn(g), i.e. where F2 fails
(COMPUTED).** No poset with 3 ≤ n ≤ 5 does. The data for n ≤ 5 cannot tell
whether the factor sgn(g) is present. The first cases are at n = 6, with g of
cycle type (2,2,2) or (6):
- the antichain, with g = (1 2)(3 4)(5 6) giving +8 on both sides, and
  g = (1 2 3 4 5 6) giving −1;
- 1<4, 2<3 plus two isolated points (+4);
- two V's, 1<5, 1<6, 2<3, 2<4 (+2);
- two Λ's (+2);
- two 3-chains (+1).

The note's three n = 6 examples do not discriminate the sign twist either.

*Why (PROVEN).* The right-hand side at g is nonzero only if g fixes some
class, that is gw = wγ^r. Then g = wγ^r w⁻¹, so g has cycle type (d^{n/d})
with d = n / gcd(n, r). Such a g is odd iff d is even and n/d is odd.
- For n odd, this never happens.
- For n = 4, the only case is d = 4, a 4-cycle. A g that permutes all of P in
  a single orbit forces P to be an antichain: x < gx would give
  x < g^k x = x. For the antichain the sum is ζ_4 + ζ_4³ = 0.
- So the first nontrivial test is at n = 6.

## Pinning the sign/Fourier convention

1. **The scalar is ζ^{+r} (PROVEN, and COMPUTED by the explicit C[S_n] check).**
   Take e_ζ = (1/n) Σ_j ζ^{−j} γ^j as in the note. Then γ^r e_ζ = ζ^r e_ζ
   exactly. This uses only powers of γ, so it does not depend on the
   composition convention. With the composition (pq)(i) = p(q(i)) and words
   read as position ↦ label, wγ^r is the word rotated left by r. So
   g(we_ζ) = wγ^r e_ζ = ζ^r we_ζ when gw = wγ^r.

   The program confirms the scalar ζ^{r_g(C)} vector by vector, for every
   class representative of every poset. A unit test also confirms it for
   n = 3: one fixed class has scalar ζ and the other ζ², not the reverse.
   This is what the note writes ("w γ^j e_ζ = ζ^j w e_ζ"), so no correction is
   needed under these conventions.

2. **The identity cannot depend on the choice of ζ (PROVEN, and COMPUTED as
   F1 passing everywhere).** The left-hand side is a rational integer. Any
   Galois automorphism ζ ↦ ζ^k with gcd(k, n) = 1 fixes it and turns
   RHS(ζ) into RHS(ζ^k). So if the identity holds for one primitive ζ, it
   holds for all of them. The case k = −1 covers both of the following:
   - ζ versus ζ^{−1}, or equivalently e_ζ defined with ζ^{+j};
   - rotating left versus right, i.e. r versus −r.

   No test case can distinguish these conventions. Only the trace-free,
   vector-level check in item 1 sees the difference.

3. **Rotating positions is forced; rotating values is not a valid
   alternative (PROVEN).** Suppose one used left orbits C_n w (rotating
   values) instead. Then g maps C_n w to (gC_n g⁻¹)(gw). This is a left
   C_n-coset only if gC_n g⁻¹ = C_n. (If Hx = Ky for subgroups H and K, then
   H = K.) So Aut(P) does not act on the value-rotation classes unless
   Aut(P) ≤ N_{S_n}(C_n). The convention in the note — rotate positions, act
   by g on values — is the only one of the two under which equation
   (characterconj) is even well posed. Writing linear extensions as
   label ↦ position maps σ = w⁻¹ just transposes everything: rotation then
   acts on the left and g acts on the right. That is the same convention
   written differently.

## What disagreed with the note

Nothing in the note's computational claims was contradicted. Two points
refine it:

- The n ≤ 5 data do **not** test the sgn(g) twist at all; see the PROVEN
  argument above. The twist is first tested at n = 6, by the antichain and by
  four other posets — none of which is among the note's three examples. The
  identity, with the twist, holds on all of them.
- The phase is already discriminated at n = 3, by the antichain. It is not
  first discriminated by the n = 6 three-2-chains example; that example is
  just one more phase test.

## Status of the conjecture after this item

Equation (characterconj) is COMPUTED to hold for every poset with n ≤ 6,
using this code and the command above. As a statement for all n it remains
CONJECTURED.

What this item does *not* do: it does not compute homology directly. It
relies on the Lefschetz/Hopf trace formula and on the fact that homology is
concentrated in top degree (CITED: Jenča–Sarkoci) to identify
(−1)^{n−3} μ(OP(P)^g) with the character χ_{H_P}(g).
