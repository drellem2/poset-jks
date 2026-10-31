# Audit: reciprocity for the cyclic order polynomial

Independent, adversarial audit of `notes/reciprocity_omega_c.md` ([R],
merged c8950e7). Every proof in [R] was re-read line by line. Every count
was recomputed with new code, `compute/audit_reciprocity_omega_c.py`, which
imports nothing from the repo and works from the definitions only. Bracketed
labels refer to `compute/output/audit_reciprocity_omega_c.txt`. Work item
mg-b2b04.

## Verdicts

| Claim | Verdict | Basis |
|---|---|---|
| Theorem R: (−1)^n Ω_C(P, −m) = Ω̄_C(P, m), every P, every T | **HOLDS** | Proof checked (§1). Recomputed on all 3107 (P, T) with n ≤ 7, 0 bad, and with a fully literal count over **all** maps P → [m], m ≤ n + 1, on every (P, T) with n ≤ 6, 0 bad / 555 bad |
| Lemma R1 (weak words, λ_T) | **HOLDS** | Proof checked, isolated-T case included (§1). 0 bad / 5 928 325 (surjective weak map, T) cases, n ≤ 7 |
| Lemma R2 (strict words, λ_T) | **HOLDS** | Proof checked, isolated-T case included (§1). 0 bad / 2 742 962 (surjective strict map, T) cases, n ≤ 7 |
| R′ (cdes form of Ω̄_C) | **HOLDS** | Two-line consequence of R and Theorem H (§2); recomputed under λ_0, 0 / 2449 bad. Minor gap: "Ω̄_C(P, 1) = 0" needs cdes ≤ n − 1, not the stated 1 ≤ cdes ≤ n (true, one line) |
| B⁺ (h_C = des on B_T under λ_T, every T) | **HOLDS** | Immediate from R1 + Theorem Ω (§2); 0 / 3107 bad |
| ★ Ω_C(P*) = Ω_C(P) | **HOLDS** | The one-line proof is complete (§3); 0 / 2450 bad |
| E (Ehrhart–Macdonald for the non-convex R_T) | **HOLDS** | Interior identification checked (§4), non-convex example verified, interior description sampled (700 sampled points, 0 disagreements). The reciprocity is legitimate as stated because it is *derived from* R, not from a general Ehrhart theorem |
| S (height ≤ 2 ⇒ Ω̄_C(m) = Ω_C(m − 1), h palindromic) | **HOLDS** | Bijection checked by hand (§5) and map by map (355 653 maps, 0 bad); identity on all 256 height-≤ 2 posets n ≤ 7 |
| S′ (palindromic classification, COMPUTED n ≤ 7) | **HOLDS as computed** | 0 mismatches on 2449 posets |
| Refutation: naive transplant, A_2 by hand | **HOLDS** (refutation correct) | §6; [ctl-naive] |
| Refutation: "lower-level-set version" | **FIXABLE** (wording) | The version tested (strict maps, lower level sets, strict `<`) fails, as stated. But the *D_T-type* lower version (≤) is TRUE on every pair: it is R for P* via ★ and f ↦ m+1−f (§6). The Verdict sentence "the dual condition does **not** move to lower level sets" overstates this |
| Refutation: h_C(P*) = reverse | **HOLDS** (refutation correct) | ★ gives h_C(P*) = h_C(P); reverse fails on 1875 |
| Extra (pm-poset): two-component identity h_C(Q ⊔ T) = W_P − t W_Q W_T | **HOLDS** | Proof checked (§7); 0 bad / 391 two-component posets n ≤ 7 |

No claim FAILS. The single FIXABLE item is a sentence of interpretation,
not a theorem.

## 1. Lemmas R1, R2 and Theorem R

Conventions as in [R] §0. I checked each step; the points where the choice
of labelling is used are listed, since that is where a gap would hide.

**R1, "w ∉ B_T ⇒ not anchored".** The case min f(U) = max f(P∖U) is the
only delicate one. With x = first letter of the last piece c and y the
letter before it, f(x) = f(y) forces λ(y) < λ(x). y is maximal (last
letter of a piece), x is minimal and not T's point (c misses T). The
argument needs: *every non-isolated minimum is labelled below every
maximal element* (rules out x a non-isolated minimum), and *every isolated
point other than T is labelled below every non-isolated maximum and below
T's point* (used for the top fibre L). λ_T satisfies both; λ_0 satisfies
the first but not the second when T is isolated. The top-fibre step uses
that a non-isolated minimum or middle element z with f(z) = max f has a
maximal z′ > z at the same value, and z′ lies in a non-singleton component,
so it is a non-isolated maximum (it cannot be T's point). Correct. P ∖ L ∋ T
is nonempty, so L is a genuine violating cluster.

**R2, "D_T fails ⇒ w̄ ∉ B_T", case min f(U) = v.** Checked:
- x ∈ F ∩ U is minimal (anything below it is in U with value < v ≤ min f(U)),
  y ∈ F ∖ U is maximal (dually). So F has no middle element and all its
  non-isolated minima lie in U.
- S = f^{−1}((v, m]) ∪ {non-isolated minima of F} equals U minus the
  isolated points of U at value v, and contains every non-singleton
  component inside U. So S is a T-free union of components.
- S is a suffix of w̄: within F the strict word sorts by decreasing label,
  and the non-isolated minima carry the smallest labels (true for λ_T).
- S ≠ ∅: S is proper (P ∖ U ≠ ∅), so a cut sits at n − |S|.
- S = ∅: then F is the top fibre, U ⊆ F consists of isolated points ≠ T,
  and the last letter of w̄ is the smallest label in F. This is exactly
  where λ_T is needed: isolated points ≠ T must be labelled below the
  non-isolated maxima **and below T's point**. Under λ_0 with T isolated
  and labelled below some other isolated point in F, the last letter can be
  T itself, and the lemma fails. My control reproduces this: [ctl-lam0]
  fires on 13 488 (map, T) cases (n ≤ 7; [R] reports 28 044 under its own
  λ_0 convention. My λ_0 orders the isolated points by element index, so the
  count is not expected to match exactly).

The isolated-T case is therefore sound under λ_T, and genuinely fails
without it. λ_T is natural (T's point is unrelated to everything, so it may
go last).

**Theorem R.** The weak and strict Stanley counts C(m + n − 1 − des, n) and
C(m + des, n) are right (choose a weakly increasing sequence with
respectively des, n − 1 − des forced strict steps). Theorem Ω + R1 gives
Ω_C = Σ_{B_T} C(m + n − 1 − des w, n); R2 gives Ω̄_C = Σ_{B_T} C(m + des w, n)
for m ≥ 1, and both sides vanish at m = 0 since des ≤ n − 1. The sign
identity C(−y, n) = (−1)^n C(y + n − 1, n) with y = m − n + 1 + des is
correct. n = 1: Ω_C = m (OP has one partition), Ω̄_C = m. **HOLDS.**

Recomputation:
- [omega]: Theorem Ω (literal count of anchored maps) equals the Möbius
  definition on every (P, T), n ≤ 7. This validates my Möbius code.
- [R-surj]: Ω̄_C from a literal enumeration of strictly order-preserving
  surjections onto [k], k ≤ n, tested for D_T by brute force over every
  T-free cluster, then Σ_k s_k C(m, k), compared with (−1)^n Ω_C(P, −m) at
  m = 0, …, n + 1 (n + 2 points; both sides have degree ≤ n, so this is an
  identity of polynomials).
- [R-all]: independently of the surjective reduction, every strictly
  order-preserving f : P → [n + 1] was enumerated, D_T tested directly, and
  the counts for each m ≤ n + 1 read off from max f (D_T does not depend on
  m). n ≤ 6.
- [Tdep]: the literal Ω̄_C is the same for every T.
- Small-value table of [R] §2 reproduced exactly (A_2, C_2 ⊔ C_1, C_2 ⊔ C_2,
  C_3 ⊔ C_1, A_4, C_3 ⊔ C_3, both h_C and Ω̄_C(1..5)).
- Antichain: D_T on A_n is "f(T) is the strict maximum" (if some x ≠ T has
  f(x) ≥ f(T), the cluster {y ≠ T : f(y) ≥ f(T)} violates D_T). So
  Ω̄_C(A_n, m) = Σ_{j=1}^{m−1} j^{n−1}, as [R] says.

## 2. R′ and B⁺

R′: Theorem H gives Ω_C = Σ_κ C(m + n − cdes κ, n); the same sign identity
with y = m − n + cdes gives C(m + cdes − 1, n). The generating function
follows from Σ_m C(m + a, n) x^m = x^{n−a}/(1−x)^{n+1}, 0 ≤ a ≤ n. The
remark "Ω̄_C(P, 1) = 0 for n ≥ 2" needs max cdes ≤ n − 1, whereas [R] only
records 1 ≤ cdes ≤ n. It is true (n distinct letters on a circle cannot all
be cyclic descents), and also obvious directly (a strict map to [1] forces
an antichain, and then U = P ∖ T violates D_T). Cosmetic. Recomputed under
λ_0 (separated): [R′].

B⁺: R1 + Theorem Ω + uniqueness of the expansion in the basis
C(m + n − 1 − j, n), j = 0..n. Recomputed for every T under λ_T: [B+].
The claim that this contains [HV] Prop. B is right: for non-singleton T,
λ_T is a λ_0; for singleton T, the component of label n − 1 under λ_0 is
isolated only if P is an antichain, where λ_T = λ_0 with T last.

## 3. ★

OP(P) is defined by acyclicity of the quotient digraph; reversing all
arrows preserves acyclicity and changes neither the partitions, the
refinement order, μ, nor |π|. The definition of Ω_C sees only these. The
proof is complete as one line. Recomputed from two independent Möbius
sums: [dual]. h_C(P*) = h_C(P) then follows, and Ω̄_C(P*) = Ω̄_C(P) by R.

## 4. E (Ehrhart, non-convex region)

- *Closedness, lattice points.* Correct: tR_T ∩ Z^P ↔ anchored
  order-preserving f = x + 1 into [t + 1].
- *Decomposition.* R1's proof uses only the order of the values, so it
  applies to real points; R_T is the union of the half-open word cells of
  B_T, hence (being closed) of the closed simplices. Correct.
- *Non-convexity example* {1 < 2, 1 < 3} ⊔ {0}, T = {1, 2, 3}: R_T is
  x_0 ≤ max(x_2, x_3) inside O(P); (1,0,0,1), (1,0,1,0) ∈ R_T, midpoint
  (1,0,½,½) ∉ R_T. Verified [E].
- *Interior.* The claimed open set is open and inside R_T. Conversely, an
  interior point has 0 < x < 1; x_a = x_b with a < b is excluded by pushing
  x_a up; equality min_U x = max_{P∖U} x is excluded by adding ε to the
  whole of U, which preserves every relation because U is a union of
  components. Correct. As an extra check I sampled points of R_T on the
  grid (¼Z)^P for every disconnected (P, T) with n = 5 and compared the
  claimed description with an ε-box test (all 3^n sign perturbations of
  size 1/1000 stay in R_T): 700 sampled points, 0 disagreements.
- *Is the reciprocity legitimate for a non-convex region?* Yes, in the
  sense stated. [R] does not invoke Macdonald's theorem for R_T; it
  identifies L_{R_T}(t) = Ω_C(P, t + 1) and L_{R_T°}(t) = Ω̄_C(P, t − 1) and
  then *uses Theorem R* to get L_{R_T}(−t) = (−1)^n L_{R_T°}(t). The
  equivalence "Theorem R ⇔ this identity" holds because both sides are
  polynomials. [R] is explicit that the PL-ball question is OPEN and that
  a topological proof is not given. One consistency check: L_{R_T}(0) =
  Ω_C(P, 1) = 1 (the constant map is anchored), which is the Euler
  characteristic a ball would have.

## 5. S (height ≤ 2)

Checked every bullet of the proof:
- g = f − 1 on non-isolated maxima and on T's point (T singleton), g = f
  elsewhere, is order-preserving into [m − 1]; the three range facts
  (non-isolated minima ≤ m − 1; isolated z ≠ T has f(z) ≤ m − 1 by
  U = {z}; f(t) ≥ 2 by U = P ∖ T) are each forced by D_T or strictness.
- The inverse f = g + 1 gives a strict map, so the bijection is onto all
  order-preserving g : P → [m − 1].
- min_U g = min_U f for T-free U (minima of a component keep their values,
  maxima drop by 1 but stay ≥ some minimum below them).
- "g not anchored ⇒ D_T fails" uses g ≥ f − 1 and integrality; "D_T fails
  ⇒ g not anchored" uses the enlarged cluster U′, and every element of
  P ∖ U′ has g < μ. Both correct.
- The palindromicity: Σ_κ x^{n+1−cdes} = x Σ_κ x^{cdes} is c ↦ n − c
  symmetry, i.e. h_j = h_{n−2−j}. Correct.

Recomputed: for every height-≤ 2 (P, T) with n ≤ 6 and m = n, every
strict D_T map f was pushed through g and checked to land in the anchored
order-preserving maps into [m − 1], injectively and onto (355 653 maps, 0 bad). The
shift identity and palindromicity hold on all height-≤ 2 posets n ≤ 7
([S]), and the shift identity fails on every poset with a 3-chain
([ctl-shift-any] 2193 / 2193).

S′ is COMPUTED in [R], not claimed proved. My recomputation ("palindromic"
= palindromic after stripping trailing zeros; "graded" = all maximal chains
have the same length) gives 0 mismatches.

## 6. Refutations

- **Naive transplant, A_2 by hand.** OP(A_2) = {0̂, 1̂}, μ(0̂, 1̂) = −1, so
  Ω_C(A_2, m) = C(m, 2) + m = m(m + 1)/2 and Ω_C(A_2, −m) = C(m, 2). The
  naive count (strict maps, no U = {0} with f(0) > f(1)) is
  #{f(0) ≤ f(1)} = C(m + 1, 2) ≠ C(m, 2). The correct D_T count is
  #{f(0) < f(1)} = C(m, 2). Verified by hand and by code. [ctl-naive]
  fires on 1160 of 3107.
- **Lower level sets.** The version [R] refutes (strict maps, forbid a
  T-free U with max f(U) < min f(P ∖ U)) does fail: [ctl-lower] 1160 of 3107.
  It is the image of the naive transplant under ★ and f ↦ m + 1 − f, so it
  fails on the same pairs. **But** the lower version with ≤ (forbid
  max f(U) ≤ min f(P ∖ U)) is the image of D_T under the same map and is
  therefore TRUE by ★ + R: [lower-D] 0 / 3107 bad. So [R]'s summary line
  "The dual condition does **not** move to lower level sets" is FIXABLE:
  the condition does move to lower level sets, provided the inequality is
  ≤. What fails is keeping the strict inequality.
- **h_C(P*) = reverse.** ★ makes h_C(P*) = h_C(P), so the claim reduces to
  "h_C palindromic", which fails whenever h_C is not. [ctl-reverse] fires
  on 1875 of 2450 (reversal after stripping trailing zeros), matching [R]
  exactly. With the untrimmed length-(n+1) vector it fails on every poset.
- Counts that match [R] exactly: 3107 pairs, 503 disconnected, 1160
  (naive, lower), 3079 (mixed), 1875 (reverse), 151 (pal-graded), 2193
  (shift-any), 256 (height ≤ 2), 1166 (any labelling). R1/R2 case counts
  are one below [R]'s (5 928 326, 2 742 963) because I start at n = 2,
  where [R] evidently includes the single n = 1 case. My denominator for the
  any-labelling control (1882) counts only disconnected labelled pairs.
- Other controls recomputed and firing: [ctl-mixed] 3079 of 3107,
  [ctl-plain] 503 of 2450 (exactly the disconnected posets), [ctl-pal_graded]
  151 of 2449, [ctl-any-lab] 1166 of 1882 (labelling, T), n ≤ 5, plus a planted bug (drop (−1)^n) that
  must fail on odd n: [ctl-signbug] 2114 odd-n pairs.

## 7. Extra: the two-component identity (prior_art_reciprocity_omega_c.md §5)

Claim: P = Q ⊔ T, Q and T connected ⇒ h_C(P)(t) = W_P(t) − t W_Q(t) W_T(t),
W = Σ_{w∈Lin} t^{des w} under a natural labelling.

Proof checked. With two components the only T-free cluster is Q, so the
non-anchored maps are the order-preserving f with min f(Q) > max f(T). These
are the (T ⊕ Q, ω)-partitions for ω natural on T and on Q and with T
labelled above Q (EC1 Lemma 3.15.3 for an arbitrary labelling). Their words
are uv, u ∈ Lin T, v ∈ Lin Q, with a forced descent at the junction, so the
count is Σ C(m + n − 1 − (des u + des v + 1), n), with h-numerator t W_T W_Q.
Subtracting from Stanley's Ω(P, m) (numerator W_P) gives the identity.
**HOLDS.** Recomputed: h_C from the Möbius definition vs. W from descents
of linear extensions: 0 bad / 391 two-component posets n ≤ 7
([two-comp]); the control without the factor t fails on 391 / 391.

## 8. Coverage and what was not checked

- Prior-art statements of [R] §7 were not re-audited (pm-poset reports
  separately that the polynomial side of R is KNOWN IN SUBSTANCE via EC1
  Lemma 3.15.9 and that the D_T reading is NOT FOUND; not re-derived here).
- R′ was recomputed only under λ_0, not under every separated labelling
  (it follows from Theorem H, audited elsewhere).
- The map-by-map bijection check of S was capped at n ≤ 6 for time;
  the identity it proves was checked at n ≤ 7.
- Unimodality U: recomputed, 0 non-unimodal h_C at n ≤ 7. OPEN, as [R]
  says.

## Reproduce

From `compute/` (Python 3, no dependencies, one core; the first command takes about 6 min, the second about 5 s):

    python3 audit_reciprocity_omega_c.py --nmax 7 --nall 6 --lmax 5 > output/audit_reciprocity_omega_c.txt
    python3 audit_reciprocity_omega_c.py --nmax 7 --twocomp > output/audit_reciprocity_omega_c_twocomp.txt

Each exits 0 iff every claim holds and every control fires. The first run
prints `ALL CLAIMS HOLD: True | ALL CONTROLS FIRE: True` on its last line.
A fast smoke test: `--nmax 5 --nall 5 --lmax 4` (about 2 s).
