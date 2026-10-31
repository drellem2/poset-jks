# Audit of h_vector_omega_c.md: the h-vector of Ω_C and cyclic descents

This is an independent audit of `notes/h_vector_omega_c.md` ([H] below). I
re-derived every proof by hand. I also recomputed every claim with my own
script, `compute/audit_h_vector_omega_c.py`, which imports nothing from the
repository and does not reuse the author's code. Bracketed labels such as
`[L1: per-class]` refer to lines of `compute/output/audit_h_vector_omega_c.txt`.

Sources: [LS] = `notes/linext_statistics.md`; [AudLS] =
`notes/audit_linext_statistics.md`; [ME] = `notes/mu_op_elementary.md`;
[AudME] = `notes/audit_mu_op_elementary.md`; [LE] =
`notes/linear_extensions.md`; [CSC] = `notes/cyclic_sieving_cyc.md`;
EC1 = Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed.

## Verdict

| Claim of [H] | Verdict |
|---|---|
| **Theorem H**: separated natural labelling, n ≥ 2 ⇒ Ω_C(P, m) = Σ_{κ∈Cyc P} C(m+n−cdes κ, n), so h_C(P)_j = #{κ : cdes κ = j+1} = #{κ : min des = j} ≥ 0 | **HOLDS.** The proof is complete given [ME] Lemma U and Theorem A, both audited in [AudME]. COMPUTED: all 2450 posets n ≤ 7 (2723 separated labelled posets at n = 7), and all 4443 separated labelled posets n ≤ 6 |
| **Lemma 1** (§2.2): a non-all-ascent class contributes exactly C(m+n−1−stat κ, n), for every natural labelling and every component T | **HOLDS.** The telescoping and the junction bookkeeping are correct (§2 below). COMPUTED on 6 828 529 (class, T, m) cases, m = 0, …, n+1 |
| **Lemma 2** (§2.3): separated ⇒ first ≤ last in every piece, no all-ascent class, stat = cdes − 1; separated labellings exist (λ_0) | **HOLDS.** COMPUTED: λ_0 is natural and separated on all 2450 posets |
| **H′**: any natural labelling with no all-ascent class ⇒ min-des on Cyc P realises h_C | **HOLDS** (Lemma 1 summed over Proposition D). COMPUTED on 5182 labelled posets n ≤ 6, 7905 in all |
| **Prop. B**: under λ_0, des on B_P realises h_C, for both the last-piece convention (component of label n−1) and the first-piece convention (component of label 0) | **HOLDS.** COMPUTED on 2449 posets 2 ≤ n ≤ 7, both conventions |
| **Prop. D** (§1): Cor. Ω-des of [LS], reproved from the Möbius definition | **HOLDS.** Steps 1–4 of [H] §1 are a complete proof of Theorem Ω. They use only [ME] Lemma U and Theorem A, nothing else from [LS]. COMPUTED on every component T, every natural labelling n ≤ 6 and two labellings at n = 7 (97 535 cases). Theorem Ω was also checked against a direct count of maps (511 cases, n ≤ 5, m ≤ 3) |
| H″ (converse of H′) | Correctly tagged **OPEN**. The data are confirmed: min-des fails on all 48 labelled posets n ≤ 6 that have an all-ascent class |
| Controls (cdes − 1 under an arbitrary labelling; des on B_P under an arbitrary separated labelling; des on Lin P) | **Refuted, as claimed**, with exactly the counts in [H]: 787 of 5230, 346 of 4443 (each convention), and des on Lin P fails exactly on the 503 disconnected posets |
| The "Dependence" paragraph (Theorem Ω "audit pending") | **FIXABLE (stale wording only).** [AudLS] has since found Theorem Ω HOLDS. Proposition D does not need it in any case |
| Consistency of cdes with [LE] and [CSC] | **HOLDS, with a naming caveat.** [H] uses the cdes of [LS] §0. [LE] and [CSC] never define cdes. [LE]'s B_P (first block contains an arbitrary base component) is a different set, and Prop. B fails for it under λ_0 on 41 of 554 (poset, base) pairs (§5) |

**No claim FAILS.** I recommend two wording fixes (§5), neither of which
affects any statement.

## 1. Proposition D and the dependence on Theorem Ω

The check asked for here is whether §1 of [H] really avoids the parts of
Theorem Ω that had not been audited. It does. It reproves Theorem Ω in
full, using only two external inputs.

- *Step 1* uses [ME] Lemma U, [π, 1̂] ≅ OP(Q_π), and [ME] Theorem A on Q_π,
  which gives (−1)^{|π|−1} μ(π, 1̂) = e_C(Q_π). Both are HOLDS in [AudME]
  (its rows 4, 9 and 12). The sign is consistent with the task statement
  Ω_C = Σ |μ(π, 1̂)| C(m, |π|). I checked (−1)^{|π|−1} μ(π, 1̂) ≥ 0 at all
  831 020 pairs (P, π) with n ≤ 7, and the signed and absolute sums agree on
  all 2450 posets `[mu-sign]`, `[signed=abs]`.
- *Step 2* is the standard fibre bijection. The fibres of an order-preserving
  f form a partition with an acyclic quotient: along a cycle of blocks f
  would be constant, so the blocks would coincide. So σ ∈ OP(P). Listing the
  fibres by value gives u ∈ Lin Q_σ. Conversely, any (σ, u, S) defines an
  order-preserving f.
- *Step 3.* A union of blocks is a union of Q_σ-components iff no
  generating relation of Q_σ crosses it. A chain in the transitive closure
  that crosses the boundary has a step that crosses it. So this is the same
  as being a union of P-components. Each P-component lies in one
  Q_σ-component. All correct.
- *Step 4.* The class of u has one member per piece, and the pieces have
  disjoint letter sets, so exactly one member has T's piece last. The
  suffixes of u that start at cuts are nested, and the smallest one is the
  last piece. So "T is in the last piece" is the same as "every nonempty
  upper level set of f that is a union of components contains T". This is
  exactly Theorem Ω.
- *Step 5.* The "Stanley word" can be checked directly, with no citation
  needed. Sort P by (f(x), label). The result is a linear extension, since
  x <_P y gives f(x) ≤ f(y) and x < y. It is strict at descents: equal
  values are sorted by label, so inside a run of equal values there is no
  descent. It is unique: inside each value run the letters must increase.
  [H] cites this as EC1 Lemma 3.15.3. I did not check that lemma number
  against the book. The direct argument makes the citation unnecessary.
- *Proposition D.* Let p ∈ C_T(w). Then {w_1, …, w_p} is a union of
  components, so T lies entirely on one side of p, and the condition of
  Step 4 at p is that f(w_p) = f(w_{p+1}). Merging the c forced equalities
  leaves n − c positions, and all des(w) descents survive among the
  n − c − 1 gaps. The number of weakly increasing sequences in [m] that are
  strict at r prescribed gaps out of k − 1 is C(m + k − 1 − r, k). Here
  k = n − c and r = des(w), which gives the stated N_T(w, m).

**Result.** Proposition D HOLDS. It depends only on [ME] Lemma U and
Theorem A, both audited. Separately, [AudLS] now reports that Theorem Ω
HOLDS, so the dependence is covered twice. My computation tests
Proposition D against Ω_C computed from the Möbius recursion
`[D: sum_w N_T = Omega_C]`. It also tests the Theorem Ω count itself
against a brute-force enumeration of order-preserving maps
`[Thm-Omega brute (maps)]`. Neither test passes through Theorem Ω.

## 2. Lemma 1: the telescoping and the junctions

I re-derived each step.

**Rotations and cuts.** Index the pieces so that T ⊆ c_s, and put
R_i = c_{i+1} ⋯ c_s c_1 ⋯ c_i. In R_i the wrap-around pair is J_i (J_0 = J_s).
The internal boundaries between pieces are the other s − 1 junctions, and
these are exactly the cuts of R_i (by [H] §0, rotation preserves the
pieces). T is contained in the prefix at a cut iff the cut lies after
c_s. In R_i, c_s is at position s − i, and the junctions after it are
J_s, J_1, …, J_{i−1}. That is i of them, so |C_T(R_i)| = i. Also
des(R_i) = d + jd − δ_i, since the descents are those inside pieces plus
those at the internal junctions. Hence R_i contributes iff
δ_s = δ_1 = ⋯ = δ_{i−1} = 0, and then N_T(R_i) = C(M + δ_i − i, n − i), where
M = m + n − 1 − d − jd.

**Case δ_s = 1.** R_i needs δ_s = 0 for every i ≥ 1, so only R_0
contributes. Its contribution is C(M + 1, n), and
stat = d + jd − max δ = d + jd − 1.

**Case δ_s = 0, jd ≥ 1.** Here q = min{k ≥ 1 : δ_k = 1} exists. Since
δ_s = 0, q ≤ s − 1 ≤ n − 1. The contributing rotations are exactly
R_0, …, R_q. For i < q we have δ_i = 0 (for i = 0 this is δ_s = 0), so
N(R_i) = C(M − i, n − i). For i = q, N(R_q) = C(M + 1 − q, n − q). The
downward induction is C(M − j, n − j) + C(M − j, n − j − 1) = C(M + 1 − j, n − j).
Pascal's rule is used only with lower index n − j − 1 ≥ n − q ≥ 1, so it is
valid as an identity of polynomials in m. At j = 0 this gives C(M + 1, n),
the same single binomial as in the first case.

**Range.** At every integer m ≥ 0 the binomials have nonnegative upper
argument, because des + c ≤ n − 1 whenever the descents and the forced
equalities occupy disjoint gaps. So the identities hold as integer counts
and as polynomials. Both cases give the same binomial for every T, which
is why "only the representative carrying the contribution moves" is right.

**s = 1.** There are no cuts, so C_T = ∅ and N = C(m + n − 1 − d, n). Correct.

**All-ascent classes** (the remark under H″). With jd = 0 every R_i
contributes C(m + n − 1 − d − i, n − i), which matches [H]'s
Σ_{i=0}^{s−1} C(M − i, n − i). I checked this by hand only.

**Computation.** `[L1: per-class]` checks Σ_{w∈κ} N_T(w, m) = C(m+n−1−min des, n)
for every non-all-ascent class, every component T, every m = 0, …, n+1, every
natural labelling for n ≤ 6, and two labellings at n = 7: 6 828 529 cases,
0 failures. Since n + 2 values agree, the identity holds as polynomials.

**Verdict: HOLDS.**

## 3. Lemma 2 and the existence of separated labellings

- (a) Anything below the first letter of a piece lies in the same
  component, hence in the same piece, hence before it. So the first letter
  is minimal. If a piece of length ≥ 2 began with an isolated point x,
  then {x} would be a proper prefix that is a union of components. The dual
  argument, which [H] leaves to the reader, also works: if the piece ended
  with an isolated point x, then the piece minus x would be a nonempty
  proper prefix that is a union of components. No element of a
  non-singleton component is both minimal and maximal. Separation is a
  condition across all components, so it applies even when first(c) and
  last(c) lie in different components of the piece. Correct.
- (b) The chain first(c_1) ≤ last(c_1) < first(c_2) ≤ ⋯ < first(c_1) is a
  contradiction for s ≥ 2. Correct.
- (c) For s = 1 and n ≥ 2, the word has distinct first and last letters, so
  w_1 < w_n strictly, and cdes = des + 1. Correct. The hypothesis n ≥ 2 is
  needed: at n = 1, cdes = 0.
- *Existence (λ_0).* Suppose x <_P y. Then x is minimal or middle, and y is
  middle or maximal. Each of the possible pairs is placed in the right
  order: min < middle, min < max, middle < middle (by the chosen
  extension), middle < max. Isolated points are unrelated to everything. So
  λ_0 is natural, and it is separated by construction. COMPUTED on all 2450
  posets `[lambda0-natural+separated]`.

Theorem H is then Proposition D summed over the classes, using Lemma 1
and Lemma 2(b, c). The h-vector is uniquely determined, since
{C(m+n−1−j, n)}_{j=0}^{n} is a basis of the polynomials of degree ≤ n that
vanish at 0, and stat ≤ n − 1. **Theorem H, H′ HOLD.**

## 4. Proposition B

The rotation in B_P is R_0, with des = d + jd − δ_s. Suppose P is not an
antichain. Then label n − 1 is a non-isolated maximum, so T's piece has
length ≥ 2 and ends in a non-isolated maximum. The next piece begins with
a non-isolated minimum or an isolated point. Under λ_0 both of those are
below every non-isolated maximum, so δ_s = 1. The first-piece convention
is the dual argument: label 0 is a non-isolated minimum. The antichain
case is trivial. **HOLDS**; COMPUTED `[B: lambda0 last-piece]`,
`[B: lambda0 first-piece]`. The general principle, "pick in each class a
rotation broken at a descent junction", follows directly from Lemma 1.

## 5. Consistency of definitions, and recommended fixes

- **cdes.** [H] §0 uses cdes(w) = des(w) + [w_n > w_1]. This is the
  definition in [LS] §0. My code uses that definition and checks that cdes
  is constant on every class `[cdes-class-const]` (458 012 classes). It
  agrees with [H]'s junction formula d + jd: the wrap-around pair is the
  broken junction. [LE] and [CSC] never define cdes, so there is nothing to
  conflict with.
- **Cuts and classes.** [LE] §0 counts k = 0 as a cut. [H] uses
  p ∈ [1, n−1] and adds w itself. These give the same class. My code builds
  each class from the cut rotations and asserts that it equals
  wC_n ∩ Lin P, for every word of every labelled poset tested.
- **B_P naming (fix 1, wording).** [LE] §0 and [LE] §4 define B_P as the
  words whose *first* block contains the base component P_1. [H] uses
  "B_P" for the *last*-piece convention of [LS] §2.2. Its "first-piece
  convention" uses the component of label 0, which is not necessarily
  P_1. Proposition B holds for both of [H]'s conventions, but not for
  [LE]'s B_P with an arbitrary base component. Under λ_0, des on the words
  whose first piece contains a given component B fails for 41 of the 554
  pairs (poset, B) with 2 ≤ n ≤ 6
  `[ctl-BP-first arbitrary base, lambda0]`. The smallest case is the
  antichain on {0, 1} with B = {1}: B_P = {10} has des 1, but h_C = (1).
  The junction entering B's piece is an ascent there. So Proposition B
  must keep its base component (label 0 for the first-piece convention,
  label n − 1 for the last-piece one), and [H] should not identify its
  B_P with [LE]'s.
- **Dependence paragraph (fix 2, stale).** "Theorem Ω of [LS] §2.1
  (PROVEN, audit pending)" should now cite [AudLS] (HOLDS). It should also
  say that §1 makes Theorem H independent of it anyway.

The data in [H] §2.4 were all reproduced from the Möbius side:
- C_2 ⊔ C_1 → (1, 1); C_2 ⊔ C_2 → (1, 3, 1); C_3 ⊔ C_1 → (1, 2);
  A_4 → (1, 4, 1).
- The antichain gives the Eulerian numbers of S_{n−1} for n ≤ 7 (the note
  claims n ≤ 5).
- Ω_C(P, 1) = 1, and Σ h = e_C.
- The positive control C_2 ⊔ C_2 with 0 < 1, 2 < 3 has exactly the classes
  {0123, 2301}, {0213}, {0231}, {2013}, {2031}, with cdes − 1 = 0, 1, 1, 1, 1.
- The all-ascent example 0 < 1, 3 < 4 ⊔ {2} has min-des distribution
  (1, 9, 8, 2) against h_C = (1, 9, 9, 1). Its unique all-ascent class is
  {23041, 30412}.
- The [LS] example {0<2} ⊔ {1<4} ⊔ {3} has the class {01423, 30142} with
  cdes 2, 2 and des 1, 2.

## 6. Computation

My script (`compute/audit_h_vector_omega_c.py`) works as follows.

- *Posets.* It generates the posets up to isomorphism by adding a maximal
  element over each order ideal, and canonicalises them by brute force over
  invariant-respecting permutations. This gives 1, 2, 5, 16, 63, 318, 2045
  posets: 2450 in all, 503 of them disconnected.
- *Ω_C.* OP(P) is computed by filtering all set partitions for an acyclic
  quotient. μ(π, 1̂) comes from the recursion
  μ(π, 1̂) = −Σ_{π<ρ} μ(ρ, 1̂). Ω_C(m) is evaluated at m = 0, …, n+1, and h
  is read off from (1−x)^{n+1} Σ Ω_C(m) x^m.
- *Labellings.* For n ≤ 6 the script tests every natural labelling,
  deduplicated as labelled posets: 5231 including n = 1, so 5230 with
  n ≥ 2, as in [H]. For n = 7 it tests the generated labelling and λ_0.
- *Coverage gap at n = 7.* All 2723 labellings tested at n = 7 happen to be
  separated. So the controls, H′ on non-separated labellings and H″ were
  tested only for n ≤ 6, which is also what [H] claims.

Results: every claim line OK, every CONTROL line refuted, exit 0.

| Line | Cases | Failures |
|---|---|---|
| `[H: cdes-1 dist = h]`, `[H: mindes=cdes-1 classwise]`, `[H: no all-ascent]` | 7166 separated labelled posets | 0 |
| `[H': mindes dist = h]` | 7905 | 0 |
| `[L1: per-class]` | 6 828 529 | 0 |
| `[D: sum_w N_T = Omega_C]` | 97 535 | 0 |
| `[Thm-Omega brute (maps)]` | 511 | 0 |
| `[B: lambda0 last-piece]`, `[B: lambda0 first-piece]` | 2449 each | 0 |
| `[h>=0]`, `[sum h = e_C]`, `[Om(1)=1]` | 2450 | 0 |
| `[lin: des on Lin P = h iff connected]` | 2449 | 0 |
| `[lin: connected, every labelling, des = h]` | 5036 | 0 |
| CONTROL `[ctl-cdes-any]` | 7953 | 787 (all at n ≤ 6, out of 5230) |
| CONTROL `[ctl-BP-last separated]`, `[ctl-BP-first separated]` | 4443 | 346 each |
| CONTROL `[ctl-H'' mindes with all-ascent]` | 48 | 48 |
| CONTROL `[ctl-BP-first arbitrary base, lambda0]` | 554 | 41 |
| CONTROL `[ctl-lin des on Lin P]` | 7953 | 2917 (labelled; on iso classes, exactly the disconnected ones) |

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 140 s):

    python3 audit_h_vector_omega_c.py --nmax 7 --lmax 6 --bmax 5 > output/audit_h_vector_omega_c.txt

The script exits with status 0 iff every claim line holds and every CONTROL
line is refuted somewhere. `--lmax` is the largest n at which every
natural labelling is tested. `--bmax` is the largest n for the brute-force
count of maps.
