# Audit of `notes/promotion_on_R_P.md`

**Verdict: HOLDS WITH FIXES.** Theorem 1 is true. For disconnected P,
∂(R_P) ⊆ R_P iff P is two chains. Every step of both "only if" cases
survives an independent re-derivation, and the certificate argument is sound
in general, not only on the examples. The case split covers every
disconnected P. Every COMPUTED count was reproduced by independent code, and
so was the positive control 9/108. The fixes F1–F3 below are about precision
and wording. None of them changes a result.

The note is cited as [N], `notes/linear_extensions.md` as [LE] and
`notes/poset_jks_theorem.tex` as [Thm]. This audit uses only [N], the
definition of R_P in [Thm] (the display before Thm `thm:S`), and [LE] §§0–2
for conventions and Lemma P. It imports nothing from `compute/`. All code is
in `compute/audit_promotion_on_R_P.py` ("[Aud]").

| # | Claim of [N] | Verdict | How checked |
|---|---|---|---|
| L1 | Lemma 1: ∂_Q has a fixed point iff Q is a chain; a union of ≥ 2 components has none | **HOLDS** (§1) | by hand |
| L2 | Lemma 2: ⟨ρ(az), uz⟩ = δ_{u,a}; Xz ∉ Sh_n | **HOLDS**, with an implicit hypothesis that should be stated (F1) | by hand; [ree] for every c ∈ S_n, n ≤ 5 |
| L3 | Lemma 3: ∂(s ⧢ t) = (s″ ⧢ t)z + (s ⧢ t″)y | **HOLDS** (§1), given [LE] Lemma P, whose proof was re-read | by hand; used by every [cert] value |
| L4 | Lemma 4: R_P is graded by the restriction tuple | **HOLDS** | by hand; asserted for every generator built by [def] |
| if | two chains ⇒ ∂(R_P) ⊆ R_P | **HOLDS** | by hand; [def], and R_P = C·ΣLin P built from its generators, on all 16 two-chain posets n ≤ 8 |
| A | case A: r = s ⧢ t with T non-chain; ∂r ∉ R_P; certificate φ | **HOLDS** (§2) | by hand; [cert] on all 2932 case-A posets n ≤ 8 (every T, s, t for n ≤ 6) |
| B | case B: k ≥ 3 chains; ∂r − r′ = (s̃ ⧢ (t − ∂_B t))σ; certificate ψ | **HOLDS** (§2) | by hand; [cert] on all 42 case-B posets n ≤ 8 (every T, s, t for n ≤ 6) |
| cov | cases A, B and "if" cover every disconnected P | **HOLDS** (§3) | by hand, edge cases listed |
| ex | the A_3 and V ⊔ C_1 examples | **HOLDS** | by hand; unit tests |
| Rem | case A: no generator with S = T maps into R_P | **HOLDS** | follows from the case-A proof, which uses arbitrary s, t; [cert] on every s, t for n ≤ 6 |
| §3 | table: 16 of 2990 for n ≤ 8, exactly the two-chain posets; 2932 A + 42 B; 9/108 | **HOLDS**, all numbers reproduced | [Aud] |
| §1 | conventions table, "the two families meet only in C_1 ⊔ C_1" | **HOLDS**; one sentence is ambiguous (F2) | — |
| §4 | corrections to [LE] | **HOLDS**; one more is owed (F3) | — |

## 1. Lemmas

**Lemma 1.** If ∂_Q(w) = w and w_1 ∥ w_2, then τ_1 moves w_2 to position 1,
and later toggles never touch position 1. So ∂_Q(w)_1 = w_2 ≠ w_1, a
contradiction. Hence w_1 < w_2. Then τ_1 is trivial, the letter in position 2
before τ_2 is w_2, and the same argument repeats. So w is a chain
w_1 < ⋯ < w_m and Q is a chain. A chain is connected, so a union of two or
more components is not a chain. On a chain, |Lin Q| = 1 and the bijection ∂_Q
is the identity. Correct.

**Lemma 2.** ρ(b_1⋯b_m) = b_1ρ(b_2⋯b_m) − ρ(b_2⋯b_m)b_1. For m ≥ 2 the second
term ends in b_1 ≠ b_m. By induction, the only word of ρ(b) ending in b_m is b,
with coefficient +1. So ⟨ρ(az), uz⟩ = δ_{u,a}, and ⟨ρ(az), Xz⟩ = X(a).
Ree's theorem (multilinear form: every Lie polynomial is orthogonal to every
proper shuffle u ⧢ v of words on complementary letter sets) gives
ρ(az) ⊥ Sh_n. So Xz ∉ Sh_n whenever X ≠ 0. Correct, under F1.
[Aud] `[ree]` checks the triangularity, and the vanishing on shuffles of
increasing and decreasing words, for every c ∈ S_n, n ≤ 5.

**Lemma 3.** Re-derived from [LE] Lemma P, which was re-read: the carried
letter stays in the component of w_1, every letter of the other side shifts
left once, and the carried letter ends in position n. So for w ∈ s ⧢ t with
w_1 ∈ A, ∂(w) has A-part ∂_A(s), B-part t, rotated pattern, and last letter
z. As the pattern runs over the patterns starting with A, the rotated
pattern runs over those ending with A. These words are exactly
(s″ ⧢ t)z, and similarly for w_1 ∈ B. The words of s ⧢ t are distinct
because the letter sets are disjoint. Correct.

**Lemma 4.** Each generator s ⧢ t has all its words with the same
restriction tuple: (w|_{T_i}) = (s|_{T_i}) for T_i ⊆ S, and (t|_{T_i})
otherwise. Grouping a representation Y = Σ c_j g_j by grade shows that every
graded piece of Y lies in R_P. Correct.

## 2. The two "only if" cases

**Case A.** T is a non-chain component, r = s ⧢ t with s ∈ Lin T,
t ∈ Lin(P|_B), B = [n] ∖ T.
- (a) r ∈ R_P: T is a nonempty proper union of components (k ≥ 2), so r is
  a defining generator.
- (b) ∂r = Y_1 + Y_2, where Y_1 has T-part ∂_T(s) and Y_2 has T-part s
  (Lemma 3). These T-parts differ by Lemma 1. So Y_1 is exactly the sum of
  the graded pieces of ∂r with T-coordinate ∂_T(s). If ∂r ∈ R_P, then
  Y_1 ∈ R_P ⊆ Sh_n by Lemma 4. But Y_1 = Xz with X = s″ ⧢ t ≠ 0, and z ∉ X's
  letters. That contradicts Lemma 2.
- **What the certificate proves.** φ(Y) = ⟨ρ(s″tz), Y_{[T = ∂_T s]}⟩ is a
  linear functional on W_P. It kills R_P because projection onto a set of
  grades maps R_P into R_P (Lemma 4) ⊆ Sh_n ⊥ ρ(…) (Ree). And
  φ(∂r) = X(s″t) = 1. So φ separates ∂r from R_P. This is a general
  argument, valid for every non-chain T and every s, t, not an example.
  The projection is needed. Y_2's words end in y ≠ z, and ρ(s″tz) has
  words ending in y, so the unprojected pairing ⟨ρ(s″tz), ∂r⟩ picks up an
  uncontrolled term ⟨ρ(s″tz), Y_2⟩. Y_2 is not known to lie in Sh_n. The
  note's φ, which projects first, is the right object.

**Case B.** All components are chains, k ≥ 3. T is any component, s its
unique word, σ its last letter, and t ∈ Lin(P|_B).
- (a) r ∈ R_P and r′ = s ⧢ ∂_B(t) ∈ R_P: both are defining generators,
  because ∂_B(t) ∈ Lin(P|_B).
- (b) Since ∂_T s = s, Lemma 3 gives ∂r = (s̃ ⧢ t)σ + (s ⧢ t″)y. The
  last-letter recursion for shuffles, (u′a) ⧢ (v′b) = ((u′a) ⧢ v′)b + (u′ ⧢ (v′b))a,
  gives r′ = (s ⧢ t″)y + (s̃ ⧢ ∂_B t)σ. So ∂r − r′ = (s̃ ⧢ (t − ∂_B t))σ.
  This also holds when s̃ is empty. B is a union of k − 1 ≥ 2 components,
  so ∂_B t ≠ t (Lemma 1). The word s̃t has B-part t, so it has coefficient 0
  in s̃ ⧢ ∂_B t and 1 in s̃ ⧢ t. Then ψ = ρ(s̃tσ) gives
  ⟨ψ, ∂r⟩ = ⟨ψ, r′⟩ + 1 = 0 + 1 = 1, while ψ ⊥ Sh_n ⊇ R_P.
- **What the certificate proves.** ψ is a single Lie element, orthogonal to
  all of Sh_n, so it kills R_P without any grading. Here a projection would
  not help: ∂r and r′ share the graded pieces with B-part ∂_B(t). That is
  why the argument subtracts r′ and does not project. The argument is
  general in T, s, t.

**A note on the convention.** [N] fixes ∂ = τ_{n−1} ∘ ⋯ ∘ τ_1. The theorem
does not depend on this choice. ∂ is a bijection of the finite set Lin P,
so ∂(R_P) ⊆ R_P forces ∂(R_P) = R_P and ∂^{−1}(R_P) = R_P.

## 3. Coverage and edge cases

Let P be disconnected, so k ≥ 2. Either some component is not a chain
(case A), or all components are chains. In the second situation, k = 2 is
the family and k ≥ 3 is case B. This is a partition, so nothing is left
over. Edge cases:
- **Components of size 1** are chains C_1. In case B, T = C_1 gives s̃
  empty, and the argument still works. This is the A_3 example, checked by
  hand: ρ(120) = 120 − 102 − 201 + 021, ∂r = 120 + 021 + 201, pairing 1.
- **A non-chain component with isolated points**, for example V ⊔ C_1 or
  V ⊔ C_1 ⊔ C_1. This is case A with T the non-chain component. B may be an
  antichain or a single point. Case A never uses a property of B: t is any
  linear extension of P|_B. Checked by hand for V ⊔ C_1:
  ∂_V(012) = 021, Y_1 = 0231 + 0321 + 3021, φ(∂r) = 1.
- **Several non-chain components.** Case A applies with any one of them as
  T. [Aud] tests every choice of T for n ≤ 6, and a random one for n = 7, 8.
- **n ≤ 3.** For n = 2, the only disconnected poset is C_1 ⊔ C_1, which is
  in the family. For n = 3 they are C_2 ⊔ C_1 (family) and A_3 (case B).
  Case A first occurs at n = 4 (V ⊔ C_1, Λ ⊔ C_1).

## 4. Computation

[Aud] decides the property in two independent ways and shares no code with
`compute/promotion_on_R_P.py`.
- **Posets.** All posets up to isomorphism, n ≤ 7, are generated by adding
  a new *minimal* element whose up-set is an order filter. A refined-
  partition canonical form is used. The counts are 1, 2, 5, 16, 63, 318,
  2045 posets and 1, 1, 3, 10, 44, 238, 1650 connected, matching OEIS
  A000112 and A000608 `[count]`. Disconnected posets with n ≤ 8 are the
  multisets of ≥ 2 connected ones. Their counts, 1, 2, 6, 19, 80, 395, 2487,
  agree with A000112 − A000608 (2487 = 16999 − 14512).
- **[def]: membership from the definition.** Membership is decided by
  sparse Gaussian elimination against the defining generators s ⧢ t, one
  graded piece at a time. Each generator is checked to be homogeneous, so
  this step does not assume Lemma 4. It uses neither Ree's theorem nor
  W_P ∩ Sh_n = R_P. Every generator r is tested in [Aud]'s own order, until
  the first r with ∂r ∉ R_P. Two primes are used, and they must agree. The
  run covers every poset whose graded pieces have dimension
  ≤ 1680: all 108 with n ≤ 6, 393 of 395 with n = 7 and 2476 of 2487 with
  n = 8, 2977 of 2990 in total. Result: the posets with the property are
  exactly the two-chain posets. **Positive control: 9 of 108 at n ≤ 6,**
  reproducing [LE] §2.
- **[cert]: the note's certificates, checked against the definition.** For
  every one of the 2974 posets outside the family, [Aud] builds the note's
  r and φ (case A) or ψ (case B) and computes ∂r by toggles. It verifies
  over Z that the functional pairs to 0 with **every** defining generator
  s ⧢ t. It does this by summing the functional over the Lin P words with a
  given (w|_S, w|_{S^c}), so it does not appeal to Ree. It also verifies
  that the functional pairs to exactly 1 with ∂r. The counts are 2932 case A
  and 42 case B, as in [N]. All four quantities are rigorous. For n ≤ 6,
  every T and every pair (s, t) is tested, which covers the Remark. For
  n = 7, 8, one random T and two random pairs are tested per poset
  (seed 1).
- **The "if" direction** is checked from the generators: on all 16
  two-chain posets, every generator equals Σ_{w ∈ Lin P} w.
- **Controls `[ctl]`.** A single word is rejected as a functional on R_{A_3}.
  [def] accepts a generator and rejects a single word.

Together, [cert] proves non-preservation for all 2974 posets outside the
family, and [def] confirms the dichotomy independently of the note's choice
of r on 2977 of the 2990. **COMPUTED: 16 of 2990, exactly the two-chain
posets** (1, 1, 2, 2, 3, 3, 4 for n = 2, …, 8). This agrees with [N] §3 row
by row.

Limits: [def] works modulo two primes. A false "∈" would need both primes to
divide one specific minor, and every "∉" it reports is also certified by
[cert]. [def] was not run on the 13 posets whose graded pieces exceed 1680
(for example A_7, C_2 ⊔ A_6, A_8). For those, the conclusion rests on [cert]
alone, which is rigorous.

## 5. Fixes

- **F1 (Lemma 2, precision).** "X a linear combination of words on
  [n] ∖ {z}" should read "of words of length n − 1 using each letter of
  [n] ∖ {z} once". Otherwise Xz is not in C[S_n] and the pairing with
  ρ(az) ∈ Lie_n is not the one Ree's theorem controls. Every use in [N]
  (X = s″ ⧢ t, s̃ ⧢ (t − ∂_B t)) satisfies this.
- **F2 (§ Verdict, wording).** "The two families meet only in C_1 ⊔ C_1
  (n = 2), where only the C[Lin P]/R_P side makes sense" can be read as
  "only the right-hand column applies", which is false, since both columns
  apply to C_1 ⊔ C_1. The intended meaning, from [LE] §2, is that the
  identification with H_P ⊗ sgn needs n ≥ 3. Suggested wording: "where the
  identification C[Lin P]/R_P ≅ H_P ⊗ sgn is not available (it needs
  n ≥ 3)".
- **F3 (§4, an owed correction).** [LE] §6 open problem 1 and the §2
  verdict line still read CONJECTURED. [N] §4 says so, but [LE] itself is
  unchanged. A reader of [LE] alone will not learn that the problem is
  settled. Per standing practice, existing notes are not edited here. A
  forward pointer from [LE] to [N] is the remaining follow-up.

## 6. Prior art (quick check)

Searches made (web, 2026-10-31):
1. "promotion linear extensions Lie module poset shuffle quotient";
2. "multilinear Lie representation poset linear extensions promotion action
   Whitehouse module";
3. "Schützenberger promotion acts on quotient by shuffles free Lie algebra
   cyclic action Lie_n";
4. "promotion linear extensions free Lie algebra / Lie elements / Ree's
   theorem disjoint union posets".

**Result: NOT FOUND.** No source found studies promotion acting on a
Lie-type quotient C[Lin P]/R_P, or on a poset version of the multilinear Lie
module. The nearest items were:
- the promotion Markov-chain papers (Ayyer–Klee–Schilling, arXiv:1205.7074,
  1307.7499; arXiv:1708.03633). 1205.7074 characterizes unions of disjoint
  chains as the posets on which the extended promotion operators satisfy
  the braid relations. This is a different property with a similar
  dichotomy, but not prior art for Theorem 1;
- Hopkins, *Order polynomial product formulas and poset dynamics*
  (arXiv:2006.01568), on promotion and Lie-theoretic indexing of P-partitions,
  not Lie modules of shuffles;
- the Whitehouse / cyclic Lie module literature (e.g. arXiv:2203.09504), with
  shuffle-quotient presentations of Lie-type modules but no promotion.

The repo's own `notes/prior_art_linear_extensions.md` covers Lemma P (known
for chains and rectangles) and finds no source for the R_P question either.
"Not found" is the result of four searches, not a proof of novelty.

## Reproduce

```
cd compute
python3 audit_promotion_on_R_P.py --nmax 8 > output/audit_promotion_on_R_P.txt   # ~17 s, one core
python3 audit_promotion_on_R_P.py --nmax 6                                       # ~3 s
python3 -m unittest test_audit_promotion_on_R_P
```

Pure Python 3, standard library only. The script exits with status 0 iff
every check passes and every control fires. The tags in brackets above
(`[count]`, `[ree]`, `[sweep]`, `[total]`, `[control]`, `[ctl]`) are its
line labels. The archived output is `compute/output/audit_promotion_on_R_P.txt`.
