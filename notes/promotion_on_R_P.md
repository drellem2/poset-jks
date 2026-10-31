# When does promotion preserve R_P?

This note settles open problem 1 of `notes/linear_extensions.md` [LE]: for
which disconnected posets P does promotion ∂ map R_P into itself, and so act
on C[Lin P]/R_P? Each claim is tagged **PROVEN**, **COMPUTED** or **CITED**.

## Verdict

**PROVEN: the conjecture holds.** Let P be a disconnected finite poset.
Then ∂(R_P) ⊆ R_P iff P has exactly two connected components and both are
chains. **COMPUTED** as well, for every disconnected poset with n ≤ 8:
16 of the 2990 disconnected posets have the property, and they are exactly the
two-chain posets. As a positive control the computation reproduces the 9 of
108 at n ≤ 6 reported in [LE] §2.

[LE] §2 already proved the "if" direction. The new part is "only if". For
each P outside the family, an explicit generator r of R_P has ∂r ∉ R_P, and an
explicit Lie element pairs nonzero with ∂r (or with a graded piece of ∂r)
while vanishing on R_P.

Together with [LE] Proposition D this gives the full picture of promotion on
the two models. Let P be disconnected.

| model | ∂ acts iff | source |
|---|---|---|
| PLie(P) = C[Lin P]/K_P | P is an antichain | [LE] Prop. D |
| C[Lin P]/R_P (≅ H_P ⊗ sgn for n ≥ 3) | P is a disjoint union of two chains | Theorem 1 below |

For connected P, K_P = R_P = 0 and ∂ acts on both models. The two families
meet only in C_1 ⊔ C_1 (n = 2), where only the C[Lin P]/R_P side makes sense
([LE] §2).

Tags: [LE] = `notes/linear_extensions.md`; [Thm] =
`notes/poset_jks_theorem.tex`. Ree's theorem, Lie_n = Sh_n^⊥ in C[S_n] under
the pairing that makes words orthonormal, is **CITED** as in [LE] §5.

## 0. Conventions

We use the conventions of [LE] §0. P is a poset on [n] with components
T_1, …, T_k, where k ≥ 2. A linear extension is a word w = w_1 ⋯ w_n, and
W_P = C[Lin P]. Promotion is ∂ = τ_{n−1} ∘ ⋯ ∘ τ_1, with τ_1 applied first;
τ_i swaps positions i and i+1 when the two letters are incomparable. For a
subposet Q (always a union of components here), ∂_Q is promotion on Lin Q.
We have

  R_P = span{ s ⧢ t : S a nonempty proper union of components, s ∈ Lin(P|_S), t ∈ Lin(P|_{S^c}) }

([Thm] eq. before Thm `thm:S`), and R_P ⊆ Sh_n, where Sh_n is the span of all
proper shuffles of words on complementary letter sets. For a word u, ũ is u
with its last letter deleted. For a word c = c_1 ⋯ c_m on distinct letters,
ρ(c) = [c_1, [c_2, …, [c_{m−1}, c_m]…]] is the right-normed bracket.

## 1. Four lemmas

**Lemma 1 (PROVEN).** Let Q be a poset. If Q is a chain, then
|Lin Q| = 1 and ∂_Q = id. If Q is not a chain, then ∂_Q has no fixed point
on Lin Q. In particular, a union of two or more components has no fixed
point.

*Proof.* The chain case is clear. Suppose ∂_Q(w) = w. If w_1 ∥ w_2, then τ_1
puts w_2 in position 1, and no later toggle touches position 1, so
∂_Q(w)_1 = w_2 ≠ w_1. Hence w_1 < w_2. Then τ_1 does nothing, and the letter
in position 2 before τ_2 is w_2. The same argument at positions 2, 3, …
gives w_1 < w_2 < ⋯ < w_m, so Q is a chain. This is the argument of
[LE] Prop. E. A union of two or more components is not connected, so it is
not a chain. ∎

**Lemma 2 (PROVEN, from Ree).** Let z ∈ [n], and let X ≠ 0 be a linear
combination of words on [n] ∖ {z}. Then Xz ∉ Sh_n. More precisely, if a is a
word with coefficient X(a) ≠ 0, then ρ(az) ∈ Lie_n and ⟨ρ(az), Xz⟩ = X(a).

*Proof.* We have ρ(b_1 ⋯ b_m) = b_1 ρ(b_2 ⋯ b_m) − ρ(b_2 ⋯ b_m) b_1. The
second term has words ending in b_1 ≠ b_m. So, by induction, the only word
of ρ(b) that ends in b_m is b itself, with coefficient +1. Hence
⟨ρ(az), uz⟩ = δ_{u,a} for every word u on [n] ∖ {z}. Since ρ(az) ∈ Lie_n is
orthogonal to Sh_n (Ree), Xz ∉ Sh_n. ∎

(This is the familiar fact that the right-normed brackets ending in a fixed
letter form a basis of Lie_n. We use only the triangularity.)

**Lemma 3 (PROVEN, from [LE] Lemma P).** Let A be a nonempty proper union of
components and B = [n] ∖ A. Take s ∈ Lin A and t ∈ Lin B, and write
∂_A(s) = s″z and ∂_B(t) = t″y, where z and y are the last letters. Then

  ∂(s ⧢ t) = (s″ ⧢ t)·z + (s ⧢ t″)·y.

Every word in the first sum has A-part ∂_A(s) and B-part t. Every word in the
second has A-part s and B-part ∂_B(t).

*Proof.* The words of s ⧢ t are distinct, because the letter sets are
disjoint. They are exactly the words with A-part s, B-part t and any pattern
in {A, B}^n with |A| letters A. Take one such word w that starts with an
A-letter. By [LE] Lemma P, ∂(w) has A-part ∂_A(s), B-part t and the rotated
pattern, which ends in A. So ∂(w) ends in z. As the pattern runs over the
patterns starting with A, the rotated pattern runs over those ending with A.
So these words contribute (s″ ⧢ t)z. The words that start with a B-letter
contribute (s ⧢ t″)y in the same way, with A and B exchanged. ∎

**Lemma 4 (PROVEN; the homogeneity part of [LE] Thm M).** Grade W_P by the
restriction tuple x(w) = (w|_{T_1}, …, w|_{T_k}). Then R_P is spanned by
homogeneous vectors. So Y ∈ R_P iff every homogeneous component of Y lies in
R_P. More generally, the sum of the components of Y over any set of grades
lies in R_P.

*Proof.* All the words of a generator s ⧢ t have the same restriction tuple.
Write Y ∈ R_P as a combination of generators and group the generators by
grade. ∎

## 2. The theorem

**Theorem 1 (PROVEN).** Let P be a disconnected finite poset. Then
∂(R_P) ⊆ R_P iff P has exactly two components and both are chains.

*Proof of "if" ([LE] §2).* Let P = C_a ⊔ C_b. Each Lin(P|_S) is a single word,
and the only generators are s ⧢ t and t ⧢ s, both equal to Σ_{w ∈ Lin P} w.
So R_P = C · Σ_{w ∈ Lin P} w. This vector is fixed by ∂, because ∂ permutes
Lin P. ∎

*Proof of "only if".* Every disconnected P outside the family falls into
exactly one of the two cases below. Either some component is not a chain
(case A), or all k components are chains and k ≥ 3 (case B). This covers
both situations named in the problem: (i) three or more components, which
is case A or case B; and (ii) two components, one of them not a chain, which
is case A. No configuration is left over.

**Case A: some component T is not a chain.** Put A = T and B = [n] ∖ T, and
choose any s ∈ Lin T and t ∈ Lin B. Then r = s ⧢ t ∈ R_P. By Lemma 3,
∂r = Y_1 + Y_2 with

  Y_1 = (s″ ⧢ t)·z  (T-part ∂_T(s)),   Y_2 = (s ⧢ t″)·y  (T-part s).

By Lemma 1, ∂_T(s) ≠ s. So Y_1 is exactly the sum of the homogeneous
components of ∂r whose T-coordinate is ∂_T(s). If ∂r ∈ R_P, then
Y_1 ∈ R_P ⊆ Sh_n by Lemma 4. But X = s″ ⧢ t ≠ 0, so Y_1 = Xz ∉ Sh_n by
Lemma 2. Hence ∂r ∉ R_P.

Here is an explicit certificate. Let φ(Y) = ⟨ρ(s″ t z), Y_{[T = ∂_T s]}⟩,
where Y_{[T = ∂_T s]} keeps the words of Y whose T-part is ∂_T(s). By
Lemma 4 and Ree, φ vanishes on R_P. Also φ(∂r) = ⟨ρ(s″tz), (s″ ⧢ t)z⟩ = 1,
since the concatenation s″t occurs in s″ ⧢ t with coefficient 1.

**Case B: all components are chains, and k ≥ 3.** Let T be any component,
with s its unique linear extension, and let B = [n] ∖ T. Choose any
t ∈ Lin B, and put r = s ⧢ t ∈ R_P. Write σ for the last letter of s. By
Lemma 1, ∂_T(s) = s, so s″ = s̃ and z = σ in Lemma 3. B is a union of
k − 1 ≥ 2 components, so ∂_B(t) ≠ t by Lemma 1. Now r′ = s ⧢ ∂_B(t) ∈ R_P.
Splitting it by its last letter gives

  r′ = s ⧢ (t″y) = (s ⧢ t″)·y + (s̃ ⧢ ∂_B t)·σ.

With Lemma 3 this gives

  ∂r − r′ = (s̃ ⧢ (t − ∂_B t))·σ.

The coefficient of s̃t in s̃ ⧢ (t − ∂_B t) is 1, because every word of
s̃ ⧢ ∂_B t has B-part ∂_B(t) ≠ t. By Lemma 2, ψ = ρ(s̃ t σ) ∈ Lie_n satisfies
⟨ψ, ∂r − r′⟩ = 1. Since ψ vanishes on Sh_n ⊇ R_P ∋ r′, we get
⟨ψ, ∂r⟩ = 1 while ψ(R_P) = 0. So ∂r ∉ R_P. (If T is a single point, s̃ is
empty.) ∎

**Smallest examples.**
- *A_3, three points (case B).* Take T = {0}, s = 0 and t = 12. Then
  r = 012 + 102 + 120. Since ∂ is rotation, ∂r = 120 + 021 + 201. With
  ∂_B(12) = 21, the certificate is
  ψ = ρ(120) = [1,[2,0]] = 120 − 102 − 201 + 021, and ⟨ψ, ∂r⟩ = 1 + 1 − 1 = 1.
  This is the remark in [LE] §2 that γ does not preserve Sh_3.
- *C_2 ⊔ C_1 ⊔ C_1, the smallest case B with a non-trivial chain.* This is
  the m = (2,1,1) example in [LE] §8.
- *V ⊔ C_1 with V = {0 < 1, 0 < 2} (case A, n = 4).* Take s = 012 ∈ Lin V and
  t = 3. Then ∂_V(012) = 021, so s″ = 02 and z = 1. The graded piece is
  Y_1 = (02 ⧢ 3)·1 = 0231 + 0321 + 3021, and φ(∂r) = ⟨ρ(0231), Y_1⟩ = 1.

**Remark.** Case A proves more than the theorem needs. Even the graded piece
of ∂(s ⧢ t) in which T has moved is outside Sh_n, for every choice of s and
t. So for P with a non-chain component T, no generator s ⧢ t with S = T is
mapped into R_P.

## 3. Computation

**COMPUTED (`compute/promotion_on_R_P.py`, `[descend-R]`, `[proof]`).**

| n | posets | disconnected | ∂(R_P) ⊆ R_P | component sizes of those |
|---|---|---|---|---|
| 2 | 2 | 1 | 1 | (1,1) |
| 3 | 5 | 2 | 1 | (1,2) |
| 4 | 16 | 6 | 2 | (1,3), (2,2) |
| 5 | 63 | 19 | 2 | (1,4), (2,3) |
| 6 | 318 | 80 | 3 | (1,5), (2,4), (3,3) |
| 7 | 2045 | 395 | 3 | (1,6), (2,5), (3,4) |
| 8 | 16999 | 2487 | 4 | (1,7), (2,6), (3,5), (4,4) |

In every row the posets with the property are exactly the two-chain posets.
The cumulative count for n ≤ 6 is 9 of 108, as in [LE] §2 (positive control,
`[control]`). For all n ≤ 8, the specific r of the proof gives ∂r ∉ R_P on
every one of the 2974 posets outside the family: 2932 in case A and 42 in
case B. In case A, the graded piece Y_1 was also checked separately: it equals
(s″ ⧢ t)z and lies outside Sh_n.

*Method.* The code is independent of `compute/linear_extensions.py`.
- Posets are generated up to isomorphism, by adding a maximal element, with a
  brute-force canonical form. The counts match OEIS A000112 (all posets) and
  A000608 (connected posets), `[count]`.
- Promotion is computed by toggles; Lemma P is not used.
- Membership uses W_P ∩ Sh_n = R_P ([Thm] Thm `thm:S`(b)) and Ree's theorem.
  Lie_n has basis ρ(c n), where c runs over the orderings of [n−1], and
  ⟨ρ(c n), L n R⟩ = (−1)^{|R|} [c ∈ L ⧢ rev R]. So Y ∈ R_P iff
  π(Y) = Σ_w Y(w) (−1)^{|R_w|} (L_w ⧢ rev R_w) is zero. All arithmetic is
  exact, over the integers.
- ∂(R_P) ⊆ R_P iff π(∂r) = 0 for every generator r. For the family posets
  every generator is checked. For the others the first failing generator is
  recorded.
- Instrument checks, `[pair]`, `[ree]`, `[ctl]`, for n ≤ 5:
  - the pairing formula, checked against the expanded brackets;
  - π kills every shuffle;
  - dim Sh_n = n! − (n−1)!, and rank π = (n−1)!, computed over Q;
  - a vector Xz is detected as non-shuffle.

## 4. Corrections and remarks on existing notes

- No errors were found in [LE]. Its §6.1 phrase "only for n ≤ 2, for
  connected P and for two chains" contains a redundancy. The only poset with
  n ≤ 2 that is disconnected is C_1 ⊔ C_1, which is two chains, and every
  poset with n = 1 is connected. Theorem 1 answers §6.1 affirmatively.
- [LE] §2 lists the "only if" direction as CONJECTURED. It is now PROVEN
  (Theorem 1).

## Reproduce

From `compute/` (plain Python 3, no dependencies; about 3 s on one core):

    python3 promotion_on_R_P.py --nmax 8 > output/promotion_on_R_P.txt
    python3 -m unittest test_promotion_on_R_P

The script exits with status 0 iff every check holds and every control
behaves as intended. The archived output is
`compute/output/promotion_on_R_P.txt`. The bracketed tags above are its line
labels. `--nmax 7` takes well under a second.
