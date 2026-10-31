# Audit of Proposition E in `notes/prior_art_cyclic_sieving_cyc_2.md`

**Verdict.**

| # | Claim | Verdict |
|---|---|---|
| 1 | Proposition E (PROVEN): f_χ(ζ) as a sum over M = {g : dim V(g, ζ^{−1}) = a} | **HOLDS** |
| 2 | Type-A specialisation, the displayed X(ζ) formula for W = S_k | **HOLDS** |
| 3 | "How [CSC] Theorem B follows", cases (ii) and (i); clause (a) ↔ a(e) = 0 | **FIXABLE** (F1–F3, all wording or a dropped nonzero factor; no conclusion changes) |
| 4 | §2 quotes from [Sp74] and Lehrer–Michel 2003 | **HOLDS** for every quote checked; Stembridge 1989 not re-obtained |

The note audited is cited as [N]. `notes/cyclic_sieving_cyc.md` is [CSC].
The re-derivations below are my own. The computations are in
`compute/audit_prior_art_cyclic_sieving_cyc_2.py` ("[Aud]"). It is plain
Python 3, imports nothing from `compute/` and nothing from the author's
uncommitted check script, and has its own positive controls. I re-obtained
[Sp74] (scan on N. Wallach's UCSD page, OCR text via `pdftotext -layout`),
Lehrer–Michel 2003 (Numdam) and Geck–Malle (arXiv:math/0311012v2).

## 1. Proposition E

**Re-derivation.** Write f_χ(q) = |G|^{−1} Σ_g χ(g) N(q)/D_g(q), with
N(q) = ∏_i (1 − q^{d_i}) and D_g(q) = det(1 − qg) = ∏_μ (1 − qμ), where μ
runs over the eigenvalues of g. g has finite order, so it is diagonalisable,
and algebraic and geometric multiplicities agree.

- *Denominator.* 1 − ζμ = 0 iff μ = ζ^{−1}, so D_g has a zero at q = ζ of
  order exactly dim V(g, ζ^{−1}). Each such factor is literally 1 − q/ζ.
- *Numerator.* 1 − q^d has simple roots. It vanishes at ζ iff e | d. For
  e | d, its derivative at ζ is −dζ^{d−1} = −dζ^{−1}, so
  1 − q^d = −dζ^{−1}(q − ζ) + O((q − ζ)²) = d(1 − q/ζ) + O((q − ζ)²). This
  matches [N]. For e ∤ d, the factor is 1 − ζ^d ≠ 0. So N has a zero of
  order exactly a, with leading coefficient ∏_{i∈A} d_i ∏_{i∉A}(1 − ζ^{d_i})
  in powers of (1 − q/ζ).
- *Bound.* [Sp74] Thm 3.4(i) (quoted in §4): for **every** root of unity
  ζ′ of order d, max_g dim V(g, ζ′) = a(d). The statement fixes "a root of
  unity ζ ∈ k* of order d" (§3.1, p. 167) and nowhere assumes regularity.
  Regularity enters only in §4. ζ^{−1} has order e, so dim V(g, ζ^{−1}) ≤ a
  for all g. Only the inequality is used. If the maximum were not attained,
  M would be empty and the formula would still hold. Springer proves the
  equality anyway.
- *Assembly.* The term of g has order of vanishing a − dim V(g, ζ^{−1}) ≥ 0
  at ζ. Terms with dim < a vanish there. For g ∈ M, the a factors (1 − q/ζ)
  cancel exactly, which leaves ∏_{i∈A} d_i ∏_{i∉A}(1 − ζ^{d_i}) ·
  ∏_{λ ≠ ζ^{−1}} (1 − ζλ)^{−1}, a finite nonzero product. Summing gives the
  displayed formula, including the |G|^{−1}.

**Orientation.** At q = ζ the poles come from eigenvalue ζ^{−1}, so
"M defined by ζ^{−1}" and "1 − ζλ" are both right. This agrees with
Springer: his (1) in the proof of 4.5 is the Molien sum at q = ζ^{−1}T, so
at T = 1 the poles come from eigenvalue ζ, and he gets χ(g) = f_χ(ζ^{−1})
for g regular with eigenvalue ζ. Springer's f_χ (2.5–2.6:
|G|^{−1}Σ χ(g) det(1 − gT)^{−1} = f_χ(T) ∏(1 − T^{d_i})^{−1}) is exactly the
f_χ of [N], with no complex conjugate. The orientation does not matter
for [CSC]: there χ = F is a permutation character, so F(g) = F(g^{−1}).

**Two remarks** (neither is a defect):
- The proof never uses that χ is a class function. Proposition E holds
  term by term for any function χ : G → C.
- "PROVEN" is justified. The only input is [Sp74] Thm 3.4(i), and that is
  correctly cited.

**Numerical check (COMPUTED, [Aud] `[sp34]`, `[propE]`).** The groups are
G(m, p, n) for (m, p, n) ∈ {(3,1,2), (4,2,2), (4,1,2), (6,2,2), (6,3,2),
(5,1,2), (2,1,3), (3,3,3), (2,2,4), (3,1,3), (4,4,3), (4,2,3), (2,1,4),
(2,2,5)}. Most of them are non-real. They include B_3, B_4, D_4, D_5 and
groups with repeated degrees.
- f_χ(ζ) is computed without the cancellation argument. The defining
  Molien sum is evaluated on |q| = 0.6, with det(1 − qg) taken from the
  matrix by Gaussian elimination, and the polynomial is recovered by an
  inverse DFT. Its degree bound is checked by a vanishing tail and by
  reproducing the sum at an unrelated point. It is then evaluated at
  ζ = e^{2πi/e}.
- The right-hand side uses exact eigen-angles in Q/Z. On every element
  these angles are checked against the matrix's det(1 − qg) (`[eig]`).
- Springer 3.4(i) holds for ζ and ζ^{−1} for every e ≤ max d_i + 2 in
  every group (`[sp34]`). Regularity was decided by brute force: does some
  ζ-eigenvector lie on no reflecting hyperplane? This instrument reproduces
  Springer's known lists for B_n (d | 2n) and D_n (d | 2(n − 1) or d | n).
- Proposition E, with random complex class functions: **113/113** (group, e)
  cases agree. 71 are at a non-regular e, and 11 of those have a(e) ≥ 1,
  which is the case that matters. Examples are B_4 with e = 3, 6, and
  G(3,1,3) with e = 2, 6.
- Positive controls (`[ctl]`), over the 39 cases with a ≥ 1 and e ≥ 3:
  - Omitting ∏_{i∈A} d_i fails in 39/39.
  - Flipping the orientation (the whole formula taken at ζ^{−1}) fails in
    25/39. The other 14 are cases where f_χ(ζ) = f_χ(ζ^{−1}) is forced: ζ
    and ζ^{−1} are G-conjugate eigenvalues, as for the real groups B_3, D_4
    at regular e. At e = 2 the flip is the identity, so e = 2 is excluded.

## 2. The type-A formula

**Re-derivation.** For W = S_k on C^k, a p-cycle has eigenvalues the p-th
roots of unity, each with multiplicity 1. So dim V(w, ζ^{−1}) is the number
of cycles of length divisible by e. ✓

For a p-cycle, ∏_{μ^p = 1}(1 − xμ) = 1 − x^p. If e ∤ p, then at x = ζ the
cycle contributes 1 − ζ^p. ✓ If e | p, remove the factor μ = ζ^{−1}:
lim_{x→ζ}(1 − x^p)/(1 − x/ζ) = (−pζ^{p−1})/(−ζ^{−1}) = pζ^p = p. ✓

The degrees are 1, …, k. A = {e, 2e, …, ⌊k/e⌋e}, so
∏_{i∈A} d_i = e^{⌊k/e⌋}⌊k/e⌋!. ✓ ∏_{i∉A}(1 − ζ^{d_i}) =
∏_{j≤k, e∤j}(1 − ζ^j). ✓ A class of type λ has |W|/z_λ elements. ✓ The
displayed X(ζ) formula follows.

**Numerical check (COMPUTED, [Aud] `[typeA]`).** For k = 2..8, e = 2..k+2
(this includes e > k, where a = 0) and **every** primitive e-th root, not
only e^{2πi/e}, with random integer F on partitions:
- X(q) is computed **exactly over Q**, by polynomial division of
  ∏(1 − q^j) by ∏_p(1 − q^p), and evaluated at ζ. It agrees with the
  displayed formula in **121/121** cases. The cases include all seven
  non-regular (k, e) with a ≥ 1 in this range (e ∤ k, e ∤ k − 1, e ≤ k): (5,3), (6,4), (7,4), (7,5), (8,3), (8,5),
  (8,6).
- Positive control: the formula without e^{⌊k/e⌋}⌊k/e⌋! fails in
  **67/67** cases with a ≥ 1.

[N]'s own figures, 21/21 agreeing and 21/21 failing for the control, are
the author's and were not re-run. My script is independent and covers a
superset of k and e.

## 3. "How [CSC] Theorem B follows"

**Re-derivation.** By [CSC] Lemma 1, w ∈ supp F has every cycle of the same
length d, with d | k_i for all i. Then dim V(w, ζ^{−1}) is Σ k_i/d if e | d,
and 0 otherwise. Also a(e) = Σ⌊k_i/e⌋.

- **(ii)** e ≤ max k_i gives a ≥ 1. Membership in M needs e | d, and then
  e | k_i for all i, which contradicts the hypothesis. So M ∩ supp F = ∅
  and X_P(ζ) = 0. **HOLDS.**
- **(i)** e | every k_i. Then a = Σ k_i/e, and e | d with Σ k_i/d = Σ k_i/e
  forces d = e. Only w of type (e^{k_i/e}) survives. Its value:
  - ∏_{i∈A} d_i over all types is ∏_i e^{k_i/e}(k_i/e)!.
  - ∏_{j ≤ k_i, e∤j}(1 − ζ^j) = e^{k_i/e}, because ∏_{t=1}^{e−1}(1 − ζ^t) = e.
  - The class has |W|/∏ e^{k_i/e}(k_i/e)! elements.
  - Each e-cycle contributes 1/e.

  The product is exactly F(w_e). **HOLDS.**
- **Clause (a) ↔ a(e) = 0.** a(e) = Σ⌊k_i/e⌋ = 0 iff e > max k_i, which is
  exactly the failure of (a). **HOLDS.** Then dim V(g, ζ^{−1}) ≤ 0 for all
  g, so M = W.

[Aud] `[thmB]` checks (i) and (ii) on W = S_{k_1} × ⋯ for 14 choices of
(k_i), including (2,4), (4,6), (3,6), (2,2,4) and (5,2), with random
positive F on the Lemma-1 support: 45/45.

**Fixes.**
- **F1 (dropped factor).** [N] says that for a(e) = 0, "X_P(ζ) is the full
  weighted sum (1/|W|) Σ_w F(w) ∏(1 − ζλ)^{−1}". That omits the nonzero
  prefactor ∏_i ∏_{j≤k_i}(1 − ζ^j). Proposition E with A = ∅ gives
  X_P(ζ) = ∏_i (ζ; ζ)_{k_i} · (1/|W|) Σ_w F(w)/det(1 − ζw). This is just the
  definition evaluated at ζ. [Aud] confirms the corrected expression in
  28/28 cases with e > max k_i, and finds that [N]'s expression differs
  from X_P(ζ) in 27/28. The one exception is a case where both are 0. The
  conclusion "nothing forces it to vanish" is unaffected, because the
  prefactor is nonzero.
- **F2 (scope of OPEN).** "This is the case left OPEN in [CSC] §9
  problem 2". Only the subcase gcd(k_i) > 1 is open. For gcd(k_i) = 1,
  [CSC] Proposition 3 proves X_P(ζ) ≠ 0. Suggested wording: "…the case
  a(e) = 0. For gcd(k_i) = 1 it is settled by [CSC] Proposition 3; for
  gcd(k_i) > 1 it is [CSC] §9 problem 2 (OPEN)." A supporting observation
  ([Aud] `[thmB]`): for W = S_2 × S_2 and e = 4, the positive function F
  with F(1) = F(w_2) = 9 has X(q) = (9/2)(1 + q²), which vanishes at i.
  So support (Lemma 1) and positivity alone do not decide the a(e) = 0
  case. The values of F matter, as [CSC] says ("a proof must use y ≥ 1").
  This F is not claimed to come from a poset.
- **F3 (wording, case (i)).** "The elements of M ∩ supp F are exactly those
  of cycle type (e^{k_i/e})_i" should read "are contained in the class of
  cycle type (e^{k_i/e})_i". They are equal iff F(w_e) ≠ 0. The value
  F(w_e) is right either way.

## 4. Spot-check of the §2 quotes

| [N] says | Source text (re-obtained) | |
|---|---|---|
| [Sp74] Thm 3.4 (i) max dim V(g, ζ) = a(d); (ii) every V(g, ζ) lies in one of maximal dimension; (iii) maximal ones conjugate | p. 167–168: "3.4. Theorem. Let G be a complex reflection group. (i) max_{g∈G} dim V(g, ζ) = a(d)… (ii) For any g ∈ G there exists h ∈ G such that V(h, ζ) has maximal dimension a(d) and that V(g, ζ) ⊂ V(h, ζ). (iii) If dim V(g, ζ) = dim V(g′, ζ) = a(d) then there exists h ∈ G with h·V(g, ζ) = V(g′, ζ)." ζ is any root of unity of order d (§3.1) | ✓ |
| Prop. 4.5 proof quote "Multiply both sides of (1) by (1 − T)^{a(d)} … conjugate to g by 4.2(iv)." | p. 171, verbatim up to OCR | ✓ |
| Thm 4.2 for regular g, eigenvalues ζ^{−p_i} | 4.2 (i)–(v), (v) "The eigenvalues of g are ζ^{−p_i}, where the p_i are the exponents" | ✓ |
| §8: "…which will allow us to extend 4.6 and 4.8 to nonregular elements"; 4.6 = products of two involutions | p. 187 verbatim; 4.6 (i) "g = st" with two involutions | ✓; 4.8 (p. 172–173): for g regular in a Weyl group, "χ(g) is a rational integer" — rationality of characters, as [N] says |
| L–M Thm 2.3, = 0 unless a(d) = b_σ(d) | p. 798, eq. (4) | ✓ |
| L–M proof of 2.3 is a pole-order computation | p. 798–799: "has a zero of order d(g, ζ) at x = ζ^{−1} in the denominator … Since the pole at x = ζ^{−1} is removable, a(d) ⩽ b_σ(d)" | ✓ |
| L–M Thm 3.1: d regular iff a(d) = b(d) (codegrees) | p. 800, Thm 3.1(ii), σ = complex conjugation | ✓ |
| L–M proof of 3.1: {g : V(g, ζ) = E} is a coset g_0 C | p. 800 verbatim | ✓; precisely, M is the **union** of these cosets over the G-conjugates of E (by 3.4(iii)), as [N] intends |
| L–M Cor. 2.4–2.7 special cases of 2.3 | p. 799 | ✓ |
| L–M "no statement about fake degrees of a general module at ζ" | Prop. 2.2 is stated for any module M with Q_M ∈ C^× Q_{∧^r M}; Thm 2.3 and §3 use only M = V^σ. Nothing on fake degrees of a general module | ✓ |
| Geck–Malle Thm 1.10 = [Sp74] 3.4, 6.2; 1.11 = [Sp74] 6.4, 4.5 (regular); 1.12 Lehrer–Springer | arXiv v2 pp. 5–6 | ✓ |

Not re-obtained: Stembridge 1989 (the msp.org PDF link was not found in
this session), Koonin 2013, and the Lehrer–Taylor table of contents. Their
rows in [N] §2 are unaudited here. [N]'s gap at Lehrer–Taylor Ch. 11 §6
stands. Nothing in this audit closes it.

## Summary of fixes

- **F1**: §1, the a(e) = 0 sentence. Restore the factor ∏_i (ζ; ζ)_{k_i}.
- **F2**: §1, last sentence. Restrict "OPEN" to gcd(k_i) > 1 and cite
  [CSC] Proposition 3 for gcd(k_i) = 1.
- **F3**: §1, case (i). Replace "exactly" with "contained in the class of".
- Minor: §2, L–M bullet on the coset g_0C. "That is the structure of M"
  should say "M is the union of such cosets over the conjugates of E".

None of these changes a verdict of [N] or its §3 attribution fixes.

## Reproduce

```
cd compute
python3 audit_prior_art_cyclic_sieving_cyc_2.py > output/audit_prior_art_cyclic_sieving_cyc_2.txt   # ~10 s, one core; exit 0 iff all checks and controls pass
python3 -m unittest test_audit_prior_art_cyclic_sieving_cyc_2
```
