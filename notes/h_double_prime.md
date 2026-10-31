# H″: an all-ascent class always breaks min-des

Question (`notes/h_vector_omega_c.md` §2.4 and §4, row H″): fix a natural
labelling of P with n ≥ 2. Theorem H′ says that if no cyclic class is
all-ascent, then the distribution of min-des over Cyc(P) is h_C(P). Is the
converse true? That is, does an all-ascent class always make the min-des
distribution differ from h_C(P)?

Tags: **PROVEN** means proved here. **COMPUTED** means checked by
`compute/h_double_prime.py`; bracketed labels refer to the lines of
`compute/output/h_double_prime.txt`. **KNOWN** means it is in the
literature. **OPEN** means not settled.

Sources: [H] = `notes/h_vector_omega_c.md`, for the notation of §0, the
descent expansion (Proposition D) and the per-class lemma (Lemma 1), all
PROVEN + audited in [AudH] = `notes/audit_h_vector_omega_c.md`.

## Verdict

**H″ is PROVEN** (not yet audited). There is an exact formula for h_C(P)
under an *arbitrary* natural labelling. The formula shows that each
all-ascent class moves the first moment of the min-des distribution by
exactly one. Together with H′ this gives:

> For n ≥ 2 and any natural labelling, min-des on Cyc(P) realises h_C(P)
> **if and only if** no cyclic class is all-ascent.

So Theorem H′ of [H] becomes an iff. Write h_C(x) = Σ_j h_j x^j,
f(x) = Σ_{κ ∈ Cyc(P)} x^{mindes κ}, and A for the number of all-ascent
classes.

| # | Statement | Status |
|---|---|---|
| L3 | An all-ascent class with s pieces and d = Σ_k des(c_k) has 1 ≤ d ≤ n − s and min-des = d. For every component T, its rotations contribute C(m+n−d, n) − C(m+n−d−s, n−s) to the descent expansion | **PROVEN** (§1); COMPUTED `[aa-d]`, `[aa-class]` |
| F | Any natural labelling, n ≥ 2: h_C(x) = Σ_{κ not all-ascent} x^{mindes κ} + Σ_{κ all-ascent} x^{d_κ−1}(1 − (1−x)^{s_κ}) | **PROVEN** (§2); COMPUTED on all 101658 natural labellings of all posets with n ≤ 7 `[formula]` |
| M | Σ_κ mindes(κ) − Σ_j j·h_j = A, i.e. f′(1) − h_C′(1) = A | **PROVEN** (§3); COMPUTED `[moment]` |
| L | If A > 0 and d_0 is the least d over all-ascent classes, then h_{d_0} − f_{d_0} = Σ (s_κ − 1) over the all-ascent classes with d_κ = d_0, which is > 0 | **PROVEN** (§3) |
| H″ | A > 0 ⇒ the min-des distribution ≠ h_C(P). With H′: min-des realises h_C ⇔ A = 0 | **PROVEN** (§3); COMPUTED on all 1080 labelled posets with n ≤ 7 that have an all-ascent class (2 at n = 5, 46 at n = 6, 1032 at n = 7) `[iff]` |
| ✗ | min-des realises h_C on every natural labelling | **FALSE**: refuted on 1080 of 101658 `[ctl-mindes-all]` (positive control) |
| ✗ | F with (1−x)^{s−1}, or with x^d in place of x^{d−1} | **FALSE**: refuted on 1080 of 1080 `[ctl-formula-s1]`, `[ctl-formula-d]` |
| ✗ | M with right-hand side 0 | **FALSE**: refuted on 1080 of 101658 `[ctl-moment-0]` |

The computation reproduces the 48 labelled posets with n ≤ 6 found in [H]
`[ctl-mindes-asc]`. It found no counterexample at n = 7. A full n = 8 sweep
was not run, because it would exceed the time bound (§5). The proof covers
every n.

## 1. The contribution of an all-ascent class

We use the notation of [H] §0. Fix a natural labelling and n ≥ 2. A class κ
has pieces c_1, …, c_s, junction indicators δ_k, d = Σ des(c_k), and
jd = Σ δ_k. It is all-ascent when s ≥ 2 and jd = 0. By [H] §0, the rotation
broken at junction J_i has des = d + jd − δ_i.

**Lemma 3 (PROVEN; COMPUTED `[aa-d]`, `[aa-class]`).** Let κ be all-ascent.
- (a) 1 ≤ d ≤ n − s, so s ≤ n − 1.
- (b) Every member of κ has des = d, so mindes κ = d.
- (c) For every component T and every integer m ≥ 0, with M = m + n − 1 − d,

    Σ_{w ∈ κ} N_T(w, m) = Σ_{i=0}^{s−1} C(M − i, n − i) = C(m + n − d, n) − C(m + n − d − s, n − s),

  where N_T is as in Proposition D of [H].

*Proof.*
- (a) des(c_k) ≤ |c_k| − 1, so d ≤ n − s. Suppose d = 0. Then every piece
  is increasing, and every junction is an ascent. Reading the word
  c_1 c_2 ⋯ c_s cyclically, every consecutive pair would increase, so
  w_1 < w_2 < ⋯ < w_n < w_1. That is impossible, so d ≥ 1.
- (b) All δ_i = 0, so every rotation has des = d + 0 − 0 = d.
- (c) Index the pieces so that T ⊆ c_s, and let R_i = c_{i+1} ⋯ c_s c_1 ⋯ c_i
  for 0 ≤ i ≤ s − 1, as in the proof of Lemma 1 of [H]. As shown there,
  |C_T(R_i)| = i, and the positions in C_T(R_i) are junctions J_s, J_1, …,
  J_{i−1}. Every junction is an ascent, so C_T(R_i) ∩ Des(R_i) = ∅. Hence
  every rotation contributes, and N_T(R_i, m) = C(M − i, n − i).

  For the closed form, use Pascal's rule
  C(a + 1, b) = C(a, b) + C(a, b − 1), valid for integers a ≥ 0 and b ≥ 1.
  With a = M − i and b = n − i it reads

    C(M + 1 − i, n − i) = C(M − i, n − i) + C(M + 1 − (i + 1), n − (i + 1)).

  Summing over i = 0, …, s − 1 telescopes to
  C(M + 1, n) = Σ_{i=0}^{s−1} C(M − i, n − i) + C(M + 1 − s, n − s).
  The hypotheses hold because a = M − i ≥ m + n − 1 − (n − s) − (s − 1) = m ≥ 0
  by (a), and b = n − i ≥ n − s + 1 ≥ 1. ∎

Every binomial in (c) has a nonnegative top, for every m ≥ 0. So (c) is
also an identity of polynomials in m, where C(t, k) means
t(t − 1)⋯(t − k + 1)/k!. The same holds for Lemma 1 of [H]: its top
m + n − 1 − stat is ≥ m, because stat ≤ n − 1.

## 2. The h-vector under an arbitrary natural labelling

h_C is defined by Ω_C(P, m) = Σ_j h_j C(m + n − 1 − j, n), which is
equivalent to Σ_{m ≥ 0} Ω_C(P, m) x^m = x·h_C(x)/(1 − x)^{n+1} ([H] §0). Say
that a polynomial p(m) **has h-polynomial** H(x) if
Σ_{m≥0} p(m) x^m = x·H(x)/(1 − x)^{n+1}. This is linear in p.

**Dictionary.**
- (i) For 0 ≤ j ≤ n − 1, the polynomial C(m + n − 1 − j, n) has
  h-polynomial x^j. It vanishes at m = 0, …, j, since its top runs over
  n − 1 − j, …, n − 1 ⊆ [0, n − 1]. For m ≥ j + 1 it equals C(u + n, n) with
  u = m − j − 1, and Σ_u C(u + n, n) x^u = 1/(1 − x)^{n+1}.
- (ii) Let 1 ≤ d ≤ k := n − s. The polynomial q(m) = C(m + k − d, k) has
  h-polynomial x^{d−1}(1 − x)^s. For 0 ≤ m ≤ d − 1 the top lies in
  [k − d, k − 1] ⊆ [0, k − 1], so q(m) = 0. For m ≥ d, q(m) = C(u + k, k) with
  u = m − d. Hence Σ_m q(m) x^m = x^d/(1 − x)^{k+1}
  = x·x^{d−1}(1 − x)^s/(1 − x)^{n+1}.

**Theorem F (PROVEN; COMPUTED `[formula]`).** Let n ≥ 2 and fix any natural
labelling. Then

  h_C(P)(x) = Σ_{κ not all-ascent} x^{mindes κ} + Σ_{κ all-ascent} x^{d_κ − 1}(1 − (1 − x)^{s_κ}).

*Proof.* Fix a component T. By Proposition D of [H], Ω_C(P, m) is the sum
over classes of Σ_{w∈κ} N_T(w, m), for every m ≥ 1. A class that is not
all-ascent contributes C(m + n − 1 − mindes κ, n) (Lemma 1 of [H]). An
all-ascent class contributes C(m + n − d, n) − C(m + n − d − s, n − s)
(Lemma 3). Each is a polynomial identity (end of §1), and two polynomials
that agree for all m ≥ 1 are equal. Apply the dictionary. By (i), the first
kind of class gives x^{mindes κ}. The term C(m + n − d, n) is (i) with
j = d − 1 ∈ [0, n − 1], by Lemma 3(a), so it gives x^{d−1}. The term
C(m + n − d − s, n − s) is (ii), so it gives x^{d−1}(1 − x)^s. ∎

When A = 0 this is H′ of [H]. When A > 0 the right-hand side has negative
coefficients (for s = 2, an all-ascent class gives 2x^d − x^{d+1}). So
Theorem F is an exact formula, not a combinatorial interpretation. The
worked example of [H] §2.4 (0 < 1, 3 < 4, 2 isolated) has one all-ascent
class, 3041 | 2, with d = 2 and s = 2. Theorem F gives
h_C = f + (2x² − x³) − x² = f + x² − x³, which takes f = (1, 9, 8, 2) to
(1, 9, 9, 1). This is checked in `test_h_double_prime.py`.

## 3. H″

By Lemma 3(b), f(x) = Σ_κ x^{mindes κ} gives x^{d_κ} to an all-ascent
class. Subtracting Theorem F from f gives

  f(x) − h_C(x) = Σ_{κ all-ascent} g_κ(x),
  g_κ(x) = x^{d−1}[x − 1 + (1 − x)^s] = −x^{d−1}(1 − x)[1 − (1 − x)^{s−1}].

**Corollary M (PROVEN; COMPUTED `[moment]`).** f(1) = h_C(1) = e_C(P), and

  Σ_κ mindes(κ) − Σ_j j·h_j = f′(1) − h_C′(1) = A.

*Proof.* g_κ(1) = 0. Write g_κ = −(1 − x)u(x) with
u(x) = x^{d−1}(1 − (1 − x)^{s−1}). Then g_κ′(1) = u(1) = 1, since s ≥ 2. ∎

**Corollary L (PROVEN).** Suppose A > 0, and let d_0 be the least d_κ over
the all-ascent classes. Then f and h_C agree below degree d_0, and

  h_{d_0} − f_{d_0} = Σ_{κ all-ascent, d_κ = d_0} (s_κ − 1) > 0.

*Proof.* (1 − x)[1 − (1 − x)^{s−1}] = (s − 1)x + O(x²). So
g_κ = −(s − 1)x^{d_κ} + O(x^{d_κ+1}). ∎

**Theorem H″ (PROVEN; COMPUTED `[iff]`).** Let n ≥ 2. For a natural labelling
with an all-ascent class, the min-des distribution on Cyc(P) is not h_C(P).
Combined with H′ of [H]: min-des realises h_C(P) if and only if no class is
all-ascent.

*Proof.* If A > 0, then f′(1) ≠ h_C′(1) by Corollary M, so f ≠ h_C. Either
Corollary M or Corollary L suffices. ∎

**Remarks.**
- *No compensation.* The concern in [H] §2.4 was that other classes might
  offset the correction Σ C(M − i, n − i). They cannot. Every non-all-ascent
  class contributes exactly x^{mindes} to both f and h_C, so it cancels in
  f − h_C. Each all-ascent class contributes a g_κ, and every g_κ has the
  same derivative 1 at x = 1, so their sum cannot vanish.
- *h_C detects A.* By Corollary M, the number of all-ascent classes equals
  Σ_κ mindes κ − Σ_j j·h_j. So the first moment of the min-des distribution,
  compared with that of h_C(P), counts the all-ascent classes exactly.
- *Separated labellings.* Lemma 2 of [H] shows A = 0 for them, so Theorem H
  is the case A = 0 of Theorem F. A labelling can have no all-ascent class
  without being separated. Then H′ applies, and the correct statistic is
  min-des, not cdes − 1 ([H] `[ctl-cdes-any]`).
- *Smallest cases.* No labelled poset with n ≤ 4 has an all-ascent class.
  There are 2 at n = 5, 46 at n = 6 and 1032 at n = 7. The largest A in a
  single labelling with n ≤ 7 is 46 (an INFO line of the output).

## 4. What is checked

`compute/h_double_prime.py` enumerates the posets up to isomorphism (1, 2,
5, 16, 63, 318, 2045 for n = 1, …, 7). For every natural labelling of every
poset with 2 ≤ n ≤ 7, it checks:
- `[formula]` Theorem F;
- `[moment]` Corollary M;
- `[iff]` min-des = h_C ⇔ A = 0;
- `[aa-d]` Lemma 3(a), (b);
- `[aa-class]` Lemma 3(c), for every component T and every m ≤ n + 1,
  evaluating N_T of Proposition D directly.

h_C is computed from the Möbius definition on OP(P) for every poset with
n ≤ 7. `[hC-indep]` also confirms that it equals the cdes − 1 distribution
under a separated labelling (Theorem H), as an end-to-end check of the class
enumeration. There are four controls, each a false variant of the claims,
and each must be refuted.

## 5. Scope of the computation

n = 7 takes about two minutes on one core (96428 labelled posets). Going to
n = 8 means 16999 posets and, extrapolating the growth from n = 6 to n = 7,
roughly 2·10⁶ labelled posets. That would take well over the 25-minute
bound used here, so the computation is reported for n ≤ 7 only. The proof
does not depend on it.

## Reproduce

From `compute/` (Python 3, no dependencies, one core, about 2 minutes):

    timeout 1500 python3 h_double_prime.py --lmax 7 --mobmax 7 > output/h_double_prime.txt
    python3 -m unittest test_h_double_prime

The script exits with status 0 iff every claim holds and every CONTROL is
refuted somewhere. `--lmax 6` reproduces the n ≤ 6 range of [H] in a few
seconds. `--mobmax` sets the largest n at which h_C comes from the Möbius
definition; above it, h_C is taken from Theorem H.
