# Cyclic sieving for automorphisms acting on Cyc(P)

This note takes up open problem 2 of [LE] (`notes/linear_extensions.md` §6).
Is there a polynomial X(q) with X(1) = e_C(P) such that (Cyc(P), ⟨g⟩, X)
is a cyclic sieving triple, with g an automorphism of P? The first test case
is P = T^{⊔k}, with g the rotation of the k copies. Every claim is tagged
**PROVEN**, **COMPUTED**, **CITED** or **OPEN**. The code is
`compute/cyclic_sieving_cyc.py`, and its output is archived in
`compute/output/cyclic_sieving_cyc.txt`. Bracketed tags such as `[tk-sigma]`
are line labels in that output.

## Verdict

**YES for the rotation of the copies, and for a precisely described class
of automorphisms. NO for a single polynomial that serves every cyclic
subgroup of Aut(P).**

| Question | Answer |
|---|---|
| A q-analogue X(q), X(1) = e_C(P), sieving the rotation σ of T^{⊔k} | **YES, PROVEN** for every T and k (Theorem C, Corollary T). X_P is the *fake-degree polynomial* of Cyc(P) as an S_k-set. It has nonnegative integer coefficients (Theorem A), and for T^{⊔k} it has the closed form (★) below, which uses only the numbers c_j = e_C(T^{⊔j}). COMPUTED on all 23 posets T^{⊔k} with \|P\| ≤ 8 (`[tk-sigma]`, `[tk-closed]`). |
| Which other g does the same polynomial serve? | Let g permute the isomorphic copies of the components, with trivial maps between copies, so g lies in W = ∏_T S_{k_T}. Then X_P sieves ⟨g⟩ **iff** the condition of Theorem C holds. Sufficiency is PROVEN. Necessity is PROVEN for one clause and COMPUTED for the other; the criterion matched all 249 tested classes (`[tk-W]`, `[sweep-W]`). Every Springer-regular element of W qualifies: powers of the k-cycle, and the (k−1)-cycle. |
| Automorphisms that also act inside components | Let g lie in a group G = ∏_T ⟨c_T⟩ ≀ S_{k_T}. The fake-degree polynomial of G sieves ⟨g⟩ for every Springer-regular g: **COMPUTED** on all 3148 regular conjugacy classes, n ≤ 7 (`[sweep-springer]`), and **CITED** (Springer's theorem). |
| One X for all of Aut(P) at once | **NO.** The smallest obstruction is the 4-element antichain A_4 (`[obst]`). A transposition and a double transposition both have order 2. They fix 0 and 2 classes respectively, so no single X can take both values at q = −1. No P with n ≤ 3 is an obstruction. |
| A P where no polynomial with nonnegative coefficients fits the data of one ⟨g⟩ | **None exists, for any P and g.** The fixed-point data of any action of a cyclic group C_N is matched by a unique X mod q^N − 1 with nonnegative integer coefficients: its coefficients are the multiplicities of the characters of C_N in the permutation representation. The real question is therefore whether a *natural* X exists. |
| Natural candidates other than the fake degree | **All fail** (`[tk-cand]`, `[sweep-cand2]`). The candidates were maj and inv on the canonical representatives B_P, maj on the lex-minimal representatives, a q-version of the block (cumulant) formula for e_C, and the product of the pattern factor with maj_T(q)^k. On the 23 rotations σ, each sieves at most 5. On the 15 non-free (P, g) with n ≤ 7, each sieves at most 4. |

The cyclic structure here is the action of S_k on the copies. The positions
play no role. That is why the q-multinomials and the necklace polynomials
of [RSW] do not apply directly. They sieve rotation of *positions*, and
under the component rotation the pattern words are permuted freely. A
correction to how the problem is usually posed: the pattern factor
e_C(C_m^{⊔k}) is a necklace count only for m = 1. For m = 2, k = 2 it is 5,
but there are 2 necklaces of content (2, 2).

## 1. Setting

P is a finite poset on [n]. Words, Lin P, cuts and cyclic classes are as
in [Thm, §1] and [LE, §0]: Cyc(P) is the set of cosets wC_n that meet
Lin P, and e_C(P) = |Cyc(P)|. Aut(P) acts by relabelling letters,
C ↦ gC.

Group the components into isomorphism types T_1, …, T_s, with T_i
occurring k_i times. Fix an isomorphism φ from a reference copy of T_i onto
each copy. The group W = ∏_i S_{k_i} then embeds in Aut(P): it permutes the
copies, and the maps between copies are the identifications φ. Changing the
φ conjugates W inside Aut(P), so nothing below depends on the choice.

Write an element of Aut(P) as (a; π). Here π permutes the copies of each
type, and a_j ∈ Aut(T_i) records the map from copy j to copy π(j). For each
cycle of π the *cycle product* is the composite of the a_j along the cycle.
Its conjugacy class does not depend on choices. An element is conjugate in
Aut(P) into W iff every cycle product is trivial.

Write F(g) = |Cyc(P)^g|. F is a class function on Aut(P).

For a cyclic group C_N = ⟨g⟩ acting on a set, (X, C_N, X(q)) is a CSP iff
X(ω^j) = F(g^j) for all j, where ω = e^{2πi/N}. Equivalently, X mod q^N − 1
is the *canonical polynomial* Σ_t m_t q^t, where m_t is the multiplicity of
the character g ↦ ω^t. The code tests the CSP exactly, by comparing
X mod q^N − 1 with the canonical polynomial (`sieves`).

## 2. Fixed points

**Lemma 1 (PROVEN).** If g ∈ Aut(P) fixes a class, then all cycles of g on
[n] have the same length o(g). In particular, if g = (1; π) ∈ W fixes a
class, then all cycles of π on the copies have the same length d = o(g),
and d divides every k_i.

*Proof.* Suppose gC = C and w ∈ C. Then gw = wγ^r for some r ([Thm, §1]),
so g(w_i) = w_{i+r}. Hence g is conjugate, as a permutation of [n], to γ^r,
whose cycles all have length n/gcd(n, r). Now let g = (1; π). An element x
in a copy lying on a π-cycle of length ℓ satisfies g^ℓ(x) = x, because the
cycle product is trivial. Its g-cycle therefore has length ℓ. ∎

**Proposition 2 (PROVEN from [LE, §4] and [FPM]; COMPUTED 23/23,
`[tk-formula]`).** Let P = T^{⊔k}, let c_j = e_C(T^{⊔j}), and let w ∈ S_k
have every cycle of length d (so d | k). Then

  F(w) = φ(d) · d^{k/d − 1} · c_{k/d}.

*Proof.* By [LE, §4] ("Fixed classes and Burnside"), F(g) = φ(o(g)) S(g).
Here S(g) is the sum of e_C(P|_{B_0}) over the partitions of the components
into o(g) unions B_0, …, B_{o−1} that g permutes cyclically. For w there
are d^{k/d − 1} such partitions. The block B_0 holds the copy containing
P_1 and one copy from each of the other k/d − 1 cycles, chosen in d ways
each. Each B_0 is a copy of T^{⊔k/d}. ∎

By Proposition F of [LE], c_j = e(T)^j · e_C(C_m^{⊔j}) with m = |T|.

## 3. The fake-degree polynomial

**Definition.** Let V = ⊕_i C^{k_i} be the permutation representation of
W. Define

  X_P(q) = ∏_i (q; q)_{k_i} · (1/|W|) Σ_{w ∈ W} F(w) / det(1 − q·w | V),

where det(1 − q·w) = ∏_{cycles c of w}(1 − q^{|c|}).

**Theorem A (PROVEN, given Chevalley's theorem, CITED).** X_P(q) equals
Σ_t ⟨C[Cyc P], R_t⟩_W q^t, where R = ⊕ R_t is the coinvariant algebra of W
on V. Hence:
- X_P ∈ N[q];
- X_P(1) = e_C(P);
- X_P(0) is the number of W-orbits on Cyc(P).

*Proof.* Molien's formula says that the Hilbert series of
(S(V) ⊗ C[Cyc P])^W is (1/|W|) Σ_w F(w)/det(1 − qw). The character F is
real, being a permutation character. Chevalley's theorem gives
S(V) ≅ S(V)^W ⊗ R as graded W-modules. Here S(V)^W is a polynomial ring
with generators in degrees 1, …, k_i for each i, so its Hilbert series is
1/∏(q; q)_{k_i}. Dividing gives the formula. R is the regular
representation, so X_P(1) = dim C[Cyc P] = e_C(P), and R_0 is the trivial
representation. ∎

For P = T^{⊔k}, only the w of Lemma 1 contribute. There are
k!/(d^{k/d}(k/d)!) such w for each d | k, so Proposition 2 gives the closed
form

  (★)  X_{T^{⊔k}}(q) = Σ_{d | k} (φ(d)/d) · (c_{k/d}/(k/d)!) · (q; q)_k / (1 − q^d)^{k/d}.

It depends only on the numbers c_j = e_C(T^{⊔j}), j | k (`[tk-closed]`,
23/23). For k = 2 it reads X = ((c_2 + c_1) + (c_2 − c_1) q)/2.

For the antichain A_k, (★) is the fake degree of S_k/C_k. By
Kraśkiewicz–Weyman and RSK it equals Σ_{w ∈ S_k, maj w ≡ 0 (mod k)} q^{maj(w^{−1})}.
This identity is a positive control for the whole computation: it is
COMPUTED for k ≤ 7, and the poset code reproduces it for k ≤ 6
(`[ctl-kw]`).

**Theorem B (PROVEN).** Let e ≥ 2 and let ζ be any primitive e-th root of
unity.
- (i) If e divides every k_i, then X_P(ζ) = F(w_e), where w_e ∈ W is any
  element all of whose cycles have length e.
- (ii) If e fails to divide some k_i and e ≤ max k_i, then X_P(ζ) = 0.

*Proof.* Group the sum by cycle type λ = (λ^{(1)}, …, λ^{(s)}). The term of
λ is a rational multiple of the polynomial
T_λ(q) = ∏_i (q; q)_{k_i} / ∏_{parts p of λ}(1 − q^p). Write z_num for the
order of vanishing at ζ of the numerator, and z_den(λ) for that of the
denominator. Then z_num = Σ_i ⌊k_i/e⌋, and z_den(λ) is the number of parts
of λ divisible by e. T_λ(ζ) ≠ 0 iff z_den(λ) = z_num.

By Lemma 1, only types with F ≠ 0 count. Such a type has all its parts
equal to some d that divides every k_i, and then z_den = Σ k_i/d if e | d,
and 0 otherwise.

In case (ii), z_num ≥ 1. Any d with e | d would make e divide every k_i, so
every contributing λ has z_den = 0 < z_num, and X_P(ζ) = 0.

In case (i), z_num = Σ k_i/e ≥ 1. If e | d, then z_den = Σ k_i/d, with
equality iff d = e. Otherwise z_den = 0. So only λ = (e^{k_i/e})_i
contributes. For that λ,

  (q; q)_k/(1 − q^e)^{k/e} = ∏_{j ≤ k, e ∤ j}(1 − q^j) · ∏_{t ≤ k/e} [t]_{q^e},

and at q = ζ this equals e^{k/e}(k/e)!, because ∏_{a=1}^{e−1}(1 − ζ^a) = e.
The class of w_e has |W| / ∏_i e^{k_i/e}(k_i/e)! elements. So
X_P(ζ) = F(w_e). ∎

**Theorem C (CSP for W).** Let g ∈ Aut(P) be conjugate into W, and let
N = o(g). Suppose that for every divisor e > 1 of N:
- (a) e ≤ max k_i, and
- (b) if e divides every k_i, then g^{N/e} has every cycle on the copies of
  length e.

Then (Cyc(P), ⟨g⟩, X_P) is a CSP (**PROVEN**). Conversely, if (b) fails,
the CSP fails (**PROVEN**). If (a) fails, the CSP failed in every computed
case (**COMPUTED** on 249 classes, n ≤ 7 and T^{⊔k} with n ≤ 8; necessity
of (a) is **OPEN** in general).

*Proof.* Take j and let e = o(g^j) > 1. Then ω^j is a primitive e-th root
of unity, and ⟨g^j⟩ = ⟨g^{N/e}⟩.

If e divides every k_i: by (b), g^j is a power of g^{N/e} prime to e, so
all its cycles have length e. Theorem B(i) gives X_P(ω^j) = F(w_e) = F(g^j).

Otherwise, by (a), Theorem B(ii) gives X_P(ω^j) = 0. Also F(g^j) = 0 by
Lemma 1, since a fixed class would force e to divide every k_i.

Converse for (b): if g^{N/e} has a cycle of length ≠ e, then F(g^{N/e}) = 0
by Lemma 1. But X_P(ω^{N/e}) = F(w_e) > 0 by Theorem B(i) and
Proposition 2. (For several types, F(w_e) > 0 because w_e fixes the class
of the concatenation u g(u) ⋯ g^{e−1}(u), where u is a linear extension of
one copy from each cycle.) ∎

**Corollary T (PROVEN).** For P = T^{⊔k} and σ the rotation of the copies,
(Cyc(P), ⟨σ⟩, X_P) is a CSP, with X_P given by (★) and X_P(1) = e_C(P).
The same polynomial sieves:
- every subgroup ⟨σ^j⟩;
- the (k−1)-cycle on k − 1 of the copies;
- more generally, every Springer-regular element of W, of cycle type
  e^{f}1^{r} in each S_{k_i} with a common e and r ∈ {0, 1}.

COMPUTED: σ on 23/23 posets (`[tk-sigma]`); the (k−1)-cycle on 8/8 with
k ≥ 3.

*Proof.* The powers of σ of order e have type e^{k/e}, so Theorem C applies.
For a regular element of order e, the powers of order e' divide e. If
e' | k_i, they have type e'^{k_i/e'}. Otherwise they fall under
Theorem B(ii). ∎

The criterion of Theorem C is wider than regularity. In A_8, g of cycle
type (6, 2) is not regular in any reflection subgroup of S_8, and ⟨g⟩ does
not act freely: F(g^3) = 48. Yet X_P sieves ⟨g⟩ (`[tk-nonreg-nonfree]`).
It is the only non-regular, non-free class among the T^{⊔k} with n ≤ 8.

**Pattern × component.** For σ on T^{⊔k}, Cyc(P) ≅ Cyc(C_m^{⊔k}) × (Lin T)^k
equivariantly ([LE] Theorem M), so fixed-point counts multiply. Hence
X_{C_m^{⊔k}}(q) · Σ_{x ∈ [e(T)]^k} q^{maj x} also sieves σ (23/23,
`[tk-pattern]`). The second factor is the [RSW] polynomial for k-tuples
under rotation. It agrees with X_P mod q^k − 1, but not as a polynomial.
The naive product X_{C_m^{⊔k}}(q) · maj_T(q)^k sieves only 12/23.

## 4. Automorphisms acting inside components (COMPUTED, CITED)

Choose a cyclic subgroup ⟨c_i⟩ ⊆ Aut(T_i) of order r_i, and put
G = ∏_i ⟨c_i⟩ ≀ S_{k_i}, a product of the complex reflection groups
G(r_i, 1, k_i) acting on V. Replace the definition of §3 by

  X_P^G(q) = ∏_i ∏_{j ≤ k_i}(1 − q^{r_i j}) · (1/|G|) Σ_{h ∈ G} F(h)/det(1 − qh | V).

Only h with every cycle product trivial fix a class, by the argument of
Lemma 1. Each such h contributes r^{−#cycles}/z_λ per cycle type λ. Theorem
A goes through unchanged, by Shephard–Todd–Chevalley, so X_P^G ∈ N[q].
Springer's theorem on regular elements [Sp74], in the CSP form of [RSW,
Thm 8.2] (stated there for coset spaces W/W′), then predicts that X_P^G
sieves ⟨g⟩ for every g regular in G. For connected P this reduces to
(e(P)/r)[r]_q, the free action.

COMPUTED (`[sweep-springer]`): for every unlabeled P with n ≤ 7 and
Aut(P) ≠ 1, take every conjugacy class of g ≠ 1. Write g in normal form,
with c_i the largest cycle product of its type; every class admits this.
Regularity is decided exactly, by testing eigenvectors against the
reflecting hyperplanes (`is_regular`).

| n | P with Aut ≠ 1 | regular classes | non-regular classes | X^G sieves (regular) | X^G sieves (non-regular) |
|---|---|---|---|---|---|
| 2 | 1 | 1 | 0 | 1 | 0 |
| 3 | 3 | 4 | 0 | 4 | 0 |
| 4 | 11 | 17 | 1 | 17 | 0 |
| 5 | 44 | 76 | 5 | 76 | 4 |
| 6 | 216 | 413 | 27 | 413 | 15 |
| 7 | 1315 | 2637 | 122 | 2637 | 95 |

So X^G sieves all 3148 regular classes. Every non-regular class with n ≤ 7
acts freely on Cyc(P), and X^G still sieves 114 of these 155. The exact
statement number in [RSW] was not checked against the paper. For G ≠ W this
section rests on the citation and the computation. Theorems A–C need
neither.

## 5. Data: P = T^{⊔k}, |P| ≤ 8

Below, σ is the rotation of the copies. The column "fix" lists
|Cyc(P)^{σ^j}| for j = 0, …, k − 1. V and Λ are the 3-element posets with
one minimum, respectively one maximum. A 4-element T is given by its cover
relations. All rows satisfy Proposition 2 and (★), and X_P sieves σ in
every row.

| T | k | n | e(T) | e_C(P) | fix | X_P mod q^k − 1 | X_P(q) |
|---|---|---|---|---|---|---|---|
| pt | 2 | 2 | 1 | 1 | 1, 1 | 1 | 1 |
| pt | 3 | 3 | 1 | 2 | 2, 2, 2 | 2 | 1 + q³ |
| pt | 4 | 4 | 1 | 6 | 6, 2, 2, 2 | 3 + q + q² + q³ | 1 + q² + q³ + 2q⁴ + q⁵ |
| pt | 5 | 5 | 1 | 24 | 24, 4, 4, 4, 4 | 8 + 4q + 4q² + 4q³ + 4q⁴ | 1 + q² + 3q³ + 4q⁴ + 6q⁵ + 4q⁶ + 3q⁷ + q⁸ + q¹⁰ |
| pt | 6 | 6 | 1 | 120 | 120, 2, 6, 8, 6, 2 | 24 + 18q + 20q² + 20q³ + 20q⁴ + 18q⁵ | degree 14, see output |
| pt | 7 | 7 | 1 | 720 | 720, 6 (×6) | 108 + 102(q + ⋯ + q⁶) | degree 21, see output |
| pt | 8 | 8 | 1 | 5040 | 5040, 4, 8, 4, 48, 4, 8, 4 | 640 + 624q + 634q² + 624q³ + 636q⁴ + 624q⁵ + 634q⁶ + 624q⁷ | degree 27, see output |
| C₂ | 2 | 4 | 1 | 5 | 5, 1 | 3 + 2q | 3 + 2q |
| C₂ | 3 | 6 | 1 | 74 | 74, 2, 2 | 26 + 24q + 24q² | 13 + 24q + 24q² + 13q³ |
| C₂ | 4 | 8 | 1 | 2118 | 2118, 2, 10, 2 | 533 + 527q + 531q² + 527q³ | 90 + 263q + 442q² + 527q³ + 443q⁴ + 264q⁵ + 89q⁶ |
| V | 2 | 6 | 2 | 76 | 76, 2 | 39 + 37q | 39 + 37q |
| Λ | 2 | 6 | 2 | 76 | 76, 2 | 39 + 37q | 39 + 37q |
| C₃ | 2 | 6 | 1 | 19 | 19, 1 | 10 + 9q | 10 + 9q |
| 0<1, 0<2, 0<3 | 2 | 8 | 6 | 2484 | 2484, 6 | 1245 + 1239q | same |
| 0<3, 1<2, 1<3 | 2 | 8 | 5 | 1725 | 1725, 5 | 865 + 860q | same |
| 0<2, 0<3, 1<2, 1<3 | 2 | 8 | 4 | 1104 | 1104, 4 | 554 + 550q | same |
| 0<1, 1<2, 1<3 | 2 | 8 | 2 | 276 | 276, 2 | 139 + 137q | same |
| 0<1, 0<2, 2<3 | 2 | 8 | 3 | 621 | 621, 3 | 312 + 309q | same |
| 0<3, 1<3, 2<3 | 2 | 8 | 6 | 2484 | 2484, 6 | 1245 + 1239q | same |
| 0<1, 0<2, 1<3, 2<3 | 2 | 8 | 2 | 276 | 276, 2 | 139 + 137q | same |
| 0<3, 1<2, 2<3 | 2 | 8 | 3 | 621 | 621, 3 | 312 + 309q | same |
| 0<2, 1<2, 2<3 | 2 | 8 | 2 | 276 | 276, 2 | 139 + 137q | same |
| C₄ | 2 | 8 | 1 | 69 | 69, 1 | 35 + 34q | 35 + 34q |

All conjugacy classes of Aut(T^{⊔k}) with n ≤ 8, not only σ (`[tk-allg]`):

| | ⟨g⟩ acts freely | ⟨g⟩ does not act freely |
|---|---|---|
| g regular in its G | 33 classes, X^G sieves all 33 | 31 classes, X^G sieves all 31 |
| g not regular | 49 classes, X^G sieves 25 | 1 class (A_8, type (6, 2)), X^G sieves it |

In 5 further classes the cycle products do not lie in one cyclic subgroup.
They occur for T with Aut(T) = S_3, and all 5 act freely.

## 6. Candidates that fail

All candidates below have X(1) = e_C(P) and do not depend on g. We tested
them on the 23 rotations σ (`[tk-cand]`). We also tested them on the
disconnected (P, g) with n ≤ 7 (`[sweep-cand2]`). There are 874 classes
where ⟨g⟩ acts freely; there the only requirement is that X be
equidistributed mod N. There are 15 classes where it does not act freely,
which is the informative case.

| candidate | sieves σ (of 23) | non-free, n ≤ 7 (of 15) | free, n ≤ 7 (of 874) |
|---|---|---|---|
| fake degree X_P (Theorem C) | 23 | 15 | 290 |
| Σ_{w ∈ B_P} q^{maj w}, natural labelling | 4 | 4 | 604 |
| the same, shifted to start at q^0 | 4 | 4 | 604 |
| Σ_{w ∈ B_P} q^{inv w} | 4 | 3 | 814 |
| maj over lex-minimal representatives | 5 | 3 | 537 |
| block q-cumulant Σ_π [\|π\|−1]_q! ∏_B maj(cutless words on B) | 4 | 2 | 351 |
| X_{C_m^{⊔k}}(q) · maj_T(q)^k | 12 | — | — |

The fake degree's 290 of 874 on free classes is expected, not a defect.
Theorem C covers only g conjugate into W, and a free class acting inside
components needs X^G (§4) instead; we did not break the 584 failures down
further. The smallest failures are already at n = 3 (`[sweep-firstfail]`). On
A_3, maj(B_P) ≡ 2 mod q² − 1, but a transposition fixes no class. Also on
A_3, inv(B_P) and the block candidate are ≡ 1 + q mod q³ − 1, but the
3-cycle fixes both classes.

## 7. Obstruction to one polynomial for all of Aut(P)

**Proposition O′ (PROVEN; COMPUTED `[obst]`).** For P = A_4, no polynomial
X sieves both ⟨(12)⟩ and ⟨(12)(34)⟩ on Cyc(A_4). Both generators have
order 2, but F((12)) = 0 and F((12)(34)) = 2, so X(−1) would have to take
both values. A_4 is the smallest such poset: for n ≤ 3, any two
automorphisms of the same order have the same fixed-point data. At n = 4,
A_4 is the only such poset.

So any answer to open problem 2 for all of Aut(P) has to depend on the
cyclic subgroup. Theorem C gives one polynomial for all the subgroups it
covers. For the rest, the canonical polynomial of §1 always exists.

## 8. Controls

All of these pass (`[ctl-*]`):
- [RSW] q-multinomial CSP for words of content m under rotation, for 9
  contents. Each perturbed polynomial (one unit moved from q^1 to q^0) is
  rejected. The obvious shift q·X is no negative control here: when the
  action is free it gives the same values.
- The fake-degree engine on the S_k-set of j-subsets of [k] returns
  [k; j]_q in all 33 cases with k ≤ 7.
- Kraśkiewicz–Weyman: the fake degree of S_k/C_k equals
  Σ_{maj w ≡ 0 (k)} q^{maj(w^{−1})} for k ≤ 7, and the poset code
  reproduces it for A_k, k ≤ 6.
- Integrality and nonnegativity of every fake-degree polynomial computed,
  and exactness of every polynomial division.
- Springer regularity: the eigenvalue order equals o(g) on every regular
  class.

## 9. Open problems

1. Give a combinatorial statistic s on Cyc(P) with X_P(q) = Σ_C q^{s(C)}.
   For A_k this would be a statistic on (k−1)! classes that is
   equidistributed with maj(w^{−1}) over {w : maj w ≡ 0 (mod k)}. The
   statistics of §6 fail. **OPEN.**
2. Is the condition e ≤ max k_i in Theorem C necessary in general?
   **OPEN.** It is necessary in all 249 computed cases.
3. Prove §4 independently of [RSW, Thm 8.2], by evaluation as in
   Theorem B. **OPEN.**

## 10. Remarks on existing notes

- We found no errors in [LE]. Its §3.1 says nothing in the theory points to
  a q-analogue, and that stands: X_P comes from the coinvariant algebra of
  the group permuting the components, not from H_P or PLie(P). Open problem
  2 of [LE] is answered here for the rotation of the copies (Corollary T)
  and for the classes in Theorem C. It is answered negatively for all of
  Aut(P) at once (Proposition O′).
- The fixed-class formula F(g) = φ(o(g)) S(g) of [LE, §4] and [FPM] is
  re-confirmed, in its closed form for T^{⊔k}, on all 23 cases.

## References

[LE] = `notes/linear_extensions.md`; [Thm] = `notes/poset_jks_theorem.tex`;
[FPM] = `notes/fixed_point_mobius_identity.md`; [RSW] = V. Reiner,
D. Stanton, D. White, *The cyclic sieving phenomenon*, JCTA 108 (2004)
17–50 (Thm 8.2 as cited by secondary sources; not checked against the
paper); [Sp74] = T. A. Springer, *Regular elements of finite reflection
groups*, Invent. Math. 25 (1974) 159–198; Kraśkiewicz–Weyman = W.
Kraśkiewicz, J. Weyman, *Algebra of coinvariants and the action of a
Coxeter element*, Bayreuth. Math. Schr. 63 (2001) 265–284; Chevalley =
C. Chevalley, *Invariants of finite groups generated by reflections*, Amer.
J. Math. 77 (1955) 778–782.

## Reproduce

From `compute/` (plain Python 3, no dependencies; about 9 s on one core):

    python3 cyclic_sieving_cyc.py --nmax 7 --tkmax 8 > output/cyclic_sieving_cyc.txt
    python3 -m unittest test_cyclic_sieving_cyc

The script exits with status 0 iff every check holds and every negative
control is rejected. `--sections ctl,tk,sweep,obst` runs a subset.
`--tkmax` bounds |T^{⊔k}|, and `--nmax` bounds the sweep and the
obstruction search.
