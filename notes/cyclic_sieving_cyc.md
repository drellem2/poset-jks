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

The YES for the rotation, and for every Springer-regular element, is **not
new**. Once Cyc(P) is viewed as an S_k-set (or a ∏_i S_{k_i}-set), it is an
instance of the regular-element CSP for fake degrees of permutation
modules: Westbury 2016 Cor. 2.6 for the long cycle, and in general Sagan's
survey Thm 8.2 or [RSW] Thm 8.2 applied orbit by orbit ([PACSC]). The same
holds for the G(r,1,k) version of §4. What was not found in the literature
searched for [PACSC] and [PACSC2] is: the closed form (★), Theorem B(ii) at roots of
unity that are not regular eigenvalues, Theorem C beyond regular elements,
and the A_4 obstruction. "Not found" is a search result, not a proof of
novelty; see §10 for what was not read.

| Question | Answer |
|---|---|
| A q-analogue X(q), X(1) = e_C(P), sieving the rotation σ of T^{⊔k} | **YES, PROVEN** for every T and k (Theorem C, Corollary T); **KNOWN** as an instance of Westbury 2016 Cor. 2.6 ([PACSC]). X_P is the *fake-degree polynomial* of Cyc(P) as an S_k-set. It has nonnegative integer coefficients (Theorem A), and for T^{⊔k} it has the closed form (★) below, which uses only the numbers c_j = e_C(T^{⊔j}). COMPUTED on all 23 posets T^{⊔k} with \|P\| ≤ 8 (`[tk-sigma]`, `[tk-closed]`). |
| Which other g does the same polynomial serve? | Let g permute the isomorphic copies of the components, with trivial maps between copies, so g lies in W = ∏_T S_{k_T}. Then X_P sieves ⟨g⟩ **iff** the condition of Theorem C holds. Sufficiency is PROVEN. Necessity of (b) is PROVEN; necessity of (a) is PROVEN when gcd(k_i) = 1 and OPEN otherwise. The criterion matched the CSP on all 206 distinct tested classes (`[tk-W]`, `[sweep-W]`; see Theorem C for the count), but clause (a) is the only failing clause in just 6 of them. Every Springer-regular element of W qualifies: powers of the k-cycle, and the (k−1)-cycle (KNOWN: Sagan Thm 8.2, [RSW] Thm 8.2). Beyond regular elements the criterion was not found in the literature searched ([PACSC]). |
| Automorphisms that also act inside components | Let g lie in a group G = ∏_T ⟨c_T⟩ ≀ S_{k_T}. The fake-degree polynomial of G sieves ⟨g⟩ for every Springer-regular g: **PROVEN given [RSW] Thm 8.2 (CITED)**, and **KNOWN** as an instance of it and of Sagan Thm 8.2 ([PACSC]). Also **COMPUTED** on all 3148 regular conjugacy classes, n ≤ 7 (`[sweep-springer]`), which is a check of a theorem. |
| One X for all of Aut(P) at once | **NO.** The smallest obstruction is the 4-element antichain A_4 (`[obst]`; not found in the literature searched, [PACSC]). A transposition and a double transposition both have order 2. They fix 0 and 2 classes respectively, so no single X can take both values at q = −1. No P with n ≤ 3 is an obstruction. |
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

**Proposition 2 (PROVEN; COMPUTED 23/23, `[tk-formula]`).** Let
P = T^{⊔k}, let c_j = e_C(T^{⊔j}), and let w ∈ S_k have every cycle of
length d (so d | k). Then

  F(w) = φ(d) · d^{k/d − 1} · c_{k/d}.

*Proof.* (Self-contained, following [AUD] §1.) Let w fix a class C. For
L ∈ C we have wL = Lγ^r, and r does not depend on L, since
w(Lγ^t) = (Lγ^t)γ^r. Now γ^r is conjugate to w, so it has order d, and
r = s·n/d with gcd(s, d) = 1. This accounts for the factor φ(d).

Cut L into d blocks of length n/d. Then w maps block j to block j + s. Let
b(x) be the block of x. If x < y in one component, then b(x) ≤ b(y), and
applying w^t gives (b(x) + ts mod d) ≤ (b(y) + ts mod d) for every t. If
b(x) < b(y), choose t with b(y) + ts ≡ 0 mod d; this contradicts the
inequality. So b is constant on components, and each block of L is a union
of components holding one copy from each cycle of w.

Conversely, let u be a linear extension of such a union and
s′ = s^{−1} mod d. Then u w^{s′}(u) w^{2s′}(u) ⋯ is a linear extension of
P whose class is fixed by w. Fix s. The lifts of a linear extension of the
quotient T^{⊔k/d} correspond to a choice of one copy per cycle, which gives
d^{k/d} lifts. Rotation by one block permutes them in orbits of size d, so
each class over a given class of the quotient is counted d times. Hence
F(w) = φ(d) · d^{k/d−1} · c_{k/d}. ∎

The same argument gives the multi-type form F(w_d) = φ(d) d^{#cycles − 1}
e_C(one copy per cycle), which [AUD] checks on all 206 classes conjugate
into W. Proposition 2 also follows from the fixed-class formula
F(g) = φ(o(g)) S(g) of [LE, §4] and [FPM]. There S(g) sums e_C(P|_{B_0})
over the partitions of the components into o(g) unions B_0, …, B_{o−1} that
g permutes cyclically, and for w there are d^{k/d − 1} such partitions.

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

Theorem A is **standard** ([PACSC]): X_P is the fake degree of the
permutation representation C[Cyc P]. For one type it is Westbury's
fd(Z(X)) (Westbury 2016 §2.2), and orbit by orbit it is Σ_x Hilb(A^{W_x}; q),
the polynomial of [RSW] Thm 8.2.

For P = T^{⊔k}, only the w of Lemma 1 contribute. There are
k!/(d^{k/d}(k/d)!) such w for each d | k, so Proposition 2 gives the closed
form

  (★)  X_{T^{⊔k}}(q) = Σ_{d | k} (φ(d)/d) · (c_{k/d}/(k/d)!) · (q; q)_k / (1 − q^d)^{k/d}.

It depends only on the numbers c_j = e_C(T^{⊔j}), j | k (`[tk-closed]`,
23/23). For k = 2 it reads X = ((c_2 + c_1) + (c_2 − c_1) q)/2. (★) is
Westbury's fd(Z(X)) with the cycle index made explicit by Lemma 1 and
Proposition 2. As a formula in the c_j it was not found in the literature
searched ([PACSC]).

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

Prior art ([PACSC]). Part (i) is **Springer's theorem**: w_e is regular
in W with regular eigenvalue ζ, and Springer's evaluation ([RSW] Thm 8.1,
from [Sp74] Prop. 4.5) gives X_P(ζ) = F(w_e). The proof above, in both
parts, is Springer's evaluation argument: at q = ζ only the w whose
ζ-eigenspace has the maximal dimension a(e) = Σ_i ⌊k_i/e⌋ ([Sp74]
Thm 3.4(i)) survive, as in the proof of [Sp74] Prop. 4.5 (see also
Lehrer–Michel 2003, proof of Thm 2.3). Part (ii) is that argument at a root
of unity that need not be a regular eigenvalue, combined with Lemma 1
([PACSC2] §1, Proposition E, audited in [AUD2]). Part (ii) also follows from
Springer's theorem itself when ζ is a regular eigenvalue of W (e divides k_i or k_i − 1 for
every i), since then F vanishes on the regular element of order e by
Lemma 1. When ζ is not a regular eigenvalue of W, for example k = 5 and
e = 3, part (ii) as a statement was not found in the literature searched
([PACSC], [PACSC2]); its method is Springer's. It rests on the support of
F (Lemma 1).

**Theorem C (CSP for W).** Let g ∈ Aut(P) be conjugate into W, and let
N = o(g). Suppose that for every divisor e > 1 of N:
- (a) e ≤ max k_i, and
- (b) if e divides every k_i, then g^{N/e} has every cycle on the copies of
  length e.

Then (Cyc(P), ⟨g⟩, X_P) is a CSP (**PROVEN**). Conversely, if (b) fails,
the CSP fails (**PROVEN**). If (a) fails and gcd(k_i) = 1, the CSP fails
(**PROVEN**, Proposition 3 below). If (a) fails and gcd(k_i) > 1, necessity
is **OPEN**; the CSP failed in every computed case.

The criterion agrees with the CSP on all **206 distinct** classes conjugate
into W that were computed (**COMPUTED**): 171 with n ≤ 7 (`[sweep-W]`) and
35 more among the T^{⊔k} with n = 8. The output lines `[tk-W]` (78 classes,
T^{⊔k} with n ≤ 8) and `[sweep-W]` (171) sum to 249, but the 43 classes of
T^{⊔k} with n ≤ 7 appear in both ([AUD] §3). Clause (a) fails in only 8 of
the 206 classes, and it is the *only* failing clause in just 6 of them
([AUD] §3): A_5 with copy-cycle type (2, 3); A_7 with (2, 5) and (3, 4);
A_5 ⊔ C_2 with (2, 3), (1); A_3 ⊔ C_2 ⊔ C_2 with (3), (2); A_8 with (3, 5).
The CSP fails in all 8.

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

Prior art ([PACSC], [PACSC2]). When every power g^j ≠ 1 is regular, Theorem C is the
regular-element CSP (Sagan Thm 8.2, [RSW] Thm 8.2). The criterion also
reaches non-regular g, such as cycle type (6, 2) on A_8. There the powers
whose order divides every k_i are regular and Springer handles them, but
the other powers need Theorem B(ii) at a non-regular ζ, which is
Springer's method at a non-regular ζ, not his theorem. No source searched
gives a CSP for the fake degree at a non-regular element, or an iff
criterion. Theorem C beyond regular elements was therefore not found in the
literature searched.

**Proposition 3 (PROVEN, [AUD] §3).** If gcd(k_i) = 1, clause (a) of
Theorem C is necessary.

*Proof.* Let e | N with e > max k_i. By Lemma 1, only cycle types whose
parts all equal a common d dividing every k_i have F ≠ 0. Here d = 1, so

  X_P = e_C(P) · ∏_i [k_i]_q! / k_i!.

Since e > k_i, no factor [j]_ζ with j ≤ k_i vanishes at a primitive e-th
root ζ, so X_P(ζ) ≠ 0. But g^{N/e} has order e > max k_i, so its cycles on
the copies are not all of length e, and F(g^{N/e}) = 0 by Lemma 1. ∎

This covers 2 of the 6 informative classes above (A_5 ⊔ C_2 and
A_3 ⊔ C_2 ⊔ C_2). Two facts constrain a proof in the remaining case
gcd(k_i) > 1 ([AUD] §3; both PROVEN):
- *The bad e are never prime powers.* An element of ∏ S_{k_i} whose order
  is divisible by ℓ^b has a cycle of length divisible by ℓ^b, so
  ℓ^b ≤ max k_i. Hence every e that violates (a) makes 1 − ζ_e a unit, and
  norm arguments alone cannot finish the proof.
- *(★) alone does not force nonvanishing.* Put y = ∏ e(T_i)^{k_i/g} with
  g = gcd(k_i). By Proposition F of [LE], X_P depends on the T_i only
  through their sizes m_i and through y. For two types with k = (4, 4) and
  e = 6, X_P(ζ_6) as a polynomial in y has a real root with 0 < y < 1 for
  every (m_1, m_2) ∈ [3]². So a proof must use y ≥ 1.

Symbolic evidence (**COMPUTED**, [AUD] `[neca]`): X_P mod Φ_e, with y as an
indeterminate, has no common root y ≥ 1 (Sturm count) for a single type
with k = 3, …, 16 and |T| = 1, …, 6 (84 pairs (k, m), 690 triples
(k, m, e)), and for two types with gcd(k_1, k_2) > 1, k_1 + k_2 ≤ 10 and
m_i ≤ 3 (81 cases, 207 bad e). So the CSP fails whenever (a) fails, for
every T of these sizes. These figures are [AUD]'s and were not re-derived
here.

**Corollary T (PROVEN; KNOWN as an instance, [PACSC]).** For P = T^{⊔k} and σ the rotation of the copies,
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

Corollary T is **not new** ([PACSC]). For σ it is an instance of Westbury
2016 Cor. 2.6 (X a permutation representation of S_r, P = fd(Z(X)), c the
long cycle), with X = Cyc(T^{⊔k}). Its restriction to ⟨σ^j⟩ is [RSW]
Remark 2.3. For every regular element of W it is an instance of Sagan's
survey Thm 8.2 (attributed there to Westbury, from Springer), with
V = C[Cyc P] and B = Cyc(P), or of [RSW] Thm 8.2 applied orbit by orbit.
In type A the regular elements are the powers of the k-cycle and of the
(k−1)-cycle ([RSW] p. 39; Sagan Prop. 6.2).

The criterion of Theorem C is wider than regularity. In A_8, g of cycle
type (6, 2) is not regular in S_8 (= W = G here), and ⟨g⟩ does
not act freely: F(g^3) = 48. Yet X_P sieves ⟨g⟩ (`[tk-nonreg-nonfree]`).
It is the only non-regular, non-free class among the T^{⊔k} with n ≤ 8.

**Pattern × component.** For σ on T^{⊔k}, Cyc(P) ≅ Cyc(C_m^{⊔k}) × (Lin T)^k
equivariantly ([LE] Theorem M), so fixed-point counts multiply. Hence
X_{C_m^{⊔k}}(q) · Σ_{x ∈ [e(T)]^k} q^{maj x} also sieves σ (23/23,
`[tk-pattern]`). The second factor is the [RSW] polynomial for k-tuples
under rotation. It agrees with X_P mod q^k − 1, but not as a polynomial.
The naive product X_{C_m^{⊔k}}(q) · maj_T(q)^k sieves only 12/23.

## 4. Automorphisms acting inside components (PROVEN given [RSW] Thm 8.2; COMPUTED)

Choose a cyclic subgroup ⟨c_i⟩ ⊆ Aut(T_i) of order r_i, and put
G = ∏_i ⟨c_i⟩ ≀ S_{k_i}, a product of the complex reflection groups
G(r_i, 1, k_i) acting on V. Replace the definition of §3 by

  X_P^G(q) = ∏_i ∏_{j ≤ k_i}(1 − q^{r_i j}) · (1/|G|) Σ_{h ∈ G} F(h)/det(1 − qh | V).

Only h with every cycle product trivial fix a class, by the argument of
Lemma 1. Each such h contributes r^{−#cycles}/z_λ per cycle type λ. Theorem
A goes through unchanged, by Shephard–Todd–Chevalley, so X_P^G ∈ N[q].
**Proposition 4 (PROVEN given [RSW] Thm 8.2, CITED; KNOWN as an
instance, [PACSC]).** X_P^G sieves ⟨g⟩ for every g whose normal form
(below) is regular in G.

[RSW] Thm 8.2 (JCTA 108 (2004) p. 37, §8, checked in the published paper
by [AUD] §4 and [PACSC] §1) reads: for c regular of order n in a finite
(complex) reflection group W, C = ⟨c⟩ and any subgroup W′ ≤ W, the triple
(W/W′, Hilb(A^{W′}; q), C) is a CSP, where A is the coinvariant algebra. It
is Springer's theorem on regular elements [Sp74] in CSP form.

*Proof.* ([AUD] §4.) Cyc(P) is a disjoint union of G-orbits G/G_x. By
Molien and Shephard–Todd–Chevalley, as in Theorem A,
X_P^G = Σ_orbits Σ_t ⟨Ind_{G_x}^G 1, A_t⟩ q^t = Σ_orbits Hilb(A^{G_x}; q).
Replacing V by V* changes nothing, because F(h) = F(h^{−1}). [RSW] Thm 8.2
applies to each orbit, and a disjoint union of CSPs for the same cyclic
group is a CSP. Finally g and its normal form are conjugate in Aut(P), so
they have the same fixed-point data. ∎

This is an instance of known results: ∏ G(r_i, 1, k_i) is a finite complex
reflection group, so Sagan's survey Thm 8.2 applies directly to
V = C[Cyc P], and [RSW] Cors. 8.5–8.6 treat C_m ≀ S_N explicitly
([PACSC]). For connected P, X_P^G reduces to (e(P)/r)[r]_q, the free
action.

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
acts freely on Cyc(P), and X^G still sieves 114 of these 155. The regular
count is a check of Proposition 4, not independent evidence for it. For
G ≠ W this section rests on the citation of [RSW] Thm 8.2. Theorems A–C do
not use it.

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

The maj and inv candidates depend on a labelling of P, and inv(B_P) also
depends on the base component. The labellings used are these. For σ on
T^{⊔k}, P is the disjoint union of k copies of T with consecutive labels
(`disjoint_copies`). For the sweep, P is the labelled representative of its
isomorphism class given by `n7_sweep.canonical_fast` (the relabelling with
least relation code). In both cases the natural labelling is position in
the lexicographically first linear extension w_0 of that labelled P
(`natural_relabel`). B_P takes from each class the rotation whose first
block contains the component of w_0[0], the element with natural label 0
(`base_reps`). Under a different canonical form, [AUD] §5 gets inv(B_P) on
1/15 non-free and 815/874 free classes, against 3/15 and 814/874 below. All
other counts in the table were reproduced exactly by [AUD], and every
candidate fails under both labellings.

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
2. Is the condition e ≤ max k_i in Theorem C necessary when
   gcd(k_i) > 1? **OPEN.** It is PROVEN necessary when gcd(k_i) = 1
   (Proposition 3). Among the 206 computed classes it is the sole failing
   clause in only 6, and the CSP fails in all of them. The symbolic check
   of [AUD] `[neca]` (single type, k ≤ 16, |T| ≤ 6; two types,
   k_1 + k_2 ≤ 10, m_i ≤ 3) finds no counterexample. A proof must use
   y ≥ 1 (see after Proposition 3).
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
- Corrections from the audit [AUD] (F1–F6) are applied in this version:
  the class count 249 → 206 and the sole-(a) count 6 (F1); Proposition 3
  and the facts after it (F2); [RSW] Thm 8.2 checked and Proposition 4
  (F3); the labelling of §6 (F4); "not regular in S_8 (= W = G)" (F5); the
  self-contained proof of Proposition 2 (F6).
- Prior art ([PACSC]). KNOWN: Theorem A (standard), Theorem B(i)
  (Springer), Corollary T and Proposition 4 (instances of Westbury 2016
  Cor. 2.6, Sagan Thm 8.2, [RSW] Thm 8.2). Not found in the literature
  searched: (★) as a formula in the c_j, Theorem B(ii) at non-regular ζ,
  Theorem C beyond regular elements, and the A_4 obstruction of
  Proposition O′. [PACSC2] read [Sp74] directly, and Lehrer–Michel 2003.
  The method of Theorem B is Springer's; no statement of B(ii) at
  non-regular ζ, of Theorem C beyond regular elements, or of (★) was
  found. Lehrer–Taylor Ch. 11 (§6, 'Eigenvalues of pseudoregular
  elements') and Lehrer–Springer 1999 could not be obtained and remain
  unread.
  Sagan theorem numbers are those of the arXiv version (arXiv:1008.0790);
  the published LMS version was not opened.

## References

[LE] = `notes/linear_extensions.md`; [Thm] = `notes/poset_jks_theorem.tex`;
[FPM] = `notes/fixed_point_mobius_identity.md`; [RSW] = V. Reiner,
D. Stanton, D. White, *The cyclic sieving phenomenon*, JCTA 108 (2004)
17–50 (Thm 8.2 on p. 37, §8, checked in the published paper by [AUD] and
[PACSC]); [AUD] = `notes/audit_cyclic_sieving_cyc.md`; [PACSC] =
`notes/prior_art_cyclic_sieving_cyc.md`; [PACSC2] =
`notes/prior_art_cyclic_sieving_cyc_2.md`; [AUD2] =
`notes/audit_prior_art_cyclic_sieving_cyc_2.md`; Westbury 2016 = B. Westbury,
*Invariant tensors and the cyclic sieving phenomenon*, Electron. J.
Combin. 23(4) (2016) #P4.25; Sagan = B. Sagan, *The cyclic sieving
phenomenon: a survey*, Surveys in Combinatorics 2011, LMS Lecture Note Ser.
392 (2011) 183–234 (theorem numbers from arXiv:1008.0790); Lehrer–Taylor =
G. Lehrer, D. Taylor, *Unitary Reflection Groups*, CUP 2009 (not read;
[PACSC2] §0.4); Lehrer–Michel 2003 = G. I. Lehrer, J. Michel, *Invariant
theory and eigenspaces for unitary reflection groups*, C. R. Acad. Sci.
Paris, Ser. I 336 (2003) 795–800 (read, [PACSC2]); [Sp74] = T. A.
Springer, *Regular elements of finite reflection groups*, Invent. Math. 25
(1974) 159–198 (read directly, [PACSC2]); Lehrer–Springer 1999 = G. I.
Lehrer, T. A. Springer, *Reflection subquotients of unitary reflection
groups*, Canad. J. Math. 51 (1999) 1175–1193 (not read; [PACSC2] §0.4); Kraśkiewicz–Weyman = W.
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
