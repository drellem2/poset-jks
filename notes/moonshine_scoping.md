# Moonshine for the alternating group: scoping

This note scopes the question raised in the section "Relation to the
moonshine motivation" of `notes/poset_jks_research_note.tex`. Now that a
poset Lie theory exists, is there an additional grading or operator whose
traces have modular properties? The theory in question is Poset JKS,
H_P ≅ sgn ⊗ Lie(P), inside the cone framework of `notes/general_theory.md`
([GT]), with the fixed-point formula of `notes/fixed_point_formula.md` ([FP])
and the plethystic-logarithm layer of
`notes/global_module_operations_plethlog.md` ([PL]).

Tags: **PROVEN** (argument given here), **COMPUTED** (checked by
`compute/moonshine_scoping.py`; see Reproduce), **CITED**, **LOOKUP** (an
OEIS or LMFDB query, recorded in `compute/output/moonshine_lookup.txt`).
Matching an eta quotient to N coefficients is COMPUTED, not PROVEN. Where
an identity is called PROVEN by a Sturm bound, the membership of both sides
in the same space of modular forms is CITED.

The PROVEN arguments here have **not** been independently audited. The
recommendation is to stop, so nothing is built on them. If this line is
ever reopened, audit them first.

## Verdict table

Criteria:
- (M) is T_g modular?
- (LE) do the coefficients count or organize linear extensions? A sibling
  item takes the linear-extension question directly, so LE is only noted here.

| # | Graded object | Group | T_g(q) | Verdict (M) | (LE) |
|---|---|---|---|---|---|
| 1 | Witt layer V_n = Prim(𝐐)[n] = ⊕_{P on [n]} Lie(P), graded by n = \|P\| | S_n, A_n in each degree: invariants, sign part, traces at cycle types d^m | Σ a_n q^n = ∏(1−q^n)^{−c_n}, with c_n = dim V_n^{S_n} | **NO SIGN.** PROVEN: every series in this grading has radius of convergence 0 (growth ≥ 2^{n²/4}). COMPUTED: c_n, c_n^−, A_n-invariants for n ≤ 18. LOOKUP: none of these four sequences is in the OEIS. | weak: a_n counts pairs (P, linear extension) |
| 2 | g-fixed P-partitions of a finite P, graded by \|σ\| | Aut(P) ∩ A_n | Σ_{w ∈ Lin(P/⟨g⟩)} q^{Σ_{j∈Des w} S_j} / ∏_j (1 − q^{S_j}) | **NO SIGN.** PROVEN (Lemma R): a rational function of q with no poles in 0 < \|q\| < 1 is never modular unless constant. COMPUTED: brute force = quotient formula, 14 (P, g) pairs. | **yes**: the numerator is a weighted descent statistic on Lin(P/⟨g⟩), and the leading pole at q = 1 is Σ_w ∏_j 1/S_j(w) |
| 3 | P-partitions of infinite posets: k·N, chain_m × N, N × N | S_k ⊇ A_k on k·N; transpose on N × N | k·N: q^{k/24} ∏_{cycles λ} η(λτ)^{−1}; chain_m × N: ∏(1−q^n)^{−min(n,m)}; N × N: MacMahon and the symmetric plane partitions | k·N: **MODULAR but generic** (the Frame shape of a permutation action; COMPUTED for all classes, k ≤ 5). chain_m × N for m ≥ 2: **NO SIGN** (PROVEN via Lemma R). N × N: **NO SIGN** (PROVEN modulo a CITED growth bound). | weak |
| 4 | Fock space Sym(Lie(P) ⊗ tC[t]); on Aut(P) ∩ A_n this equals Sym(H_P ⊗ tC[t]) | Aut(P), Aut(P) ∩ A_n | q^{dim/24}/η_g, with η_g = ∏_t η(tτ)^{r_t} the Frame shape of g on Lie(P) | **MODULAR always, generic** (PROVEN: this holds for any rational representation of any finite group). COMPUTED for 8 posets and all classes. Curiosity: on the 24-dimensional Lie_5, every η_g is a multiplicative eta product. The regular representation of S_4 does the same, so this is not specific to posets. | none |

**Recommendation: STOP.** The only source of modularity found is the
Frame-shape mechanism (candidates 3 and 4). It turns the character of any
rational representation of any finite group into eta products. The data
that is specific to posets either grows super-exponentially (candidate 1)
or gives rational functions of q (candidate 2). Neither can be modular, and
both statements are proved, not just observed. Restricting to the
alternating group changes nothing (§3.4). There is no formulation here
worth pursuing as moonshine. Candidate 2 does carry linear-extension
content, but that belongs to the sibling linear-extension item, and its
generating functions are classical P-partition series.

## 1. The structural analogy, stated precisely

**Borcherds' denominator layer.** Let V = ⊕_{n≥1} V_n be a graded space and
L(V) the free Lie algebra on V. Let g be a graded automorphism of V. By PBW,
U(L(V)) ≅ T(V) as graded g-modules. Taking graded traces gives

    1 / (1 − Σ_n tr(g | V_n) q^n)  =  Σ_n tr(g | T(V)_n) q^n  =  ∏_{n≥1} det(1 − g q^n | L(V)_n)^{−1}.   (W_g)

At g = 1 this is the Witt product ∏(1 − q^n)^{−dim L_n}. Moonshine starts
when the dimensions dim V_n, or the exponents, are the coefficients of a
modular function. In Borcherds' proof, the exponents c(mn) in
p^{−1}∏(1 − p^m q^n)^{c(mn)} = j(p) − j(q) come from j.

**The poset version ([PL] §4).** 𝐐 is the Hopf monoid of pairs (P, ℓ), with
ℓ a linear extension of P. S_n acts freely on 𝐐[n], and 𝐐 ≅ E ∘ Prim(𝐐)
(Cartier–Milnor–Moore and PBW for species). The cycle-index form of
(W_g) is therefore

    Z_𝐐 = A(p_1) = Exp(Z_{Prim 𝐐}),    Prim(𝐐)[n] ≅ V_n := ⊕_{P on [n]} Lie(P).

Specializing p_d ↦ q^d (taking invariants) gives the Witt product
A(q) = Σ a_n q^n = ∏(1 − q^n)^{−c_n}, where c_n = dim V_n^{S_n}. Here
a_n = |{naturally labeled posets on [n]}| (OEIS A006455). The analogy is
exact at this level:
- 𝐐 plays T(V) = U(L(V));
- ⊕_P Lie(P) plays L(V);
- the fixed-point formula supplies the "twisted" exponents, namely the
  traces of g on each Lie(P). On a single Lie(P) these are
  χ(g) = μ(o) Σ_{x∈F(P,g)} e_C(P|_{B_0(x)}) ([PL] item 1).

The cone theory gives the same layer one level down. Corollary EZ′ of [FP]
is a PBW decomposition C[V] ≅ ⊕_{[X]} Ind Lie(V_X), so chambers play U and
cone Lie modules play L.

What is missing is the moonshine half. Moonshine needs the exponents
(c_n, or the twisted c_n(g)) to come from a modular object. In every
grading below they do not, except where the modularity comes from the
generic Frame-shape mechanism (§3.3, §3.4).

## 2. The eta-quotient detector and its controls (COMPUTED)

For a series f = c q^a (1 + …) the detector proceeds as follows:
1. It solves f = c q^a ∏_n (1 − q^n)^{e_n} exactly (inverse Euler
   transform, via q f′/f).
2. It Möbius-inverts e_n = Σ_{t|n} r_t.
3. It declares f an eta quotient ∏ η(tτ)^{r_t} (times a q-power) if c = ±1,
   every r_t is an integer, and the support of r lies in the first half of
   the window. The second half then certifies the zeros.

For an identified quotient, `eta_form_data` returns:
- the weight Σ r_t / 2;
- the least level N with Σ t r_t ≡ Σ (N/t) r_t ≡ 0 (mod 24) (Gordon–Hughes–Newman);
- the character d ↦ ((−1)^k ∏ t^{r_t} / d);
- Ligozat's order of vanishing at every cusp c/d, d | N.

The sufficiency of these conditions for membership in M_k(Γ_0(N), χ) is
CITED (Ono, *The web of modularity*, Thms 1.64–1.65).

Controls, all passing:

| Input | Expected | Found |
|---|---|---|
| Σ (−1)^k q^{k(3k−1)/2} (Euler) | η: 1^1 | 1^1 |
| θ_3 = Σ q^{n²} | 1^{−2} 2^5 4^{−2}, weight 1/2, level 4, holomorphic | same |
| q∏(1−q^n)^{24} | τ(1..5) = 1, −24, 252, −1472, 4830; τ(11) = 534612; 1^{24}, level 1 | same |
| Witt: U(free Lie on one generator per degree) = (1−q)/(1−2q) | ∏(1−q^n)^{−l_n} with n l_n = Σ_{d\|n} μ(n/d)(2^d − 1), l = 1, 1, 2, 3, 6, 9, 18, 30, … (A059966) | exact for n < 61 |
| (1−q)/(1−2q), Σ q^{n³}, MacMahon ∏(1−q^n)^{−n} | rejected | rejected; MacMahon gives r_t = −φ(t), with unbounded support |

## 3. The candidates

### 3.1 Candidate 1: the Witt layer, graded by |P|

Set b_n := n[x^n] log A(x). Then dim V_n = (n−1)! b_n, and b_n = |B_n|
([PL] §1). From
ch V_n = Σ_{d|n} (μ(d)/d) [x^{n/d}] log A · p_d^{n/d} (COMPUTED, with the
a_n from OEIS A006455, n ≤ 18, and brute force for n ≤ 6):

- b_n = 1, 3, 16, 131, 1561, 26532, 637890, 21580043, 1021943455, …
- c_n = dim V_n^{S_n} = (1/n) Σ_{d|n} μ(d) b_{n/d}
      = 1, 1, 5, 32, 312, 4419, 91127, 2697489, 113549271, 6735956412, …
- c_n^− = ⟨ch V_n, e_n⟩ = 1, 2, 5, 32, 312, 4424, 91127, 2697489, 113549271, 6735956724, …
- dim V_n^{A_n} = c_n + c_n^− = 2, 3, 10, 64, 624, 8843, 182254, 5394978, …
- the trace of a cycle type d^m on V_{dm} is μ(d) d^{m−1} (m−1)! b_m.
  For d = 2 this gives −1, −6, −128, −6288, −599424, …

Checks (COMPUTED):
- For n ≤ 5, c_n and c_n^− agree with a direct sum over unlabeled posets of
  (1/|Aut P|) Σ_g χ_{Lie(P)}(g) (respectively sgn(g)χ), computed with the
  closed character formula.
- A(q) = ∏(1 − q^n)^{−c_n} holds through q^{18}.
- c_n, c_n^− ≥ 0.
- The dimensions 32, 786, 37464, 3183840 (n = 3..6) agree with [PL].

c_n − c_n^− = (2/n) Σ μ(d) b_{n/d} over the d | n with d even and n/d odd,
so c_n = c_n^− unless n ≡ 2 (mod 4) (PROVEN from the formula; seen in the
data).

LOOKUP: b_n, c_n, c_n^− and c_n + c_n^− are not in the OEIS.

**Growth obstruction (PROVEN).** Split [n] into {1..k} and {k+1..n}, with
k = ⌊n/2⌋. Every set of relations i < j with i ≤ k < j is transitive (there
are no chains of length 3) and naturally labeled. So
a_n ≥ 2^{⌊n/2⌋⌈n/2⌉} (COMPUTED as a check for n ≤ 18; the ratio
a_{n+1}a_{n−1}/a_n² stays near 1.35–1.4). Hence A(q) has radius of
convergence 0.

Since c_n ≥ 0, a bound c_n ≤ e^{Cn} would make ∏(1−q^n)^{−c_n} converge
for |q| < e^{−C}. So c_n, and with it c_n + c_n^− ≥ c_n and dim V_n ≥ c_n,
grow faster than any exponential. The cycle-type traces have absolute value
d^{m−1} dim V_m, so they grow the same way. No series in this grading
defines a function on the upper half-plane, so none is modular. This is a
property of the count of posets, not of the Lie structure.

### 3.2 Candidate 2: g-fixed P-partitions, g ∈ Aut(P) ∩ A_n

A P-partition here is an order-reversing σ: P → N (x <_P y ⇒ σ(x) ≥ σ(y)).
Put T_g(q) = Σ_{σ∘g=σ} q^{|σ|}.

**Quotient formula (PROVEN; COMPUTED).**
- g-fixed σ are the order-reversing maps on Q = P/⟨g⟩ (a poset by [PL]
  Lemma 2.1), and the orbit O has weight |O|.
- Label Q naturally. Sorting σ decreasingly, with ties in increasing label,
  gives a unique w ∈ Lin(Q) with σ(w_1) ≥ … ≥ σ(w_m), strict at the
  descents of w.
- Writing σ(w_i) = Σ_{j≥i} δ_j gives

      T_g = Σ_{w∈Lin(Q)} q^{Σ_{j∈Des w} S_j(w)} / ∏_{j=1}^m (1 − q^{S_j(w)}),   S_j(w) = |w_1| + … + |w_j|.

  The prefix sums S_j are correct for this convention. They replace the
  suffix-sum version in the earlier draft, which used a different
  convention and was never checked.
- Brute-force enumeration over P agrees with the formula for 14 (P, g)
  pairs: antichain 4, 2+2, bowtie, 2+2+2, 3+3, B_3, and every class of
  Aut(P) ∩ A_n, through q^{29} (n ≤ 4) or q^{15} (n ≥ 6).
- For 3+3 the swap of the two chains is odd, so Aut(P) ∩ A_6 = 1. The
  alternating restriction loses the symmetry entirely there.

**Lemma R (PROVEN).** Let R be a rational function with no poles in
0 < |q| < 1, and F(τ) = R(e^{2πiτ}). Suppose F(γτ) = v(γ)(cτ+d)^k F(τ) for
all γ in a finite-index Γ ≤ SL_2(Z), with k real and |v(γ)| = 1. Then F is
constant, and F = 0 if k ≠ 0.

*Proof.*
1. Fix τ_0 ∈ H. The limit set of a finite-index subgroup of SL_2(Z) is
   R ∪ {∞} (CITED: Fuchsian group of the first kind). So for every real x
   there are γ_j ∈ Γ with γ_j τ_0 → x. Then
   Im γ_jτ_0 = Im τ_0 / |c_jτ_0 + d_j|² → 0, so |c_jτ_0 + d_j| → ∞.
2. R has finitely many poles on |q| = 1. Take x with e^{2πix} not a pole.
   Then F(γ_jτ_0) → R(e^{2πix}), which is finite.
3. If k > 0, then |F(τ_0)| = |c_jτ_0 + d_j|^{−k} |F(γ_jτ_0)| → 0, so
   F ≡ 0.
4. If k < 0, then |F(γ_jτ_0)| → 0, so R vanishes at all but finitely many
   points of the circle, and R ≡ 0.
5. If k = 0, then |F(τ_0)| = |R(e^{2πix})| for every τ_0. So |F| is
   constant on H, and F is holomorphic (R has no poles in the disk), hence
   constant. ∎

The same holds for q^a R(q) with a ∈ Q: apply the lemma to a power that
clears the denominator of a.

Every T_g above is rational, with poles only at roots of unity. So no T_g
is modular, for any normalization q^a T_g. The detector rejects all 14 as a
check. LOOKUP: the g = 1 series are classical P-partition series, e.g.
A000292, A006918, A038163, A117485, and A003404 ("solid partitions
supported on the graph of the cube" for B_3). The fixed-point series are
quasi-polynomial or of Molien type (A002264, A142150, A029073, A256976,
A128498). The bowtie series 1, 2, 3, 6, 10, 14, 20, … and the 2+2 swap
series have no OEIS entry.

**Linear-extension content.** For g = 1 the numerator is Σ_{w∈Lin P} q^{maj w},
and lim_{q→1} (1−q)^n T_1 = e(P)/n!. For general g:
- the numerator is the joint distribution of descents of w ∈ Lin(P/⟨g⟩),
  weighted by orbit-size prefix sums;
- lim_{q→1} (1−q)^m T_g = Σ_{w∈Lin(P/⟨g⟩)} ∏_j 1/S_j(w);
- the number of terms is |Lin(P/⟨g⟩)|, e.g. 90 for 2+2+2 at g = 1, 6 at
  (2,2,1,1), and 1 at (3,3).

This meets the linear-extension criterion (LE) in a mild way. It is P-partition
theory, not moonshine, and it is left to the sibling linear-extension item.

### 3.3 Candidate 3: P-partitions of infinite posets

- **k·N with S_k (COMPUTED, k ≤ 5, every class).** A g-fixed k-tuple of
  partitions is constant on cycles, so T_g = ∏_{cycles λ} 1/(q^λ; q^λ)_∞.
  This is q^{k/24}/∏ η(λτ), with weight −ℓ(cycle type)/2. The detector
  recovers the Frame shape exactly, for example 2^{−2} for (2,2) ∈ A_4 and
  1^{−1}3^{−1} for (3,1). **MODULAR, but** this is the Frame shape of the
  permutation representation of S_k on k letters. Any permutation group
  gives the same, and nothing about posets enters except "disjoint union of
  copies of N". The alternating restriction only removes classes.
- **chain_m × N** (plane partitions with ≤ m rows). Brute force agrees
  with ∏(1−q^n)^{−min(n,m)} through q^{17}. LOOKUP: A000990 (m = 2),
  A000991 (m = 3). Its product with (q^{−1/24}η)^m is the nonconstant
  polynomial ∏_{n<m}(1−q^n)^{m−n}, so for m ≥ 2 Lemma R rules out
  modularity of q^a T, for every a: **NO SIGN** (PROVEN).
- **N × N.** The identity gives MacMahon's ∏(1−q^n)^{−n}. The transpose
  gives the symmetric plane partitions,
  ∏(1−q^{2i−1})^{−1} ∏_{i<j}(1−q^{2(i+j−1)})^{−1}. Brute force agrees
  through q^{19}, and the series is A005987 (LOOKUP).
  - Both are holomorphic and nonvanishing on H, so a modular one would be
    weakly holomorphic.
  - Weakly holomorphic forms have log|a_n| = O(√n) (CITED: the standard
    bound |F(x+iy)| ≪ e^{B/y} plus the saddle point).
  - Both series have log a_n ≍ n^{2/3} (CITED: Wright 1931 for MacMahon;
    Meinardus' theorem for the symmetric case, whose exponent of
    (1 − q^{2k})^{−1} grows like k/2).
  - So the verdict is **NO SIGN** (PROVEN modulo these CITED growth
    statements). The detector rejects both.

### 3.4 Candidate 4: the Fock space of Lie(P), and what A_n buys

T_g := Σ_n tr(g | Sym(Lie(P) ⊗ tC[t])_n) q^n = ∏_{n≥1} det(1 − g q^n | Lie(P))^{−1}.

Lie(P) is defined over Q, so the characteristic polynomial of g is
∏_t (x^t − 1)^{r_t}, the Frame shape. Here t r_t = Σ_{e|t} μ(t/e) χ(g^e),
and the χ(g^e) come from the fixed-point formula. Hence
T_g = q^{dim/24}/∏_t η(tτ)^{r_t}. This is a weakly holomorphic modular form
of weight −Σr_t/2 (PROVEN; this is the eta-quotient form of (W_g), and it
holds for **every** rational representation of **every** finite group).

COMPUTED for Lie_4 … Lie_7, 2+2, 2+2+2, 1+1+2 and the bowtie, over all
classes of Aut(P):
- The closed character formula agrees with the cyclic-class trace for
  every power of g.
- Every Frame-shape exponent is integral.
- T_g, computed from the characters alone as exp Σ_k Σ_m χ(g^k) q^{mk}/k,
  is recognized by the detector as exactly 1/η_g.

Sample Frame shapes:
- connected P (bowtie): free action, o^{e_C/o};
- Lie_5 at a 5-cycle: 1^{−1}5^5;
- Lie_6 at (2,2,2): 1^{−8}2^{64};
- Lie_6 at (3,3): 1^{−3}3^{41};
- Lie_6 at a 6-cycle: 1^1 2^{−2} 3^{−3} 6^{22};
- Lie_7 at a 7-cycle: 1^{−1}7^{103}.

For a p-cycle on Lie_p the shape is 1^{−1} p^{((p−1)!+1)/p}, which is
integral by Wilson's theorem.

**What A_n buys (PROVEN, COMPUTED).** On Aut(P) ∩ A_n we have
H_P ≅ Lie(P), so the homological and Lie versions of every candidate
coincide (checked: identical Frame shapes for every even g above). For odd
g, H_P carries −g. That changes the Frame shape only by
t^r ↦ (2t)^r t^{−r} for odd t (checked on every odd class above), which is
again an eta product. **The sign twist never obstructs modularity, so
removing it buys nothing.** In candidates 1–3 the twist does not enter at
all.

**The one near-miss: Lie_5 is 24-dimensional.** The q-order of η_g is
dim/24, which is 1 exactly for Lie_5 (dim 4! = 24).
- On S_5, χ_{Lie_5} vanishes off the identity and the 5-cycles, so:
  - elements of order t ∈ {2, 3, 4, 6} act freely, giving t^{24/t};
  - the 5-cycle gives 1^{−1}5^5.
- COMPUTED: all seven η_g are multiplicative through q^{120}:
  1^{24}, 2^{12} (twice), 3^8, 4^6, 6^4 and 1^{−1}5^5.
- The holomorphic ones are newforms. LMFDB 1.12.a.a, 4.6.a.a, 9.4.a.a,
  16.3.c.a and 36.2.a.a agree with η(tτ)^{24/t} for every n < 100. The
  Sturm bounds are 1, 3, 4, 6 and 12, so these identities are PROVEN given
  the CITED Gordon–Hughes–Newman membership and the LMFDB data.
- η(5τ)^5/η(τ) = Σ_n (Σ_{d|n} (n/d | 5) d) q^n. This is Ramanujan's
  identity: the Eisenstein series E_2^{χ_5,1} ∈ M_2(Γ_0(5), χ_5) (CITED:
  Diamond–Shurman §4.6). It is checked through q^{200} against a Sturm
  bound of 1, so it is PROVEN given the membership.

This is a Mason-style picture: a 24-dimensional representation whose Frame
shapes give multiplicative eta products, like the multiplicative eta
products attached to M_24. It is **not** specific to posets. The regular
representation of S_4 (control, COMPUTED) gives 1^{24}, 2^{12}, 3^8, 4^6,
all multiplicative. The only input from Lie theory is χ(5-cycle) = μ(5) = −1
and dim = 24.

Lie_7 already has q-order 30 at every class, so it has no normalized
eigenform. A negative control, 1^{20}2^2 (q-order 1), is correctly found
not multiplicative. **SUGGESTIVE of nothing beyond dim Lie_5 = 24.**

**Twisted traces T_{g,h} (not computed).** For commuting g, h the
generalized-moonshine trace on the h-twisted sector of this free-boson Fock
space has modes in (1/o(h))Z. One expects again eta products in τ/o(h),
fixed by the joint eigenvalues of (g, h). That is the same Frame-shape
mechanism. Since nothing poset-specific beyond the character can enter, it
was not pursued.

## 4. Recommendation

**Stop.** Each natural grading on the poset/cone Lie theory falls into one
of three cases:
- it is too big: the Witt layer grows super-exponentially, so there is not
  even a q-series on H (PROVEN);
- it is too small: equivariant P-partitions are rational in q, and the
  non-rational infinite-poset products are not modular (PROVEN, part
  modulo CITED growth bounds);
- it is modular for a generic reason: Frame shapes of a rational
  representation, the same mechanism for any finite group.

The fixed-point formula and the vanishing criterion supply the characters,
and Frame shapes turn any characters into eta products. That is a fact
about eta functions, not about posets. The alternating group adds nothing.

The single coincidence, that Lie_5|_{S_5} has only multiplicative Frame
shapes, is explained by dim Lie_5 = 24 and is shared by the regular
representation of S_4.

What would change this verdict is a grading not considered here whose
exponents (the c_n(g) in a Witt product) are themselves modular. That would
mean a *sub*-family of posets whose counts grow like e^{C√n}, together with
a group acting on it that is not just a permutation action on components.
No candidate for such a family arose from the theory itself. Engineering
one to fit a q-series is what the scoping was asked to avoid.

## 5. Corrections to the earlier draft

- The draft's formulas for row 1 were right with b_n = |B_n| = n[x^n] log A;
  the definition is now stated.
- The draft's quotient formula used suffix sums with an unstated
  convention. It is replaced by the verified prefix-sum form in §3.2.
- The draft's "MODULAR" for k·N is kept, with the qualifier "generic".
- No error was found in the existing notes. The dimensions and the closed
  character formula of [PL] were reproduced along the way.

## Reproduce

Run in `compute/`. The scripts are plain Python 3, exact arithmetic. They
import `poset_jks_check.py` and `poset_lie_structure.py`.

    python3 moonshine_scoping.py > output/moonshine_scoping.txt    # all sections, ~2 s, exit 0 iff all 217 checks pass
    python3 moonshine_scoping.py --controls   # detector controls (9 checks)
    python3 moonshine_scoping.py --witt       # candidate 1 (13)
    python3 moonshine_scoping.py --ppart      # candidate 2 (28)
    python3 moonshine_scoping.py --infinite   # candidate 3 (24)
    python3 moonshine_scoping.py --fock       # candidate 4, Lie_5 multiplicativity, Sturm check (143)
    python3 -m unittest test_moonshine_scoping
    python3 moonshine_lookup.py > output/moonshine_lookup.txt      # network: OEIS + LMFDB, ~1-3 min

`moonshine_lookup.py` is informational and asserts nothing. The LMFDB
answers Python's urllib with a captcha page, so the script uses curl. When
rate-limited it prints "not compared" rather than failing. The archived
outputs are `compute/output/moonshine_scoping.txt` and
`compute/output/moonshine_lookup.txt`.

## References

- [PL] `notes/global_module_operations_plethlog.md`.
- [GT] `notes/general_theory.md`.
- [FP] `notes/fixed_point_formula.md`.
- R. E. Borcherds, Monstrous moonshine and monstrous Lie superalgebras,
  Invent. Math. 109 (1992).
- G. Mason, M_24 and certain automorphic forms, Contemp. Math. 45 (1985).
- D. Dummit, H. Kisilevsky, J. McKay, Multiplicative products of
  η-functions, Contemp. Math. 45 (1985).
- K. Ono, The web of modularity, CBMS 102 (2004), Thms 1.64–1.65.
- F. Diamond, J. Shurman, A first course in modular forms, §4.6, §5.9
  (Sturm).
- E. M. Wright, Asymptotic partition formulae I: plane partitions, Quart.
  J. Math. 2 (1931).
- G. Meinardus, Asymptotische Aussagen über Partitionen, Math. Z. 59 (1954).
- R. P. Stanley, Ordered structures and partitions, Mem. AMS 119 (1972).
