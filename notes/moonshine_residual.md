# Residual moonshine candidates after the moonshine_scoping audit

This note takes the four candidates that `notes/audit_moonshine_scoping.md`
([AUD]) left open, in its recommended order: item 6(d), item 8, item 7,
item 1 of its §3. The scoping note is `notes/moonshine_scoping.md` ([MS]).
Tags: **PROVEN** (argument given here), **COMPUTED** (checked by
`compute/moonshine_residual.py`; see Reproduce), **CITED**. Nothing here was
looked up on the network.

## Verdict

| Item of [AUD] §3 | Before | After this note |
|---|---|---|
| 6(d) unlabeled component-closed classes with exponential connected counts | OPEN | **No general obstruction exists, and none can** (Prop. E: an arbitrary class realizes the meromorphic modular form 1/E_6(20τ)). **Every natural class tested is excluded from every function meromorphic on H** (Lemma P, Lemma L): rooted forests, posets with tree Hasse diagrams, N-free (= series-parallel) posets, posets whose Hasse diagram is a union of cycles. Classes of height ≤ h (h ≥ 2), graded posets and the whole of 𝐏 have radius 0 ([AUD] 6(a)). |
| 8 mock modularity of the rational P-partition series T_g | OPEN | **Excluded for cuspidal shadows** (Lemma M, PROVEN). It needs only v(γ) ≠ 0, and it reproves Lemma R for these series. A non-cuspidal shadow needs a regularized period integral, which is not written out here. |
| 7 other infinite posets, broad sense | OPEN | **Shifted quadrant: excluded** (Lemma D of [AUD]; product formula COMPUTED to q^16, CITED). **Infinite binary tree: excluded** (Lemma P; radius exactly 1/4, B(1/4) ≤ 2.65). **N^k (k ≥ 3): excluded on every group with one cusp class** (Prop. C). **On groups with several cusps it stays OPEN**, and Example G shows that growth, positivity and holomorphy at ∞ cannot close it. |
| 1 T_{g,h} on twisted sectors | by citation only | **COMPUTED** for 7 commuting pairs (Lie_4, Lie_5, Lie_6, 2+2, bowtie). The S-, T- and Γ(N)-laws hold to 1e-8, and a conjugate pair of eigenlines is identified with a Siegel function. **Generic.** The phrase "eta products in τ/o(h)" in [MS] is wrong in general: Lie_5 at (g, g²) has a non-real q-coefficient. |

**Recommendation: STOP still holds.** The one escape left is the
multi-cusp broad sense for N^k (k ≥ 3), where the modular function would
have to have an essential singularity at some cusp. No moonshine
formulation needs such an object, and none has been proposed. Item 6(d) is
closed in the only sense it can be closed. Arbitrary classes can hit
genuine meromorphic modular forms, so any candidate there is engineered,
and [MS] §4 already rules engineered candidates out. Every class the
theory itself suggests is excluded by proof.

## 1. Item 6(d): unlabeled component-closed classes

**Set-up.** Let 𝒞 be a set of connected unlabeled posets, and let u_n be
the number of them of size n. The disjoint unions of members of 𝒞 form a
component-closed class. Its type series is

    A_𝒞(q) = Exp(U)(q) = ∏_{n≥1} (1 − q^n)^{−u_n} = exp Σ_{k≥1} U(q^k)/k,   U(x) = Σ u_n x^n.

Suppose U has radius ρ ∈ (0, 1). Then A_𝒞 also has radius ρ: it dominates
1 + U coefficientwise, and it converges wherever U does. The question is
whether q^a A_𝒞 can be the expansion at ∞ of any function meromorphic on H,
and in particular of a meromorphic modular form or a Borcherds product.

**Reduction (PROVEN).** If F is meromorphic on H and F(τ) = q^a A(q) for
Im τ large, then F(τ+1) = e^{2πia}F(τ) by the identity theorem. So
F e^{−2πiaτ} = M(q) with M meromorphic on 0 < |q| < 1, and M = A on |q| < ρ.
Since ρ < 1, M is meromorphic in a neighborhood of q = ρ.

**Lemma P (PROVEN).** Let A = Σ a_n q^n with a_n ≥ 0, radius ρ ∈ (0, 1), and
Σ a_n ρ^n < ∞. Then A has no meromorphic continuation to any neighborhood
of q = ρ. In particular q^a A is not the expansion of any function
meromorphic on H. That includes weakly holomorphic and meromorphic modular
forms, Borcherds products and holomorphic parts of harmonic Maass forms.

*Proof.* Pringsheim: q = ρ is a singular point of A. A continuation M
would be bounded on [0, ρ), by A(ρ) < ∞, so it has no pole at ρ. Hence M is
holomorphic at ρ, a contradiction. ∎

For type series, A_𝒞(ρ) < ∞ ⟺ U(ρ) < ∞. Indeed U(x)/x is increasing, so
Σ_{k≥2} U(ρ^k)/k ≤ U(ρ) Σ_k ρ^{k−1}.

**Lemma L (log criterion, PROVEN).** Keep the set-up and assume U(ρ) = ∞.
If A_𝒞 continues meromorphically to a neighborhood of ρ, then for some
**positive integer** m the function U(x) + m log(1 − x/ρ) continues
holomorphically to a neighborhood of ρ.

*Proof.* V(q) := Σ_{k≥2} U(q^k)/k is holomorphic on |q| < ρ^{1/2}, and
ρ^{1/2} > ρ. So exp U = M e^{−V} is meromorphic near ρ. Write it as
(1 − q/ρ)^{−m} h with m ∈ Z and h holomorphic and nonvanishing near ρ. On
the disk, U is a branch of log(exp U), so U + m log(1 − q/ρ) agrees with a
branch of log h, which is holomorphic near ρ. Finally U(x) → +∞ as x → ρ⁻,
which forces m > 0. ∎

So A_𝒞 can be meromorphic at ρ only if u_n behaves like a necklace count,
u_n ≈ m ρ^{−n}/n, with integral m. Square-root or algebraic singularities of
U, finite values U(ρ), and non-integral logarithmic coefficients are all
excluded.

### 1.1 Natural classes

All counts are COMPUTED, and checked against a brute-force pass over all
unlabeled posets with n ≤ 6.

| Class 𝒞 (connected members) | u_n | Obstruction | Status |
|---|---|---|---|
| rooted trees, root minimal (posets in which every element has ≤ 1 lower cover; their disjoint unions are the rooted forests) | A000081: R = x Exp(R) | R(ρ) ≤ 1 | **PROVEN excluded** (Lemma P) |
| posets whose Hasse diagram is a tree (= oriented trees) | A000238: 1, 1, 3, 8, 27, 91, … | T(ρ) ≤ R_o(ρ) ≤ 1/2 | **PROVEN excluded** (Lemma P) |
| connected N-free posets (= series-parallel) | 1, 1, 3, 9, 30, 103, 375, … (total A003430) | C(ρ) < 1.15 | **PROVEN excluded** (Lemma P) |
| posets whose Hasse diagram is a cycle | 0, 0, 0, 2, 2, 7, … | log coefficient m = 1/2 | **PROVEN excluded** (Lemma L) |
| height ≤ h (h ≥ 2), graded posets, all of 𝐏 | ≥ 2^{n²/4}/n! | radius 0 | excluded ([AUD] 6(a)) |
| chains | u_n = [n = 1] | radius 1 | modular, generic ([AUD] 6(b)) |
| polynomially bounded u_n | | radius 1 | eta quotient or nothing ([AUD] 6(c), Kohnen) |

Interval orders and semiorders are not component-closed, since 2+2 is
neither. Width ≤ w is not closed under disjoint union either.

**Rooted trees (PROVEN).** R = x e^R A(x) with A = exp Σ_{k≥2} R(x^k)/k, which
is increasing on [0, ρ). So R e^{−R} = xA(x) is strictly increasing in x.
Suppose R(x_1) > 1. By continuity R(x_0) = 1 for some x_0 < x_1, and then
x_1A(x_1) > x_0A(x_0) = e^{−1} ≥ R(x_1)e^{−R(x_1)}, a contradiction. So
R ≤ 1 on [0, ρ), and R(ρ) ≤ 1 by monotone convergence. Here ρ = 0.3383…
(CITED: Otter 1948). COMPUTED: the partial sum through x^120 at
x = (1 − 2/120)·u_119/u_120 = 0.3369 is 0.886.

**Oriented trees (PROVEN).**
- A Hasse diagram that is a tree is the same as an oriented tree. Every
  orientation of a tree is a Hasse diagram, because the path between two
  vertices is unique, so no edge is implied by transitivity.
- Rooted oriented trees satisfy R_o = x Exp(2R_o): each child hangs by an up
  edge or a down edge. The argument above, with w e^{−2w}, gives R_o ≤ 1/2.
- T_n ≤ R_{o,n} ≤ n T_n, so T and R_o have the same radius and T(ρ) ≤ 1/2.
- COMPUTED: T = R_o − R_o² matches A000238 and the brute force. This
  dissymmetry formula is not needed for the bound.

**Series-parallel (PROVEN).**
- Finite N-free posets are exactly the series-parallel posets (CITED:
  Valdes–Tarjan–Lawler 1982; COMPUTED n ≤ 6).
- A connected one with ≥ 2 elements is an ordinal sum of k ≥ 2 ordinally
  indecomposable pieces, uniquely. Each piece is a point or a disconnected SP
  poset. So C = x + Σ_{k≥2} s^k, with s = x + D and D = Exp(C) − 1 − C.
- For 0 ≤ x < ρ all terms are ≥ 0, so C(x) < ∞ forces s(x) < 1. Then
  e^C − 1 − C ≤ D < 1, so C < 1.15 on [0, ρ), and C(ρ) ≤ 1.15.

**Cycle-Hasse posets (PROVEN).**
- An n-cycle with an edge orientation w ∈ {±}^n is a Hasse diagram iff it is
  acyclic and no edge is implied. That means w is not constant and is not
  "two runs, one of length 1".
- Isomorphism is the dihedral action: a reflection reverses the word and
  flips every sign. COMPUTED: this matches the brute-force poset count for
  n ≤ 6.
- Burnside gives u_n = (1/2n) Σ_{d|n} φ(n/d) 2^d − 2 + Refl_n/(2n), where each
  of the n reflections fixes ≤ 2^{⌈n/2⌉} words. (A position fixed by the
  reflection would need w_i = −w_i; otherwise one value per 2-orbit.) So

      U(x) = −½ log(1 − 2x) + W(x),   W holomorphic on |x| < 2^{−1/2},

  since the necklace part is ½ Σ_e (φ(e)/e)(−log(1 − 2x^e)).
- Lemma L would need U + m log(1 − 2x) holomorphic at 1/2. That forces
  m = 1/2, which is not an integer. COMPUTED: n u_n 2^{−n} = 0.586, 0.531,
  0.510 at n = 10, 14, 18.

The obstruction here is the reflection symmetry: dihedral counting halves
the necklace coefficient. An integral coefficient needs necklace-type
counting (cyclic symmetry, no reflections). No component-closed class of
posets with that kind of counting came up.

COMPUTED, for orientation: the singular exponent α in u_n ~ Cρ^{−n}n^α,
estimated by −(n−1)²(u_n u_{n−2}/u_{n−1}² − 1) at n = 120, is
- −1.502 for rooted trees;
- −2.505 for oriented trees;
- −1.509 for connected SP posets;
- −1.000 for the necklace control (a logarithmic singularity, which Lemma L
  needs).

### 1.2 No general obstruction

**Proposition E (PROVEN, modulo the bound marked below).**
- Component-closed classes realize every sequence 0 ≤ u_n ≤ (number of
  connected unlabeled posets on n points): take 𝒞 to be any u_n of them in
  each size.
- The exponents of 1/E_6 = ∏(1 − q^n)^{−u_n} are positive integers,
  u = 504, 143388, 51180024, …, and n u_n e^{−2πn} → 1 (a simple pole at
  q = e^{−2π}, so m = 1).
- The labeled height-2 posets on L ⊔ U with |L| = ⌊N/2⌋ that contain every
  relation (min L, ·) and (·, max U) are connected. So there are at least
  2^{(⌊N/2⌋−1)(⌈N/2⌉−1)}/N! connected unlabeled posets on N points.
- For N = 20n this exceeds u_n. So **1/E_6(20τ), a meromorphic modular form of
  weight −6 on Γ_0(20) with radius e^{−π/10}, is the type series of a
  component-closed class.**

COMPUTED:
- u_n > 0 for n ≤ 150;
- |n u_n e^{−2πn} − 1| ≤ 1.36 e^{−πn} for n ≤ 10 (the next poles of 1/E_6
  are at |q| = e^{−π});
- the poset bound exceeds 2e^{2πn} for n < 2000.

For all n, positivity and the bound u_n ≤ 2e^{2πn} follow from the pole
structure of 1/E_6 (Bruinier–Kohnen–Ono: g_n = 12σ_1(n) + j_n(i)/2 for
q d/dq log(1/E_6)) with an effective bound on j_n(i) − 2e^{2πn}. That bound is
not written out here.

So no argument that uses only growth, positivity and integrality can close
6(d). Any obstruction must use the structure of a particular class, as §1.1
does. The point of [MS] §4 stands: a class built to hit a modular form is
engineering, not moonshine.

## 2. Item 8: mock modularity of the rational series

**Lemma M (PROVEN).** Let R be a rational function with no poles in
|q| < 1 and a pole at a root of unity ζ_0 = e^{2πiθ}. Let a ∈ R and
f(τ) = e^{2πiaτ}R(e^{2πiτ}). Suppose there are
- a real weight k;
- a finite-index Γ ≤ SL_2(Z);
- a multiplier v with v(γ) ≠ 0;
- a cusp form g of weight 2 − k (with the conjugate multiplier).

Let g*(τ) = C ∫_{−τ̄}^{i∞} \overline{g(−w̄)} (w + τ)^{−k} dw be its
non-holomorphic Eichler integral. Then f̂ = f + g* does **not** satisfy
f̂(γτ) = v(γ)(cτ+d)^k f̂(τ) for all γ ∈ Γ. The case g = 0 is included, so this
also reproves Lemma R of [MS] for such R, without |v| = 1.

*Proof.*
1. **The period.** Fix γ = (a b; c d) ∈ Γ with c ≠ 0. Put h(u) = \overline{g(−ū)}
   and γ′ = (a −b; −c d). Substitute w = γ′u, using
   −\overline{γτ} = γ′(−τ̄) and w + γτ = (u+τ)/((−cu+d)(cτ+d)). This gives

       g*(τ) − v(γ)^{−1}(cτ+d)^{−k} g*(γτ) = C ∫_{d/c}^{i∞} h(u)(u + τ)^{−k} du =: r_γ(τ).

   As a function of τ, r_γ is holomorphic off −d/c − i[0, ∞), because the
   integrand is singular only at τ = −u. The integral converges, since h
   decays exponentially at both cusps d/c and i∞. So r_γ is continuous on a
   neighborhood of every real x ≠ −d/c = γ^{−1}(∞).
2. **The law.** The transformation law becomes
   f(γτ) = v(γ)(cτ+d)^k (f(τ) + r_γ(τ)).
3. **Choice of points.** The points x_t = γ^{−1}(θ + t), t ∈ Z, are
   distinct reals ≠ −d/c, and they accumulate only at −d/c. So infinitely
   many of them are distinct mod 1. R has finitely many poles on the circle,
   so some x_t has e^{2πix_t} not a pole of R.
4. **Contradiction.** Let τ → x_t vertically. Then γτ → θ + t, so the left
   side blows up: e^{2πiγτ} → ζ_0, a pole, and |e^{2πiaγτ}| → 1. The right
   side tends to the finite value
   v(γ)(cx_t+d)^k (e^{2πiax_t}R(e^{2πix_t}) + r_γ(x_t)). ∎

Every T_g of [MS] candidate 2 has a pole at q = 1, from the constant maps.
So **no q^a T_g is a mock modular form with cuspidal shadow**, for any
weight, group or multiplier. That covers every mock theta function of
Ramanujan type, whose shadows are unary theta series that are cusp forms.

*Not covered.* Non-cuspidal shadows, e.g. Zagier's weight-3/2 class-number
series with shadow θ. There the Eichler integral has to be regularized, and
r_γ picks up terms in (τ + d/c)^{1−k}. These are again regular at real
x ≠ −d/c, so the same proof should go through, but the regularized formula
is not derived here. Higher-depth (mixed) mock forms are not addressed.

## 3. Item 7: other infinite posets, broad sense

"Broad sense" means F(γτ) = v(γ)(cτ+d)^k F(τ) on a finite-index Γ, with
v(γ) ≠ 0 and no condition at the cusps.

**Shifted quadrant {(i, j) : i ≤ j} (PROVEN given the product formula).**
COMPUTED by direct enumeration through q^16: its P-partitions have

    F = ∏_{n≥1} (1 − q^n)^{−⌈n/2⌉}.

The floor(n/2) variant fails, as a negative control. This is the shifted hook
formula for the unbounded shifted shape (CITED: Gansner 1981; Sagan 1982;
not re-read). The exponents are polynomially bounded and
Σ_{d|N} d⌈d/2⌉ ≥ N²/2, so G(iy) ≫ y^{−3}, against Lemma D of [AUD]: **no
transformation law of any kind.** COMPUTED: y³ G(iy) = 0.004950 and 0.004877
at y = 0.01 and 0.003, tending to ζ(3)/(2π)³ = 0.004846.

**The infinite binary tree, root minimal (PROVEN).**
- A P-partition has finite support, which is a finite subtree containing
  the root, and values that weakly decrease upward.
- With B_m the series for root value ≤ m, B_m = B_{m−1} + q^m B_m² and
  B = lim B_m. COMPUTED: this matches a direct search through q^8:
  1, 1, 3, 8, 24, 72, 229, 740, 2460.
- **Value at 1/4.** B_1 is the Catalan series, with B_1(1/4) = 2. At
  x = 1/4, B_m = 2B_{m−1}/(1 + √(1 − 4^{1−m}B_{m−1})) ≤ B_{m−1}/(1 − 2·4^{−m}B_{m−1}).
  By induction from B_2(1/4) = 8 − 4√2 = 2.343, every
  B_m(1/4) ≤ 2.343·∏_{m≥3}(1 − 5.4·4^{−m})^{−1} < 2.65.
- **Each B_m converges at 1/4** (induction). If B_m had radius < 1/4, the
  closed form would be analytic at that radius, against Pringsheim.
- The coefficients of B_m increase to those of B. So B(1/4) ≤ 2.65, and the
  radius is exactly 1/4, since B ≥ B_1.
- Lemma P: **B is not the expansion of any function meromorphic on H.**
  COMPUTED: sup_m B_m(1/4) = 2.467, and α = −1.498 at n = 200 (square root).
- The k-ary tree satisfies B_m = B_{m−1} + q^m B_m^k with the Fuss–Catalan
  radius. The same argument applies; it is not written out here.
- If the root is maximal, the only finite-support P-partition is σ = 0.

**N^k, k ≥ 3.** The counts dominate the plane partitions, so
log a_n ≫ n^{2/3} ([AUD] §2.4). The series is not a product, so Lemma D does
not apply.

- **Proposition C (PROVEN).** If Γ has a single cusp class, no q^a F_{N^k}
  satisfies a broad-sense law on Γ.
  *Proof.* Every cusp is γ∞ with γ ∈ Γ, and F|_kγ = v(γ)F has the same
  q-expansion up to a constant. So F is meromorphic at every cusp, and
  holomorphic on H (radius 1). Hence it is weakly holomorphic and
  log|a_n| = O(√n) ([MS] §3.3, CITED), a contradiction. ∎
  This covers SL_2(Z) and every one-cusp subgroup, congruence or not.
- **Example G (PROVEN; growth COMPUTED).** Groups with several cusps cannot
  be handled by growth. Let f = (η(2τ)/η(τ))^{24} = q∏(1 + q^n)^{24}, the
  Hauptmodul of Γ_0(2): zero at ∞, pole at 0. Put F = ∏_{j≥0}(1 + f/2^j).
  - F is Γ_0(2)-invariant and holomorphic on H.
  - F is holomorphic at ∞ (F(∞) = 1), with an essential singularity at the
    cusp 0.
  - Its q-coefficients are positive, being a positive power series in f,
    which has nonnegative coefficients.
  - Near the cusp 0, f(iy) ≈ 2^{−12}e^{π/y}, so log F(iy) ≈ (π/y)²/(2 log 2),
    and the saddle point gives log a_n ≍ n^{2/3}, the same order as N × N.

  COMPUTED: log a_n/√n = 13.1, 16.5, 20.4 at n = 50, 100, 200, increasing.
  So holomorphy on H and at ∞, positivity and N × N-type growth together
  do not exclude Γ_0(2). (F's coefficients are not integers. Whether
  integrality obstructs such essential-singularity examples is not known
  to me.)

**Verdict for N^k (k ≥ 3): OPEN only on groups with ≥ 2 cusp classes, and
only for functions with an essential singularity at some cusp not
equivalent to ∞.** Excluding this needs structural information about solid
partitions that is not available.

## 4. Item 1: twisted traces T_{g,h}

Let g, h commute in Aut(P). Write V = Lie(P), split into joint eigenlines
with g = e^{2πis}, h = e^{2πir}, s, r ∈ [0, 1). On the h-twisted sector a
line with h-eigenvalue e^{2πir} has modes in r + Z_{≥0}, excluding 0. With
the free-boson vacuum energy,

    T_{g,h}(τ) = ∏_{lines (s,r)} q^{−B_2(r)/4} ∏_{n≥0, n+r>0} (1 − e^{2πis} q^{n+r})^{−1}.

At h = 1 this is q^{−dim/24} times the T_g of [MS]. The multiplicities come
from the character of Lie(P) on ⟨g, h⟩, computed with the closed formula
of [PL]: m(s, r) = (1/(o_g o_h)) Σ_{a,b} χ(g^a h^b) e^{−2πi(as+br)}.

**Structure (PROVEN, given CITED transformation laws).**
- V is defined over Q, so the lines are closed under (s, r) ↦ (−s, −r).
- The untwisted lines (0, 0) give η^{−d_0}, with d_0 = dim V^{⟨g,h⟩}.
- A self-conjugate line with 2s, 2r ∈ Z gives an eta quotient: η(τ)/η(2τ),
  η(τ)/η(τ/2) or η(τ/2)η(2τ)/η(τ)², up to q-powers.
- A conjugate pair (s, r), (−s, −r) with 0 < r < 1 equals
  −e^{πis(r−1)}/g_{(r,s)}, where g_a is the Siegel function of Kubert–Lang
  (COMPUTED to 1e-10). Pairs with r = 0, s ≠ 0 are the same with a = (0, s).
- The Siegel functions satisfy g_a ∘ γ = ε(γ) g_{aγ}, with ε a 12th root of
  unity (CITED: Kubert–Lang, *Modular Units*, Ch. 2).
- Hence T_{g,h}(−1/τ) = c (−iτ)^{−d_0/2} T_{h^{−1},g}(τ) and
  T_{g,h}(τ+1) = c′ T_{gh,h}(τ).
- So T_{g,h} is modular of weight −d_0/2 on Γ(lcm(o_g, o_h)), with a
  multiplier of finite order. This is the generalized-moonshine pattern for
  a free boson, and it depends on the joint character alone.

**COMPUTED** (numerical evaluation at three points τ):
- the S-law with partner (h^{−1}, g);
- the T-law with partner (gh, h);
- the law for γ = (1+N  N; −N  1−N) ∈ Γ(N): ratio constant to 1e-6, of
  modulus 1.

These were checked for:

| Pair | dim | joint lines (s, r): mult | weight |
|---|---|---|---|
| Lie_4, (12)(34), (13)(24) | 6 | (0,½):2, (½,0):2, (½,½):2 | 0 |
| Lie_4, (1234), (13)(24) | 6 | (0,0):1, (¼,½):2, (½,0):1, (¾,½):2 | −1/2 |
| Lie_5, (12345), (12345)² | 24 | (0,0):4, (j/5, 2j/5):5 for j = 1..4 | −2 |
| Lie_6, (123)(456), (14)(25)(36) | 120 | (0,0):18, (0,½):20, (⅓,0):19, (⅓,½):22, (⅔,·) likewise | −9 |
| Lie_6, (12)(34)(56), (135)(246) | 120 | the S-image of the previous row | −9 |
| 2+2, swap, swap | 5 | (0,0):2, (½,½):3 | −1 |
| bowtie, (12), (34) | 4 | each character of Z_2² once (free action) | −1/2 |

Negative controls:
- the partner (h, g) in place of (h^{−1}, g) fails the S-law for Lie_5;
- a single line (1/3, 1/4) without its conjugate fails the S-law.

**Correction to [MS].** "Eta products in τ/o(h)" is wrong in general. For
Lie_5 at (g, g²), the only line with r = 1/5 is (3/5, 1/5), with multiplicity
5. So the coefficient of q^{1/5} in q^{−E_0}T_{g,g²} is 5e^{6πi/5}, which is
not real, and an eta quotient has integer coefficients. These are Siegel
products, as [AUD] said.

**Verdict: generic.** Only the joint character of (g, h) on Lie(P) enters,
and any rational representation of any finite group gives the same
modularity. Nothing poset-specific appears, matching [MS] candidate 4.

## Reproduce

Run in `compute/`. Plain Python 3, exact arithmetic except where noted in
the docstring. Imports `poset_jks_check.py` (enumeration of unlabeled
posets) and `poset_lie_structure.py` (closed formula for χ_{Lie(P)}).

    python3 moonshine_residual.py > output/moonshine_residual.txt   # ~35 s, exit 0 iff all 42 checks pass
    python3 moonshine_residual.py --U   # item 6(d): natural classes, Lemma P/L inputs (17)
    python3 moonshine_residual.py --E   # item 6(d): 1/E_6(20 tau) is realizable (5)
    python3 moonshine_residual.py --S   # item 7: shifted quadrant (3)
    python3 moonshine_residual.py --B   # item 7: infinite binary tree (4)
    python3 moonshine_residual.py --G   # item 7: the Gamma_0(2) example (3)
    python3 moonshine_residual.py --T   # item 1: twisted traces (10)
    python3 -m unittest test_moonshine_residual

## References

- [MS] `notes/moonshine_scoping.md`; [AUD] `notes/audit_moonshine_scoping.md`;
  [PL] `notes/global_module_operations_plethlog.md`.
- J. H. Bruinier, W. Kohnen, K. Ono, The arithmetic of the values of
  modular functions and the divisors of modular forms, Compositio Math. 140
  (2004).
- E. R. Gansner, The Hillman–Grassl correspondence and the enumeration of
  reverse plane partitions, J. Combin. Theory A 30 (1981).
- D. Kubert, S. Lang, *Modular Units*, Springer 1981, Ch. 2.
- R. Otter, The number of trees, Ann. of Math. 49 (1948).
- B. E. Sagan, Enumeration of partitions with hooklengths, European J.
  Combin. 3 (1982).
- J. Valdes, R. E. Tarjan, E. L. Lawler, The recognition of series parallel
  digraphs, SIAM J. Comput. 11 (1982).
- D. Zagier, Ramanujan's mock theta functions and their applications,
  Séminaire Bourbaki 986 (2007).
