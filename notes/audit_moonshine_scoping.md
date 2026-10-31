# Audit of moonshine_scoping.md

**Verdict: STOP HOLDS ON A NARROWER SPACE.** The space is exact modularity
of graded traces built from three kinds of object:
- the free poset Hopf monoid 𝐐 (or Q′), every sub-Hopf monoid of it, and its
  bigrading by number of relations;
- finite or finitely generated graded objects attached to a single P, and
  the plain and twisted Fock spaces of Lie(P);
- P-partitions of k·N, chain_m × N and N × N.

Here "exact modularity" means a transformation law F(γτ) = v(γ)(cτ+d)^k F(τ)
on some finite-index Γ ≤ SL_2(Z), with k real and v(γ) ≠ 0, and with no
condition at the cusps.

Three things are outside that space and are still open:
- mock modularity of the rational P-partition series;
- type (unlabeled) series of component-closed classes of the poset monoid 𝐏
  whose connected counts grow exponentially;
- infinite posets other than the three tested, beyond weak holomorphy.

The note's closing claim, that "each natural grading" falls into one of its
three cases, has not been established outside that space.

This audit was written from the note alone. It imports nothing from
`compute/moonshine_scoping.py` or `compute/moonshine_lookup.py`, and no other
review of the note was read first. Tags are as in the note: **PROVEN**
(argument given here), **COMPUTED** (by `compute/audit_moonshine_scoping.py`,
which is self-contained), **CITED**.

Inside the space, every PROVEN argument of the note survives
re-derivation. Two of them get stronger here:
- **N × N.** The note's "PROVEN modulo CITED growth bounds" becomes PROVEN
  with no growth citation (Lemma D below). It also becomes a statement about
  every transformation law, not just weakly holomorphic forms. On the way, the
  Meinardus citation turns out to be misapplied: its hypothesis fails.
- **The Witt layer.** The growth obstruction extends to every sub-Hopf monoid
  of 𝐐 and Q′ other than the antichains, and to every linear specialization of
  the (size, relations) bigrading (Lemma H below). That closes, for sub-Hopf
  monoids, the escape route the note left open in §4.

## 1. Per-claim table

| Claim (note §) | Note's tag | Audit | Notes |
|---|---|---|---|
| Witt layer: A(q) = Σ a_n q^n = ∏(1−q^n)^{−c_n}; b_n, c_n, c_n^−, the d^m traces (§3.1) | COMPUTED | **HOLDS** | Re-derived from the plethystic logarithm. a_n is recomputed by my own recursion for n ≤ 8 (= A006455), and b_n, c_n, c_n^−, the 2^m traces and dim V_n agree with the note for n ≤ 8. |
| c_n = c_n^− unless n ≡ 2 (mod 4) (§3.1) | PROVEN | **HOLDS** | c_n − c_n^− = Σ_{d\|n} μ(d) b_m/(dm) · (1 − (−1)^{(d−1)m}), with m = n/d. This is nonzero only if d = 2·odd and m is odd. Example: c_6 − c_6^− = (1/3)(μ(2)b_3 + μ(6)b_1) = −5. |
| Growth obstruction (§3.1) | PROVEN | **HOLDS, stronger than stated; two wording fixes** | See §2.1. Radius 0 rules out every function holomorphic on H, and every function meromorphic near the cusp. That includes meromorphic modular forms and Borcherds products, not only weakly holomorphic ones. *Fix 1:* the table's "growth ≥ 2^{n²/4}" is proved for a_n only. For c_n the argument gives only "faster than any exponential" (c_n/a_n = 0.96 at n = 8). *Fix 2:* for non-squarefree d the d^m trace series is identically 0, not of size d^{m−1} dim V_m. |
| Quotient formula, prefix sums S_j (§3.2) | PROVEN; COMPUTED (14 pairs) | **HOLDS** | Re-derived (§2.2). Brute force agrees on 9 (P, g) pairs of my own, 5 of which the note did not test: the odd 4-cycle on the 4-antichain, the claw with a 3-cycle, the 6-crown with rotation, 2+2+2 with a 3-cycle, and the bowtie with a single swap. A suffix-sum variant fails (negative control). |
| Leading pole Σ_w ∏ 1/S_j(w); e(P)/n! at g = 1 (§3.2) | PROVEN | **HOLDS** | Immediate from the formula; COMPUTED on 2+2. |
| Lemma R (§3.2) | PROVEN | **HOLDS** | Each of the five steps is re-derived (§2.3). It needs no condition at the cusps, so it excludes every exact transformation law. It does **not** address mock modularity. Quantum modularity is excluded by Lemma Q (§2.3). |
| chain_m × N: ∏(1−q^n)^{−min(n,m)}, NO for m ≥ 2 (§3.3) | PROVEN via Lemma R | **HOLDS** | Brute force agrees for m = 1, 2, 3 through q^12. The product with (q;q)^m is a nonconstant polynomial for m ≥ 2 and constant for m = 1 (positive control). |
| N × N and its transpose: NO SIGN, modulo Wright and Meinardus (§3.3) | PROVEN mod CITED | **HOLDS WITH FIXES** | (i) "A modular one would be weakly holomorphic" does not follow from "holomorphic and nonvanishing on H". For example, exp((η(2τ)/η(τ))^{24}) is Γ_0(2)-invariant and holomorphic on H, but has an essential singularity at the cusp 0. So the cited argument excludes only weakly holomorphic forms. (ii) Wright 1931 is correctly cited for MacMahon's function. (iii) **Meinardus does not apply as stated** to the symmetric case. Its hypothesis is that D(s) = Σ a(n) n^{−s} has a single simple pole in Re s ≥ −C_0. Here D(s) = 2^{−s−1}ζ(s−1) + (1−2^{−s})(1−2^{−s−1})ζ(s), which has a second pole at s = 1 with residue 3/8 (COMPUTED numerically: 0.375). The conclusion log a_n ≫ n^{2/3} still holds, since a_sym(N) ≥ pp(⌊N/4⌋) coefficientwise (proof in §2.4; COMPUTED for N ≤ 80). (iv) Lemma D (§2.4) makes both citations unnecessary and proves NO for every transformation law. |
| Weakly holomorphic ⇒ log\|a_n\| = O(√n) (§3.3) | CITED | **HOLDS** | Standard: \|F(x+iy)\| ≪ y^{−c} e^{B/y}, and a_n = ∫ F e^{−2πin(x+iy)} dx with y ≍ n^{−1/2}. |
| Frame-shape rule: T_g = q^{dim/24}/η_g for every rational representation (§3.4) | PROVEN | **HOLDS** | Re-derived (§2.5). COMPUTED for Lie_4 … Lie_7 at every class, through q^30. The inversion refuses a class function that is not a rational character (negative control in the tests). |
| The six sample Frame shapes and the Wilson formula (§3.4) | COMPUTED | **HOLDS** | Recomputed from the classical character of Lie_n. |
| Sign twist t^r ↦ (2t)^r t^{−r} for odd t (§3.4) | PROVEN; COMPUTED | **HOLDS** | Eigenvalues of −g on a t-cycle block: the roots of x^t + 1 when t is odd, and the same set when t is even. COMPUTED on every odd class of S_4 … S_7. |
| k·N: MODULAR, generic (§3.3) | COMPUTED | **HOLDS, and the genericity is argued** | T_g depends only on the cycle type of g on k letters. It is the Fock trace of the permutation representation. |
| Lie_5: seven multiplicative η_g, "shared with Reg(S_4)" (§3.4) | COMPUTED; PROVEN given LMFDB | **HOLDS, and the sharing is a theorem** | Lie_n restricted to S_{n−1} *is* the regular representation (§2.6; COMPUTED for n ≤ 9). So the "control" is a restriction of Lie_5 itself. The data outside S_4 is 6^4 on (123)(45), which is a free action and so generic, and 1^{−1}5^5 on the 5-cycle. Lie_5 is Lie(antichain), the classical free Lie module, so none of this involves posets. |
| η(5τ)^5/η(τ) = Σ_n Σ_{d\|n} (n/d \| 5) d q^n (§3.4) | PROVEN given membership | **HOLDS** | COMPUTED through q^200, with a negative control (Σ (d\|5) d fails). |
| "What A_n buys: nothing" (§3.4) | PROVEN | **HOLDS, stronger** | See §2.6. For any S_n-equivariant construction, split A_n-classes give identical series. The only A_n-specific series come from irrational isotypic pieces, and those are again generic (Siegel functions). |
| T_{g,h} "again eta products" (§3.4) | not computed | **imprecise; covered only by citation** | With root-of-unity twists these are generalized eta (Siegel-type) products, not eta products. See §3, item 1. |
| LOOKUP claims (OEIS / LMFDB) | LOOKUP | **not re-checked** | This audit did no network lookups. The LMFDB identities are re-proved here only for η(5τ)^5/η(τ), by series comparison against the note's Sturm bound. |

No error was found that reverses a verdict.

## 2. Re-derivations

### 2.1 The growth obstruction, and how far it reaches

- **Lower bound for a_n (PROVEN; COMPUTED n ≤ 8).** Split [n] at k = ⌊n/2⌋.
  Every relation set made of pairs i < j with i ≤ k < j is transitive
  (there are no 3-chains) and naturally labeled. So
  a_n ≥ 2^{⌊n/2⌋⌈n/2⌉}.
- **From a_n to c_n.** The coefficients c_n are ≥ 0, being dimensions of
  invariants. If c_n ≤ e^{Cn}, the product ∏(1−q^n)^{−c_n} would converge on
  |q| < e^{−C} and represent A there, contradicting radius 0. The note's
  argument is correct.
- **What it excludes.** A power series with radius 0 has no disk of
  convergence. It is therefore not the q-expansion of any function that is
  holomorphic, or meromorphic, on a neighborhood {Im τ > Y} of the cusp.
  This excludes holomorphic, weakly holomorphic and meromorphic modular
  forms, Borcherds products (whose expansions converge for Im τ large), and
  the holomorphic parts of mock modular forms. So for candidate 1 the
  obstruction is stronger than the note says.

**Lemma H (PROVEN; COMPUTED n ≤ 8).** The obstruction persists in the
following cases:
- (a) **Q′, component-closed classes.** Let 𝒞 be a class of connected
  posets, and let Q′_𝒞 ⊆ Q′ be spanned by the (P, ℓ) whose components all
  lie in 𝒞. This is a sub-Hopf monoid: it is closed under disjoint union,
  and under restriction to unions of components. If 𝒞 contains some R with
  m = |R| ≥ 2, then the number of naturally labeled posets ≅ kR on [km] is
  at least (km)!/(k!(m!)^k). That bound is the number of set partitions of
  [km] into blocks of size m: each block carries at least one natural
  labeling of R, and the blocks are recovered as components. The bound is
  superexponential in n = km. So A_𝒞 has radius 0. By CMM–PBW (CITED as in
  the note), A_𝒞 = ∏(1−q^n)^{−c_n^𝒞} with c_n^𝒞 ≥ 0, so the exponents are
  superexponential too. If 𝒞 = {point}, one gets the classical Lie species
  with A = 1/(1−q), which is rational, and Lemma R applies.
- (b) **𝐐, hereditary classes.** A sub-Hopf monoid of 𝐐 given by a class of
  posets has to be closed under + and under every restriction. If the class
  is not just the antichains, it contains the 2-chain, hence every disjoint
  union of 2-chains and points. Naturally labeled, these are counted by the
  involution numbers 1, 1, 2, 4, 10, 26, 76, 232, 764, … (COMPUTED by
  filtering my enumeration), which grow like (n/e)^{n/2}. In particular the
  height filtration (height ≤ h is hereditary and +-closed) has radius 0 at
  every level h ≥ 2. Height ≤ 2 already reaches 2^{n²/4} (COMPUTED).
- (c) **The relation bigrading (Theorem 8 of general_theory.md).** Q′ is
  bigraded by (n, r(P)), and its coproduct preserves both degrees. So
  A(x, y) = ∏(1 − x^n y^r)^{−c_{n,r}} with c_{n,r} ≥ 0. Specialize
  x = q^α, y = q^β with α > 0 and β ≥ 0. The bipartite posets with exactly
  n relations number C(⌊n/2⌋⌈n/2⌉, n) ≥ (n/4)^n, all of weight (α+β)n. So
  every such specialization diverges for every τ ∈ H. COMPUTED:
  a_{n,r} ≥ C(⌊n/2⌋⌈n/2⌉, r) for all n ≤ 8 and all r.

So the note's §4 escape clause ("a sub-family … whose counts grow like
e^{C√n}") cannot be met by any sub-Hopf monoid of 𝐐 or Q′. Because S_n acts
freely, invariants count *naturally labeled* objects, and those are already
superexponential for the smallest nonclassical class. The clause can still
be met outside the free monoid; see §3, item 6.

### 2.2 The quotient formula

- **Order-reversing maps on the quotient.** Since g has finite order, the
  orbit preorder on Q = P/⟨g⟩ is antisymmetric. If x ≤ g^b x, then
  x ≤ g^b x ≤ g^{2b} x ≤ … ≤ x, so equality holds throughout. A map σ that
  is constant on orbits is order-reversing on P if and only if σ̄ is
  order-reversing on Q, and its weight is Σ_O |O| σ̄(O).
- **Unique linear extension.** Label Q naturally. Sort σ̄ decreasingly, with
  ties in increasing label. This gives the unique w ∈ Lin(Q) with
  σ̄(w_1) ≥ … ≥ σ̄(w_m), strict at the descents of w. The sorted order is a
  linear extension: if O < O′, then either σ̄(O) > σ̄(O′), or the values are
  equal and the label of O is smaller.
- **Summing.** Put δ_j = σ̄(w_j) − σ̄(w_{j+1}) ≥ [j ∈ Des w]. Then
  Σ_i |w_i| σ̄(w_i) = Σ_j δ_j S_j(w), with prefix sums S_j. This is the
  note's formula.

### 2.3 Lemma R, and quantum modularity

The five steps are correct as written:
- the limit set is all of R ∪ {∞}, since the group is of the first kind;
- if γ_jτ_0 → x, then |c_jτ_0 + d_j| → ∞;
- there are finitely many poles on the circle;
- the cases k > 0 and k < 0 give F ≡ 0, and k = 0 gives |F| constant, hence
  F constant.

The reduction from q^a R to R, by taking a power, is correct. The lemma uses
no condition at the cusps, so it excludes every exact transformation law on a
finite-index subgroup.

**Lemma Q (PROVEN).** Let R be rational with at least one pole ζ_0 on the
unit circle. Then f(x) = R(e^{2πix}) is not a quantum modular form, in
Zagier's sense that h_γ(x) = f(x) − (cx+d)^{−k} f(γx) extends real-analytically
to R minus finitely many points.

*Proof.*
- Write ζ_0 = e^{2πiθ}. Since the T_g have poles only at roots of unity,
  take θ rational.
- Take γ ∈ Γ with c ≠ 0. The points x_t = γ^{−1}(θ + t), t ∈ Z, accumulate
  at γ^{−1}∞ = −d/c.
- (cx+d)^{−k} f(γx) has a pole at each x_t.
- f has poles only on the finitely many cosets θ_i + Z, so it is finite at
  x_t for all but finitely many t.
- Hence h_γ has infinitely many poles. ∎

Every T_g has a pole at q = 1, because the constant maps are P-partitions.
So no candidate-2 series is quantum modular either.

**Not addressed by the note or by this audit: mock modularity.** A mock
modular form satisfies the law only up to a period integral, so Lemma R
does not apply. It is very plausible that a rational q-series with nonzero
shadow does not exist, but no proof or reference was found.

### 2.4 Lemma D: the N × N case without growth citations

**Lemma D (PROVEN).** Let F = q^a ∏_{n≥1}(1−q^n)^{−c(n)}, with c(n) real and
|c(n)| ≤ C n^K. Then F is holomorphic and nonvanishing on H. Suppose
F(γτ) = v(γ)(cτ+d)^k F(τ) for all γ in a finite-index Γ ≤ SL_2(Z), with k
real and v(γ) ≠ 0, and with no condition at the cusps. Then the log-derivative

    G := (1/2πi) F′/F = a + Σ_N (Σ_{n|N} n c(n)) q^N

satisfies G(iy) = O(y^{−2}) as y → 0⁺.

*Proof.*
1. **G is quasimodular.** Differentiate the law. This gives
   G(γτ) = (cτ+d)² G(τ) + (k/2πi) c(cτ+d). The multiplier drops out,
   because v(γ) is a nonzero constant.
2. **Subtract E_2.** E_2 satisfies the same law with k = 12. So
   H := G − (k/12)E_2 is invariant of weight 2 under Γ, and holomorphic on H.
3. **H is holomorphic at every cusp.** The coefficients of G and of E_2 are
   polynomially bounded, so |H(x+iy)| ≪ 1 + y^{−K−2} uniformly in x. For
   γ ∈ SL_2(Z) we have Im γτ = y/|cτ+d|², so (H|_2γ)(τ) grows at most
   polynomially as Im τ → ∞. A term with a negative power of the local
   parameter would grow exponentially. So H|_2γ has none, and H ∈ M_2(Γ).
4. **Bound for M_2(Γ).** A form in M_2(Γ) satisfies |H(τ)| ≪ y^{−2}. To see
   this, move τ into the standard fundamental domain by some δ ∈ SL_2(Z).
   Then H|δ^{−1} is bounded there, since there are finitely many cosets and
   each is holomorphic at ∞. Also Im δτ ≤ 1/y.
5. **Conclusion.** E_2(iy) = O(y^{−2}) as well, by its quasimodular law at S.
   So G(iy) = H(iy) + (k/12)E_2(iy) = O(y^{−2}). ∎

**Corollary (PROVEN).** No q^a·(MacMahon) and no q^a·(symmetric plane
partitions) satisfies any transformation law of the kind above.

*Proof.* In both cases c(n) ≥ 0, so Σ_{n|N} n c(n) ≥ N c(N).
- MacMahon: G(iy) ≥ Σ_N N² e^{−2πNy} ≍ y^{−3}.
- Symmetric: c(4j) = j, so G(iy) ≥ Σ_j 4j² e^{−8πjy} ≍ y^{−3}.

Both contradict Lemma D. ∎

COMPUTED as an illustration:
- MacMahon: y³G(iy) → 2ζ(3)/(2π)³ = 0.009692 at y = 0.01 and 0.003.
- Symmetric: y³G(iy) → ζ(3)/(4(2π)³) = 0.001212 at y = 0.001 and 0.0003.
- y³E_2(iy) → 0.
- Positive control 1/(q;q)_∞, which is modular: y²G stays bounded (→ 1/24).
- chain_3 × N has bounded c(n), so Lemma D says nothing there, and Lemma R
  is needed. That is the note's route.

This proof needs neither Wright nor Meinardus. As noted in §1, Meinardus'
hypothesis fails for the symmetric case. An elementary replacement for the
growth statement is the coefficientwise bound
∏_k (1−q^{2k})^{−⌊k/2⌋} ≥ ∏_j (1−q^{4j})^{−j} = M(q^4), taken from the
factors with k = 2j, together with the fact that 1/(q;q²)_∞ has every
coefficient ≥ 1. Together these give a_sym(N) ≥ pp(⌊N/4⌋).

**Same reach for infinite posets not in the note.** A P-partition of N^k
with k ≥ 3 that is supported on N² × {0} is a plane partition. So the
counts for N^k dominate pp(n), and log a_n ≫ n^{2/3}: weak holomorphy is
excluded. These series are not products, so Lemma D does not apply, and the
broad sense stays open.

### 2.5 The Frame-shape rule

A rational representation of ⟨g⟩ is a sum of the rational irreducibles, with
characteristic polynomials Φ_d (d | o). So
det(x − g) = ∏_d Φ_d^{m_d} = ∏_t (x^t − 1)^{r_t}, with integers r_t. Taking
traces of powers gives χ(g^e) = Σ_{t|e} t r_t, and Möbius inversion gives the
note's formula. Then det(1 − gq^n) = ∏_t (1 − q^{nt})^{r_t}, and
T_g = ∏_t (q^t; q^t)_∞^{−r_t} = q^{dim/24} ∏_t η(tτ)^{−r_t}, since
Σ t r_t = dim. Each η(tτ) is modular on Γ_0(t) with a multiplier. So T_g is
weakly holomorphic of weight −Σr_t/2 on Γ_0(N) with a multiplier system.
Correct.

### 2.6 Genericity, argued rather than asserted

- **k·N.** The fixed P-partitions are k-tuples of partitions constant on
  cycles. So T_g = ∏_{cycles λ} (q^λ; q^λ)^{−1}, the Fock trace of the
  permutation representation C^k. Nothing about posets enters beyond
  "copies of N".
- **Lie_5 and Reg(S_4) (PROVEN).** The character of Lie_n is
  μ(d) d^{m−1}(m−1)! on cycle type d^m, and 0 off those types (CITED,
  classical: Reutenauer, *Free Lie algebras*, Ch. 8; it is the antichain case
  of [PL]). Every element of S_{n−1} has a fixed point, so its cycle type is
  d^m only if it is the identity. Hence χ_{Lie_n}|_{S_{n−1}} = (n−1)! δ_e,
  and **Lie_n restricted to S_{n−1} is the regular representation of
  S_{n−1}** (COMPUTED n ≤ 9). The note's control, Reg(S_4), is therefore not
  an independent object that happens to agree with Lie_5. It *is* Lie_5,
  restricted. On S_5, the classes outside S_4 are:
  - (123)(45), which acts freely and gives 6^4, as any free action does;
  - the 5-cycle, which gives 1^{−1}5^5 from χ = μ(5) = −1 and nothing else.

  Lie_5 = Lie(antichain) is the classical free-Lie module. The near-miss
  owes nothing to posets.
- **A_n-specific series (PROVEN; COMPUTED).** The question to settle is
  whether some A_n-specific trace series differs from what S_n, or the
  regular representation, already gives.
  - Every module in the note (Lie(P), H_P, V_n, the P-partition spaces) is
    an Aut(P)- or S_n-module with a *rational* character. Its restriction to
    A_n takes the same value on the two halves of a split class. So no
    construction in the note can tell split classes apart. Restricting to
    A_n only deletes classes, and the series on the remaining classes are
    the S_n series.
  - A_n-specific series exist only on pieces with irrational characters.
    Example: Lie_5|_{A_5} = 3 + 3′ + 2·4 + 2·5 (COMPUTED from the A_5
    character table).
  - On the Fock space of the 3-isotypic piece, the class 5a has eigenvalues
    {1, ζ_5, ζ_5^{−1}}, and the trace series begins 1 + φq + 2.618q² + ….
  - The class 5b has eigenvalues {1, ζ_5², ζ_5^{−2}}, and its series begins
    1 + (1−φ)q + 0.382q² + ….
  - These are A_5-specific, and they differ from each other and from every
    rational Frame shape. They are products ∏_n (1 − λq^n)^{−1} over an
    inversion-closed set of roots of unity, i.e. Siegel-function
    (generalized eta) products, which are modular on Γ(N) up to a multiplier
    of finite order (CITED: Kubert–Lang, *Modular Units*, Ch. 2; not
    re-read).
  - So they are modular for the same generic reason. The only input is the
    A_5 character table, not posets.

## 3. Natural gradings the note did not try

| # | Candidate | Covered by the note? | Status after this audit |
|---|---|---|---|
| 1 | Twisted traces T_{g,h} on the h-twisted sector of Sym(Lie(P) ⊗ tC[t]) | No (not computed) | **Covered by a generic mechanism, by citation only.** Joint eigenvalues (λ, e^{2πij/o}) give ∏_n (1 − λq^{n+j/o})^{−1}, a generalized Dedekind eta (Siegel-type) product, modular on Γ(N) with a multiplier (CITED: Kubert–Lang; Y. Yang, Bull. LMS 36 (2004); not re-read). The note says "eta products in τ/o(h)". With root-of-unity twists that is imprecise. Only the joint character of (g, h) enters, so the mechanism is generic. Not computed here. |
| 2 | A_n-isotypic pieces with irrational characters | No | **Covered here** (§2.6): A_n-specific, Siegel-type, generic. |
| 3 | Bigrading by number of relations r(P) (Theorem 8 filtration) | No | **Covered here** (Lemma H(c)): radius 0 for every specialization x = q^α, y = q^β with α > 0, β ≥ 0. |
| 4 | Height / width filtrations, and every sub-Hopf monoid of 𝐐 or Q′ | Only implicitly (§4 escape clause) | **Covered here** (Lemma H(a), (b)). The only exception is the antichain monoid: there A = 1/(1−q) is rational, so Lemma R applies. |
| 5 | Finite graded objects attached to one P: C[Lin P] graded by maj, gradings of Lie(P) of Kraśkiewicz–Weyman type, bounded P-partitions, order-polynomial series Σ_m Ω(P, m) q^m, Molien series of Sym(Lie(P)) | No | **Covered by Lemma R.** These are polynomials, or rational functions with poles only at roots of unity. |
| 6 | Type (unlabeled) series of the poset Hopf monoid 𝐏 and of its component-closed classes. 𝐏 is not free, so its invariants count *unlabeled* posets | No | **Partly covered.** (a) All of 𝐏: unlabeled count ≥ 2^{n²/4}/n!, so radius 0. (b) Disjoint unions of chains: 1/(q;q)_∞ = q^{1/24}/η, modular and generic, the same as k·N. (c) Classes with polynomially bounded connected counts u_n: Lemma D says the product is modular only if Σ_{n\|N} n u_n are the coefficients of (k/12)E_2 + M_2(Γ). For Γ_0(N) with N squarefree, Kohnen's theorem makes such a product an eta quotient (CITED: W. Kohnen, Proc. AMS 133 (2005) 65–70; hypotheses not re-checked). (d) Classes whose connected counts grow exponentially, for example forests, counted by rooted trees: the product has positive radius < 1. Radius-0 arguments therefore say nothing, and meromorphic modularity (Borcherds-type) is not excluded by anything in the note or here. For forests specifically, the square-root singularity of Otter's rooted-tree series rules out meromorphy (CITED, not re-checked). The general case is **OPEN**. This is where the note's §4 escape clause can still be met. |
| 7 | Other infinite posets: N^k (k ≥ 3), shifted shapes, infinite trees | No | **Partly covered.** Weak holomorphy is excluded for N^k (§2.4). The broad sense, and the other families, are **OPEN**. |
| 8 | Mock / quantum modularity of the candidate-2 series | No | **Quantum: excluded** (Lemma Q). **Mock: OPEN.** |
| 9 | Cone counts of other arrangements (type B, framework (a) of general_theory.md) | No | **Covered.** Any intersection of half-spaces of A_{n−1} ⊂ B_n is a cone of B_n, so #cones(B_n) ≥ #posets on [n] ≥ 2^{n²/4}. Dividing by \|W\| = 2^n n! leaves this superexponential, so radius 0. |
| 10 | Characters of Q′ into QSym (Aguiar–Bergeron–Sottile) and their principal specializations | No | **Covered by Lemma R.** Principal specializations of P-partition quasisymmetric functions are the rational series of candidate 2. |

## 4. Conclusion

The four PROVEN arguments are correct, with one gap: the N × N step
"modular ⇒ weakly holomorphic". Lemma D closes that gap and removes the
growth citations. The "generic" verdicts are argued, not just asserted, and
§2.6 strengthens them: in any S_n-equivariant construction, A_n cannot
separate its split classes. The Lie_5/Reg(S_4) agreement is the identity
Lie_n|_{S_{n−1}} ≅ C[S_{n−1}].

The candidate space was too small for "every natural grading" as the note
states it. Most of the missing gradings (items 2–5, 9, 10) are covered by
arguments given here. Item 1 is covered only by citation. Items 6(d), 7 and
8 are open. Item 6(d) is the substantive one: it is exactly where the note's
own §4 escape clause can be met, outside the free Hopf monoid.

**Recommendation.** Keep STOP for the poset Lie theory proper, meaning 𝐐,
Q′, Lie(P), H_P, their Fock spaces and their sub-Hopf monoids. That space is
closed by proofs, not by observation. If the direction is reopened, start
with item 6(d): unlabeled component-closed classes of 𝐏 with exponentially
growing connected counts, tested for meromorphic (Borcherds-type)
modularity. Item 8 (mock) comes second.

## Reproduce

Run in `compute/`. Plain Python 3; self-contained (no imports from other
scripts in `compute/`).

    python3 audit_moonshine_scoping.py > output/audit_moonshine_scoping.txt   # ~25 s, exit 0 iff all 59 checks pass
    python3 audit_moonshine_scoping.py --W    # Witt layer, n <= 8 (10)
    python3 audit_moonshine_scoping.py --H    # sub-Hopf monoids, bigrading (4)
    python3 audit_moonshine_scoping.py --P    # quotient formula, 9 pairs + controls (11)
    python3 audit_moonshine_scoping.py --I    # chain_m x N, N x N, symmetric, Meinardus pole (10)
    python3 audit_moonshine_scoping.py --D    # Lemma D asymptotics + controls (9)
    python3 audit_moonshine_scoping.py --F    # Frame shapes, twist, Lie_n|S_{n-1}, eta(5t)^5/eta(t) (11)
    python3 audit_moonshine_scoping.py --A    # A_5 split classes (4)
    python3 -m unittest test_audit_moonshine_scoping

The archived output is `compute/output/audit_moonshine_scoping.txt`.

## References

- W. Kohnen, On a certain class of modular functions, Proc. AMS 133 (2005)
  65–70.
- D. Kubert, S. Lang, *Modular Units*, Springer 1981, Ch. 2.
- G. Meinardus, Asymptotische Aussagen über Partitionen, Math. Z. 59
  (1954). Hypotheses as restated in G. E. Andrews, *The Theory of
  Partitions*, Thm 6.2.
- C. Reutenauer, *Free Lie Algebras*, Oxford 1993, Ch. 8.
- E. M. Wright, Asymptotic partition formulae I: plane partitions, Quart.
  J. Math. 2 (1931).
- Y. Yang, Transformation formulas for generalized Dedekind eta functions,
  Bull. London Math. Soc. 36 (2004).
- D. Zagier, Quantum modular forms, Clay Math. Proc. 11 (2010).
