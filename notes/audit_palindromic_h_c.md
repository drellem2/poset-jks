# Audit of `palindromic_h_c.md`: the classification S′

This is an independent, adversarial audit of `notes/palindromic_h_c.md`
(below [PH]). [PH] claims that for a finite poset P on n ≥ 2 points, h_C(P)
is palindromic iff P is connected and graded, or every component of P has
height ≤ 2. Every proof in [PH] was re-derived line by line. Every claim was
recomputed with new code, `compute/audit_palindromic_h_c.py`, which imports
nothing from the repository. In that code h_C comes straight from the Möbius
definition of Ω_C, and every other quantity is a literal count.

Sources: [R] = `notes/reciprocity_omega_c.md` (Theorem Ω, Theorem R,
Lemma R2, Prop. B⁺, Prop. S, all PROVEN + audited in
`notes/audit_reciprocity_omega_c.md`; they are not re-audited here, only
checked to be used within their hypotheses); [PAR] =
`notes/prior_art_reciprocity_omega_c.md`; EC1 = Stanley, *Enumerative
Combinatorics* vol. 1, 2nd ed.

## Verdict

| Claim | Verdict | Basis |
|---|---|---|
| P0 | **HOLDS** | Proof re-derived (§1). COMPUTED 2443 / 2443 posets with L ≥ 2, n ≤ 7, 0 bad |
| E0 | **HOLDS** | Proof re-derived (§2). COMPUTED on the Möbius h_C, 2449 posets n ≤ 7, and by a literal count of anchored maps into [1] and [2], 19 448 posets n ≤ 8; 0 bad |
| E1 | **HOLDS** | Proof re-derived (§3). COMPUTED: d = n − L and the formula for h_d on the Möbius h_C, 2443 posets n ≤ 7; parts (a), (b), (c) by a literal count of strict maps with D_T, 19 441 posets n ≤ 8; 0 bad |
| E2 | **HOLDS** | Proof re-derived (§4). COMPUTED: "every strict map into [L+1] satisfies D_T" literally on 16 044 posets n ≤ 8, and the identity on the Möbius h_C on 1820 posets n ≤ 7; 0 bad. It fails off its hypotheses, as stated in [PH] |
| I | **HOLDS** | Proof re-derived (§5), for every finite K, connected or not. COMPUTED on all 19 448 posets n ≤ 8; the injection itself checked map by map, 404 posets n ≤ 6; 0 bad |
| G | **HOLDS** | Proof re-derived (§6). Mixed component heights are covered by the case h_d ≥ 2, and E2 is never applied to them. COMPUTED: 2637 / 2637 disconnected posets with a 3-chain, n ≤ 8, by literal end coefficients; 379 / 379 on the Möbius h_C, n ≤ 7; 0 bad |
| S′ (§5 assembly) | **HOLDS** | All three branches checked (§7). Imported facts are used within their hypotheses. The connected case is a citation, and the transfer of the citation to h_C is valid via P0 with r = 1. COMPUTED on all 2449 posets 2 ≤ n ≤ 7 from the Möbius h_C, 0 bad; at n = 8 the disconnected "only if" is COMPUTED through G |

No claim FAILS and nothing needs fixing. There are two cosmetic remarks,
neither of which affects any proof:
- [PH] §6 reports `[next]` on 16 038 posets, and this audit counts 16 044
  posets with L ≥ 3 and all L_K = L. The difference is the six chains
  C_3, …, C_8. They have d = 0, so h_{d−1} is not an entry, and [PH]
  evidently left them out. E2 holds for them with h_{−1} = 0.
- The sentence after P0 ("the shift is forced: s = L − 1") is informal.
  It is true in the sense that a shift s with Ω̄_C(P, m) = Ω_C(P, m − s) is
  unique if it exists: both sides have degree n and the same leading
  coefficient, so the coefficient of m^{n−1} fixes s. P0 itself does not
  need this.

## 1. P0

*Claim.* Let n ≥ 2, L ≥ 2. Then d = n − L, and h_C is palindromic iff
Ω̄_C(P, m) = Ω_C(P, m − L + 1) for all m.

*Check.* d = n − L is Lemma E1 (§3). For the equivalence: by Theorem R,
Ω_C(P, −k) = (−1)^n Ω̄_C(P, k). This is zero for k = 0 (C(0, n) = 0 for
n ≥ 1) and for 1 ≤ k ≤ L − 1 (no strict map of an L-chain into [k]). So
m ↦ Ω_C(P, m − s), with s = L − 1, vanishes at m = 0, …, s. The generating
functions of [PH] are correct. Σ_{m≥0} C(m + n − 1 − j, n) x^m = x^{j+1}/(1 − x)^{n+1}
for 0 ≤ j ≤ n − 1, because the polynomial vanishes at m = 0, …, j, where
0 ≤ m + n − 1 − j ≤ n − 1. And Σ_{m≥0} C(m + j, n) x^m = x^{n−j}/(1 − x)^{n+1}
for 0 ≤ j ≤ n. The only terms of Σ_{m≥0} Ω_C(P, m − s) x^m that were not
accounted for are the m < s terms, and these are zero. So both series have
the form x^L N(x)/(1 − x)^{n+1}, with numerators Σ h_j x^j and
Σ h_j x^{d−j}, and n − j = L + (d − j). The numerators are equal iff h_C is
palindromic.

Hypotheses of the imported facts: B⁺ and (R̄) need n ≥ 2, Theorem R needs
nothing. **HOLDS.** COMPUTED `[P0]`: here Ω̄_C is taken from the Möbius
Ω_C via Theorem R, and the polynomial identity is tested at
m = 0, …, n + 2. Separately, (R̄) is tested against a literal count of
strict maps with D_T for every m ≤ n + 1 and n ≤ 6 (`[Rbar-lit]`,
3084 / 3084).

## 2. E0

*Check.* B⁺ at m = 1 and m = 2 gives h_0 and (n + 1)h_0 + h_1. B⁺ is a
statement about all coefficients, not only the trimmed ones, so h_1 = 0
when d = 0 is consistent. The constant map is anchored because
max f(P ∖ U) is taken over a nonempty set (U misses T) and is equal to
min f(U). A map into [2] fails anchoring for U iff f^{−1}(2) = U. Distinct U
give distinct maps, and every T-free cluster is an up-set. So exactly
2^{r−1} − 1 maps are not anchored. **HOLDS.**

COMPUTED: h_0 = 1 and h_1 = J − 2^{r−1} − n on the Möbius h_C (2449 / 2449,
n ≤ 7). The anchored counts into [1] and [2] were also made literally
(19 448 / 19 448, n ≤ 8). Control `[ctl-h1-r]`: h_1 = J − n − 1 is refuted
on 503 / 2449, which is exactly the set of disconnected posets with n ≤ 7.

## 3. E1

*Check.* (a) is immediate. (b): f maps an L-chain of T onto [L], so
max f(P ∖ U) = L for every T-free U. A non-singleton component has an
internal relation, so its minimum is < L. T itself is not a singleton
because L ≥ 2, so the isolated points of value L are exactly the
obstructions. (c): the count factors because D_T is decided by (b)
independently on each component. s(K, L) ≥ 1 via δ, since L_K ≤ L. Then
Lemma 2.1 gives m_0 = L. Lemma 2.1 itself is (R̄) read at its first two
nonzero values; it uses C(m + j, n) = 0 for 0 ≤ m + j < n. **HOLDS.**

COMPUTED: d = n − L and h_d = (L − 1)^i ∏ s(K, L) on the Möbius h_C
(2443 / 2443, n ≤ 7). Literally on 19 441 posets with n ≤ 8 and L ≥ 2:
Ω̄_C(P, L − 1) = 0; Ω̄_C(P, L) equals the product; and (b) holds map by map.

## 4. E2, and why the mixed case never reaches it

*Check.* For a component with an L-chain c_1 < ⋯ < c_L and strict
f : P → [L + 1] we have f(c_1) ≤ 2 and f(c_L) ≥ L. If every component has
L_K = L, then every cluster has minimum ≤ 2 < 3 ≤ L ≤ max f(T). So D_T
holds for every T, and the formula is Lemma 2.1 at m_0 + 1. **HOLDS.**

COMPUTED: the strict-map statement literally on 16 044 posets n ≤ 8, with
L ≥ 3 and all L_K = L (connected ones included). The h-identity was checked
on the Möbius h_C on 1820 posets n ≤ 7. Positive controls, both refuted:
- `[ctl-E2-L2]`, the identity at L = 2: refuted on 118 / 250.
- `[ctl-E2-mixed]`, Ω̄_C(P, L + 1) = ∏ s(K, L + 1) with L ≥ 3 and some
  L_K < L: refuted on 2575 / 2591 (n ≤ 8). The smallest instance is
  C_3 ⊔ C_1, with 11 maps against the product 16. The isolated point at
  value 4 = L + 1 violates D_T.

*Mixed heights in G.* This was the main target of the audit. The proof of G
uses E2 only in the case h_d = 1. It then shows that h_d = 1 forces both
i = 0 and L_K = L for every K, and both steps are correct:
- an isolated point contributes the factor L − 1 ≥ 2;
- a non-singleton K with L_K < L has the two distinct strict maps δ_K and
  δ_K + 1 into [L_K + 1] ⊆ [L], so s(K, L) ≥ 2.

So every P with mixed component heights, isolated points included, has
h_d ≥ 2 > 1 = h_0, and E2 is never invoked there. The failure of E2
in the mixed case (`[ctl-next-mixed]` of [PH], and `[ctl-E2-mixed]` here) is
therefore harmless. This was confirmed on data: in all 21 disconnected
posets with a 3-chain and h_d = 1 (n ≤ 8), every component has L_K = L
and there is no isolated point.

## 5. Lemma I

*Check.* δ(x) (the longest chain with top x) satisfies 1 ≤ δ ≤ L_K and
δ(y) ≥ δ(x) + 1 for x < y. For an order-preserving g : K → [2], the map
f = g + δ − 1 takes values in [1, L_K + 1] and is strict. g ↦ f is
injective because δ is fixed. Order-preserving maps K → [2] correspond to
up-sets, and there are as many up-sets as order ideals, J(K). Nothing in the
proof uses connectedness. **HOLDS.**

COMPUTED: s(P, L + 1) ≥ J(P) on all 19 448 posets n ≤ 8, connected or not.
The injection was checked map by map (strict, into [L + 1], J(P) distinct
images) on all 404 posets with n ≤ 6. I also reproduce the side observation
of [PH] that on connected K equality holds iff K is graded (16 458 / 16 458,
n ≤ 8). [PH] correctly marks it as COMPUTED only and does not use it in any
proof; only the remark after G mentions it.

## 6. Theorem G

*Check.* With the two facts of §4, the case h_d = 1 has no isolated points
and all L_K = L ≥ 3. Then E2 gives h_{d−1} = ∏ s(K, L + 1) − (n + 1). E0
gives h_1 = ∏ J(K) − 2^{r−1} − n, using J(P) = ∏ J(K). Their difference is
the displayed identity. It is ≥ 2^{r−1} − 1 by I, because a product of
positive integers is monotone in each factor. The indices d − 1 and 1 are
distinct, since n ≥ rL ≥ 2L gives d = n − L ≥ L ≥ 3. In the other case
h_d ≥ 2 ≠ 1 = h_0. Either way a pair of mirror entries differs. **HOLDS.**

COMPUTED, two independent ways:
- `[G-lit]`, n ≤ 8: h_d = Ω̄_C(P, L) and h_{d−1} = Ω̄_C(P, L + 1) − (n + 1)h_d
  from literal strict-map counts with D_T, and h_1 from a literal count of
  anchored maps into [2]. All 2637 disconnected posets with a 3-chain
  satisfy G. The split is h_d ≥ 2 for 2616 of them and h_d = 1 for 21. In
  each of those 21 the identity holds and the gap is exactly 2^{r−1} − 1.
  All these numbers match [PH] §6.
- `[G]`, n ≤ 7: on the Möbius h_C, 379 / 379 satisfy G and are not
  palindromic.

The examples in [PH] are confirmed: h_C(C_3 ⊔ C_1) = (1, 2) and
h_C(C_3 ⊔ C_3) = (1, 8, 9, 1) (Möbius). For 3·C_3 (n = 9) the literal end
coefficients give h_d = 1 and h_{d−1} − h_1 = 3 (unit test).

## 7. The assembly of S′, and the citation

- *Connected P.* With r = 1 there is no T-free cluster, so Theorem Ω gives
  Ω_C = Ω, Stanley's order polynomial. COMPUTED: Ω_C(P, m) = Ω(P, m) for
  m ≤ 3 on 296 connected posets, n ≤ 6. **The citation transfers.** The
  classical statement (as recorded in [PAR] §4 and [R] §6) is "P graded of
  length ℓ ⇔ Ω(P, −ℓ − m) = (−1)^n Ω(P, m)". By reciprocity this is
  Ω̄(P, m) = Ω(P, m − ℓ), and ℓ = L − 1. A connected P with n ≥ 2 has
  L ≥ 2, so P0 applies with r = 1 and turns this into the palindromicity of
  the trimmed h_C, with d = n − L by E1. Neither trimming nor the shift
  causes a mismatch. Trimming is harmless because E1 shows that the
  untrimmed vector has zeros exactly beyond n − L. The shift is ℓ = L − 1
  on both sides. Edge cases: n ≥ 2 and connected rule out L = 1, and
  connected of height ≤ 2 forces graded, so the two alternatives of S′
  agree on connected P. The equation number EC1 Cor. 3.15.18(b) was not
  re-read for this audit; it is taken from [PAR]. Its content is classical,
  and the "only if" direction is the part being cited. COMPUTED: connected
  P is palindromic iff graded, 1946 / 1946, n ≤ 7.
- *Disconnected, all heights ≤ 2.* Prop. S of [R] is used with its
  hypotheses (n ≥ 2, no 3-chain; the antichain is included). It gives
  h_j = h_{n−2−j} for 0 ≤ j ≤ n − 2. Since cdes ≤ n − 1, h_{n−1} = 0, and
  h_{n−2} = h_0 = 1. So d = n − 2 and the trimmed vector is palindromic.
  This branch is the only place where L = 1 occurs, and P0 is not used
  there, as [PH] says.
- *Disconnected with a 3-chain.* This is G, with r ≥ 2 and L ≥ 3 as
  required.

COMPUTED `[S']`: 2449 / 2449 posets 2 ≤ n ≤ 7, from the Möbius h_C. The
palindromic disconnected counts are 1, 2, 5, 11, 29, 76 for n = 2, …, 7,
matching [PH] and [R]. At n = 8 the full Möbius h_C was not computed
(about 70 times the cost of n = 7); there the disconnected "only if" is
covered by `[G-lit]`, which relies on B⁺ and (R̄) (both audited).

Positive control `[ctl-graded]`: "palindromic iff every component is
graded" is refuted on 151 / 2449. Examples are C_3 ⊔ C_3 with (1, 8, 9, 1),
and the six-point example found by the script, (three minima below 4,
4 < 5) ⊔ C_1: both components are graded, and h_C = (1, 12, 15, 2).

## 8. Method

`compute/audit_palindromic_h_c.py` (Python 3, standard library only, one
core):
- *Posets.* Every poset on n points is obtained from one on n − 1 points
  by adding a new maximal element above an order ideal. Isomorphism classes
  are taken by a canonical form: the minimum relation code over the
  permutations that preserve an iterated (down-degree, up-degree,
  neighbourhood) invariant. Counts 1, 2, 5, 16, 63, 318, 2045, 16 999 for
  n = 1, …, 8.
- *Ω_C (n ≤ 7).* OP(P) is the set of set partitions whose quotient digraph
  (edges between distinct blocks) is acyclic. μ(π, 1̂) is computed by
  μ(1̂, 1̂) = 1 and μ(π, 1̂) = −Σ_{σ > π, σ ∈ OP(P)} μ(σ, 1̂), with every
  coarsening σ enumerated as a set partition of the blocks of π. The
  definition's sign (−1)^{|π|−1} μ(π, 1̂) ≥ 0 was confirmed on every π
  (2449 / 2449 posets). h_C is the trimmed numerator of
  Σ_m Ω_C(P, m) x^m (1 − x)^{n+1}.
- *Literal counts.* s(K, m) by backtracking, cross-checked against all m^n
  maps for n ≤ 5, m ≤ 4 (unit test). J by a scan of subsets. D_T and
  anchoring are tested against every T-free cluster.

The script does not use B⁺, Theorem H or the word encodings, which were
[PH]'s two routes. For n ≤ 7 its h_C depends only on the Möbius definition.

## Reproduce

From `compute/` (about 85 s on one core; the run is bounded by `timeout`):

    timeout 1500 python3 audit_palindromic_h_c.py --mobmax 7 --endmax 8 --litmax 6 > output/audit_palindromic_h_c.txt
    python3 -m unittest test_audit_palindromic_h_c

The script exits 0 iff every check has 0 bad and every control is refuted
somewhere. `--mobmax 8` would extend the Möbius computation to n = 8, but at
roughly 70 times the n = 7 cost it was not run.
