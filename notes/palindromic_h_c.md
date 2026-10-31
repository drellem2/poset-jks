# When is h_C(P) palindromic? The classification S′

Question ([R] §6, §8): prove S′. For a finite poset P on n ≥ 2 points,
h_C(P) is palindromic iff either P is connected and graded, or every
component of P has height ≤ 2 (no 3-element chain). The "if" half and the
connected case were already settled. The missing piece was the "only if" for
disconnected P: a component with a 3-element chain should force h_C to be
non-palindromic.

Tags: **PROVEN** means proved here. **COMPUTED** means checked by
`compute/palindromic_h_c.py`; bracketed labels refer to the lines of
`compute/output/palindromic_h_c.txt`. **KNOWN** means it is in the
literature. **OPEN** means not settled. The claims tagged PROVEN in this
note (P0, E0, E1, E2, I, G and the assembly of S′) are **PROVEN + audited**
in [AudP] = `notes/audit_palindromic_h_c.md`, which re-derived every proof
and recomputed every claim with independent code; no fixes were needed.

Sources: [R] = `notes/reciprocity_omega_c.md` (Theorem Ω, Theorem R,
Lemma R2, Proposition B⁺, Proposition S, all PROVEN + audited in [AudR] =
`notes/audit_reciprocity_omega_c.md`); [PAR] =
`notes/prior_art_reciprocity_omega_c.md`; EC1 = Stanley, *Enumerative
Combinatorics* vol. 1, 2nd ed.

## Verdict

**S′ is PROVEN + audited ([AudP]) for every number of components.** The
"only if" for disconnected P reduces to two pairs of end coefficients, and no induction
on the number of components is needed. Let d = deg h_C. Then h_0 = 1 always.
If P is disconnected and has a 3-element chain, then either h_d ≥ 2, or
h_d = 1 and h_{d−1} − h_1 ≥ 2^{r−1} − 1 ≥ 1, where r is the number of
components. Either way h_d ≠ h_0 or h_{d−1} ≠ h_1, so h_C is not palindromic.

| # | Statement | Status |
|---|---|---|
| P0 | n ≥ 2, L = longest chain size: d = n − L when L ≥ 2, and h_C palindromic ⇔ Ω̄_C(P, m) = Ω_C(P, m − L + 1) for all m | **PROVEN + audited** (§2); COMPUTED `[deg]` |
| E0 | h_0 = 1 and h_1 = J(P) − 2^{r−1} − n, where J(P) is the number of order ideals | **PROVEN + audited** (§1); COMPUTED `[h0]`, `[h1]` |
| E1 | L ≥ 2: h_d = (L − 1)^i · ∏_{K non-singleton} s(K, L), where i is the number of isolated points and s(K, m) is the number of strictly order-preserving maps K → [m] | **PROVEN + audited** (§2); COMPUTED `[top]` |
| E2 | L ≥ 3 and every component has longest chain L: every strict map P → [L + 1] satisfies D_T, so h_{d−1} + (n + 1)h_d = ∏_K s(K, L + 1) | **PROVEN + audited** (§3); COMPUTED `[next]` |
| I | s(K, L_K + 1) ≥ J(K) for every finite poset K with longest chain L_K | **PROVEN + audited** (§3, an explicit injection; K need not be connected); COMPUTED `[inj]` (on connected K, with equality iff K is graded) |
| G | r ≥ 2 and L ≥ 3 ⇒ h_d ≥ 2, or else h_d = 1 and h_{d−1} − h_1 = ∏_K s(K, L + 1) − ∏_K J(K) + 2^{r−1} − 1 ≥ 2^{r−1} − 1 ≥ 1 | **PROVEN + audited** (§4); COMPUTED `[gap]` |
| S′ | n ≥ 2: h_C palindromic ⇔ (P connected and graded) or (every component has height ≤ 2) | **PROVEN + audited** (§5, [AudP]): disconnected "only if" by G; "if" for height ≤ 2 by Prop. S of [R]; connected case KNOWN (EC1 Cor. 3.15.18(b)). COMPUTED on all 19 448 posets with 2 ≤ n ≤ 8 `[pal-class]` |
| ✗ | "h_C palindromic iff every component is graded" | **FALSE** `[ctl-graded]`, e.g. C_3 ⊔ C_3 with h_C = (1, 8, 9, 1) |
| ✗ | E0 without the factor 2^{r−1}, i.e. h_1 = J(P) − n − 1 | **FALSE** on every disconnected P `[ctl-h1-r]` |
| ✗ | E2 with L = 2 | **FALSE** `[ctl-next-L2]`; e.g. C_2 ⊔ C_2 has 9 strict maps into [3], but only 8 satisfy D_T |
| ✗ | E2 when some component has a shorter longest chain | **FALSE** `[ctl-next-mixed]` |

## 0. Conventions and the facts used

P is a poset on n ≥ 2 points with components K_1, …, K_r. h_C(P) is the
trimmed vector of [R] §6 (trailing zeros removed), and d = deg h_C, so
h_d ≠ 0. "Palindromic" means h_j = h_{d−j} for 0 ≤ j ≤ d. L is the largest
number of elements in a chain of P, and L_K is the same for a component K.
"Height ≤ 2" means L_K ≤ 2. An element is isolated if it is a singleton
component, and i is the number of isolated points. J(Q) is the number of order
ideals of Q, equivalently the number of order-preserving maps Q → [2].
s(Q, m) is the number of strictly order-preserving maps Q → [m].

A **T-free cluster** is a nonempty union U of components with U ∩ T = ∅.
f is **T-anchored** if no T-free cluster U has min f(U) > max f(P ∖ U).
f satisfies **D_T** if no T-free cluster U has min f(U) ≥ max f(P ∖ U).

Three facts from [R], all PROVEN + audited in [AudR], hold for every
component T:

- (Ω) Ω_C(P, m) = #{f : P → [m] order-preserving and T-anchored} (Theorem Ω).
- (B⁺) Ω_C(P, m) = Σ_j h_j C(m + n − 1 − j, n) ([R] §3, Prop. B⁺, with
  h_j = #{w ∈ B_T : des w = j}).
- (R̄) Ω̄_C(P, m) := #{f : P → [m] strictly order-preserving with D_T}
  = Σ_j h_j C(m + j, n). This is the second display in the proof of
  Theorem R ([R] §2), regrouped by des w with B⁺. In particular Ω̄_C does not
  depend on T.

Only the first terms of these sums matter. For an integer m ≥ 0,
C(m + j, n) = 0 when m + j < n, and C(n, n) = 1, C(n + 1, n) = n + 1.

## 1. The bottom pair (h_0, h_1)

**Lemma E0 (PROVEN; COMPUTED `[h0]`, `[h1]`).** h_0 = 1 and
h_1 = J(P) − 2^{r−1} − n. (Read h_1 = 0 if d = 0.)

*Proof.* By (B⁺) at m = 1, only j = 0 contributes, so Ω_C(P, 1) = h_0. At
m = 2, only j = 0 and j = 1 contribute, so Ω_C(P, 2) = (n + 1)h_0 + h_1.

Now count with (Ω). The constant map to [1] is anchored, since min f(U) =
max f(P ∖ U) for every U. So h_0 = 1. An order-preserving f : P → [2] is
determined by the up-set f^{−1}(2), so there are J(P) of them. Since the values lie in
{1, 2}, a T-free cluster U has min f(U) > max f(P ∖ U) iff f = 2 on U and
f = 1 on P ∖ U, i.e. iff f^{−1}(2) = U. So the non-anchored maps correspond
to the nonempty T-free clusters, and there are 2^{r−1} − 1 of these. Hence
Ω_C(P, 2) = J(P) − 2^{r−1} + 1, and h_1 = J(P) − 2^{r−1} + 1 − (n + 1). ∎

## 2. The top coefficient h_d, and the shift

**Lemma 2.1 (PROVEN).** Put m_0 = n − d. Then Ω̄_C(P, m) = 0 for
0 ≤ m < m_0, Ω̄_C(P, m_0) = h_d, and Ω̄_C(P, m_0 + 1) = (n + 1)h_d + h_{d−1}
(with h_{−1} = 0). In particular m_0 is the least m with Ω̄_C(P, m) ≠ 0.

*Proof.* In (R̄), the term j contributes to Ω̄_C(P, m) only when m + j ≥ n.
For m < m_0 every j ≤ d has m + j < n. At m = m_0 only j = d survives, with
C(n, n) = 1. At m = m_0 + 1 the terms j = d and j = d − 1 survive, with
C(n + 1, n) = n + 1 and C(n, n) = 1. Since h_d ≠ 0, m_0 is the first m with a
nonzero value. ∎

**Lemma E1 (PROVEN; COMPUTED `[deg]`, `[top]`).** Suppose L ≥ 2, and let T
be a component that contains an L-element chain. Then:
- (a) Ω̄_C(P, m) = 0 for m < L;
- (b) a strict f : P → [L] satisfies D_T iff no isolated point has value L;
- (c) Ω̄_C(P, L) = (L − 1)^i · ∏_{K non-singleton} s(K, L) ≥ 1.

Hence d = n − L, and h_d = (L − 1)^i ∏_{K non-singleton} s(K, L).

*Proof.* (a) A strict map sends an L-chain injectively and monotonically
into [m], so m ≥ L.

(b) Let f : P → [L] be strict. f maps the L-chain of T onto 1, …, L, so
max f(T) = L. For a T-free cluster U, P ∖ U ⊇ T, so max f(P ∖ U) = L, and U
violates D_T iff min f(U) = L, i.e. iff every component inside U has
minimum value L. A non-singleton component K has min f(K) < max f(K) ≤ L,
so this happens iff U consists of isolated points of value L. T is not a
singleton, since L ≥ 2. So D_T fails iff some isolated point z has f(z) = L
(take U = {z}).

(c) By (b), the strict maps with D_T are the products of independent
choices: any strict map on each non-singleton component, and a value in
[L − 1] at each isolated point. Each factor is ≥ 1: L − 1 ≥ 1, and
s(K, L) ≥ 1 because L ≥ L_K (map x to the size of a longest chain ending at x).

So Ω̄_C(P, L) ≥ 1, and Ω̄_C vanishes below L. By Lemma 2.1, m_0 = L, so
d = n − L and h_d = Ω̄_C(P, L). ∎

**Proposition P0 (PROVEN).** Let n ≥ 2 and L ≥ 2. Then h_C(P) is palindromic
iff Ω̄_C(P, m) = Ω_C(P, m − L + 1) for all m ≥ 0, as polynomials.

*Proof.* Put s = L − 1. By Theorem R, Ω_C(P, −k) = (−1)^n Ω̄_C(P, k), and
this vanishes for 0 ≤ k ≤ L − 1 (Lemma E1(a), and Ω̄_C(P, 0) = 0). So the
values of m ↦ Ω_C(P, m − s) at m = 0, …, s are all 0. Summing (B⁺) and (R̄)
termwise gives

  Σ_{m≥0} Ω_C(P, m − s) x^m = x^s Σ_j h_j x^{j+1} / (1 − x)^{n+1}
                            = x^L Σ_j h_j x^j / (1 − x)^{n+1},
  Σ_{m≥0} Ω̄_C(P, m) x^m     = Σ_j h_j x^{n−j} / (1 − x)^{n+1}
                            = x^L Σ_j h_j x^{d−j} / (1 − x)^{n+1},

using n = L + d. The two series are equal iff Σ_j h_j x^j = Σ_j h_j x^{d−j},
i.e. iff h_C is palindromic. Two polynomials in m that agree for all m ≥ 0
are equal. ∎

So in the reformulation of the question, the shift is forced: s = L − 1, the
length of P. Precisely, a shift s with Ω̄_C(P, m) = Ω_C(P, m − s) for all m
is unique if it exists: both sides are polynomials in m of degree n with the
same leading coefficient, so comparing the coefficients of m^{n−1} determines
s. P0 itself does not need this uniqueness. For a connected P this is Stanley's
Ω̄(P, m) = Ω(P, m − ℓ). For height ≤ 2 it is Prop. S of [R]. For the
antichain (L = 1) the shift is 1 (Prop. S), and P0 is not needed.

## 3. The next coefficient h_{d−1}, when all components reach length L ≥ 3

**Lemma E2 (PROVEN; COMPUTED `[next]`).** Suppose L ≥ 3 and every component
K has L_K = L. Then every strictly order-preserving f : P → [L + 1]
satisfies D_T, for every component T. Hence

  Ω̄_C(P, L + 1) = ∏_K s(K, L + 1), and h_{d−1} = ∏_K s(K, L + 1) − (n + 1) h_d.

*Proof.* Let K be a component, with an L-chain c_1 < ⋯ < c_L, and let f be
strict into [L + 1]. Then f(c_1) ≤ (L + 1) − (L − 1) = 2 and f(c_L) ≥ L.
So min f(K) ≤ 2 and max f(K) ≥ L ≥ 3, for every K. For any T-free cluster U,

  min f(U) ≤ 2 < 3 ≤ L ≤ max f(T) ≤ max f(P ∖ U),

so U does not violate D_T. The strict maps of a disjoint union are products
of strict maps on the components. The formula for h_{d−1} is Lemma 2.1 with
m_0 = L (Lemma E1). ∎

This is the step that uses the 3-element chain: the gap 2 < L needs L ≥ 3.
For L = 2 the claim is false (`[ctl-next-L2]`). For example, C_2 ⊔ C_2 has
s(C_2, 3)^2 = 9 strict maps into [3], and the map with f = (2, 3) on the
T-free component and (1, 2) on T violates D_T, so only 8 survive.
The claim also fails when a component has a shorter chain, because then its
minimum can be large (`[ctl-next-mixed]`).

**Lemma I (PROVEN; COMPUTED `[inj]`).** For every finite poset K with
longest chain L_K (connected or not), and every m ≥ L_K + 1, s(K, m) ≥ J(K).

*Proof.* Let δ(x) be the number of elements of a longest chain with top x.
Then x < y implies δ(y) ≥ δ(x) + 1, and 1 ≤ δ ≤ L_K. Send an order-preserving
g : K → [2] to f = g + δ − 1. Then 1 ≤ f ≤ 2 + L_K − 1 ≤ m. For x < y,
f(y) − f(x) = (g(y) − g(x)) + (δ(y) − δ(x)) ≥ 0 + 1, so f is strict. The map
g ↦ f is injective, since δ is fixed. There are J(K) maps g. ∎

The computation also shows that on connected K, equality s(K, L_K + 1) = J(K)
holds iff K is graded (`[inj]`). That is not used below, and it is not proved
here. (For graded K, g ↦ g + ρ is the classical bijection, which gives "if".)

## 4. The gap theorem

**Theorem G (PROVEN; COMPUTED `[gap]`).** Let P be disconnected (r ≥ 2), with
a 3-element chain (L ≥ 3). Then either h_d ≥ 2, or h_d = 1 and

  h_{d−1} − h_1 = ∏_K s(K, L + 1) − ∏_K J(K) + 2^{r−1} − 1 ≥ 2^{r−1} − 1 ≥ 1.

In particular h_C(P) is not palindromic.

*Proof.* Fix a component T that contains an L-chain. By Lemma E1,
h_d = (L − 1)^i ∏_{K non-singleton} s(K, L).

*Case h_d ≥ 2.* Since h_0 = 1 (Lemma E0), h_d ≠ h_0.

*Case h_d = 1.* Every factor is a positive integer, so every factor equals 1.
- L − 1 ≥ 2, so i = 0: P has no isolated points.
- Every component K has L_K = L. Otherwise L_K < L, and a strict map
  f : K → [L_K] gives two distinct strict maps f and f + 1 into [L], so
  s(K, L) ≥ 2.

So the hypotheses of Lemma E2 hold, and h_{d−1} = ∏_K s(K, L + 1) − (n + 1).
By Lemma E0, h_1 = J(P) − 2^{r−1} − n, and J(P) = ∏_K J(K), since an order
ideal of a disjoint union is a choice of an order ideal in each component.
Subtracting gives the displayed identity. By Lemma I, applied to each K with
m = L + 1 = L_K + 1, ∏_K s(K, L + 1) ≥ ∏_K J(K). So
h_{d−1} − h_1 ≥ 2^{r−1} − 1 ≥ 1, since r ≥ 2. (Here d = n − L ≥ L ≥ 3,
because a second component also has L elements, so h_{d−1} and h_1 are two
distinct entries.) So h_{d−1} ≠ h_1. ∎

Remarks.
- The two cases are both needed, and both occur. C_3 ⊔ C_1 has
  h_C = (1, 2), with h_d = 2. C_3 ⊔ C_3 has h_C = (1, 8, 9, 1), with h_d = 1
  and h_2 − h_1 = 4·4 − 4·4 + 2 − 1 = 1. Three copies of C_3 give a gap of
  2^2 − 1 = 3 (unit test).
- In the case h_d = 1, the bound is attained exactly when every component
  satisfies s(K, L + 1) = J(K). By the computation `[inj]` that means every
  component is graded. The minimum gap 2^{r−1} − 1 is then exactly the
  number of non-anchored maps into [2], which lower h_1 (Lemma E0), while no
  strict map into [L + 1] is lost on the h_{d−1} side (Lemma E2).
- The connected case is exactly where this argument gives nothing. For
  r = 1 the correction 2^{r−1} − 1 vanishes, and h_{d−1} − h_1 =
  s(P, L + 1) − J(P), whose positivity for non-graded P is the classical
  content (next section).

## 5. S′

**Theorem S′ (PROVEN + audited in [AudP]; COMPUTED `[pal-class]`, all 19 448 posets with
2 ≤ n ≤ 8).** For n ≥ 2, h_C(P) is palindromic iff either P is connected
and graded, or every component of P has height ≤ 2.

*Proof.*
- *P connected.* Then there is no T-free cluster, Ω_C(P, m) = Ω(P, m) is
  Stanley's order polynomial, and h_C = W_P is the descent polynomial of a
  natural labelling. W_P is palindromic iff P is graded. This is
  **KNOWN**: EC1 Cor. 3.15.18(b), after Stanley's 1972 Memoir Prop. 19.3;
  also Beck–Sanyal Ex. 6.27 ([PAR] §4). A connected poset with n ≥ 2 and
  height ≤ 2 is graded: it has no isolated point, so every maximal chain
  has exactly 2 elements. So the two alternatives of S′ agree on connected P.
- *P disconnected, "if".* Every component has height ≤ 2: Prop. S of [R]
  (PROVEN + audited) gives h_j = h_{n−2−j} for 0 ≤ j ≤ n − 2. In particular
  h_{n−2} = h_0 = 1, so d = n − 2 and this is palindromicity of the trimmed
  vector.
- *P disconnected, "only if".* If some component has a 3-element chain,
  then h_C(P) is not palindromic, by Theorem G. ∎

The PROVEN content new to this note is the disconnected "only if". It needs
only Theorem Ω, Prop. B⁺ and Theorem R of [R], and the elementary counts above.
The connected case is cited, not reproved.

## 6. Computation

`compute/palindromic_h_c.py` runs over every poset with 2 ≤ n ≤ 8, up to
isomorphism: 2, 5, 16, 63, 318, 2045 and 16 999 posets, 19 448 in all, from
the enumerator of `h_vector_omega_c.py`. The n ≤ 7 counts match [R].

h_C is computed independently in two ways for every poset, and in three ways for n ≤ 7:
- from Prop. B⁺, by counting w ∈ Lin P with T in the last piece under
  λ_T, for every component T (λ_T and the piece test are written in the
  script);
- from Theorem H of `notes/h_vector_omega_c.md` (cdes over cyclic classes,
  separated labelling);
- for n ≤ 7, from the Möbius definition of Ω_C.

All agree `[agree]`. The ingredients of the proof are checked against
counts made independently of h_C. s(K, m) is counted by backtracking over
strict maps of each component, and cross-checked against a literal count over
all maps in the unit tests. J is counted by brute force over subsets.

Results (`compute/output/palindromic_h_c.txt`, 200 s on one core; every
line PASS):

| Tag | Checked | Bad |
|---|---|---|
| `[agree]` (B⁺ for every T = Theorem H; = Möbius for n ≤ 7) | 19 448 | 0 |
| `[h0]`, `[h1]` | 19 448 | 0 |
| `[deg]`, `[top]` (L ≥ 2, i.e. all but the 7 antichains) | 19 441 | 0 |
| `[next]` (L ≥ 3, all L_K = L, d ≥ 1) | 16 038 | 0 |
| `[inj]` (connected K: s(K, L+1) ≥ J(K), = iff graded) | 16 458 | 0 |
| `[gap]` (disconnected, with a 3-chain) | 2 637 | 0 |
| `[pal-class]` (S′) | 19 448 | 0 |

The 2 637 posets of `[gap]` split by which end pair breaks the symmetry:
h_d ≥ 2 for 1 + 8 + 50 + 316 + 2241 = 2 616 of them (n = 4, …, 8), and
h_d = 1 with h_{d−1} > h_1 for 1 + 3 + 17 = 21 (n = 6, 7, 8). In the second
case the bound 2^{r−1} − 1 is attained at every n = 6, 7, 8. Palindromic
disconnected posets: 1, 2, 5, 11, 29, 76, 229 for n = 2, …, 8. At n = 7 the
counts 319 non-palindromic and 76 palindromic disconnected posets match [R].

The `[next]` count leaves out the six chains C_3, …, C_8. They have L ≥ 3 and
a single component with L_K = L, but d = 0, so h_{d−1} is not an entry. E2
holds for them with h_{−1} = 0; including them gives 16 044, the count of
[AudP].

| Control | Refuted on |
|---|---|
| `[ctl-first]` | 2 450 / 2 990 disconnected |
| `[ctl-h1-r]` | 2 990 / 2 990 |
| `[ctl-next-L2]` | 96 / 96 |
| `[ctl-next-mixed]` | 2 575 / 2 591 |
| `[ctl-graded]` | 653 / 19 448 |


Positive controls. Each control below fails somewhere, so the instrument can
see a wrong statement:
- `[ctl-first]`: B⁺ with "T in the first piece" instead of the last
  disagrees with Theorem H. This shows that `[agree]` is not vacuous.
- `[ctl-h1-r]`: dropping 2^{r−1} from E0 fails on every disconnected
  poset.
- `[ctl-next-L2]`, `[ctl-next-mixed]`: E2 fails outside its hypotheses,
  which shows that L ≥ 3 and equal chain lengths are used.
- `[ctl-graded]`: the classification "every component graded" fails.

## 7. Open points

- **Audit.** Done: E0, E1, E2, I, G, P0 and the assembly of S′ all hold in
  the independent audit [AudP], with no fixes needed.
- s(K, L_K + 1) = J(K) iff K is graded, for connected K: COMPUTED `[inj]`,
  not proved here ("if" is the classical bijection g ↦ g + ρ). A proof would
  give a self-contained proof of the connected case of S′ by the same
  end-coefficient argument, in the sub-case s(K, L) = 1.
- The quantitative form, h_{d−1} − h_1 in terms of the components, holds only in the
  sub-case h_d = 1. A formula for h_C with three or more components (the
  inclusion–exclusion of [R] §6) remains open.

## Reproduce

From `compute/` (Python 3, no dependencies, one core):

    python3 palindromic_h_c.py --nmax 8 --mobmax 7 > output/palindromic_h_c.txt
    python3 -m unittest test_palindromic_h_c

The script exits with status 0 iff every claim holds and every CONTROL is
refuted somewhere. `--nmax 7` reproduces the range of [R].
