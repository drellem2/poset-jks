# Audit of `notes/lean_js_route.md` §1 and §3 (Route C)

**Verdict: HOLDS WITH FIXES.** Lemma K, the decomposition of §3.2, Proposition C, Theorem V
and the derivation of (D) from (V) are all correct, and every proof survives a re-derivation
by hand. The fixes are one sign-bookkeeping slip in the proof of Lemma K (G1, the product of
the two signs is right, but each factor as written is off by −1 with the note's own `j`),
exact signs for the two leftover terms (G2), and a citation fix (G3). None of them changes a
result. Every combinatorial claim was recomputed by independent code with **exact** ranks
over ℚ on all 405 posets with `n ≤ 6`.

The note is cited as [R]. Its other tags are as in [R]. This audit was written from [R] §§1–3,
`notes/mu_op_elementary.md` §§0–2 ([ME]) for Lemmas M and U, and the Lean sources named below.
It imports nothing from `compute/`: all code is in `compute/audit_lean_js_route.py` ("[Aud]").
No other review of [R] was read.

| # | Claim of [R] | Verdict | How checked |
|---|---|---|---|
| K | Lemma K (§3.1): the stated `p` gives an exact augmented complex, via the operator `s` and the filtration `F_k` | **HOLDS.** Re-derived with every sign (§1). In the case `τ ∈ c` the sign is stated with the wrong `j` (G1). The signs of the two leftover terms should be given (G2) | `[K]`: the identity with exactly [R]'s signs on all 2,474,956 chains of all 911 `Q`'s (n ≤ 6, empty chain included). Opposite sign fails on 402 posets; `τ = p(max c)` fails on 381 |
| BW | "At the homotopy level this is [BW]" | **HOLDS for Route C as a whole; not the citation for Lemma K alone** (G3, §2) | by reading; [BW] and Quillen cited from memory |
| i | §3.2 (i): `Q` satisfies Lemma K with `t = π_a`, `p = · ∧ π_a`; `Q = L̄ ∖ A` is `L̄` minus the meet-complements of `π_a` | **HOLDS** (§3) | `[M]`, `[Pz]` on all 911 pairs `(P, a)` with n ≥ 3 |
| ii, iv–vi | `π_ab` minimal; `strip_b ∘ ∂ = −∂ ∘ strip_b`; support; `strip ∘ cons` | **HOLDS** (§3), including the degree-0 edge case | by hand |
| iii | Lemma U as used: `(π_ab, 1̂) ≅ L̄(P/π_ab)` | **HOLDS** (§3) | `[U]`: the map σ ↦ σ/π_ab is a bijection onto the proper part of `OP(P/π_ab)` and preserves and reflects refinement, on every pair; Betti numbers agree |
| C | Proposition C (`d ≥ 1` and `d = 0`) | **HOLDS** (§4) | by hand; `[Qac]` (Q acyclic over ℚ) on all 911 pairs |
| V | Theorem V: induction, base cases, degree bookkeeping | **HOLDS** (§5) | `[JS]`, `[rel]` (in the stronger all-`d ≥ 0` form, G4) |
| D | §1: (D) from (V) via `trace_HP_of_vanishing` at `g = 1` and `mu_OP_eq` | **HOLDS** (§6) | by reading the Lean statements |
| JS | `β_d(L̄) = 0` for `d ≠ n − 3`, `β_{n−3} = e_C(P)` | **HOLDS** on 405/405 posets, n ≤ 6 | `[JS]`, exact rank over ℚ; rank code controlled by three complexes, one of them with homology in three degrees and one (RP²) that separates ℚ from 𝔽₂ |

---

## 1. Lemma K, re-derived with every sign

Setting: `R` finite, `t ∈ R`, `p` monotone, `p ≤ id`, `p ≤ t`, `p = id` on `R_{≤t}`. Chains are
increasing tuples `c = (c_0 < ⋯ < c_{m−1})`; `∂c = Σ_i (−1)^i (c ∖ c_i)`
(`lean/PosetJKS/OrderComplex.lean`, `bd`).

*Shape of a chain.* If `c_i ≤ t` and `c_k < c_i` then `c_k ≤ t`, so `c_≤ = (c_0, …, c_{j−1})`
with `j = |c_≤|`, and `h = c_j` when `c_> ≠ ∅`.

*Where τ goes.* If `c_> = ∅`, `τ = t` lies above all of `c`. Otherwise every `y ∈ c_≤` has
`y = p(y) ≤ p(h)` (monotone, `p = id` below `t`), and `p(h) < h` (`p(h) ≤ h`, and `p(h) ≤ t`
while `h ≰ t`). So in both cases `τ ≥ c_{j−1}` and `τ < c_j`:
- `τ ∉ c` ⇒ `c ∪ τ` is a chain with `τ` at position `j`;
- `τ ∈ c` ⇒ `τ = c_{j−1}` (`j ≥ 1`), i.e. τ sits at position **`j − 1`** of `c`.

*Stability.* Adding or removing `τ` (which is `≤ t`) does not change `c_>`; removing any
`x ≠ h` does not change `min c_>`. So `τ(c ∪ τ) = τ(c ∖ τ) = τ(c ∖ x) = τ(c)` for `x ≠ h`.
This is [R]'s list, and it is right.

`s(c) = (−1)^j [c ∪ τ]` if `τ ∉ c`, else `0`.

**Case τ ∉ c**, `c' = c ∪ τ` (`m + 1` elements, τ at position `j`).
- Face `j` of `c'` is `c`, coefficient `(−1)^j · (−1)^j = +1`.
- `x = c_i`, `i < j`: in `∂s(c)` the face of `c'` at position `i` has coefficient
  `(−1)^j (−1)^i`. In `s∂(c)`: `(−1)^i s(c ∖ c_i)`, and `c ∖ c_i` has `j − 1` low elements, so
  this is `(−1)^{i+j−1} [(c ∖ c_i) ∪ τ]`. They cancel.
- `x = c_i`, `i > j` (high, `≠ h`): in `c'` it is at position `i + 1`, coefficient
  `(−1)^{j+i+1}`. In `s∂(c)`: `(−1)^i (−1)^j`. They cancel.
- `x = h = c_j`: the leftover is
  **`−[(c ∖ h) ∪ τ] + (−1)^j s(c ∖ h)`**, both in `F_{k−1}`.

These are exactly [R]'s signs `(−1)^{j+i}` / `(−1)^{i+j−1}` (`i < j`) and `(−1)^{j+i+1}` /
`(−1)^{i+j}` (`i ≥ j`, `i ≠ j`).

**Case τ ∈ c** (τ at position `j − 1`). `s(c) = 0`.
- The face removing τ has coefficient `(−1)^{j−1}`. `c ∖ τ` has `j − 1` low elements and
  `τ(c ∖ τ) = τ ∉ c ∖ τ`, so `s(c ∖ τ) = (−1)^{j−1}[c]`. Product **`+c`**.
- A face removing `x ∉ {τ, h}` still contains `τ = τ(c ∖ x)`, so `s` kills it.
- The face removing `h` gives **`(−1)^j s(c ∖ h)`** ∈ `F_{k−1}`.

**Case k = 0.** No `h`, so every non-diagonal term cancels and the identity is exact. This
includes the empty chain: `s(∅) = [t]`, `∂[t] = ∅`, and `∂` is zero on `C_{−1}`.

**G1 (fix).** [R] writes the τ-removing face's sign as `(−1)^j`, with `j` defined just above as
`|c_≤|`. With that `j` the sign is `(−1)^{j−1}`, and so is the sign of `s(c ∖ τ)`. The product
`+1` is unaffected, so the proof is right, but a Lean lemma written from the text with
`j = hcount`-style low count would be false. State it with `j' = j − 1`, the position of τ in
`c`: `s(face c j') = (−1)^{j'} [c]`.

**G2 (fix).** [R] gives the two leftover terms as `±`. The slice S2 needs them: for `τ ∉ c`
they are `−[(c ∖ h) ∪ τ(c)]` and `(−1)^j s(c ∖ h)`; for `τ ∈ c`, `(−1)^j s(c ∖ h)`. (Only
membership in `F_{k−1}` is used, so the proof does not depend on them.)

*Exactness.* `∂` and `s` preserve every `F_k` (faces and τ ≤ t add no high element). By
linearity `(∂s + s∂ − id)(F_k) ⊆ F_{k−1}` and `= 0` on `F_0`. For a cycle `z ∈ F_k`,
`s∂z = 0`, so `z − ∂(sz) ∈ F_{k−1}` is a cycle; induction on `k ≤ |R|` ends at `F_{−1} = 0`.
`R ∋ t` is nonempty, so exactness also holds at degree `−1`. **Lemma K HOLDS.**

## 2. Citation (G3)

**G3 (fix).** The homotopy form of Lemma K is not Björner–Walker's theorem. It is Quillen's
order-homotopy lemma: monotone maps `f ≤ g` induce homotopic maps of order complexes
(Quillen, *Homotopy properties of the poset of nontrivial p-subgroups of a group*, Adv. Math.
28 (1978), §1, Prop. 1.6 and the cone remark 1.5), in the form "a monotone `f` with `f ≤ id`
makes `Δ(f(R))` a deformation retract of `Δ(R)`" (Björner, *Topological methods*, Handbook of
Combinatorics (1995), Cor. 10.12). Here `p(R) = R_{≤t}` is a cone with apex `t`, so `Δ(R)` is
contractible. Lemma K is the chain-level, filtration-by-high-part version of that; the
specific operator `s` (insert `p(min c_>)`) is not in either source as far as I recall.

[BW]'s homotopy complementation formula is the right citation for **Route C as a whole**
(Lemma K + Proposition C ⇒ `Δ(L̄) ≃ ⋁_b Σ Δ(π_ab, 1̂)`, and this is how [R] §2.5 uses it). Its
hypotheses hold here: by Lemma M(b) the meet-complements of `π_a` are exactly the atoms
`π_ab ∈ OP(P)`; they are also join-complements, since `π_ab ∨ π_a` is at least the partition
join, which is `1̂`; and atoms form an antichain with `Δ(0̂, π_ab) = ∅`. The [BW] proof (as
recalled) also removes the complements and contracts the rest by the closure `x ↦ x ∧ c`,
which is §3.2 (i). All three sources are cited from memory and were not re-read; theorem
numbers are not re-checked.

## 3. §3.2 (i)–(vi)

(i) Each bullet re-checked: `x ∧ π_a ∈ OP(P)` (Lemma M(a), `isOrderPreserving_inf`);
`≠ 0̂` on `Q` by Lemma M(b) (`inf_pa_eq_bot_iff'`: `s ⊓ pa a = ⊥ ↔ s = ⊥ ∨ ∃ b ≠ a, s = pab a b`);
`≠ 1̂` because `≤ π_a ≠ 1̂`; `∉ A` because `π_ab ≰ π_a`. `π_a ∈ Q` needs `n ≥ 3` (else
`π_a = 0̂`). Monotone, `p ≤ id`, `p ≤ t`, `p = id` below `t` are meet-semilattice facts.
`Q = L̄ ∖ A` is exactly `L̄` minus `{x ≠ 0̂ : x ∧ π_a = 0̂}`. Note `A` contains only the atoms
`π_ab` with `a` in the pair; other atoms `π_cd` stay in `Q`, correctly. `[M]`, `[Pz]` on all
911 pairs.

(ii) `π_ab` covers `0̂` in the partition lattice, so it is an atom of `OP(P)` and minimal in
`L̄`; two distinct atoms are incomparable, so a chain meets `A` at most once, at its bottom.

(iii) Lemma U ([ME] §1) sends `π_ab ↦ 0̂` and `1̂ ↦ 1̂`, so the open interval goes to the proper
part. The Lean `Contr a b h` carries `u ≤ v ↔ Reach (pab a b) u v`, the transitive closure of
the quotient digraph, i.e. `Q_{π_ab}`, with `n − 1` points (`Contr.card_eq`). `[U]` checks the
order isomorphism directly on all 911 pairs.

(iv) For `c = (π_ab, y_0, …, y_{m−1})`: face 0 has no `π_ab`; face `i ≥ 1` removes `y_{i−1}`
with sign `(−1)^i = −(−1)^{i−1}`. So `strip_b ∂ c = −∂ strip_b c`. Edge case `c = (π_ab)`:
`∂c = ∅`, `strip_b ∅ = 0`, and `∂` of the degree-(−1) chain is 0. Equivalently
`∂ cons_b(e) = e − cons_b(∂e)`. (v) `strip_b` is a coordinate projection, bijective from the
chains with bottom `π_ab`; by (ii) a chain with no coefficient on any such chain lies in `C(Q)`.
(vi) clear.

## 4. Proposition C

Re-derived as in [R]: `c_b = strip_b z` is a cycle by (iv); `c_b = ∂e_b`; with
`w = z + Σ_b ∂ cons_b e_b`, (iv) and (vi) give `strip_b w = c_b − ∂e_b = 0`; by (v) `w ∈ C(Q)`,
a cycle; Lemma K gives `w = ∂r`. Degrees: `z` has `d + 1` elements, `c_b` has `d`, `e_b` has
`d + 1`, `cons_b e_b` has `d + 2`. For `d = 0`, `c_b` is a multiple of `∅`, and `∂_0` onto
`C_{−1}` needs the interval nonempty (`range_bd_zero [Nonempty L]`). For `d ≥ 1` an empty
interval is harmless (`c_b = 0`). **HOLDS.**

## 5. Theorem V and the degree bookkeeping

- `n ≤ 2`: `OP(P) ⊆ {0̂, 1̂}`, `L̄ = ∅`, `C_m = 0` for `m ≥ 1`, so `redHom d = 0` for every
  `d ∈ ℕ`. Correct: the nonzero `H̃_{−1}(∅)` is outside the Lean range `d ∈ ℕ`.
- `n ≥ 3`, `d ≥ 1`: `(d−1) + 3 ≠ n − 1 ⇔ d + 3 ≠ n`, the induction hypothesis at `n − 1`
  transported along (iii).
- `n ≥ 3`, `d = 0`: `d + 3 ≠ n` gives `n ≥ 4`, so `|P/π_ab| ≥ 3` and the interval is nonempty.
- `d ≠ n − 3 ⇔ d + 3 ≠ n` for `n ≥ 3` (natural subtraction is harmless there).

**HOLDS.** The induction needs no base case beyond `n ≤ 2`, and none of `n = 3` (where
`β_0(L̄) = |A|`) is used.

**G4 (remark, optional).** The relation `β_d(L̄) = Σ_b β_{d−1}((π_ab, 1̂))` holds for **every**
`d ≥ 0`, not only `d ≥ 1`, with `β_{−1}(∅) = 1`: the strip maps give an isomorphism of
complexes `C(L̄)/C(Q) ≅ ⊕_b C((π_ab, 1̂))[−1]` (differential negated, augmentation included),
and `C(Q)` is exact. At `n = 3` this reads `β_0(L̄) = |A| = e_C(P)`. `[rel]` checks the all-`d`
form on all 911 pairs. Proposition C is its vanishing half, which is all (V) needs.

## 6. §1: (D) from (V)

`trace_HP_of_vanishing hn hV 1 : trace (actHP 1) = (−1)^{n−3} · muFixed 1`
(`TraceHP.lean:194`); `mu_OP_eq : muFixed 1 = (−1)^{n−1} e_C` (`MuOP.lean:966`). With
`actHP 1 = id` the left side is `(finrank ℂ (HP α) : ℂ)`, and `(n−3) + (n−1) = 2n − 4` is even
for `n ≥ 3`, so `finrank = e_C` after `Nat.cast_injective`. **HOLDS.** Two small Lean notes:
`actHP 1 = homMap (actProper 1) _`, and `actProper 1` is the identity only up to `Subtype.ext`
and `Setoid.comap id = id` (an `ext`, not `rfl`); `chainMap` of it is then `mapDomain` of a
function equal to `id` by `OrderEmbedding.ext`. Both are one-liners.

## 7. Direct computation (n ≤ 6)

[Aud] enumerates unlabelled posets itself (add a maximal element above a down-set,
canonical form by brute force: 1, 2, 5, 16, 63, 318), computes `OP(P)` from acyclicity of the
quotient digraph, all chains of `L̄` (empty chain in degree −1), and the reduced Betti numbers
from **exact ranks over ℚ** (sparse Gaussian elimination in `Fraction` arithmetic). `e_C(P)`
is counted directly as rotation classes of linear extensions.

| n | posets | `β_d = 0` for `d ≠ n − 3` | `β_{n−3} = e_C(P)` | top-degree values seen |
|---|---|---|---|---|
| 1, 2 | 3 | all `d ≥ 0` (L̄ = ∅) | — | — |
| 3 | 5 | 5/5 | 5/5 | 1, 2 |
| 4 | 16 | 16/16 | 16/16 | 1–6 |
| 5 | 63 | 63/63 | 63/63 | 1 … 24 |
| 6 | 318 | 318/318 | 318/318 | 1 … 120 |

Positive controls for the rank code (all fire):
- crown `{a, b} < {c, d}` plus an isolated point: `β_0 = β_1 = 1` (two degrees);
- face poset of `∂Δ³ ⊔ ∂Δ²`: `β_0 = β_1 = β_2 = 1` (three degrees);
- face poset of the 6-vertex RP²: all `β = 0` over ℚ, but `β_1 = β_2 = 1` over 𝔽₂ with the
  same chain code. So the ℚ-rank is genuinely a characteristic-0 rank.

Route C checks (all 911 pairs `(P, a)`, `n ≥ 3`; [R]'s 915 also counts the 4 pairs with
`n ≤ 2`): `[M]`, `[Pz]`, `[K]` (2,474,956 chains), `[Qac]` (exact), `[U]`, `[rel]` all hold
on 405/405. Controls: opposite sign of `s` fails `[K]` on 402 posets, `τ = p(max c)` on 381,
`Q := L̄` fails acyclicity on 402. The first and third agree with [R]'s C1 and C3 counts (402,
402), recomputed independently. [R]'s C4 count (397) is for a different check (`[inv]`) and
is not comparable.

## Reproduce

    cd compute
    python3 audit_lean_js_route.py --nmax 6 --procs 3 > output/audit_lean_js_route_n6.txt   # ~4 min
    python3 -m unittest test_audit_lean_js_route

Output: `compute/output/audit_lean_js_route_n6.txt`, ending `ALL CHECKS PASS`.

## Not checked

- [BW], Quillen 1978 and Björner 1995 are cited from memory; theorem numbers not re-checked.
- The Lean-level indexing of S1–S4 (e.g. `Fin.insertNth`/`succAbove` lemmas). G1 and G2 give
  the signs the slices should state; whether the Mathlib API names exist was not checked.
- Line estimates (§5, §6 of [R]) are out of scope.
