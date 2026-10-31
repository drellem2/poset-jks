# Scoping the last Lean input: `jencaSarkoci_homology`

As of main `17cfb51`, `jencaSarkoci_homology` (`lean/PosetJKS/MainTheorem.lean:95`) is the
only `sorry` in `lean/PosetJKS`. `trace_HP` and `main_iso` use nothing else that is open. The
statement, for a finite poset `P` on `n ≥ 3` points with `L̄` the proper part of `OP(P)`, is:

    (V)  H̃_d(Δ(L̄); ℂ) = 0 for d ≠ n − 3,      (D)  dim H_P = e_C(P).

This note compares routes to it and recommends one. It does not change `lean/`.

## Verdict

| Claim | Status |
|---|---|
| (D) follows from (V) and results already in Lean: `trace_HP_of_vanishing` at `g = 1` and `mu_OP_eq`. About 50 lines | **PROVEN** (§1) |
| Euler characteristic plus the lower bound `dim H_P ≥ e_C(P)` (Theorem S(c) + Prop. Φ) cannot give (V). Route 3 is not a route to (V). Its upper-bound half is redundant after §1 | **PROVEN** (§2.3) |
| Restating the theorem so that only top homology appears either changes nothing (`H_P` already *is* `ker ∂_{n−3}`) or leaves `main_iso` unprovable by the current proof, or weakens `main_iso` to a virtual-character statement. Not faithful | **PROVEN** (§2.4) |
| **Route C** (homological complementation at `π_a`): (V) follows by induction on `n`, from Lemma K (an explicit chain contraction) and Lemma M(b) / Lemma U, which are already in Lean. No shelling, no Morse lemma, no topology, and no counting beyond what `mu_OP_eq` already did | **PROVEN** here (§3). Its combinatorial claims are **COMPUTED** on all 405 posets with `n ≤ 6` (all 915 pairs (P, a minimal)), with four positive controls (§4) |
| Route C costs about 1,100–1,700 new lines in four slices. Shelling costs about 3,000–5,000 and discrete Morse about 2,000–3,500 | ESTIMATE (§5), calibrated on the M1–M3 actuals |
| **Recommendation: Route C**, slices S1–S4 (§6) | — |

Tags: [Thm] = `notes/poset_jks_theorem.tex`; [ME] = `notes/mu_op_elementary.md`;
[Lit] = `notes/literature_novelty_jks_maps.md`; [CS] =
`notes/conjecture_s_splitting_cycles_span.md`; [JS] = Jenča–Sarkoci, JCTA 122 (2014),
arXiv:1112.5782v2; [SW] = Schweig–Woodroofe, Adv. Math. 2017, arXiv:1604.03115;
[BW] = Björner–Walker, *A homotopy complementation formula for partially ordered sets*,
European J. Combin. 4 (1983) 11–19 (cited from memory, not re-read).

Conventions are those of `lean/PosetJKS/OrderComplex.lean`. `Chains L m` is spanned by the
`m`-element chains. `∂c = Σ_i (−1)^i (c minus its i-th element)`. The empty chain is in degree
`−1`. `redHom L d = ker ∂_d / im ∂_{d+1}`, where `d`-chains have `d + 1` elements and `d ∈ ℕ`.

## 1. (D) is free once (V) is proved

At `g = 1`, `trace_HP_of_vanishing hn hV 1` gives
`tr(actHP 1) = (−1)^{n−3} μ(OP(P))`. Here `actHP 1 = id`: `actProper 1` is the identity
(`actSetoid_one`), and `chainMap` of the identity is `mapDomain id = id`. So the left side is
`finrank ℂ H_P` (`LinearMap.trace_id`). `mu_OP_eq` gives `μ(OP(P)) = (−1)^{n−1} e_C(P)`. The
product of the signs is `+1`, so `finrank H_P = e_C(P)`. ∎

So all of the content of `jencaSarkoci_homology` is (V). The count `e_C(P)` enters only through
`mu_OP_eq`, which is proved (Proof W of [ME], via `eC_rec`).

## 2. The candidate routes

### 2.1 Route 1: lexicographic shelling

**What has to be formalized.**
- (a) An EL- or CL-labelling of `\widehat{OP(P)}`. [SW] Thm 1.5 shows that `OP(P)` is
  comodernistic, hence CL-shellable (per [Lit, §1.1]; not re-read). [JS] does not shell.
- (b) CL-labelling ⇒ the lex order on maximal chains is a shelling (Björner–Wachs). This
  needs rooted intervals, recursive labellings and lexicographic comparison of label words.
- (c) Shellable ⇒ reduced homology is concentrated in the top degree, for the hand-rolled
  complex. Each new facet meets the earlier ones in a pure codimension-1 subcomplex. That
  needs a relative-homology or Mayer–Vietoris step per facet, or a Morse matching inside
  each facet.
- (d) The comodernism of `OP(P)` itself: left-modular or modular elements in every
  interval. Mathlib has `IsModularLattice` for the whole lattice, but no left-modular elements.

**Mathematics.** Written down ([SW]; Björner–Wachs), but none of it has been re-checked in this
repo. The count of decreasing chains is not needed, because (D) is free (§1).

**Size.** 3,000–5,000 lines. (a)+(d) alone is a lattice-theory development larger than
`OPLattice.lean` + `Interval.lean` (817 lines), and (b)+(c) is a general shelling library.

**Risks.** It is the largest route. It has a long dependency on an external proof that has not
been re-read, and the lex-order bookkeeping is index-heavy (M1's index-heavy words ran 4×
over estimate, §5).

### 2.2 Route 2: an acyclic matching (algebraic discrete Morse theory)

**What has to be formalized.**
- (a) The algebraic Morse lemma for a based complex of finite-dimensional spaces. Only
  the weak form is needed: if the critical cells all lie in degree `n − 3`, then the
  homology vanishes elsewhere. Even that form needs either the Morse complex or a
  filtration by a linear extension of the matching digraph, together with a proof of
  acyclicity.
- (b) [JS] Thm 3.8's matching. It is built by induction using Kozlov's patchwork theorem
  (Thm 11.10) and Forman's theorem ([ME] §5, [AudME] §2). So the patchwork theorem has to
  be formalized as well.
- (c) The acyclicity of the glued matching.

**Mathematics.** Written down in [JS] §3 (not re-read here in detail).

**Size.** 2,000–3,500 lines.

**Risks.** Acyclicity proofs of matchings are notoriously fiddly. The matching has to be
defined on `Fin m ↪o L̄` for every `m` at once, with the inductive structure of [JS].
Route C below is the same induction (it peels off the atoms `π_ab` at a minimal `a`).
It replaces (a)–(c) by one explicit chain contraction whose identity has been checked
numerically.

### 2.3 Route 3: linear algebra only (Euler characteristic and lower bound)

What is available:
- Hall + Hopf at `g = 1`: `Σ_d (−1)^d dim H̃_d = χ̃(Δ(L̄)) = μ(OP(P)) = (−1)^{n−1} e_C(P)`,
  homology-free on the Möbius side.
- [CS] Remark after Thm 5.3: Theorem S(c) + Prop. Φ + (D-cycles) give
  `dim H_P ≥ e_C(P)` without [JS]. This costs 1,500+ lines (Prop. Φ needs Wachs and Ree;
  PLAN.md §1).

What it gives. Write `t = n − 3` and `β_d = dim H̃_d`. The Euler identity says
`β_t − e_C = Σ_{d<t} (−1)^{t−d+1} β_d`. The lower bound says the left side is `≥ 0`. Neither
says anything about the individual `β_d` for `d < t`. For example, `β_{t−1} = β_t − e_C`
with all other `β_d = 0` is consistent with both. So **route 3 cannot prove (V)**. Without
(V), it cannot pin down `β_t` either.

What it would need. Exactly (V). And given (V), the upper bound and the lower bound are both
redundant by §1. So the 1,500+-line lower bound is off the critical path. It is still useful
for the explicit isomorphism, Theorem S(d), but not for `jencaSarkoci_homology`.

### 2.4 Route 4: restate the theorem in terms of top homology

- (a) "Top homology := kernel of the top boundary." This already holds. `L̄` has no chain
  with `n − 1` elements (the number of blocks strictly decreases along a chain, from at most
  `n − 1` to at least `2`), so `im ∂_{n−2} = 0` and `H_P = ker ∂_{n−3}` on the nose. The
  restatement changes nothing and gains nothing.
- (b) Keep only (D), or only "`H_P` has dimension `e_C`". This is a faithful *partial*
  statement of [JS], but `trace_HP` needs (V). The Hopf trace formula isolates
  `tr(g | H_P)` only when the other `H̃_d` vanish. With (b), `main_iso` is no longer proved.
- (c) Restate `main_iso` for the Lefschetz virtual module `Σ_d (−1)^d H̃_d`. That is a
  virtual-character identity, strictly weaker than an isomorphism of `Aut(P)`-modules.
  **It changes the mathematics. Rejected.**
- (d) Prove `main_iso` without Hopf, from Theorem S(d) (an explicit embedding
  `sgn ⊗ PLie(P) ↪ H_P`). This still needs `dim H_P ≤ e_C(P)`, which is [JS] again, plus
  Prop. Φ. Not cheaper.

Verdict: no faithful restatement avoids (V).

### 2.5 Route C (new here): homological complementation at `π_a`

This is the chain-level form of the step that `mu_op_rec` (Lemma D: dual Weisner at `π_a`)
performs on Möbius values. Fix a minimal `a`. The complements of the coatom-like element
`π_a` are the atoms `π_ab`. Removing them leaves an acyclic subposet `Q` (Lemma K). Each
atom contributes the suspension of its upper interval `(π_ab, 1̂) ≅ L̄(P/π_ab)` (Lemma U).
Induction on `n` then gives (V). At the homotopy level this is the [BW] homotopy
complementation formula. The complements of `π_a` form an antichain, and `Δ(0̂, π_ab) = ∅`.
The homology-level proof below is self-contained and needs no topology.

## 3. Route C: statements and proofs

### 3.1 Lemma K (a retraction onto a cone is acyclic)

**Lemma K.** Let `R` be a finite poset, `t ∈ R`, and `p : R → R` monotone with `p(x) ≤ x`,
`p(x) ≤ t` for all `x`, and `p(x) = x` for `x ≤ t`. Then the augmented chain complex of
`Δ(R)` is exact. In particular `H̃_d(Δ(R)) = 0` for every `d ≥ 0`.

*Proof.* For a chain `c`, let `c_≤ = {x ∈ c : x ≤ t}` (an initial segment) and `c_> = c ∖ c_≤`
(the *high* part). Put `τ(c) = t` if `c_> = ∅`, and `τ(c) = p(h)` with `h = min c_>`
otherwise.

- *`c ∪ {τ(c)}` is a chain, and `τ(c)` lies above `c_≤` and below `c_>`.* For `y ∈ c_≤` we have
  `y < h`, so `y = p(y) ≤ p(h)`. Also `p(h) ≤ h`, and `p(h) ≠ h` because `h ≰ t` while
  `p(h) ≤ t`. So `p(h) < h ≤` every element of `c_>`.
- *`τ` is stable.* `τ(c ∪ {τ(c)}) = τ(c)` because `τ(c) ≤ t` leaves the high part unchanged.
  If `τ(c) ∈ c`, then `τ(c ∖ {τ(c)}) = τ(c)`. For `x ∈ c` with `x ≠ h` we have
  `τ(c ∖ {x}) = τ(c)`.

Define `s : C_k → C_{k+1}` on basis chains by `s(c) = (−1)^j [c ∪ {τ(c)}]` if `τ(c) ∉ c`, and
`s(c) = 0` otherwise. Here `j = |c_≤|` is the position of `τ(c)` in `c ∪ {τ(c)}`. Let `F_k` be
the span of the chains with at most `k` high elements (`F_{−1} = 0`). These are subcomplexes,
since faces do not add high elements.

*Claim:* `(∂s + s∂)(c) − c ∈ F_{k−1}` for every chain `c` with `k` high elements, and
`(∂s + s∂)(c) = c` when `k = 0`.

- If `τ ∉ c`, then `∂s(c)` contains `+c` (the face at position `j`, with sign `(−1)^j (−1)^j`).
  For every `x ∈ c` with `x ≠ h`, the face `(c ∖ x) ∪ τ` of `∂s(c)` cancels against `s` of the
  face `c ∖ x` of `∂c`. Both have `τ(c ∖ x) = τ`. The signs are those of the classical cone
  computation: for `x` at position `i < j` they are `(−1)^{j+i}` and `(−1)^{i+j−1}`, and for
  `i ≥ j` they are `(−1)^{j+i+1}` and `(−1)^{i+j}`. What remains is the two terms coming from
  `x = h`, namely `±[(c ∖ h) ∪ τ(c)]` and `±s(c ∖ h)`. Both have `k − 1` high elements.
- If `τ ∈ c`, then `s(c) = 0`. In `s(∂c)` the face removing `τ` (sign `(−1)^j`) returns
  `(−1)^j (−1)^j c = c`. A face removing `x ∉ {τ, h}` keeps `τ(c ∖ x) = τ ∈ c ∖ x`, so `s`
  kills it. The face removing `h` gives a term in `F_{k−1}`.
- If `k = 0`, there is no `h`, and the identity is exact.

*Exactness.* Let `z ∈ F_k` be a cycle. Then `z − ∂(s z) = z − (∂s + s∂) z ∈ F_{k−1}`, and this
is a cycle. By induction on `k`, it is a boundary, so `z` is a boundary. ∎

`[N]` in §4 checks this identity, with exactly these signs, on every chain of every `Q` that
arises for `n ≤ 6`. Control C1 (the sign `(−1)^{j+1}`) fails it.

### 3.2 The decomposition of `L̄`

Let `n ≥ 3`, let `a` be minimal in `P`, and let `A = {π_ab ∈ OP(P) : b ≠ a}` and `Q = L̄ ∖ A`.

- (i) *`Q` satisfies Lemma K with `t = π_a` and `p(x) = x ∧ π_a` (the partition meet).*
  - `π_a ∈ OP(P)` (`isOrderPreserving_pa`).
  - `x ∧ π_a ∈ OP(P)` (`isOrderPreserving_inf`).
  - For `x ∈ Q` we have `x ∧ π_a ≠ 0̂`, by Lemma M(b) (`inf_pa_eq_bot_iff'`):
    `x ≠ 0̂` and `x ∉ A`.
  - `x ∧ π_a ≤ π_a < 1̂`.
  - `x ∧ π_a ∉ A`, because `π_ab ≰ π_a` (`a` and `b` lie in different blocks of `π_a`).
  - `t = π_a ∈ Q`: for `n ≥ 3`, `π_a ≠ 0̂`, and `π_a ∉ A` since `{a}` is a block of `π_a`.
  - Monotonicity, `p ≤ id`, `p ≤ t`, and `p(x) = x` for `x ≤ t` are lattice facts.
- (ii) *Each `π_ab ∈ A` is minimal in `L̄`.* A strict refinement of `π_ab` is `0̂`. So a chain
  of `L̄` contains at most one element of `A`, and only as its least element.
- (iii) *`(π_ab, 1̂)_{OP(P)} ≅ L̄(P/π_ab)`* is Lemma U ([ME] §1). In Lean the poset `P/π_ab` is
  `Contr a b h`, and `pullOP` with the facts used in `mu_pab_top` gives the order isomorphism.

For `b` with `π_ab ∈ A`, let `strip_b : C_m(L̄) → C_{m−1}((π_ab, 1̂))` send a chain with least
element `π_ab` to its tail, and every other chain to `0`. Let `cons_b` be the inverse on such
chains, which prepends `π_ab`.

- (iv) `strip_b ∘ ∂ = −∂ ∘ strip_b`. Removing `π_ab` gives a chain without it. Removing the
  `(i+1)`-st element gives sign `(−1)^{i+1}`. Faces of chains without `π_ab` do not contain it.
- (v) A chain `x` with `strip_b x = 0` for all `b` lies in the image of `C(Q)`, by (ii).
- (vi) `strip_b ∘ cons_b = id`, and `strip_{b'} ∘ cons_b = 0` for `b' ≠ b`.

**Proposition C.** Let `d ≥ 1`. If `H̃_{d−1}((π_ab, 1̂)) = 0` for every `π_ab ∈ A`, then
`H̃_d(L̄) = 0`. If every `(π_ab, 1̂)` is nonempty, then `H̃_0(L̄) = 0`.

*Proof.* Let `z ∈ C_d(L̄)` be a cycle and `c_b = strip_b z`.

- By (iv), `∂ c_b = −strip_b(∂z) = 0`. So `c_b = ∂ e_b`, by the hypothesis. For `d = 0`, `c_b`
  is a multiple of the empty chain, and `∂_0` is onto when the interval is nonempty
  (`range_bd_zero`).
- Put `w = z + Σ_b ∂ cons_b(e_b)`. By (iv) and (vi), `strip_b w = c_b − ∂ e_b = 0`. So by (v),
  `w` is the image of a chain `q` of `Q`. Since `w` is a cycle and the inclusion is an injective
  chain map, `q` is a cycle.
- By Lemma K and (i), `q = ∂ r`. So `z = ∂(r − Σ_b cons_b e_b)`. ∎

**Theorem V.** For every finite poset `P` on `n` points and every `d ∈ ℕ` with `d + 3 ≠ n`,
`H̃_d(Δ(L̄)) = 0`.

*Proof.* Induction on `n`.

- For `n ≤ 2`, `L̄ = ∅`, so `C_m = 0` for `m ≥ 1`.
- For `n ≥ 3`, pick a minimal `a`. Each `P/π_ab` has `n − 1` points.
  - For `d ≥ 1`, `(d − 1) + 3 ≠ n − 1`, so the induction hypothesis transported along (iii)
    gives the hypothesis of Proposition C.
  - For `d = 0`, `d + 3 ≠ n` forces `n ≥ 4`, so `|P/π_ab| ≥ 3` and `(π_ab, 1̂)` is nonempty
    (`properOP_nonempty`).
- Then Proposition C. ∎

For `n ≥ 3`, `d ≠ n − 3 ⇔ d + 3 ≠ n`. So Theorem V is (V), and §1 gives (D).

*Shadow.* The Euler characteristic of Proposition C is Lemma D (`mu_op_rec`). Route C is the
chain-level lift of the dual-Weisner proof that is already formalized. Lemma C (`eC_rec`, the
bijection on cyclic classes) is **not** needed again: the count reaches `H_P` through
`trace_HP_of_vanishing` and `mu_OP_eq`.

## 4. Computational check (n ≤ 6)

`compute/lean_js_route.py` checks the following for every unlabeled poset with
`1 ≤ n ≤ NMAX` and every minimal `a`:

- `[M]` Lemma M(b) for the partition meet.
- `[Pz]` (i).
- `[inv]` `τ` is a fixed-point-free involution on all chains of `Q`, the empty chain included.
- `[N]` The identity of the Claim in §3.1, with the signs of §3.1, in exact integer arithmetic.
- `[Qac]` `Δ(Q)` has all reduced Betti numbers `0`.
- `[rel]` `β_d(L̄) = Σ_b β_{d−1}((π_ab, 1̂))` for `d ≥ 1`, and Lemma U as a bijection onto the
  proper part of `OP(P/π_ab)`.
- `[JS]` `β_d(L̄) = 0` for `d ≠ n − 3`, and `β_{n−3} = e_C(P)`.

Ranks are taken mod `2^31 − 1`. A rank mod p is at most the rank over ℚ, so a mod-p Betti
number of `0` is `0` over ℚ. When all but one vanish, the remaining one agrees with its value
over ℚ by the Euler characteristic.

Positive controls, each of which must fail somewhere:

- C1: `s` with the opposite sign. Fails `[N]`.
- C2: `π_a` replaced by an arbitrary `z ∈ L̄`, with its meet-complements in place of `A`
  (`n ≤ 5`). Fails the `[rel]` formula, because the complements need not be atoms.
- C3: `Q = L̄`. Fails `[Qac]`.
- C4: `τ(c) = p(max c)`. Fails `[inv]`.

    cd compute
    python3 lean_js_route.py --nmax 6 --procs 3 > output/lean_js_route_n6.txt   # ~55 s
    python3 -m unittest test_lean_js_route

Output (`compute/output/lean_js_route_n6.txt`): 405 posets (1, 2, 5, 16, 63, 318 for
`n = 1..6`) and 915 pairs `(P, a)`. `[M]`, `[Pz]`, `[inv]`, `[N]`, `[Qac]`, `[rel]` and `[JS]`
hold on 405/405. C1 fails on 402 posets, C2 on 79, C3 on 402 and C4 on 397. `ALL CHECKS PASS`.

## 5. Size estimates, calibrated on M1–M3

Lines added under `lean/PosetJKS` (from `git show --numstat`), against the estimates in
`lean/PLAN.md` §1:

| Milestone | Commits | Lines added | PLAN estimate | Ratio |
|---|---|---|---|---|
| M1 (Thm S(a),(b), Ψ, Cor. Ψ.1; `Words`, `Bridge`, `Milestone`) | a7ede35, 22ab5e5, 4571e47, 8842855 | 2,129 | "500 (milestone)" | ≈ 4× over |
| M2 lattice (`OPLattice`, `Interval`) | 89976f8 (part), 73a3324 | 817 | 400–700 | ≈ 1.2–2× over |
| M2 `trace_PLie` (`LieTrace`) | 89976f8 (part) | 181 | ~200 | on target |
| M2 `prop:Lside`, `ECTransport`, Ramanujan | 9756e41, b5dd5f3 | 982 | — | — |
| M2c `mu_OP_eq` (`MuOP`: Lemmas M(b), U, D, C, Thm A) | 5d4a0f0 | 970 | — | — |
| M2 `prop:Mside` (`Mside`) + assembly | a4d621a, cf1e150, 1554145 | 873 | — | — |
| M3b equal characters ⇒ iso, `main_iso` | 6405fad | 456 (361 non-test) | 300–500 | on target |
| M3a Hall + Hopf + `trace_HP` | 17cfb51 | 633 (608 in the three files) | 500–900 | ≈ 0.7–1.2× |

Pattern: linear algebra over chain complexes (Hopf, `TraceHP`, the `∂∂ = 0` proof) came in at or
under estimate. Index-heavy combinatorics of words (M1) ran about 4× over. Route C's Lemma K is
index-heavy: chain insertion and face signs. So its estimate carries a 1.5× margin. The
closest comparators are `MuOP.lean` (970 lines, the Möbius shadow of the same induction, of
which Lemma C is about 500 lines that Route C does not repeat) and `TraceHP.lean` + `Hopf.lean`
(454 lines of chain-complex work in this repo's `Chains`/`bd` setup).

| Route | What is new to formalize | Math written? | Lines | Main risks |
|---|---|---|---|---|
| 1. CL/EL shelling | comodernism of `OP(P)`, CL-labelling, lex shelling, shellable ⇒ concentrated homology | yes ([SW], Björner–Wachs); not re-checked here | 3,000–5,000 | largest; external proof not re-read; lex/label index bookkeeping; no Mathlib support |
| 2. Discrete Morse | algebraic Morse lemma (weak form), patchwork theorem, [JS] Thm 3.8 matching and its acyclicity | yes ([JS] §3, Kozlov, Forman) | 2,000–3,500 | acyclicity of glued matchings; matching defined on all `Fin m ↪o L̄` at once |
| 3. Euler + lower bound | Prop. Φ (Wachs, Ree), Thm S(c) | yes ([CS]) | 1,500+ | **does not prove (V)** (§2.3); off the critical path |
| 4. Restatement | — | — | — | unfaithful (§2.4 (c)) or insufficient (§2.4 (b)) |
| **C. Complementation at `π_a`** | chain-map/transport tools, Lemma K, the decomposition of §3.2, the induction | yes, §3 here (homotopy form: [BW]); computed for `n ≤ 6` | **1,100–1,700** | sign/index work in Lemma K (mitigated: exact signs fixed and checked by `[N]`); transport across `Contr` types (template: `mu_OP_eq_aux`) |

## 6. Recommendation and milestone slices

**Recommended route: C.** It is the cheapest route by a factor of 2–3. Its only new
mathematics is Lemma K and Proposition C (§3), which are short, classical in spirit, and whose
sign-sensitive identity has been checked chain by chain. It reuses `pa`, `pab`, `Contr`,
`pullOP`, `inf_pa_eq_bot_iff'`, `isOrderPreserving_inf`, `range_bd_zero`, `properOP_nonempty`,
`trace_HP_of_vanishing` and `mu_OP_eq` unchanged. The statement of `jencaSarkoci_homology` does
not change.

Each slice ends with `lake build` and a sorry count from
`grep -rn "sorry" lean/PosetJKS`. The count is 1 after S1–S3 and 0 after S4. Each slice adds
positive controls to `Test.lean`, in the style of the existing ones.

**S1. `PosetJKS/ChainTools.lean` — general chain tools (300–450 lines; sorry count stays 1).**
- `chainMapEmb (f : L ↪o L') (m) : Chains L m →ₗ[ℂ] Chains L' m` (`Finsupp.lmapDomain`),
  `bd_chainMapEmb` (commutes with `bd`), and `chainMapEmb_injective`. `chainMap` on `L ≃o L` is
  the special case.
- `subsingleton_redHom_iff : Subsingleton (redHom L d) ↔ ∀ z, bd L d z = 0 → z ∈ range (bd L (d+1))`.
- `subsingleton_redHom_of_orderIso (e : L ≃o L')`, transported in both directions.
- `subsingleton_redHom_of_isEmpty`: `Chains L (d+1) = 0` when `L` is empty.
- Chain insertion `insertAt (c : Fin m ↪o L) (t : L) (j : Fin (m+1))` (via `Fin.insertNth`,
  under the betweenness hypotheses), with the face lemmas
  `face (insertAt c t j) j = c` and
  `face (insertAt c t j) (j.succAbove i) = insertAt (face c i) t (j.predAbove ...)`.
- Control: `redHom` of a two-point antichain is not subsingleton in degree 0.

**S2. `PosetJKS/ConeRetract.lean` — Lemma K (350–550 lines; sorry count 1).**
- The data `t`, `p` with the hypotheses of §3.1, `hcount c` (the number of high elements),
  `tau c`, `s : Chains R m →ₗ Chains R (m+1)`, and the subcomplexes `F k`.
- `bd_s_add_s_bd (c) : bd (s c) + s (bd c) - c ∈ F (hcount c - 1)`, with equality when
  `hcount c = 0`. This is the sign-heavy core. Proceed by the two cases of §3.1, using S1's face lemmas.
- `exact_of_retract : ∀ d, Subsingleton (redHom R d)`, by induction on `k` (§3.1, "Exactness").
- If this slice runs long, split it: S2a is the pure cone (`p ≡ t` on `R = (·, t]`, a sanity
  milestone), and S2b is the general `p`.
- Control: the hypotheses fail for a two-point antichain (no `t`), whose `redHom 0` is nonzero.

**S3. `PosetJKS/Complement.lean` — the decomposition at `π_a` (250–400 lines; sorry count 1).**
- `Q a := {x : ProperOP α // ∀ b, x.1 ≠ pab a b}`, and the retraction `p x = x ⊓ pa a`. Verify
  the hypotheses of Lemma K (§3.2 (i)) from `inf_pa_eq_bot_iff'` and `isOrderPreserving_inf`.
- `pab_minimal` (§3.2 (ii)).
- `strip b`, `cons b`, and the identities (iv)–(vi).
- The order isomorphism `{x : ProperOP α // pab a b < x.1} ≃o ProperOP (Contr a b h)`, from
  `pullOP` and the surjectivity argument already inside `mu_pab_top`.
- `propC` (Proposition C), in the two forms `d ≥ 1` and `d = 0`.

**S4. `PosetJKS/JSHomology.lean` and closing the sorry (150–250 lines; sorry count 1 → 0).**
- `vanish_aux : ∀ n (β) [..], Fintype.card β = n → ∀ d, d + 3 ≠ n → Subsingleton (redHom (ProperOP β) d)`,
  by strong induction with a minimal `a`, as in `mu_OP_eq_aux`.
- `actHP_one : actHP (1 : α ≃o α) = LinearMap.id`, and `finrank_HP` (§1).
- Replace the `sorry` in `MainTheorem.jencaSarkoci_homology` by these two results.
- Rerun `scripts/CheckDeps.lean` and `scripts/PrintAxioms.lean`. Expect no `sorryAx` anywhere,
  and `main_iso` depending only on `propext`, `Classical.choice` and `Quot.sound`.
- Update `lean/PLAN.md` §1, §4 and §5.

Optional and parallel: an independent audit of §3 before S2 starts. The numerical `[N]` check
covers the sign identity but not the Lean-level indexing.

## 7. Not checked

- [BW] and [SW] are cited from memory or from [Lit]. Neither was re-read. Route C does not
  depend on them.
- The Mathlib API names in S1 (`Fin.insertNth` and its `succAbove`/`predAbove` lemmas) were not
  grepped against the pinned Mathlib. No Mathlib checkout was available in the worktree.
- The line estimates are estimates. Their only grounding is the table in §5.
