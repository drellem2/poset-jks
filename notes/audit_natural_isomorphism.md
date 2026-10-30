# Audit of the natural-isomorphism note: Theorem Ψ, Theorems 1–2

Work item: mg-583e6. Audited: `notes/natural_isomorphism.md` (the "note") and
`compute/natural_isomorphism.py` (the "note's script"), as merged in b85ac7a
(mg-2d2b3). Nothing in either was changed.

Every claim below is tagged PROVEN, COMPUTED, CITED or CONJECTURED. My own
code is `compute/audit_natural_isomorphism.py`. It imports no module of this
repo. Posets, linear extensions, components, cuts, shuffles, combs and rank
arithmetic are all re-implemented there.

## Verdict

**Theorem Ψ: HOLDS.**
- I re-derived the weighted contraction induction step by step (§2) and found
  no gap. One sub-step is stated loosely in the note, and §2.2 gives a
  cleaner route to it.
- Corollary Ψ.1 (ψ_P : L_P → M_P is an Aut(P)-isomorphism for every P) holds.
  It is **elementary**: it uses only Lemma 1, Lemmas 2–4 and Theorem B of the
  Conjecture S note, not (Φ), (D) or (JS).
- Theorem 2 (Θ_P = ψ_P^{−1} ∘ Φ_P) holds given (Φ), (D) and (JS), as the note
  labels it.
- Independent computation confirms invertibility for all 1 + 2 + 5 + 16 + 63
  + 318 unlabeled posets with n ≤ 6:
  - λ ≡ ζ, for every primitive n-th root ζ, at two primes;
  - three random admissible weight vectors per poset.

**Θ escapes Prop. C / C′ legitimately.** It is not the restriction of any one
ambient map: its P-dependence is the truncation pr_P. This P-dependence is
exactly what makes Θ fail extension-naturality on disconnected posets (§3).

**"R_P e_ζ = 0 ⇔ P connected": HOLDS**, with the note's qualifier "or n ≤ 2".
That qualifier is needed: the 2-antichain has R_P e_ζ = 0.

**One defect, in the note's computational evidence. It does not affect the
theorem.**
- The note's `[wgt]` check, and the sentence "[λ ≡ 1] also drops for 63 of the
  80 disconnected posets at n = 6", are computed on a wrong object.
- The script takes as class representative the lexicographically least
  rotation, and that word need not lie in Lin P. The true count is **80/80**.
  In fact the rank drop at λ ≡ 1 is PROVEN for every disconnected P (§5).

## Claim table

| # | Claim in the note | Note's label | Audit verdict |
|---|---|---|---|
| 1 | Lemma Ψ.0: s_λ(wγ^m) = λ(w_1⋯w_m) s_λ(w) at cuts | PROVEN | **HOLDS.** Re-derived (§2.1). COMPUTED `[psi0]`: 1926 cases, n ≤ 5. |
| 2 | Theorem Ψ: for admissible λ, the class sums s_λ(C) are independent mod Sh | PROVEN | **HOLDS.** Re-derived (§2). COMPUTED `[psi]`, n ≤ 6, all posets. |
| 3 | Step-1 claim: E_{a,x} s_λ(v) = ±s_{λ′}(v∖x), with λ′ admissible on Q | PROVEN | **HOLDS.** COMPUTED `[con]`: 13 624 cases, n ≤ 5. Control: the wrong weight λ′(a) = λ(a) breaks it in 298/1096 cases. |
| 4 | Cor. Ψ.1: ψ_P = (pr_P mod Sh) is an Aut(P)-isomorphism L_P → M_P for every P | PROVEN | **HOLDS, unconditionally.** It needs no (Φ), (D), (JS) (§2.4). COMPUTED `[psi]`, `[equi]`. |
| 5 | Theorem 2: Θ_P is an Aut(P)-isomorphism commuting with relabelings; explicit Θ_P^{−1} | PROVEN given (Φ),(D),(JS) | **HOLDS** with that label. The inverse formula and the sign (−1)^{(n−1)k} are re-derived. |
| 6 | Theorem 2 gives a proof of eq. (mainconj) without the character identity | PROVEN given (Φ),(D),(JS) | **HOLDS.** Its inputs are those of Conjecture S. |
| 7 | "Θ is relabeling-natural / canonical, no choices" | — | **HOLDS, in a precise and limited sense** (§3.1). Θ is a natural isomorphism on the groupoid 𝒢, given by one P-uniform recipe. It is not natural on ℰ. The choice of ζ is the one already made in defining Lie(P). |
| 8 | Θ does not contradict Prop. C / C′ | implicit | **HOLDS** (§3.2). COMPUTED `[prc]`: Θ fails extension-naturality along some P → C_w for 2/2, 6/6, 19/19, 80/80 disconnected P (n = 3..6). |
| 9 | Theorem 1(i): any η_P compatible with all chain extensions P → C_w is non-injective when P is disconnected and n ≥ 3 | PROVEN given (Φ),(D) | **HOLDS** (§4). COMPUTED `[ext]`: witness coefficient exactly 1/n in 14 + 100 + 802 + 7542 cases, n = 3..6. |
| 10 | Theorem 1(ii): on connected P, ρ_w⊗1 ↦ sgn(w) we_ζ is natural on the connected subcategory, unique up to c_n | PROVEN | **HOLDS** (§4). |
| 11 | R_P e_ζ = 0 ⇔ (P connected or n ≤ 2) | PROVEN + COMPUTED | **HOLDS.** COMPUTED `[ext]`: all posets n ≤ 6, at two primes. |
| 12 | Cor. Ψ.2: C[S_n]e_ζ ∩ Sh_n = 0; ·e_ζ is injective on Lie_n; hence Klyachko | PROVEN (uses Ree) | **HOLDS.** COMPUTED `[lie]`: rank Lie_n e_ζ = (n−1)! for every primitive ζ, n ≤ 6. **Novelty:** see §6. |
| 13 | Prop. 3 (ordinal sums): compatible families exist but are non-canonical; incompatible with any family that is identity-on-connected | PROVEN | **HOLDS** by re-reading. Minor notation issue: in q^L, "ue_ζ" must use a primitive \|P\|-th root, not the n-th. Not recomputed. |
| 14 | Prop. 4 (restriction / deconcatenation / cobracket on the e_ζ side) and the M-side cobracket | PROVEN + COMPUTED | **HOLDS** by re-reading, including the tensor-intersection step left implicit in the note (§4.3). Not recomputed. |
| 15 | §3.3: φ_Σ is Aut-equivariant; invertible for disconnected P, n ≤ 6 | PROVEN / COMPUTED | Invertibility re-COMPUTED for n ≤ 5 (`[sum]`: 1 + 2 + 6 + 19 posets). n = 6, the size-weighted variant, equivariance and `[dyn]` were not re-run. |
| 16 | Conjecture 3.3 (φ_Σ invertible for all P) | CONJECTURED | **Correctly labeled.** |
| 17 | `[wgt]`: random admissible weights give independence "2 draws per poset, n ≤ 6" | COMPUTED | **The script tests the wrong object** on posets whose least rotation is not in Lin P (§5). The statement itself is confirmed by my `[psi]`, which uses the correct class sums. |
| 18 | "λ ≡ 1 … drops for 63 of the 80 disconnected posets at n = 6" (and 5/6, 16/19 at n = 4, 5 in the archived output) | COMPUTED | **WRONG.** The drop occurs for **all** disconnected P. It is PROVEN (§5) and COMPUTED 2/2, 6/6, 19/19, 80/80. The wrong numbers come from the defect in row 17. |
| 19 | `[psi]` at n = 7 (2045 posets) | COMPUTED | Not re-run; my enumerator stops at n = 6. The note's `[psi]` code (unlike `[wgt]`) uses the correct class sums (§5). |

## 1. Objects and conventions

These are the note's §0 conventions, re-checked against `poset_jks_check.py`:
- the product is composition;
- wγ^k is the left rotation by k;
- e_ζ = (1/n) Σ_j ζ^{−j} γ^j, so wγ^k e_ζ = ζ^k we_ζ.

Further definitions:
- L_P = Lie(P) = span{we_ζ : w ∈ Lin P}. This agrees with eq. (posetLie) of
  the seed note.
- M_P = W_P/(W_P ∩ Sh_n) = W_P/R_P, using Theorem B of the Conjecture S note,
  which is elementary.
- pr_P : C[S_n] → W_P is the coordinate truncation.

Two facts used throughout (PROVEN):
- **Cuts and classes.** By Lemma 4 of the Conjecture S note, wγ^k ∈ Lin P iff
  k is a cut. So pr_P(we_ζ) = (1/n) Σ_{k cut} ζ^{−k} wγ^k = s_ζ(w)/n, with
  λ ≡ ζ, where λ(w_1⋯w_k) = ζ^k.
  - COMPUTED `[cut]`: Lemma 4 holds in 75 414 cases (P, w, k), n ≤ 6.
- **L_P has basis {w_C e_ζ}.** If w and wγ^j are both in Lin P, then j is a
  cut. So distinct classes lie in distinct rotation orbits. Each we_ζ is
  nonzero and supported on its orbit. Hence dim L_P = e_C(P) = dim M_P.
  - COMPUTED `[psi]`: dim M_P = e_C = dim L_P for all 404 posets with
    2 ≤ n ≤ 6.

## 2. Theorem Ψ, step by step

### 2.1 Lemma Ψ.0 and well-definedness

Let w′ = wγ^m with m a cut, V = {w_1, …, w_m}, and z = wγ^k with prefix set U.
- If k ≥ m, then z = w′γ^{k−m} and its w′-prefix is U∖V. The phase is
  λ(U∖V)^{−1} = λ(V)λ(U)^{−1}.
- If k < m, then z = w′γ^{n−m+k} and its w′-prefix is (A∖V) ∪ U. The phase is
  λ(A)^{−1}λ(V)λ(U)^{−1}, which equals λ(V)λ(U)^{−1} because λ(A) = 1.

Both cases agree with λ(V)·(the phase of z in s_λ(w)). This is exactly where
λ(A) = 1 is used. ∎

**Well-definedness of ψ_P and Θ_P.**
- ψ_P(y) = pr_P(y) + Sh is a function of the element y ∈ C[S_n], not of a
  representative. So no choice enters.
- pr_P(y) ∈ W_P, and W_P ∩ Sh = R_P. So the image is a well-defined element
  of M_P = W_P/R_P.
- This answers the question "well defined modulo R_P?": **yes**, trivially.

### 2.2 The induction (n ≥ 3)

Let X = Σ_C c_C s_λ(C) ∈ Sh_A. The note's c̃(v) is simply **the coefficient
of v in X**, because s_λ(v) has coefficient 1 at v. Lemma Ψ.0 then gives the
twisted relation (Ψ.1): c̃(v) = λ(v_1⋯v_m) c̃(vγ^m) at every cut m.

**Step 1.** The note groups X by Q-classes and applies the per-class claim
E(s_λ(v)) = ±s_{λ′}(v∖x). That is correct (COMPUTED `[con]`). A shorter route
avoids the class bookkeeping entirely; I checked it independently.
- By (★) of the Conjecture S note,
  E_{a,x}(X) = Σ_{v′∈Lin Q} d(v′)v′, where d(v′) = c̃(v′[a→xa]) − c̃(v′[a→ax]).
- **d satisfies the twisted relation for (Q, λ′).**
  - Let m′ be a Q-cut of v′ with prefix U′, and let v₁ = v′[a→xa].
  - The pullback of U′ is a union of P-components containing both a and x or
    neither (Lemma 2(c)). So it is a P-cut of v₁ (when v₁ ∈ Lin P), of length
    m′ or m′ + 1.
  - The rotation keeps xa adjacent: v₁γ^{m} = (v′γ^{m′})[a→xa].
  - The phase is λ(pullback) = λ′(U′).
  - Membership in Lin P is the same for v₁ and its rotation. By Lemma 2(b),
    w′[a→xa] ∈ Lin P iff not a <_P x, independently of w′ ∈ Lin Q, and
    v′γ^{m′} ∈ Lin Q.
  - The same argument works for ax.
- A coefficient function on Lin Q with the twisted relation is
  Σ_{C′} d(v′_{C′}) s_{λ′}(v′_{C′}).
- **λ′ is admissible.**
  - λ′(A∖x) = λ(A) = 1.
  - A nonempty proper union U′ of Q-components pulls back to a nonempty proper
    union U of P-components, and λ′(U′) = λ(U) ≠ 1.
- By Lemma 1 (PROVEN in the Conjecture S note, and audited in
  `notes/audit_conjecture_s.md`), E_{a,x}(X) ∈ Sh.
- The induction hypothesis for (Q, λ′), on n − 1 ≥ 2 letters, gives d ≡ 0 on
  Lin Q. That is (Ψ.2).

**Step 2.**
- For w ∈ Lin P with y = w_i, z = w_{i+1}, take x = y, a = z, v′ = w∖y ∈ Lin Q
  (Lemma 2(a)). Then (Ψ.2) reads c̃(w) = c̃(w with y, z swapped).
- The swapped word is in Lin P iff y ∥ z. Otherwise c̃(w) = 0, since c̃ is
  extended by 0.
- By Lemma 3, c̃ is constant on Lin P.
- **Disconnected P:** a proper cut exists, and (Ψ.1) gives c = λ(U)c with
  λ(U) ≠ 1.
- **Connected P:** an adjacent cover gives c = 0.

**Base cases.**
- n = 1: Sh = 0.
- n = 2: the chain has a single word, and single words are not in Sh. The
  antichain has s = xa + λ(x)^{−1}ax ∉ C(xa + ax), because λ(x) ≠ 1.
- n ≥ 3 is needed in Step 1 only so that the one rotation separating x from a
  (which begins with a and ends with x) is not linearly adjacent. With the (★)
  route this point is automatic.

No gap.

### 2.3 Where admissibility is used, and that it is needed

Admissibility is used in three places:
- λ(A) = 1 in Lemma Ψ.0;
- λ(U) ≠ 1 in the n = 2 base case and at the end of Step 2;
- inheritance by λ′.

It cannot simply be dropped. COMPUTED `[ctl]`:
- λ ≡ 1 drops the rank on the antichain for n = 2..6, and in fact on every
  disconnected P (§5);
- a root of unity of non-primitive order d | n drops the rank for 3 posets at
  (n, d) = (4, 2), 30 at (6, 2) and 15 at (6, 3).

### 2.4 Corollary Ψ.1 is elementary

- **Injectivity:** ψ_P(w_C e_ζ) = s_ζ(C)/n, and Theorem Ψ applies.
- **Surjectivity:** dim L_P = e_C(P) = dim M_P, by Lemma 4 and Theorem B.

Neither (Φ) nor (D) nor (JS) appears. So L_P ≅ M_P as Aut(P)-modules is
PROVEN outright. (Φ), (D) and (JS) enter only through Φ_P : H_P ⊗ sgn ≅ M_P
(Cor. 5.5 of the Conjecture S note).

**Equivariance and the sign twist.**
- ψ_P has no sign twist: both L_P and M_P carry the left-multiplication
  action.
  - Aut(P) permutes Lin P, so pr_P(gy) = g pr_P(y).
  - Sh is S_n-stable.
  - COMPUTED `[equi]`: 19 694 cases, n ≤ 5.
- The twist lives entirely in Φ_P(ρ_w ⊗ 1) = sgn(w) w̄:
  g(ρ_w ⊗ 1) = sgn(g) ρ_{gw} ⊗ 1 ↦ sgn(g) sgn(gw) gw̄ = g·(sgn(w) w̄).
- **Θ_P^{−1} formula:** Φ_P^{−1}(v̄) = sgn(v) ρ_v ⊗ 1, and
  sgn(wγ^k) = sgn(w)(−1)^{(n−1)k}, since γ is an n-cycle. This matches the
  note.

## 3. What "relabeling-natural" means, and why Θ escapes Prop. C

### 3.1 The precise sense

- Let 𝒢 be the groupoid of posets on [n] and relabelings (note §1.1). Then Θ
  is a natural isomorphism of functors on 𝒢:
  Θ_{σP}(σ·h) = σ·Θ_P(h).
  - This holds because pr_{σP}(σy) = σ pr_P(y): Lin(σP) = σ Lin P. COMPUTED
    `[equi]` with a random σ per poset.
  - Φ is S_n-equivariant after the twist.
- As the note itself says (§1.1), naturality on 𝒢 alone is contentless. Any
  Aut-isomorphism chosen per isomorphism class and transported is natural on
  𝒢.
- The real content of Theorem 2 is that the isomorphism is given by **one
  recipe, uniform in P, involving no choice of representative, base
  component or basis**: "truncate to Lin P, read mod Sh, apply Φ^{−1}".
  That claim is correct, with two caveats:
  - "canonical" here is an informal notion, not a functorial one;
  - the recipe depends on ζ, exactly as Lie(P) itself does.
- Θ is **not** natural on the extension category ℰ. The note says so, and
  Theorem 1(i) shows nothing can be.

### 3.2 Why Θ is not a uniform J (no contradiction with Prop. C / C′)

Prop. C forbids a single linear J on the ambient space with
J(H_P ⊗ sgn) = W_P e_ζ for all P. Prop. C′ forbids an S_n-equivariant J
doing this even for one chain.

**Θ is not of this form.** Suppose J|_{H_P} = Θ_P held for all P with one J.
- For the chain C_w, Θ_{C_w}(ρ_w ⊗ 1) = n·sgn(w) we_ζ, since a chain has one
  class and one cut.
- For any disconnected P ∋ w, compatibility would force
  Θ_P(ρ_w ⊗ 1) = n·sgn(w) we_ζ, i.e. pr_P(we_ζ) − w/n ∈ Sh.
- This fails for some w ∈ Lin P, for **every** disconnected P with n ≤ 6.
  COMPUTED `[prc]`: 2/2, 6/6, 19/19, 80/80.
- It must fail for every disconnected P with n ≥ 3: otherwise the family
  would be extension-natural along all P → C_w, contradicting Theorem 1(i).

So the P-dependence of Θ lies precisely in the truncation pr_P. As a family,
{Θ_P} is not the restriction of any one map. Each Θ_P is only
Aut(P)-equivariant. That is exactly the "Aut(P)-equivariant J_P" case that the
audit of the literature note (§1.3) lists as *not* refuted.

**The obvious uniform candidate fails.** The map
q : y ↦ y mod Sh is S_n-equivariant and, by Cor. Ψ.2, injective on
C[S_n]e_ζ. But it sends L_P onto M_P for only 4/5, 6/16, 8/63 and 10/318
posets (n = 3..6), and never for a chain. COMPUTED `[prc]`. This is Prop. C′
seen from the M side.

The difference between ψ_P and q is the off-Lin-P part of we_ζ, which ψ_P
discards.

## 4. Theorem 1 and the "iff connected" characterization

### 4.1 Theorem 1(i)

- H_{C_w} = Cρ_w, so η_P(ρ_w ⊗ 1) = c_w we_ζ.
- For a nonempty proper union S of components, name the parts so that
  |T| ≥ 2. This is possible because n ≥ 3.
- Then Σ_{z∈sшt} sgn(z) ρ_z = 0 by (Φ), since s ш t ⊆ Lin P.
- Take u = t_1 s t_2⋯t_b. Every proper rotation of u puts some t_k (k ≥ 2)
  before t_1:
  - a rotation starting inside s does so, and this uses s ≠ ∅;
  - a rotation starting at t_k does so.
  So no proper rotation of u lies in s ш t, and the coefficient of u is
  sgn(u)c_u/n.
- Hence c_u = 0. But ρ_u ≠ 0, because u ∉ Sh by (Φ).

The proof is correct. It uses (D) only through H_{C_w} ⊆ H_P.

### 4.2 Theorem 1(ii), (iii), and R_P e_ζ = 0 ⇔ (connected or n ≤ 2)

- **Connected P:** R_P = 0 by definition, since there is no nonempty proper
  union of components. W_P ∩ Sh = 0 is Cor. A′. Single-word classes give the
  basis {we_ζ}.
- **Uniqueness up to c_n:**
  - chains force η_P(ρ_w ⊗ 1) = c_w we_ζ;
  - naturality under relabelings of chains forces c_{σw} = sgn(σ) c_w.
  Correct.
- **⇐ of the characterization:** connected P gives R_P = 0. For n = 2,
  (01 + 10)e_{−1} = 0; COMPUTED (unit test).
- **⇒:** the same witness u as in §4.1, without signs, gives coefficient 1/n.
  COMPUTED exactly 1/n in every one of 8458 cases (P, S, s, t) with
  3 ≤ n ≤ 6, and R_P e_ζ ≠ 0 at both primes.
- The qualifier "or n ≤ 2" is necessary. The ticket's paraphrase "iff P is
  connected" omits it, but the note states it correctly.

### 4.3 Props. 3 and 4 (re-read only)

**Prop. 3(i).**
- Aut(R) = Π Aut(R_i), because the ordinal decomposition is canonical and
  its order is preserved.
- R_{R_i} ≅ W ∩ K_ζ as Aut-modules, by Cor. Ψ.1 and Maschke.
- The squares commute by linearity.

**Prop. 3(ii).**
- With R = P ⊕ 1, compatibility forces η_P(ū) = c′ ue_ζ.
- This is ill-defined because R_P e_ζ ≠ 0.
- The argument is unaffected if c depends on n. This is the relevant case for
  Θ, where the constant is n on connected posets.

**Prop. 4, M side.**
- Δ̄(u ш v) ≡ u ⊗ v + v ⊗ u mod (Sh ⊗ T + T ⊗ Sh). I checked this term by
  term: every other term has a proper shuffle in one tensor factor.
- Descent to M_P ⊗ M_Q needs
  (Sh ⊗ T + T ⊗ Sh) ∩ (W_P ⊗ W_Q) = R_P ⊗ W_Q + W_P ⊗ R_Q.
  This holds because over a field the kernel of U ⊗ V → U/(A∩U) ⊗ V/(B∩V)
  is (A∩U) ⊗ V + U ⊗ (B∩V).
- The note leaves this step implicit. It is fine.

## 5. The defect in the note's `[wgt]` check (and the 63/80 figure)

**The defect.** `natural_isomorphism.py`, `weighted_rank` (≈ line 529):
- It takes class representatives from `pj.cyclic_classes(lin)`, which returns
  `min(rot(w, j))`, the least rotation of the word.
- That word is often **not** in Lin P.
- It then sums the λ-twisted rotations of that representative at its own
  union-prefix cuts. For such posets this is not s_λ(C): the k = 0 term is
  the representative itself, which lies outside Lin P.

**Consequences.**
- The `[wgt]` "independent 636/636" line does not test Theorem Ψ on those
  posets.
- The λ ≡ 1 control counts (5/6, 16/19, 63/80) are wrong.
- Diagnostic (COMPUTED, run from `compute/`, importing the note's script for
  diagnosis only): the 17 disconnected posets at n = 6 for which the note's
  code reports no drop **all** have some class whose least-rotation
  representative lies outside Lin P. There are 55 disconnected posets at
  n = 6 with such a representative, so the defect is necessary for a missed
  drop but does not always cause one. The posets without the defect all
  drop, as they must. The command is in Reproduce.
- The note's `[psi]` check is **not** affected. It sums over w ∈ Lin P with
  phases relative to the representative, which changes each class sum only by
  a scalar.

**Correct statement (PROVEN).** For every disconnected P, the λ ≡ 1 class sums
are dependent mod Sh.
- Proof: Σ_C s_1(C) = Σ_{w∈Lin P} w. Write P = P_1 + P′ with P_1 a component.
  Then Lin P is the disjoint union of the shuffle sets s ш t over
  s ∈ Lin P_1, t ∈ Lin P′, so the sum lies in Sh.
- So the note's remark "though admissibility is only sufficient" is
  misleading as applied to λ ≡ 1. That inadmissible λ always fails.
- COMPUTED: 2/2, 6/6, 19/19, 80/80 for n = 3..6 (my `psi_rank`, and the unit
  test for n ≤ 4).

Recommended fix (not applied): replace the representative by a member of the
class lying in Lin P (as `[psi]` effectively does), and correct the 63/80
sentence in the note's §3.2.

## 6. Cor. Ψ.2 and novelty (light check)

The mathematics holds:
- C[S_n]e_ζ ∩ Sh = 0 is the antichain case of Theorem Ψ.
- Injectivity of ·e_ζ on Lie_n follows by the dimension/duality argument with
  Lie_n^⊥ = Sh_n (Ree, CITED in the Conjecture S note).
- COMPUTED `[lie]`: n ≤ 6, every primitive ζ, two primes.

Novelty (one web search, not a literature review):
- Klyachko's theorem has several known proofs: Klyachko 1974,
  Kraśkiewicz–Weyman, and Jöllenbeck–Schocker (2000, a Lie-idempotent
  approach). A cyclic-sieving proof is in arXiv:1808.06043.
- I found no proof via contraction operators modulo shuffles.
- The antichain case of Theorem A (independence of Lyndon-type words mod
  shuffles) is classical, so Cor. Ψ.2 is plausibly folklore-adjacent.

**Verdict:** the note's "Novelty: unclear … likely known in some form" is the
appropriate label. Nothing stronger should be claimed without an expert or a
library search.

## 7. Reproduce

Run from `compute/`:

    python3 audit_natural_isomorphism.py --nmax 6 > output/audit_natural_isomorphism.txt   # ~40 s, exit 0
    python3 -m unittest test_audit_natural_isomorphism

- The first command ends with `ALL CHECKS PASSED`. Its output is archived at
  `compute/output/audit_natural_isomorphism.txt`.
- Options: `--nsh` (default 5) is the range of the Ree-free check that comb
  pairing has kernel exactly Sh_n. `--ncon` (default 5) is the range of the
  Step-1 contraction check. `--nsum` (default 5) is the range of the φ_Σ
  check.

Diagnostic for §5. This one imports the note's script, read-only:

    python3 -c "
    import natural_isomorphism as N, poset_jks_check as pj, audit_natural_isomorphism as A
    ps=A.enumerate_posets(6); p=N.P1; bad=mis=0
    for r in ps[6]:
      if len(A.components(r,6))<2: continue
      lin=set(pj.linear_extensions(r,6))
      rk,e=N.weighted_rank(r,6,[1]*6,p)
      if rk==e: bad+=1; mis+=any(x not in lin for x in pj.cyclic_classes(lin))
    print(bad, mis)"          # prints: 17 17

Rigour:
- Arithmetic is modulo p ∈ {1000000021, 3000000361}, both ≡ 1 (mod 60), with
  ζ of exact order n mod p.
- Full rank mod p implies full rank over Q(ζ). So `[psi]`, `[lie]` and `[sum]`
  are proofs for the stated n.
- A nonzero coordinate certifies non-vanishing. This covers `[ext]` for
  disconnected P, and `[prc]` (ii) and the chain case.
- Vanishings are evidence only. They are checked at both primes, and the ones
  used are PROVEN anyway.
- Membership in Sh is tested by pairing with the (n−1)! left combs. For
  n ≤ 5, `[sh]` re-proves without Ree that this pairing has kernel exactly
  Sh_n: the combs kill every proper shuffle, have rank (n−1)!, and the proper
  shuffles span dimension n! − (n−1)!. At n = 6 this rests on Ree (CITED).

Positive controls:
- λ ≡ 1 and non-primitive roots drop the rank;
- the wrong contraction weight is rejected;
- a single word is not in Sh, while 0 ш 12 is;
- (01 + 10)e_{−1} = 0;
- the uniform map q fails on chains.
