# Linear-extension statistics from the poset Lie machinery: a survey

Question (Daniel, 2026-10-31): which identities on statistics of Lin(P)
(des, maj, inv, sign-imbalance, P-partition generating functions,
q-analogues) follow from the machinery of this repository, and are any of
them new? We ignore Aut(P) and symmetry except where they give an identity
valid for every P. Every claim is tagged **PROVEN**, **COMPUTED**,
**CITED** or **OPEN**. Prior art is reported as a search result:
**KNOWN**, **KNOWN IN SUBSTANCE** or **NOT FOUND**. NOT FOUND is not a claim
of novelty. The code is `compute/linext_statistics.py`. Bracketed tags such
as `[omegaC-f]` are line labels in `compute/output/linext_statistics.txt`.

Tags: [Thm] = `notes/poset_jks_theorem.tex`; [GT] = `notes/general_theory.md`;
[ME] = `notes/mu_op_elementary.md`; [LE] = `notes/linear_extensions.md`;
[Nat] = `notes/natural_isomorphism.md`; EC1 = Stanley, *Enumerative
Combinatorics* vol. 1, 2nd ed.; [Sta05] = R. P. Stanley, *Some remarks on
sign-balanced and maj-balanced posets*, Adv. Appl. Math. 34 (2005) 880–902,
arXiv:math/0211113.

Audits and prior art: [AudLS] = `notes/audit_linext_statistics.md` (the
independent audit of this note); [H] = `notes/h_vector_omega_c.md`
(Theorem H, the h-vector of Ω_C); [AudH] = `notes/audit_h_vector_omega_c.md`
(its independent audit); [PA] = `notes/prior_art_linext_statistics.md` (the
prior-art check of Theorem Ω, Corollary Ω-des and Theorem H). Inside [PA]:
[DMR] = Develin–Macauley–Reiner, *Toric partial orders*, arXiv:1211.4247;
[AGRR] = Adin–Gessel–Reiner–Roichman, *Cyclic quasi-symmetric functions*,
arXiv:1811.05440; [Pet] = T. K. Petersen, *Cyclic descents and
P-partitions*, arXiv:math/0405479; [ARR] = Adin–Reiner–Roichman, *On cyclic
descents for tableaux*, arXiv:1710.06664.

**Audit status.** [AudLS] re-derived every proof and recomputed every
number with independent code. Theorem Ω, Corollary Ω-des, the three
refutations (§1.3, §3, §4) and Propositions 3, 3′ and 4 all HOLD, and no
claim fails. These are tagged **PROVEN + audited** below. Not covered by
the audit: Proposition 1 (KNOWN, EC1), §5, §6 and the B_P control counts
708 and 811 of §2.2.

## Verdict

**The machinery gives one identity that we did not find in the literature,
Theorem Ω (with its descent expansion, Corollary Ω-des, and its h-vector,
Theorem H of [H]). Everything else it gives about statistics is P-partition theory
we already know, or follows from the word combinatorics of disjoint unions.**
The argument has three parts.

1. *All of the theory's numerical content is e_C and the Möbius function of
   OP(P).* For connected P, e_C = e, and PLie(P) = C[Lin P] is the regular
   module, so it carries no statistic ([LE] §§3.1, 4). For disconnected P,
   pattern coordinates ([LE] §0, Prop. F, Thm M) reduce everything to
   shuffles of the components. Shuffles carry exactly the q-multinomial
   statistics of MacMahon, and those are classical.
2. *The theory does have one grading that [LE] §3.1 did not consider.* This
   is the number of blocks |π| on OP(P), which is the face dimension on the
   cone C_P. [LE] §3.1 is right that H_P and PLie(P) have no grading or
   q-deformation, so that claim stands, but its scope is H_P and PLie(P)
   only. The rank grading of OP(P) carries descent information, through
   P-partitions:
   - Read from 0̂ (the face numbers), it gives Stanley's order polynomial and
     the des-distribution on Lin P (§1, KNOWN).
   - Read from 1̂ (the Möbius values μ(π, 1̂)), it gives a "cyclic order
     polynomial" Ω_C(P, m) (Theorem Ω, §2, PROVEN + audited, NOT FOUND for
     general P). Its leading coefficient is e_C(P)/n!, and it is a
     P-partition refinement of the basis count |B_P| = e_C(P).
   - Its h-vector is the cyclic-descent distribution on the rotation
     classes of Lin P, under a separated natural labelling (Theorem H of
     [H], PROVEN + audited in [AudH], NOT FOUND for general P). So it is
     nonnegative.
3. *The four leads.*
   - Kraskiewicz–Weyman: only the dimension-level statement survives, and
     only for prime n, by a folklore rotation lemma (§3).
   - The characteristic polynomial at t = −1 is **not** e(P); only the
     lineality-restricted sum is (§1.3).
   - Sign-imbalance is unrelated to μ(OP(P)) (§4).
   - The descent algebra cannot act on PLie(P) (§5).

| # | Identity | Status | Prior art |
|---|---|---|---|
| 1 | Face numbers of C_P: w_k = Σ_{\|π\|=k} e(Q_π), so Ω(P,m) = Σ_π e(Q_π) C(m,\|π\|) = Σ_{w∈Lin P} C(m+n−1−des w, n) | PROVEN; COMPUTED n ≤ 7 `[faces]` | KNOWN (EC1 §3.15) |
| 1′ | Euler step of [GT] Thm 2 = Lemma W = Ω(P,−1) = (−1)^n[P antichain] | PROVEN ([ME]) | KNOWN (Stanley reciprocity at m = 1; already noted in [ME]) |
| 2 | **Theorem Ω**: Σ_{π∈OP(P)} \|μ(π,1̂)\| C(m,\|π\|) = #{f: P→[m] order-preserving, every upper level set that is a nonempty union of components contains T} | **PROVEN + audited** ([AudLS] §1); COMPUTED n ≤ 6, m ≤ 3, every T `[omegaC-f]`; recomputed in [AudLS] as an identity of polynomials, all 405 posets n ≤ 6, every T | NOT FOUND (general P; [PA]). It is not a toric order polynomial of [DMR]/[AGRR] (leading coefficient, and numerically). KNOWN for the antichain ([Pet] Prop. 1.1, credited there to Fulman; §2.3) |
| 2′ | Descent expansion of Ω_C (Corollary Ω-des) | **PROVEN + audited** ([AudLS] §2); COMPUTED: all natural labellings for n ≤ 5, canonical labelling for n ≤ 7 `[omegaC-des]`; all natural labellings for n ≤ 6 in [AudLS] | NOT FOUND ([PA]) |
| 2″ | h-vector of Ω_C: under a separated natural labelling, h_C(P)_j = #{rotation classes κ of Lin P : cdes κ = j + 1}, so h_C(P) ≥ 0 (**Theorem H** of [H]) | **PROVEN + audited** ([H] §2, [AudH]); COMPUTED n ≤ 7 `[omegaC-h]` and in [H], [AudH], [PA] | NOT FOUND (general P; [PA]). KNOWN for the antichain ([Pet] Prop. 1.1, after Fulman). The statistic is Cellini's cyclic descent number. h_C is not an [ARR] cyclic-descent-extension distribution |
| 2‴ | The quasisymmetric lift K_{C,T}(P) of Ω_C is F-positive, for every component T | **PROVEN (Theorem Q)** + audited (Corollary F+ of `notes/qsym_refinement_omega_c.md`; `notes/audit_qsym_refinement_omega_c.md`); COMPUTED n ≤ 7 | **KNOWN IN SUBSTANCE (Gessel–Stanley)**: the fundamental lemma of P-partitions with the anchor labelled last. The criterion (E*_T) of Theorem Q is NOT FOUND, and elementary |
| 2⁗ | **Theorem R** (reciprocity): (−1)^n Ω_C(P, −m) = #{f : P → [m] strictly order-preserving, no T-free union of components U has min f(U) ≥ max f(P ∖ U)} (the strict anchoring D_T), for every component T | **PROVEN + audited** (`notes/reciprocity_omega_c.md` §2, with Lemmas R1, R2, R′, B⁺, E, S; `notes/audit_reciprocity_omega_c.md`, all hold); COMPUTED on all 3107 (P, T), n ≤ 7 | Polynomial side **KNOWN IN SUBSTANCE**: Stanley's reciprocity is word by word (EC1 Lemma 3.15.9; Grinberg–Reiner Prop. 7.1.7(iii) + 5.2.19), so it applies to the word set B_T. The D_T reading (Lemma R2) **NOT FOUND** (`notes/prior_art_reciprocity_omega_c.md`) |
| 2⁗′ | **★**: Ω_C(P*, m) = Ω_C(P, m), so h_C(P*) = h_C(P) | **PROVEN + audited** (`notes/reciprocity_omega_c.md` §4; audit §3); COMPUTED on 2450 posets | KNOWN IN SUBSTANCE (connected case: the classical Ω(P*) = Ω(P)) |
| 3 | maj(w_2⋯w_n w_1) ≡ maj(w) − cdes(w) (mod n), so for **n prime**, #{u ∈ Lin(P)C_n : maj u ≡ r} = e_C(P) = dim PLie(P) for every r | **PROVEN + audited** ([AudLS] §4); COMPUTED n ≤ 7 `[maj-rot]`, `[maj-rot-closure]`; fails for composite n | KNOWN IN SUBSTANCE (folklore rotation lemma) |
| 3′ | P disconnected and gcd(component sizes) = 1 ⇒ maj is equidistributed mod n on Lin P | **PROVEN + audited** ([AudLS] §4); COMPUTED 485 posets `[maj-equi]` | KNOWN IN SUBSTANCE (MacMahon–Stanley factorisation) |
| 4 | \|I(P)\| = \|[n; m]_{q=−1}\| ∏ \|I(T_i)\| for P = ⊔ T_i; so two odd components ⇒ sign-balanced | **PROVEN + audited** ([AudLS] §4); COMPUTED 503 posets `[sign-union]` | KNOWN IN SUBSTANCE (MacMahon inv-shuffle at q = −1); not found stated in [Sta05] |
| ✗ | (−1)^{n−1} χ_P(−1) = e(P) with χ_P(t) = Σ_{π∈OP} μ(0̂,π) t^{\|π\|−1} | **FALSE**: holds on 6 of 2449 posets (the antichains) `[chi-full]`. Refutation audited ([AudLS] §3; recomputed for n ≤ 6) | — |
| ✗ | #{w ∈ Lin P : maj w ≡ 1 (mod n)} = e_C(P) (KW at dimension level, on Lin P) | **FALSE** on 2443 of 2449 `[maj-KW-dim]`. Refutation audited ([AudLS] §3) | — |
| ✗ | \|I(P)\| = e_C(P) = \|μ(OP(P))\| | **FALSE** on 2443 of 2449 `[sign-ctl-eC]`. Refutation audited ([AudLS] §3) | — |
| ✗ | Descent-algebra / Garsia–Reutenauer action on PLie(P) | PROVEN: PLie(P) is an S_n-module iff PLie(P) = Lie_n iff e_C(P) = (n−1)!; otherwise there is nothing for the descent algebra to act on (§5) | — |

## 0. Conventions

P is a poset on [n] with a natural labelling (x <_P y ⇒ x < y as integers).
OP(P), Q_π, κ, e_C and the cuts, blocks and B_P are as in [ME] §0 and
[LE] §0. OP(P) is ordered by refinement, with 0̂ discrete and 1̂ the single
block. An order-preserving map f : P → [m] satisfies x <_P y ⇒ f(x) ≤ f(y).
Ω(P, m) is the number of such maps. des, maj and inv are taken on words
w = w_1⋯w_n ∈ Lin P, and cdes(w) = des(w) + [w_n > w_1]. The
sign-imbalance is I(P) = Σ_{w∈Lin P} sgn(w). Changing the natural labelling
multiplies every sign by one fixed sign, so |I(P)| depends only on P. The
same holds for the distribution of des and maj over Lin P (EC1 §3.15).

## 1. The face grading: order polynomial and descents (KNOWN)

### 1.1 Face numbers

The faces of C_P are the P-compatible set compositions F : P ↠ [k]
([GT] §1.3, [ME] §3). The proof of Lemma F in [ME] gives a bijection
(σ ∈ OP(P), u ∈ Lin Q_σ) ↔ F with k = |σ|, where u lists the fibres in
order. Hence:

**Proposition 1 (PROVEN; COMPUTED `[faces]`, 2450 posets n ≤ 7, brute
force for n ≤ 6, m ≤ 3; control des ↦ des + 1 refuted everywhere).**

  w_k(P) := #{faces of C_P with k blocks} = Σ_{|π|=k} e(Q_π),
  Ω(P, m) = Σ_k w_k(P) C(m, k) = Σ_{w ∈ Lin P} C(m + n − 1 − des(w), n).

*Proof.* The first equation is the bijection above. The second holds
because an order-preserving map to [m] is a face, together with a choice of
its k values. The third is Stanley's fundamental lemma on P-partitions
(CITED: EC1 Lemma 3.15.3 and Thm 3.15.8; numbers not re-checked). Each f
corresponds to exactly one pair (w, f) with f(w_1) ≤ ⋯ ≤ f(w_n) and strict
inequality at the descents of w. ∎

So the face numbers of C_P, which are the rank sizes of the face poset, are
equivalent to the descent distribution on Lin P (the h-vector of Ω). This is
the "grading the earlier note missed". It is not a grading of H_P.
**Prior art: KNOWN**. It is EC1 §3.15, and the triangulation of the order
cone (or order polytope) by its chambers is Stanley's.

### 1.2 The Euler step is reciprocity at m = 1

The topological step of [GT] Thm 2 is f(Y) = (−1)^{dim Y}[Y ⊆ L]. At Y = R^d
it is [ME] Lemma W: Σ_F (−1)^{k(F)} = (−1)^n [P antichain], which is
Ω(P, −1) = (−1)^n Ω̄(P, 1). [ME] already records this. Applying it to each
quotient Q_π gives [ME] Lemma F. So the Euler-characteristic input of the
cone machinery is exactly Stanley reciprocity at m = 1. **KNOWN**.

### 1.3 Lead 2: the characteristic polynomial at t = −1

Put χ_P(t) = Σ_{π∈OP(P)} μ(0̂, π) t^{|π|−1}, the characteristic polynomial
of Λ(C_P) ≅ OP(P)^op measured from its top. The brief's hypothesis was
that t = −1 gives e(P). This is **FALSE** without the lineality
restriction:
- For the chain C_3, OP(C_3) ≅ B_2, so χ = (t − 1)², and
  (−1)^{n−1}χ(−1) = 4 ≠ 1.
- Over all 2449 posets with 2 ≤ n ≤ 7 it holds only for the 6 antichains,
  where OP = Π_n and this is Zaslavsky's count `[chi-full]`.

The correct statement is [ME] Prop. Z ([GT] Thm 2), which restricts the sum
to σ ≥ κ: (−1)^n e(P) = Σ_{σ≥κ} (−1)^{|σ|} μ(0̂, σ) `[chi-restr]`. For
connected P only σ = 1̂ survives. The other evaluations of the unrestricted
χ_P have no meaning we could find. OP(P) is not the intersection lattice of
an arrangement (it is not even an order ideal of Π_n), so the finite-field
method does not apply to it. Status: **OPEN**, and we do not recommend
pursuing it.

## 2. Theorem Ω: the Möbius values μ(π, 1̂) count P-partitions up to cut rotation

### 2.1 Statement

For a finite poset P on n ≥ 1 points define the **cyclic order polynomial**

  Ω_C(P, m) := Σ_{π ∈ OP(P)} (−1)^{|π|−1} μ_{OP(P)}(π, 1̂) C(m, |π|).

**Theorem Ω (PROVEN + audited in [AudLS] §1; COMPUTED `[omegaC-mu]`,
`[omegaC-f]`).** Fix a
component T of P. For every m ≥ 0,

  Ω_C(P, m) = Σ_{π∈OP(P)} e_C(Q_π) C(m, |π|)
            = #{ f : P → [m] order-preserving : every nonempty upper level set f^{−1}([v, m]) that is a union of components contains T }.

In particular:
- (−1)^{|π|−1} μ(π, 1̂) ≥ 0;
- the count does not depend on T;
- Ω_C(P, m) = Ω(P, m) for connected P;
- Ω_C(P, ·) has degree n and leading coefficient e_C(P)/n!.

*Proof.*
1. *Coefficients.* By [ME] Lemma U, [π, 1̂] ≅ OP(Q_π). By [ME] Theorem A
   applied to Q_π, μ(π, 1̂) = μ(OP(Q_π)) = (−1)^{|π|−1} e_C(Q_π). This gives
   the first equality.
2. *Order-preserving maps as triples.* An order-preserving f : P → [m]
   corresponds bijectively to a triple (σ, u, S). Here σ ∈ OP(P) is the
   partition into nonempty fibres, S ⊆ [m] with |S| = |σ| is the image, and
   u = (F_1, …, F_k) ∈ Lin Q_σ lists the fibres in increasing value. This is
   the bijection in the proof of [ME] Lemma F, followed by a choice of
   values.
3. *Cuts of u are cuts of P.* Let 0 < j < k. Then F_1 ∪ ⋯ ∪ F_j is a union
   of components of Q_σ iff it is a union of components of P.
   - (⇐) If there is no relation of P between this set and its complement,
     then there is no edge of P/σ between these sets of blocks, so no
     relation of Q_σ either.
   - (⇒) If x ∈ F_1 ∪ ⋯ ∪ F_j and y ∉ it are related in P, their blocks are
     related in Q_σ, which contradicts the set being a union of
     Q_σ-components.

   It follows that the blocks of σ meeting T all lie in a single component
   T_σ of Q_σ, because a path of relations inside T crosses between blocks
   only through relations of Q_σ.
4. *One rotation per class.* The cyclic class of u is {u γ^j : j a cut}
   ([LE] §0; [Thm] Lemma `lem:rot`). As in the proof of [GT] Lemma 1.3, the
   class corresponds to the cyclic sequence of the irreducible pieces of u,
   and rotating at a cut rotates that sequence. (Two-line argument, from
   [AudLS] §1: the old piece boundaries are cuts of the rotated word,
   being differences of nested unions of components; and a cut of the
   rotated word strictly inside a piece would give, after adding or
   removing the moved pieces, a cut of u strictly inside that piece.) The
   pieces have pairwise disjoint letter sets. So exactly one member of the class has the piece
   containing T_σ as its last piece. Hence

     e_C(Q_σ) = #{u ∈ Lin Q_σ : the last piece of u contains T_σ}.

5. *Translation.* By step 3, the cuts j of u are exactly the indices for
   which F_{j+1} ∪ ⋯ ∪ F_k is a nonempty union of components of P. That set
   is the upper level set f^{−1}([v, m]), where v is the (j+1)-th smallest
   element of S. Every nonempty upper level set arises this way, with j = 0
   giving P itself. T lies entirely on one side of each cut. So "the last
   piece of u contains T_σ" holds iff "every nonempty upper level set that
   is a union of components contains T".
6. *Sum.* Sum over σ, with C(m, |σ|) choices of S for each. The leading
   coefficient comes from |σ| = n, where Q_{0̂} = P. ∎

### 2.2 Descent expansion

**Corollary Ω-des (PROVEN + audited in [AudLS] §2; COMPUTED
`[omegaC-des]`: every component T, all natural labellings for n ≤ 5, the
canonical labelling for n ≤ 7, 3666 cases; [AudLS] checked every natural
labelling for n ≤ 6, 57,075 cases).** Fix a natural labelling and a component T. For w ∈ Lin P, let
C_T(w) be the set of cuts p ∈ [1, n−1] of w with T ⊆ {w_1, …, w_p}, and put
c = |C_T(w)|. Then

  Ω_C(P, m) = Σ_{w ∈ Lin P, C_T(w) ∩ Des(w) = ∅} C(m + n − 1 − des(w) − c, n − c).

*Proof.* Use Stanley's word (Proposition 1): f ↔ (w, f), where f is weakly
increasing along w and strictly increasing at Des(w).
- The nonempty upper level sets of f are the suffixes of w that start at a
  value change of f. Such a suffix is a union of components iff the
  boundary p is a cut of w.
- So the condition of Theorem Ω says: at every cut p ∈ C_T(w),
  f(w_p) = f(w_{p+1}). That is impossible if p is a descent. Otherwise it
  merges positions p and p + 1.
- After merging there are n − c positions, with des(w) strict steps. The
  number of such sequences in [m] is C(m + n − 1 − des(w) − c, n − c). ∎

*Why there is no single des formula.* The obvious guess replaces the
condition by "w ∈ B_P", i.e. the last block of w contains T:
Σ_{w∈B_P} C(m+n−1−des w, n). With T the component of the largest label, it
agrees with Ω_C on the canonical labelling of every one of the 405 posets
with n ≤ 6, so it looks right at first. It fails
in 708 (poset, labelling, T) cases `[omegaC-ctl-BP]`. The first-block
version fails in 811 `[omegaC-ctl-first]`. Failures start at n = 4. A transparent one is
P = {0<2} ⊔ {1<4} ⊔ {3} with T = {1, 4} (unit test
`test_two_chains_plus_point_example`): the map with fibres {0,1,4} < {2,3}
forms a class of size one, yet w = 01423 is not in B_P. The reason is that
a fibre boundary of f and a cut of w are different things. Ω_C is
intrinsic, so its h-vector h_C(P) is a poset invariant that refines e_C(P).
It is nonnegative on all 2450 posets with n ≤ 7 `[omegaC-h]`.

*Update: Theorem H.* Nonnegativity, with a statistic that realises it, is
now **Theorem H** of [H] (PROVEN + audited in [AudH]). Call a natural
labelling *separated* if every minimal element of a non-singleton component
has a smaller label than every maximal element of a non-singleton
component; such labellings always exist. Under a separated labelling, for
n ≥ 2,

  Ω_C(P, m) = Σ_{κ ∈ Cyc(P)} C(m + n − cdes(κ), n),

so h_C(P)_j = #{κ ∈ Cyc(P) : cdes κ = j + 1} ≥ 0. Here Cyc(P) is the set
of rotation classes of Lin P, and cdes is constant on a class. The B_P
failures above are explained in [H] §3: the representative must be a
rotation broken at a descent junction, and under the labelling λ_0 of [H]
the last-piece B_P, with T the component of the largest label, is one
([H] Prop. B, audited). That B_P (fixed by label, last piece) is not the
B_P of [LE] §0 (first block contains an arbitrary base component): for the
latter, des fails to realise h_C under λ_0 on 41 of 554 (poset, base)
pairs with n ≤ 6 ([AudH] §5). The F-positivity of the quasisymmetric lift of
Ω_C, which is stronger, is **PROVEN (Theorem Q)** and audited
(`notes/qsym_refinement_omega_c.md`, `notes/audit_qsym_refinement_omega_c.md`);
it is **KNOWN IN SUBSTANCE (Gessel–Stanley)**.

Small values of the h-vector h_C (its entries sum to e_C):

| P | h_C | e_C | des-distribution on Lin P |
|---|---|---|---|
| A_3 | 1, 1 | 2 | 1, 4, 1 |
| C_2 ⊔ C_1 | 1, 1 | 2 | 1, 2 |
| C_2 ⊔ C_2 | 1, 3, 1 | 5 | 1, 4, 1 |
| A_4 | 1, 4, 1 | 6 | 1, 11, 11, 1 |
| C_3 ⊔ C_1 | 1, 2 | 3 | 1, 3 |

### 2.3 Controls and prior art

*Controls.* Each of these must fail, and does:
- dropping the condition, which gives Ω (516 cases, `[omegaC-ctl-noT]`);
- the condition "max f is attained on T" (322 cases, `[omegaC-ctl-max]`);
- the naive B_P descent sums above.

*Antichain.* OP = Π_n and |μ(π, 1̂)| = (|π| − 1)!. Theorem Ω reads

  Σ_k S(n, k) (k − 1)! C(m, k) = #{f : [n] → [m] : f(1) = max f} = Σ_{j=1}^m j^{n−1}.

This is a classical identity. It follows from the Stirling expansion of
power sums together with (k−1)! = |μ_{Π_k}|. **KNOWN**. It is also the
dimension-level shadow of B_{A_n} = {words starting with 1}.

*Antichain, attribution.* [PA] finds the antichain case in [Pet]
Prop. 1.1 (credited there to Fulman): the bijection S_n/C_n ↔ S_{n−1}
that puts n last is the antichain case of the T-anchoring in Theorem Ω.

*Prior art for general P.* **NOT FOUND** (a search result, [PA]). We
searched for the Möbius function of OP(P) (order congruences) together with
order polynomials and P-partitions. We found Jenča–Sarkoci
(arXiv:1112.5782), which has μ and the sphere count but no polynomial, and
standard order-polynomial material. [PA] then read the toric and cyclic
literature ([DMR] in full, [AGRR], [Pet], [ARR]):
- Ω_C is **not** a toric order polynomial. [DMR] defines none; the toric
  P-partitions of [AGRR] give order polynomials with leading coefficient
  n·|L^tor|/n!, whereas Ω_C has e_C(P)/n!. Numerically, Ω_C(P, ·) is not
  in the cone of toric order polynomials for any P with n ≤ 5 ([PA] §1).
- Petersen's cyclic P-partitions build Cellini's cyclic Eulerian algebra on
  S_n, not a cut-rotation quotient for general P.
- Corollary Ω-des was not found: in [AGRR] every rotation counts, while in
  Ω-des only rotations at cuts count, with cut positions forced to be
  equalities.

*Reciprocity.* We tested two natural guesses, and both fail:
- (−1)^n Ω_C(P, −m) equals the strict version of the Theorem-Ω count on 212
  of 258 cases;
- it equals Ω_C(P, m − 1) on 158 of 258 (n ≤ 5, m ≤ 3).

The reciprocity law is now **PROVEN + audited** (Theorem R of
`notes/reciprocity_omega_c.md`, audited in
`notes/audit_reciprocity_omega_c.md`): (−1)^n Ω_C(P, −m) counts the strictly
order-preserving f : P → [m] such that no T-free union of components U has
min f(U) ≥ max f(P ∖ U). The first guess fails because it keeps the strict
inequality > of Theorem Ω; the anchoring must become ≥. The second holds
exactly when every component has height ≤ 2 (Prop. S there). Also PROVEN +
audited there: ★, Ω_C(P*, m) = Ω_C(P, m). Prior art
(`notes/prior_art_reciprocity_omega_c.md`): the polynomial side of
Theorem R is KNOWN IN SUBSTANCE (EC1 Lemma 3.15.9 word by word;
Grinberg–Reiner Prop. 7.1.7(iii) + 5.2.19); the D_T reading (Lemma R2) is
NOT FOUND. The palindromicity classification S′ is PROVEN + audited
(`notes/palindromic_h_c.md`, audited in `notes/audit_palindromic_h_c.md`):
its connected case is KNOWN (EC1 Cor. 3.15.18(b), Beck–Sanyal Ex. 6.27),
and the "only if" for disconnected P is proved there. Still OPEN:
unimodality U of h_C (COMPUTED n ≤ 7). For connected P, U is the open
unimodality of W_P for naturally labelled P. h_C is not real-rooted in general (Stembridge's
poset, n = 17, EC1 Fig. 3.88); unimodality is not refuted.

## 3. Lead 1: Kraskiewicz–Weyman and maj mod n

KW: the multiplicity of S^λ in Lie_n is #{SYT of shape λ : maj ≡ 1 (mod n)}.
The proof uses Lie_n ≅ Ind_{C_n}^{S_n} ω together with the principal
specialisation of fake degrees. Both ingredients need an S_n-action on the
module. PLie(P) has one only when it equals Lie_n itself (§5). So the only possible analogue
is at the level of dimensions, dim PLie(P) = e_C(P).

**The naive analogue is false.** #{w ∈ Lin P : maj w ≡ 1 (mod n)} = e_C(P)
holds on only 6 of 2449 posets `[maj-KW-dim]`. For example, C_2 ⊔ C_1 has
maj values {0, 1, 2} on Lin P but e_C = 2.

**Proposition 3 (PROVEN + audited in [AudLS] §4; COMPUTED `[maj-rot]` on S_n, n ≤ 7, and
`[maj-rot-closure]` on all 2449 posets).**
- (a) For w ∈ S_n, maj(w_2 ⋯ w_n w_1) ≡ maj(w) − cdes(w) (mod n), and cdes
  is invariant under rotation.
- (b) If n is prime, then for every P and every r,
  #{u ∈ Lin(P)·C_n : maj(u) ≡ r (mod n)} = e_C(P) = dim PLie(P).
- (c) (b) fails for composite n: on 211 of the 334 posets with n ∈ {4, 6}
  `[maj-rot-closure-ctl]`. The antichain still satisfies it at every n,
  because there Lin(P)C_n = S_n.

*Proof.*
- (a) Write w = a v. Then
  maj(v a) − maj(a v) = −des(v) − [a > v_1] + (n − 1)[v_{n−1} > a]
  ≡ −(des(a v) + [v_{n−1} > a]) = −cdes(w) (mod n).
- (b) Lin(P)C_n is a union of e_C(P) free C_n-orbits ([LE] §3.1). On the
  orbit of w, maj takes the values maj(w) − j·cdes(w), for j = 0, …, n − 1,
  mod n. For n ≥ 2 we have 1 ≤ cdes ≤ n − 1, which is a unit mod a prime n.
  So each orbit meets every residue exactly once. ∎

Prior art: **KNOWN IN SUBSTANCE**. The rotation lemma (a) is folklore and
is the usual step in proving that maj is equidistributed mod n. The only
poset content in (b) is the orbit count e_C(P), which [LE] already has. (b)
is a dimension count, not a KW multiplicity statement.

**Proposition 3′ (PROVEN + audited in [AudLS] §4; COMPUTED `[maj-equi]`, 485 posets; control:
fails on 1871 connected posets).** If P is disconnected with components of
sizes m_1, …, m_k and gcd(m_i) = 1, then maj is equidistributed mod n on
Lin P.

*Proof.* W_P(q) := Σ_{w∈Lin P} q^{maj w} = (q; q)_n Σ_f q^{|f|}, where the
sum is over P-partitions (EC1 Thm 3.15.7; CITED). The P-partition
generating function is multiplicative over components, so
W_P = [n; m]_q ∏ W_{T_i}. At a nontrivial n-th root of unity of order d,
[n; m]_q vanishes unless d divides every m_i (q-Lucas). That cannot happen
when gcd(m_i) = 1. ∎

Prior art: **KNOWN IN SUBSTANCE** (MacMahon; EC1 §3.15). The pattern
coordinates of [LE] give the same factorisation and add nothing to it. For
the promotion CSPs of [LE] Thm U, the standard CSP consequence
#{w : maj w ≡ r} = #{∂-orbits O : (n/|O|) | r} holds. At r = 1 it counts
free promotion orbits, which looks like KW in form, but it is a property of
every CSP and does not come from PLie.

## 4. Lead 3: sign-imbalance

**Proposition 4 (PROVEN + audited in [AudLS] §4; COMPUTED `[sign-union]`, all 503 disconnected
posets with n ≤ 7).** Let P = T_1 ⊔ ⋯ ⊔ T_k with |T_i| = m_i. Then

  |I(P)| = |[n; m_1, …, m_k]_{q=−1}| · ∏_i |I(T_i)|.

In particular P is sign-balanced whenever two components have odd size.

*Proof.* Choose a natural labelling in which each T_i occupies an interval
of labels, with T_1 below T_2 below ⋯. This is allowed because |I| does not
depend on the natural labelling (§0). Under the pattern bijection
Lin P → Pat(m) × ∏ Lin T_i ([LE] §0) we have
inv(w) = inv(p(w)) + Σ_i inv(w|_{T_i}): a pair from different components is
an inversion exactly when the pattern letters are inverted. Hence
I(P) = (Σ_{p∈Pat(m)} (−1)^{inv p}) ∏ I(T_i). MacMahon's inv-generating
function of multiset permutations is the q-multinomial (CITED). Evaluating
at q = −1 gives zero when two of the m_i are odd. ∎

Prior art: **KNOWN IN SUBSTANCE**. It is MacMahon's shuffle factorisation
at q = −1, the sign analogue of Prop. 3′. We did not find it stated in
[Sta05]: a full-text read of the ar5iv version finds no disjoint-union
statement. [Sta05] Thm 5.1(a) gives the maj-analogue W_P(−1) as a count of
P-domino tableaux. Sjöstrand's and White's papers were not checked.

**No link to μ.** |I(P)| = e_C(P) = |μ(OP(P))| holds on 6 of 2449 posets
`[sign-ctl-eC]`. On connected P the theory reduces to C[Lin P], which
carries no sign information beyond the signs of the words themselves. On
odd n, rotation at a cut preserves sign (sgn γ^k = (−1)^{k(n−1)}), so
I(P) = Σ_{classes} sgn(class)·|class ∩ Lin P|. This is a reorganisation,
not an identity. Verdict: the machinery gives no sign-balance result beyond
Proposition 4.

## 5. Lead 4: descent algebra and Garsia–Reutenauer

The Garsia–Reutenauer theory is about the left S_n-module C S_n · e for an
idempotent e in Solomon's descent algebra Σ_n. Its descent and maj
statements are statements about Frobenius characteristics. For PLie(P) we
have the following (**PROVEN**):
- PLie(P) = span{w e_ζ : w ∈ Lin P} ⊆ C S_n e_ζ ≅ Lie_n. If it is stable
  under left multiplication by S_n, then it contains u e_ζ for every word
  u, because S_n acts transitively on words. So it is all of C S_n e_ζ.
  Comparing dimensions, PLie(P) is an S_n-submodule iff it equals Lie_n,
  iff e_C(P) = (n−1)!, iff Lin(P)C_n = S_n.
- COMPUTED: exactly 2n − 2 posets for each 2 ≤ n ≤ 7. They are the
  antichain, the posets A_j ⊔ (one point below the other n − j − 1 points),
  and their duals. For example, C_2 ⊔ C_1 has PLie = Lie_3. On these
  posets KW and Garsia–Reutenauer apply verbatim, because the module is
  Lie_n, and they say nothing about P.
- For every other P there is no S_n-action. A right action would have to
  commute with e_ζ to preserve C S_n e_ζ, and γ acts by the scalar ζ.

So apart from the 2n − 2 posets above, PLie(P) has no Frobenius
characteristic and no descent-algebra action.
The Klyachko idempotent κ_n = (1/n)Σ ω^{maj w} w generates the same left
ideal as e_ζ only up to isomorphism. span{wκ_n : w ∈ Lin P} is a different
subspace, and we found no reason to study it. The descent information that
does exist reaches the theory through the faces of C_P (§1), not through
the Lie module. The nearest literature, *P-partitions and a multi-parameter
Klyachko idempotent* (arXiv:math/0509125, cited in
`notes/audit_conjecture_s.md`), goes the other way: it realises shuffles as
linear extensions. **Verdict: no.**

## 6. The other machinery, checked for statistic content

- *Theorem Ψ / C[Lin P]/R_P* ([Nat], [Thm] Thm `thm:S`). R_P is homogeneous
  for des or maj on none of 603 (P, natural labelling) pairs with n ≤ 5
  ([LE] §5, [AudLE] §8). So the quotient is not graded by these statistics.
  Theorem M's restriction multigrading is the only grading, and it is
  statistic-free.
- *Vanishing criteria (TA-CR, Theorem CC).* These decide when the
  character χ_{C_P}(g) vanishes for g ∈ ±S_n stabilising C_P. That is a
  question about Aut(P)-symmetry with no statistic attached. Excluded by
  the brief.
- *Cyclic sieving notes* ([CSC], [CSG]). The polynomial X_P sieves Aut(P)
  acting on classes. This is symmetry again, and nothing in it holds for
  every P. [LE] Thm U (promotion CSP for disjoint unions) is the one
  statistic result, and it is already recorded, with prior art.

## 7. Ranked shortlist

1. **Theorem Ω, with its h-vector.** This is the only identity here that
   reads the machinery (μ on upper intervals of OP(P)) as a statistic, and
   it explains the most for the least: one line from Theorem A and Lemma U,
   plus the piece-rotation argument. Next steps, in order:
   - (i) prior art against toric and cyclic P-partition theory: **done**
     ([PA]; NOT FOUND for general P, KNOWN for the antichain);
   - (ii) h_C(P) ≥ 0 with a realising statistic: **done**, Theorem H of
     [H] (cdes on the rotation classes, separated labelling), audited in
     [AudH];
   - (iii) look for a reciprocity law: **done**, Theorem R of
     `notes/reciprocity_omega_c.md`, PROVEN + audited (polynomial side
     KNOWN IN SUBSTANCE via EC1 Lemma 3.15.9; the D_T reading NOT FOUND);
   - (iv) prove the F-positivity of the quasisymmetric lift K_C(P):
     **done**, PROVEN (Theorem Q of `notes/qsym_refinement_omega_c.md`),
     audited; KNOWN IN SUBSTANCE (Gessel–Stanley).

   The independent audit is done: [AudLS] finds that the proof holds.
2. **Nothing else is worth proving.** Props 1, 3, 3′ and 4 are correct and
   now verified, but they are KNOWN or KNOWN IN SUBSTANCE. They should be
   cited, not re-proved.

The honest summary: apart from Theorem Ω, the machinery gives nothing beyond
known P-partition theory. The reasons are that its numerical content is
e_C, that e_C = e on connected posets, and that on disconnected posets
everything factors through shuffles.

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 4 minutes):

    python3 linext_statistics.py --nmax 7 --lmax 5 --fmax 6 > output/linext_statistics.txt
    python3 -m unittest test_linext_statistics

The script exits with status 0 iff every claim holds and every CONTROL line
is refuted somewhere. Options:
- `--sections faces,omegaC,chi,maj,sign` runs a subset;
- `--lmax` sets the largest n at which all natural labellings are tested;
- `--fmax` sets the largest n for the brute-force P-partition count, which
  runs over m ≤ 3.
