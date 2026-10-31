# Reciprocity for the cyclic order polynomial: what Ω_C(P, −m) counts

Question ([LS] §7 item 1(iii)): find and prove a reciprocity law for the
cyclic order polynomial Ω_C(P, m), the analogue of Stanley's
Ω(P, −m) = (−1)^n Ω̄(P, m). Also: is h_C(P*) related to the reverse of
h_C(P), does an Ehrhart reading apply, and for which P is h_C palindromic?

Tags: **PROVEN** means proved here. **PROVEN + audited** means, in
addition, re-proved line by line and recomputed with independent code in
[AudR]. **COMPUTED** means checked by
`compute/reciprocity_omega_c.py`, with bracketed line labels from
`compute/output/reciprocity_omega_c.txt`. **OPEN** means not settled.
**KNOWN** means found in the literature; **KNOWN IN SUBSTANCE** means a
special case or the same mechanism is in a source read; **NOT FOUND** is
a search result ([PAR]), not a proof of novelty.

**Audit and prior art.** Every claim of this note was independently
audited in [AudR] = `notes/audit_reciprocity_omega_c.md`: Theorem R,
Lemmas R1 and R2 (the isolated-T case included, under λ_T), R′, B⁺, ★, E
and S all HOLD; no claim fails; one sentence of interpretation (lower level
sets) was FIXABLE and is fixed below (§4). The literature was checked in
[PAR] = `notes/prior_art_reciprocity_omega_c.md`. In short: the
*polynomial* side of Theorem R is **KNOWN IN SUBSTANCE**, since Stanley's
reciprocity holds word by word (EC1 Lemma 3.15.9; equivalently the QSym
antipode, Grinberg–Reiner Prop. 7.1.7(iii) with Prop. 5.2.19) and so holds
for the word set B_T. What was **NOT FOUND** is the *combinatorial*
reading: the strict anchoring D_T and Lemma R2.

Sources: [LS] = `notes/linext_statistics.md` (Theorem Ω, PROVEN + audited
in [AudLS]); [HV] = `notes/h_vector_omega_c.md` (Theorem H, Proposition B,
PROVEN + audited in [AudH]); [ME] = `notes/mu_op_elementary.md`;
[PA] = `notes/prior_art_linext_statistics.md`; EC1 = Stanley,
*Enumerative Combinatorics* vol. 1, 2nd ed.; [Q] =
`notes/qsym_refinement_omega_c.md`; [AudR] =
`notes/audit_reciprocity_omega_c.md`; [PAR] =
`notes/prior_art_reciprocity_omega_c.md`; [GR] = Grinberg–Reiner, *Hopf
algebras in combinatorics*, arXiv:1409.8356; [PH] =
`notes/palindromic_h_c.md` (Theorem S′, PROVEN + audited in
`notes/audit_palindromic_h_c.md`).

## Verdict

**Ω_C(P, −m) counts strict maps under the strict form of the anchoring.**
The two anchorings differ only in whether the inequality between level
sets is strict, and the strict order goes with the weak anchoring and
vice versa. For every finite poset P on n points and every component T of P:

  (−1)^n Ω_C(P, −m) = Ω̄_C(P, m) := #{f : P → [m] strictly order-preserving :
      no nonempty T-free union of components U has min f(U) ≥ max f(P ∖ U)}.

Compare Theorem Ω of [LS]: Ω_C(P, m) counts the order-preserving f such
that no nonempty T-free union of components U has min f(U) > max f(P ∖ U).
The proof is Stanley's proof, run on one rotation per cyclic class. Under a
suitable labelling λ_T, the set B_T of linear extensions whose last piece
contains T indexes both sides: the weak words give Ω_C and the strict words
give Ω̄_C (Lemmas R1 and R2).

| # | Statement | Status |
|---|---|---|
| R | (−1)^n Ω_C(P, −m) = Ω̄_C(P, m), for every P and every component T | **PROVEN + audited** (§2; [AudR] §1, recomputed on all 3107 (P, T), n ≤ 7, and by a literal count over all maps P → [m], n ≤ 6). Polynomial side KNOWN IN SUBSTANCE (EC1 Lemma 3.15.9; [GR] Prop. 7.1.7(iii) + 5.2.19); the D_T reading NOT FOUND ([PAR]); COMPUTED as a polynomial identity, by literal enumeration of strict maps, on all 3107 pairs (P, T) with n ≤ 7 `[recip]` |
| R1 | Under λ_T: f is T-anchored iff the last piece of its weak Stanley word contains T | **PROVEN + audited** (§1; [AudR] §1, isolated T included). KNOWN IN SUBSTANCE (row F+ of [Q]: Gessel–Stanley with the anchor labelled last; [PAR]); COMPUTED on 5 928 326 (surjective map, T) cases, n ≤ 7 `[lemma-weak]` |
| R2 | Under λ_T: f satisfies D_T iff the last piece of its strict Stanley word contains T | **PROVEN + audited** (§1; [AudR] §1, isolated T under λ_T included; fails under λ_0, as the control shows). NOT FOUND ([PAR]); COMPUTED on 2 742 963 cases, n ≤ 7 `[lemma-strict]` |
| R′ | Ω̄_C(P, m) = Σ_{κ∈Cyc P} C(m + cdes κ − 1, n) for a separated labelling, n ≥ 2; generating function Σ_κ x^{n+1−cdes κ}/(1 − x)^{n+1} | **PROVEN + audited** (§3, from R and Theorem H; [AudR] §2); COMPUTED on 2449 posets `[recip-cdes]`. NOT FOUND for general P ([PAR]) |
| B⁺ | Under λ_T, for every component T (an isolated T included): h_C(P)_j = #{w ∈ B_T : des w = j}. This gives a second proof of h_C ≥ 0 and extends Prop. B of [HV] | **PROVEN + audited** (§3, from R1 and Theorem Ω; [AudR] §2, 0 / 3107 bad) |
| ★ | Ω_C(P*, m) = Ω_C(P, m), so h_C(P*) = h_C(P) and Ω̄_C(P*, m) = Ω̄_C(P, m) | **PROVEN + audited** (§4, one line; [AudR] §3); COMPUTED on 2450 posets `[dual]`. KNOWN IN SUBSTANCE (the connected case is the classical Ω(P*) = Ω(P); [PAR]) |
| E | R_T, the closed region of T-anchored points of the order polytope, is not convex in general. It satisfies Ehrhart–Macdonald reciprocity L_{R_T}(−t) = (−1)^n L_{R_T°}(t) | **PROVEN + audited** (§5, interior identified, then R; [AudR] §4). Mechanism KNOWN IN SUBSTANCE (half-open decompositions, Beck–Sanyal §5.3); the statement for R_T NOT FOUND ([PAR]) |
| S | n ≥ 2 and every component has height ≤ 2 (no 3-element chain) ⇒ Ω̄_C(P, m) = Ω_C(P, m − 1) and h_j = h_{n−2−j} | **PROVEN + audited** (§6, explicit bijection; [AudR] §5, checked map by map); COMPUTED on 256 posets `[shift-h2]`. Connected case and antichain KNOWN; general disconnected P NOT FOUND ([PAR]) |
| S′ | n ≥ 2: h_C palindromic iff (P connected and graded) or (every component has height ≤ 2) | COMPUTED on all 2449 posets 2 ≤ n ≤ 7 `[pal-class]`, recomputed in [AudR]. **PROVEN + audited** in [PH]. The connected case is **KNOWN** (EC1 Cor. 3.15.18(b); Beck–Sanyal Ex. 6.27). The "only if" for disconnected P is proved in [PH] (Theorem G, end coefficients) |
| U | h_C(P) unimodal | COMPUTED: true (and log-concave, [PAR]) on all 2450 posets n ≤ 7. **OPEN** in general. For connected P, h_C = W_P, so U contains the open unimodality question for W_P of naturally labelled posets (Neggers–Stanley, weak form; [PAR] §5) |
| 2C | P = Q ⊔ T, Q and T connected ⇒ h_C(P)(t) = W_P(t) − t · W_Q(t) · W_T(t), W = des generating function of Lin under a natural labelling | **PROVEN + audited** ([PAR] §5; [AudR] §7, 0 bad / 391 two-component posets n ≤ 7); §6 below |
| ✗ | h_C real-rooted | **FALSE** at n = 17: Stembridge's poset S (EC1 Fig. 3.88) is connected, so h_C(S) = W_S, which has non-real zeros ([PAR] §5). True for n ≤ 7. Unimodality is not refuted |
| R_low | Lower-level-set form of D_T: Ω̄_C(P, m) = #{strict f : no T-free cluster U has max f(U) ≤ min f(P ∖ U)} | **PROVEN + audited**: the image of Theorem R for P* under ★ and f ↦ m + 1 − f ([AudR] §6, 0 / 3107 bad) |
| ✗ | Naive transplant: strict maps with the Theorem Ω anchoring (> kept) | **FALSE** on 1160 of 3107 (P, T) `[ctl-naive]`. Smallest case: A_2 gives C(m + 1, 2), not C(m, 2) |
| ✗ | Strict maps anchored on LOWER level sets with the strict inequality kept (forbid max f(U) < min f(P ∖ U)) | **FALSE** on 1160 of 3107 `[ctl-lower]`. The ≤ version is TRUE (row R_low) |
| ✗ | Order-preserving maps with D_T (strictness moved to the anchoring only) | **FALSE** on 3079 of 3107 `[ctl-mixed]` |
| ✗ | Stanley's Ω̄(P, m) with no anchoring | **FALSE** on exactly the 503 disconnected posets `[ctl-plain]` |
| ✗ | h_C(P*) = reverse of h_C(P) | **FALSE** on 1875 of 2450 `[ctl-reverse]` |
| ✗ | R2 with an isolated T labelled below the non-isolated maxima (λ_0 instead of λ_T) | **FALSE** on 28 044 (map, T) cases `[ctl-lemma-iso]` |
| ✗ | R2 under an arbitrary natural labelling | **FALSE** on 1166 of 2287 labelled (P, T), n ≤ 5 `[ctl-lemma-any]` |
| ✗ | h_C palindromic iff every component is graded | **FALSE** on 151 of 2449 `[ctl-pal-graded]`, e.g. C_3 ⊔ C_3 has h_C = (1, 8, 9, 1) |
| ✗ | Ω̄_C(P, m) = Ω_C(P, m − 1) for every P | **FALSE** on all 2193 posets with a 3-chain `[ctl-shift-any]` |

Answers to the three leads of the question:
- *Strict maps with an anchoring condition:* yes (Theorem R). The dual
  condition also moves to lower level sets, provided the inequality is ≤:
  forbidding a T-free cluster U with max f(U) ≤ min f(P ∖ U) gives the
  same count (row R_low, via ★ and f ↦ m + 1 − f). What fails is keeping
  the strict inequality on lower level sets (`[ctl-lower]`); by ★ that
  version counts the same thing as the naive transplant on P*. In both
  forms, what changes is the strictness of the anchoring inequality.
- *h-vector side:* h_C(P*) equals h_C(P), not its reverse (★). The reversal
  x^{n+1}·H(1/x), with H(x) = Σ_κ x^{cdes κ}, is the numerator of the
  generating function of Ω̄_C (R′). That is the analogue of Stanley's
  Σ_m Ω̄(P, m) x^m = Σ_w x^{1+des w}/(1 − x)^{n+1}.
- *Ehrhart side:* Ω_C(P, t + 1) is the Ehrhart count of a closed region
  R_T, which is a union of closed order-polytope simplices. R_T is not
  convex in general, so Ehrhart–Macdonald does not apply off the shelf.
  Theorem R is exactly the statement that the reciprocity holds for R_T (E).

## 0. Conventions

P is a poset on n ≥ 1 points with components K_1, …, K_r, and T is one of
them. A **T-free cluster** is a nonempty union U of components with
U ∩ T = ∅. For a map f : P → [m]:

- f is **T-anchored** if no T-free cluster U has min f(U) > max f(P ∖ U).
  This is the condition of Theorem Ω of [LS]: a T-free cluster U with
  min f(U) > max f(P ∖ U) is exactly an upper level set f^{−1}([v, m]) that
  is a nonempty union of components missing T, and conversely.
- f satisfies **D_T** if no T-free cluster U has min f(U) ≥ max f(P ∖ U).

Equivalently, anchoring forbids a T-free cluster with f(U) ⊆ [v + 1, m]
and f(P ∖ U) ⊆ [1, v]. D_T also forbids f(U) ⊆ [v, m] together with
f(P ∖ U) ⊆ [1, v], where the two sides may share the value v.

**Theorem Ω ([LS] §2, PROVEN + audited).** For every component T,
Ω_C(P, m) = #{f : P → [m] order-preserving and T-anchored}. Here
Ω_C(P, m) := Σ_{π∈OP(P)} |μ(π, 1̂)| C(m, |π|).

Put Ω̄_C(P, m) := #{f : P → [m] strictly order-preserving with D_T}. A
priori this depends on T. Theorem R shows that it does not.

*Words.* For w ∈ Lin P, the cuts, pieces and cyclic classes are those of
[HV] §0. A **cut** is a p ∈ [1, n − 1] such that {w_1, …, w_p} is a union of
components. The **last piece** of w is the suffix after the last cut, or all
of w if there is no cut. Put B_T = {w ∈ Lin P : T ⊆ last piece of w}.

*Element types.* An element is **isolated** if it is a singleton component.
Otherwise it is a **non-isolated minimum** (nothing below it), a
**non-isolated maximum** (nothing above it), or a **middle** element. Two
facts are used repeatedly. The first letter of a piece is minimal in P,
because everything below it lies in its component, hence in its piece,
hence before it. A piece of length ≥ 2 does not start with an isolated
point, since then that point alone would be a proper prefix that is a union
of components. Dually, the last letter of a piece is maximal in P, and a
piece of length ≥ 2 does not end with an isolated point.

**The labelling λ_T.** List, in this order: the non-isolated minima; the
middle elements, in a linear extension of their subposet; the isolated
points other than T; the non-isolated maxima; and finally T's point, if T
is a singleton. Label them 0, …, n − 1 in this order. Isolated points are
unrelated to everything. Everything below a middle element is minimal or
middle, and everything above it is middle or maximal. So λ_T is a natural
labelling. If T is not a singleton, λ_T is a λ_0 of [HV] §2.3. If T is a
singleton of a non-antichain, λ_T differs from λ_0 by moving T's point to
the end, and this matters (`[ctl-lemma-iso]`).

*Stanley words (EC1 Lemma 3.15.3, with its strict counterpart).* Fix a
natural labelling λ.
- *Weak.* An order-preserving f corresponds to its **weak word**
  w(f) ∈ Lin P, obtained by sorting P by (f(x), λ(x)), together with a
  sequence that is weakly increasing along w(f) and strict at Des(w(f)).
  For fixed w there are C(m + n − 1 − des w, n) such f.
- *Strict.* A strictly order-preserving f corresponds to its **strict word**
  w̄(f), obtained by sorting by (f(x), −λ(x)), together with a sequence that
  is weakly increasing and strict at the ascents of w̄(f). For fixed w there
  are C(m + des w, n) such f.

Both correspondences are bijections onto pairs (w, sequence).

## 1. The two word lemmas

**Lemma R1 (PROVEN + audited [AudR] §1; COMPUTED `[lemma-weak]`).** Let n ≥ 2, use λ_T, and let f
be order-preserving. Then f is T-anchored iff w(f) ∈ B_T.

*Proof.* Write w = w(f).
- *Not anchored ⇒ w ∉ B_T.* Take U with min f(U) > max f(P ∖ U). Every
  letter of U sorts after every letter of P ∖ U, so U is a suffix of w.
  Since 1 ≤ |U| ≤ n − 1 and P ∖ U is a union of components, position n − |U|
  is a cut. So the last piece lies inside U and misses T.
- *w ∉ B_T ⇒ not anchored.* Let c be the last piece. It misses T, so c is
  not all of w, and there is a cut just before c. Its letter set U is a
  T-free cluster and a suffix, so min f(U) ≥ max f(P ∖ U). If the
  inequality is strict, we are done. Otherwise let x be the first letter of
  c, and y the letter just before c. Then f(x) = f(y) = v, so λ(y) < λ(x).
  Now y is maximal in P, being the last letter of a piece. So it is a
  non-isolated maximum, an isolated point other than T, or T's point. And
  x is minimal: a non-isolated minimum, or an isolated point other than T.
  Every non-isolated minimum has a smaller label than every maximal
  element, so x is an isolated point. Then c = {x}, and x is the last
  letter of w, with f(x) = v = max f.

  Let L = f^{−1}(v) be the top fibre. Take z ∈ L. If z is a non-isolated
  maximum or T's point, then λ(z) > λ(x) and f(z) = f(x), so z sorts after
  x, a contradiction. If z is a non-isolated minimum or a middle element,
  some maximal z′ > z has f(z′) = v and is a non-isolated maximum, again a
  contradiction. So L consists of isolated points other than T. It is a
  T-free cluster with min f(L) = v > max f(P ∖ L), and f is not anchored. ∎

**Lemma R2 (PROVEN + audited [AudR] §1; COMPUTED `[lemma-strict]`).** Let n ≥ 2, use λ_T, and let
f be strictly order-preserving. Then f satisfies D_T iff w̄(f) ∈ B_T.

*Proof.* Write w̄ = w̄(f).
- *w̄ ∉ B_T ⇒ D_T fails.* The letters U of the last piece form a T-free
  cluster and a suffix of w̄. So min f(U) ≥ max f(P ∖ U).
- *D_T fails ⇒ w̄ ∉ B_T.* Take U with min f(U) ≥ v := max f(P ∖ U).

  If min f(U) > v, then U is a suffix of w̄ and a union of components. As
  in R1, the last piece lies inside U.

  If min f(U) = v, let F = f^{−1}(v). It meets both U and P ∖ U.
  - Every x ∈ F ∩ U is minimal in P. Anything below x lies in its
    component, hence in U, and has a value < v, since f is strict.
  - Dually, every y ∈ F ∖ U is maximal in P.
  - So F has no middle elements, and every non-isolated minimum in F lies
    in U.

  Every element of f^{−1}((v, m]) lies in U. Put
  S = f^{−1}((v, m]) ∪ {non-isolated minima in F}. Then S is U minus the
  isolated points of U at value v. Every non-singleton component inside U
  is contained in S, because its elements at value v are non-isolated
  minima. So S is a T-free union of components. Within F, w̄ lists letters
  by decreasing label, and the non-isolated minima carry the smallest
  labels. So they come last within F, and S is a suffix of w̄.

  If S ≠ ∅, then S is a nonempty, proper, T-free suffix that is a union of
  components, so the last piece lies inside S.

  If S = ∅, then v = max f and U consists of isolated points other than T,
  all in the top fibre F. F contains no non-isolated minimum, since such an
  element has something above it with a larger value. So F consists of
  non-isolated maxima, isolated points other than T, and possibly T's
  point. Of these, the isolated points other than T have the smallest
  labels under λ_T. F contains one of them, namely any point of U. So the
  last letter z of w̄, which is the smallest-labelled element of F, is an
  isolated point other than T. {z} is a final piece, and it misses T. ∎

## 2. Theorem R

**Theorem R (PROVEN + audited [AudR] §1; COMPUTED `[recip]`, 3107 pairs (P, T), n ≤ 7, as an
identity of polynomials, with Ω̄_C enumerated literally and Ω_C taken from
the Möbius definition).** For every finite poset P on n points and every
component T,

  (−1)^n Ω_C(P, −m) = Ω̄_C(P, m).

In particular Ω̄_C(P, m) does not depend on T.

*Proof.* If n = 1, then Ω_C(P, m) = m, D_T is vacuous, and Ω̄_C(P, m) = m.
Let n ≥ 2 and use λ_T. By Theorem Ω, Lemma R1 and the weak word bijection,

  Ω_C(P, m) = Σ_{w ∈ B_T} C(m + n − 1 − des w, n).

By Lemma R2 and the strict word bijection,

  Ω̄_C(P, m) = Σ_{w ∈ B_T} C(m + des w, n).

As polynomials in m, C(−y, n) = (−1)^n C(y + n − 1, n). With
y = m − n + 1 + des w this gives

  C(−m + n − 1 − des w, n) = (−1)^n C(m + des w, n),

term by term. ∎

This is Stanley's proof of Ω(P, −m) = (−1)^n Ω̄(P, m) (EC1 §3.15),
restricted to the words of B_T. The only new input is that one set B_T of
words serves both the weak and the strict side. That needs λ_T: under an
arbitrary natural labelling R2 fails (`[ctl-lemma-any]`).

*Prior art ([PAR] §1).* The polynomial identity is **KNOWN IN
SUBSTANCE**: Stanley's reciprocity holds word by word (EC1 Lemma 3.15.9
for one word, then Lemma 3.15.11), so it holds for any set of words, B_T
included. In QSym language ps¹(f)(−m) = ps¹(S f)(m) ([GR] Prop. 7.1.7(iii))
and S(F_w) = (−1)^n F_{w^opp} ([GR] Prop. 5.2.19), applied to K_C = Σ_{w∈B_T}
F_{Des w} (row F+ of [Q]). What was **NOT FOUND** in any source read is the
combinatorial reading of the right-hand side: the strict anchoring D_T,
i.e. Lemma R2.

*Sanity checks.*
- Connected P: there is no T-free cluster, D_T is vacuous, and R is
  Stanley's reciprocity.
- Antichain A_n, n ≥ 2: D_T says that f(T) > f(x) for every x ≠ T, so
  Ω̄_C(A_n, m) = Σ_{j=1}^{m−1} j^{n−1}. The Theorem Ω side is
  Σ_{j≤m} j^{n−1}, and R becomes the classical reciprocity
  S_k(−N) = (−1)^{k+1} S_k(N − 1) for the power sums S_k(N) = Σ_{j≤N} j^k.
  This is checked in the unit tests.
- Small values, with Ω̄_C(P, m) for m = 1, …, 5:

| P | h_C | Ω̄_C(P, 1..5) |
|---|---|---|
| A_2 | (1) | 0, 1, 3, 6, 10 |
| C_2 ⊔ C_1 | (1, 1) | 0, 1, 5, 14, 30 |
| C_2 ⊔ C_2 | (1, 3, 1) | 0, 1, 8, 31, 85 |
| C_3 ⊔ C_1 | (1, 2) | 0, 0, 2, 11, 35 |
| A_4 | (1, 4, 1) | 0, 1, 9, 36, 100 |
| C_3 ⊔ C_3 | (1, 8, 9, 1) | 0, 0, 1, 16, 99 |

*Controls.* The naive transplant, with strict maps and the Theorem Ω
anchoring (> kept), fails already on A_2. With T = {1} it counts
f(0) ≤ f(1), which gives C(m + 1, 2) rather than C(m, 2) (`[ctl-naive]`,
1160 of 3107). The other controls of the table in the Verdict are also
refuted.

## 3. Corollaries

**R′ (PROVEN + audited [AudR] §2, from Theorem R and Theorem H of [HV]; COMPUTED
`[recip-cdes]`).** Let n ≥ 2 and use a separated labelling. Then

  Ω̄_C(P, m) = Σ_{κ∈Cyc(P)} C(m + cdes κ − 1, n),
  Σ_{m≥0} Ω̄_C(P, m) x^m = Σ_κ x^{n+1−cdes κ} / (1 − x)^{n+1}.

*Proof.* Theorem H gives Ω_C(P, m) = Σ_κ C(m + n − cdes κ, n). Apply
C(−y, n) = (−1)^n C(y + n − 1, n) with y = m − n + cdes κ. Since
1 ≤ cdes κ ≤ n − 1 (n distinct letters on a circle are not all cyclic
descents; [AudR] §2), the term C(m + c − 1, n) is nonzero exactly for
m ≥ n + 1 − c. That gives the generating function. ∎

So Ω̄_C(P, m) = 0 for 0 ≤ m ≤ n − max cdes. For n ≥ 2, Ω̄_C(P, 1) = 0.

**B⁺ (PROVEN + audited [AudR] §2, from Theorem Ω and Lemma R1).** For every component T, under λ_T,

  Ω_C(P, m) = Σ_{w∈B_T} C(m + n − 1 − des w, n),
  so h_C(P)_j = #{w ∈ B_T : des w = j}.

This gives a second proof that h_C ≥ 0. It uses neither Theorem H nor its
per-class telescoping lemma, only Theorem Ω. It contains Proposition B of
[HV], which is the case λ_T = λ_0 and T = the component of label n − 1. It
extends that proposition to isolated T, using the relabelling λ_T. R1 is
also a set-level statement: the T-anchored maps are exactly the maps
whose weak word lies in B_T, with no reweighting.

## 4. Duality P ↔ P*

**Proposition ★ (PROVEN + audited [AudR] §3; COMPUTED `[dual]`, 2450 posets).** Ω_C(P*, m) = Ω_C(P, m).

*Proof.* A set partition π is in OP(P) iff the quotient digraph of P by π
is acyclic ([ME] §0). Reversing every arrow preserves acyclicity, so
OP(P*) = OP(P) as sets of partitions, with the same refinement order, the
same Möbius function and the same block counts. ∎

Hence h_C(P*) = h_C(P). Theorem R then gives Ω̄_C(P*, m) = Ω̄_C(P, m). The
candidate "h_C(P*) is the reverse of h_C(P)" fails on 1875 of 2450 posets
(`[ctl-reverse]`). The reversal of h_C belongs to Ω̄_C (R′), not to P*.
Through f ↦ m + 1 − f, ★ also gives a second form of Theorem Ω: Ω_C(P, m)
equally counts the maps whose bottom clump contains T, that is, the maps
in which every nonempty lower level set that is a union of components
contains T.

The same move applies to Theorem R (**R_low**, PROVEN + audited, [AudR]
§6). f ↦ m + 1 − f is a bijection between strict maps on P* and strict
maps on P, and it turns "min f(U) ≥ max f(P ∖ U)" on P* into
"max f(U) ≤ min f(P ∖ U)" on P. So by R for P* and ★,

  Ω̄_C(P, m) = #{f : P → [m] strictly order-preserving : no T-free cluster
      U has max f(U) ≤ min f(P ∖ U)}.

So D_T does move to lower level sets, with ≤. Keeping the strict
inequality instead (forbid max f(U) < min f(P ∖ U)) is the image of the
naive transplant, and it fails (`[ctl-lower]`, 1160 of 3107; [AudR]
recomputes it and also confirms the ≤ version, 0 / 3107 bad).

## 5. The Ehrhart reading

Let O(P) ⊂ [0, 1]^P be the order polytope, and let

  R_T = {x ∈ O(P) : no T-free cluster U has min_U x > max_{P∖U} x}.

This set is closed, since its complement in O(P) is defined by finitely
many strict inequalities between continuous functions. Its lattice points
satisfy #(tR_T ∩ Z^P) = Ω_C(P, t + 1), via x = f − 1. The proof of Lemma R1 uses only the
order of the values, so it holds for real-valued x. Hence R_T is the
disjoint union of the half-open cells of the words w ∈ B_T, and, being
closed, R_T is the union of the closed simplices {x_{w_1} ≤ ⋯ ≤ x_{w_n}} over w ∈ B_T.

*R_T is not convex in general (PROVEN by example).* Take P = {1 < 2, 1 < 3} ⊔ {0}
and T = {1, 2, 3}. The only T-free cluster is {0}, so R_T is cut out by
x_0 ≤ max(x_2, x_3). The points (x_0, x_1, x_2, x_3) = (1, 0, 0, 1) and
(1, 0, 1, 0) lie in R_T, but their midpoint (1, 0, ½, ½) does not. (Found
by a scan of n ≤ 5; this is the smallest instance found.)

**Proposition E (PROVEN + audited [AudR] §4).** The interior of R_T in R^P is

  R_T° = {x : 0 < x < 1, x strictly order-preserving, and
          min_U x < max_{P∖U} x for every T-free cluster U}.

Hence #(tR_T° ∩ Z^P) = Ω̄_C(P, t − 1), and Theorem R is equivalent to
Ehrhart–Macdonald reciprocity for R_T:

  L_{R_T}(−t) = Ω_C(P, 1 − t) = (−1)^n Ω̄_C(P, t − 1) = (−1)^n L_{R_T°}(t).

*Proof.* The right-hand set is open, since it is defined by finitely many
strict inequalities between continuous functions. It is contained in R_T.
So it lies in R_T°.

Conversely, let x ∈ R_T°. Then 0 < x < 1. If x_a = x_b for some a <_P b,
pushing x_a up leaves O(P), so x is strictly order-preserving. Suppose
min_U x = max_{P∖U} x for some T-free cluster U. (It cannot be >, since x
is in R_T.) Add ε > 0 to every coordinate in U. Order relations hold only
inside components, so the order relations still hold, and for small ε we
stay inside the cube. But now min_U > max_{P∖U}, so the perturbed point
has left R_T, and x was not interior. ∎

Macdonald reciprocity is classically proved for polytopes, and for
polyhedral complexes that are manifolds with boundary (Stanley 1974,
Prop. 6.1, after Macdonald; [PAR] §3). Here R_T is
non-convex, and we did not determine whether it is a ball. Proposition E
plus Theorem R shows that the identity holds for R_T regardless. Whether
R_T is always a PL ball is **OPEN**. That would give a topological proof
of Theorem R.

## 6. Palindromicity

h_C here is the trimmed vector. Write h_C(P)_j = #{κ : cdes κ = j + 1} under a
separated labelling ([HV] Theorem H).

**Proposition S (PROVEN + audited [AudR] §5; COMPUTED `[shift-h2]`, 256 posets).** Let n ≥ 2,
and suppose every component of P has height ≤ 2, that is, no chain has 3
elements. Then Ω̄_C(P, m) = Ω_C(P, m − 1). Equivalently, h_C(P)_j = h_C(P)_{n−2−j}
for 0 ≤ j ≤ n − 2: the cdes distribution on Cyc(P) is symmetric under
c ↦ n − c.

*Proof.* Fix T. For strict f with D_T, define g by:
- g = f − 1 on the non-isolated maxima, and on T's point if T is a singleton;
- g = f elsewhere, that is, on the non-isolated minima and on the isolated
  points other than T.

First, g is an order-preserving map to [m − 1]:
- Every relation is (minimum < maximum), and g(y) = f(y) − 1 ≥ f(x) = g(x).
- A non-isolated minimum x lies below some y, so f(x) ≤ m − 1.
- For an isolated z ≠ T, f(z) = m would make U = {z} violate D_T.
- If T = {t}, then f(t) ≥ 2. Otherwise f(t) = 1, and U = P ∖ T violates
  D_T (U is nonempty since n ≥ 2).

Conversely, f = g + 1 on the same elements takes any order-preserving
g : P → [m − 1] to a strict map P → [m]. So the two maps are inverse
bijections between the strict f with f(z) ≤ m − 1 on the isolated z ≠ T and
f(t) ≥ 2, and all order-preserving g into [m − 1]. It remains to show that
D_T(f) holds iff g is T-anchored.

On a non-singleton component, the f-interval [a, b] (minimum over its minima,
maximum over its maxima) becomes [a, b − 1]. The interval of T's point
drops by 1. An isolated point other than T keeps its interval [f(z), f(z)].
For a T-free cluster U, min_U g = min_U f.
- *g not anchored ⇒ D_T fails.* If min_U g > max_{P∖U} g ≥ max_{P∖U} f − 1,
  then min_U f ≥ max_{P∖U} f.
- *D_T fails ⇒ g not anchored.* Suppose μ := min_U f ≥ max_{P∖U} f =: v.
  Let U′ be U together with the isolated points z ≠ T of P ∖ U that have
  f(z) = μ. Then min_{U′} g = μ. On P ∖ U′, non-singleton components and T
  have g ≤ v − 1 < μ. The remaining isolated points have g = f < μ. So
  min_{U′} g > max_{P∖U′} g, and P ∖ U′ ∋ T is nonempty.

Hence Ω̄_C(P, m) = Ω_C(P, m − 1) for m ≥ 1. With R′ and Theorem H this reads

  Σ_κ x^{n+1−cdes κ} = x · Σ_κ x^{cdes κ}. ∎

This is the analogue of the rank-function bijection f ↦ f − ρ, which gives
Stanley's Ω̄(P, m) = Ω(P, m − ℓ) for graded P. Here only rank 1 is
allowed, plus a unit shift at the anchor, which is what the antichain needs.

**S′ (PROVEN + audited in [PH]; COMPUTED `[pal-class]`, all 2449 posets
2 ≤ n ≤ 7).** For
n ≥ 2, h_C(P) is palindromic iff either P is connected and graded, or
every component of P has height ≤ 2.
- *Connected P:* h_C is Stanley's h-vector W_P, and palindromic iff graded
  is **KNOWN**: EC1 Cor. 3.15.18(b) (graded of length ℓ ⇔ Ω_P(−ℓ − m) = (−1)^n Ω_P(m)),
  after Stanley's 1972 Memoir, Prop. 19.3; stated verbatim as Beck–Sanyal
  Ex. 6.27 ([PAR] §4). (Not EC1 Thm 3.15.16, which concerns maj.)
- *Disconnected P:* "if" is Proposition S. "Only if" (a component with a
  3-chain forces non-palindromic h_C) is **PROVEN + audited** in [PH]
  (Theorem G: h_d ≥ 2, or h_d = 1 and h_{d−1} − h_1 ≥ 2^{r−1} − 1). It was
  first COMPUTED for n ≤ 7 (319 + 76 disconnected posets at n = 7, matching
  the prediction exactly).
- Gradedness of the components is not the right condition
  (`[ctl-pal-graded]`): C_3 ⊔ C_1 gives (1, 2), and C_3 ⊔ C_3 gives
  (1, 8, 9, 1). No poset with a 3-chain (connected or not) has
  Ω̄_C(P, m) = Ω_C(P, m − 1) (`[ctl-shift-any]`, 2193 of 2193, n ≤ 7).

The data in the question fit this: C_2 ⊔ C_2 gives (1, 3, 1) and A_4 gives
(1, 4, 1), both of height ≤ 2. C_3 ⊔ C_1 gives (1, 2) and has a 3-chain.

*Unimodality (COMPUTED).* Every h_C(P) with n ≤ 7 is unimodal
(recomputed in [AudR] §8) and log-concave ([PAR] §5). **OPEN** in general, and
not a realistic general target: for connected P, h_C = W_P, so U for all
P contains the unimodality of W_P for every naturally labelled poset. That
is the surviving weak form of the Neggers–Stanley conjecture, and it is
open (proved for graded P, Reiner–Welker; for sign-graded P, Brändén; for
width two, Alexandersson–Jal; [PAR] §5). A tractable form is relative: if
W_K is unimodal for every component K, is h_C(P) unimodal?

*Real-rootedness is FALSE ([PAR] §5).* h_C is real-rooted on all 2450
posets with n ≤ 7, but not in general: Stembridge's 17-element naturally
labelled poset S (EC1, solution to Ex. 3.165, Fig. 3.88) is connected, so
h_C(S) = W_S, which has non-real zeros. This does not refute U: h_C(S) is
unimodal and log-concave, as is h_C(S ⊔ X) for the small X tested in [PAR].

**Two-component identity (PROVEN + audited; [PAR] §5, [AudR] §7).** Let
P = Q ⊔ T with Q and T connected, and let W denote the descent generating
function of the linear extensions under a natural labelling. Then

  h_C(P)(t) = W_P(t) − t · W_Q(t) · W_T(t).

*Proof sketch* (full proof in [PAR] §5). With two components the only
T-free cluster is Q, so by Theorem Ω the non-anchored order-preserving maps
are those with min f(Q) > max f(T). These are the P-partitions of the
ordinal sum T ⊕ Q with T labelled above Q; their words are uv, u ∈ Lin T,
v ∈ Lin Q, with a forced descent at the junction, so their h-numerator is
t W_T W_Q. Subtract from Stanley's Ω(P, m), whose h-numerator is W_P. ∎

COMPUTED: 0 bad on all 391 two-component posets with n ≤ 7 ([AudR] §7,
recomputed independently; the control without the factor t fails on
391 / 391), and on S ⊔ C_2 (n = 19, [PAR]). It gives
h_C(C_m ⊔ C_n) = W(m ⊔ n) − t, the same shape as Brändén's W(m ⊔ n) − 1;
the former is real-rooted for 1 ≤ m ≤ n ≤ 30 ([PAR], COMPUTED). Not found
in the sources read. With three or more components the non-anchored maps
need inclusion–exclusion over T-free clusters; that was not done.

## 7. Prior art (search result)

The full pass is [PAR] (`notes/prior_art_reciprocity_omega_c.md`), which
supersedes the two-query search first recorded here. Its verdicts:

- **Theorem R, polynomial side: KNOWN IN SUBSTANCE.** Stanley's
  reciprocity is word by word (EC1 Lemma 3.15.9, Lemma 3.15.11), so it
  holds for the word set B_T; equivalently the QSym antipode
  ([GR] Prop. 7.1.7(iii) with Prop. 5.2.19) applied to K_C. The connected
  case is Stanley's reciprocity (EC1 Cor. 3.15.12; Stanley 1974 Prop. 2.1;
  Beck–Sanyal Thm 1.3.2); the antichain case is classical power-sum
  reciprocity.
- **Theorem R, the D_T reading (Lemma R2): NOT FOUND.** No source read has
  a strict anchoring condition, or any reciprocity for a cyclic or anchored
  order polynomial. Petersen's *Cyclic descents and P-partitions*
  (arXiv:math/0405479) was read in full: it has no reciprocity section.
  Develin–Macauley–Reiner (toric posets) and Adin–Gessel–Reiner–Roichman
  (cyclic QSym) have no reciprocity statement either.
- **R1: KNOWN IN SUBSTANCE** (row F+ of [Q]). **R′: NOT FOUND** for general P.
- **★: KNOWN IN SUBSTANCE** (the connected case Ω(P*) = Ω(P) is classical).
- **E:** mechanism KNOWN IN SUBSTANCE (half-open unimodular simplices,
  Beck–Sanyal §5.3, §6.3); the statement for the non-convex R_T NOT FOUND.
- **S:** connected case and antichain KNOWN (EC1 Lemma 3.15.17(b),
  Cor. 3.15.18(b); Beck–Sanyal Ex. 6.28); general disconnected P NOT FOUND.
- **S′:** connected case KNOWN (EC1 Cor. 3.15.18(b); Beck–Sanyal Ex. 6.27);
  the "only if" for disconnected P NOT FOUND; it is proved in [PH], so the
  disconnected classification is new to these notes.
- **U:** connected case is the open unimodality of naturally labelled W_P
  (§6). h_C is not real-rooted in general (Stembridge's poset, n = 17).
- **Two-component identity:** not found in the sources read.

## 8. Open points

- Whether R_T is a PL ball, or just a manifold with boundary, which would
  suffice for Macdonald's theorem (§5).
- Unimodality of h_C (COMPUTED n ≤ 7). Its connected case is the open
  unimodality of naturally labelled W_P (§6), so the relative form "W_K
  unimodal for each component K ⇒ h_C(P) unimodal" is the realistic target.
- h_C for three or more components in terms of W-polynomials (§6).
- A direct bijective proof of the T-independence of Ω̄_C, analogous to the
  clump rotation of [LS] Step 4 (here it follows only from Theorem R).

## Reproduce

From `compute/` (Python 3, no dependencies, one core, about 100 s; it
imports the poset enumerator, the Möbius computation of Ω_C and the word
helpers from `h_vector_omega_c.py`; every count of maps is a literal
enumeration of surjective maps written in the script):

    python3 reciprocity_omega_c.py --nmax 7 --lmax 5 > output/reciprocity_omega_c.txt
    python3 -m unittest test_reciprocity_omega_c

The script exits with status 0 iff every claim holds and every CONTROL is
refuted somewhere. The unit tests also count Ω̄_C by enumerating all
maps P → [m] (not only the surjective ones) and testing D_T by brute force
over every U, for A_2, C_2 ⊔ C_1, C_2 ⊔ C_2, C_3 ⊔ C_1 and {0, 1 < 2} ⊔ {3}.
