# The quasisymmetric refinement of Theorem H

Question (from [PA] §3): the T-anchored P-partition enumerator

  K_{C,T}(P) := Σ x^f over order-preserving f : P → {1, 2, …} such that
  every nonempty upper level set f^{−1}[v, ∞) that is a union of
  components contains T

is a quasisymmetric lift of the cyclic order polynomial Ω_C(P, m). [PA]
found it F-positive in Gessel's fundamental basis on all 2450 posets with
n ≤ 7, for one component T per poset. Is K_{C,T}(P) = Σ_{κ∈Cyc(P)} F_{D(κ)}
for an explicit set D(κ) attached to each cyclic class?

Tags: **PROVEN** means proved here; **COMPUTED** means checked by
`compute/qsym_refinement_omega_c.py`, with bracketed line labels from
`compute/output/qsym_refinement_omega_c.txt`. **OPEN** means not settled.
**PROVEN + audited** means the proof was re-derived and every count
recomputed by independent code in [AudQ].

Sources: [H] = `notes/h_vector_omega_c.md` (Theorem H); [AudH] =
`notes/audit_h_vector_omega_c.md`; [PA] = `notes/prior_art_linext_statistics.md`;
[LS] = `notes/linext_statistics.md`; [AudQ] =
`notes/audit_qsym_refinement_omega_c.md` (independent audit of this note:
every PROVEN claim HOLDS, two wording fixes, both applied below). This note uses only claims of [H] that
[AudH] marks HOLDS: [H] §0 (pieces, classes, junctions), [H] §1 Steps 1–5
and Proposition D, Lemma 2(a) and Theorem H.

## Verdict

**Yes, with a T-adapted labelling. The set D(κ) is the descent set of the
rotation whose last piece contains T.** Under some labellings fixed in
advance (for example C_2 ⊔ C_1 with the isolated point labelled 0, and T the
isolated point), no choice of rotations works (§4.2). No rule D(κ) that
ignores T, of any kind, can work when K_{C,T} depends on T (492 of 2450
posets with n ≤ 7, row 0). But for n ≤ 7 every poset has some labelling,
fixed in advance, under which a T-dependent choice of one rotation per
class works for every T: COMPUTED on all 503 disconnected posets with
n ≤ 7 ([AudQ] §2 `[rot-choice]`, by bipartite matching, not an explicit
rule). The per-class telescoping of Theorem H (Lemma 1) does not lift to
the quasisymmetric level. The proof of the lifted statement is shorter than
the proof of Theorem H, and it reproves Theorem H for the labelling λ_T.

**Prior art, split ([AudQ] §3).**
- **F+ is KNOWN IN SUBSTANCE.** It is the Stanley–Gessel fundamental lemma
  of P-partitions, K_P = Σ_{w∈Lin P} F_{Des w} cell by cell, once the
  anchor's maxima are labelled last (λ_T): anchoring then becomes "the
  Stanley word has T's piece last", a union of cells. This is the
  "put n last" move of [Pet] Prop. 1.1, which is the antichain case. It is
  an observation, not a new positivity theorem.
- **The characterisation (i) ⇔ (E*_T) of Theorem Q is NOT FOUND.** It is
  correct and elementary (§3.2, facts (a) and (b)). The other new content is
  equally small: K_{C,T} depends on T while its specialisation does not
  (row 0), and the Lemma 1 per-class contributions are not F-positive (✗1).
- Both are search results, not proofs of absence.

| # | Statement | Status |
|---|---|---|
| 0 | K_{C,T}(P) depends on T. So "K_C(P)" has to name T. Its principal specialisation does not depend on T: it is Ω_C(P, m) | **PROVEN + audited** ([AudQ]) (§1, by example; specialisation by [H] §1); COMPUTED: depends on T for 492 of 2450 posets `[T-dep]`, specialisation equals the Möbius Ω_C on all 3107 (P, T) `[spec]` |
| D_q | For every natural labelling and every T, K_{C,T}(P) = Σ_{w∈Lin P} G_T(w), where G_T(w) = [C_T(w) ∩ Des w = ∅] Σ_{S⊆C_T(w)} (−1)^{\|S\|} F_{Des(w)∪S} | **PROVEN + audited** ([AudQ]; KNOWN IN SUBSTANCE: cell decomposition + inclusion–exclusion) (§2); COMPUTED on 6996 separated labelled pairs `[propD-qsym]` |
| **Q** | **Theorem Q.** For a natural labelling and a component T, the following are equivalent: (i) K_{C,T}(P) = Σ_{κ∈Cyc(P)} F_{Des R_T(κ)}, where R_T(κ) is the unique rotation in κ whose last piece contains T; (ii) every w whose last piece misses T has a descent at some cut after T's piece; (iii) in every such w, the junction leaving T's piece is a descent; (iv) the label condition (E*_T) of §3 | **PROVEN + audited** ([AudQ] §1) (§3); the characterisation (E*_T) is NOT FOUND in the literature, and elementary; COMPUTED on every natural labelling n ≤ 6 (8267 labelled pairs: (i) holds on 5894, fails on 2373, always exactly when (ii) holds) `[thmQ-iff]`, `[E*]` |
| Q′ | For every P and T, the labelling λ_T (§3.3) is natural, separated and satisfies (E*_T). Under it, \|Des R_T(κ)\| = cdes(κ) − 1, so K_{C,T}(P) = Σ_κ F_{Des R_T(κ)} with \|Des R_T(κ)\| = cdes κ − 1 | **PROVEN + audited** ([AudQ]) (§3.3); COMPUTED on all 3107 pairs (P, T), n ≤ 7 `[lamT]`, `[thmQ]` |
| F+ | K_{C,T}(P) is F-positive for every finite P and every component T. The F-coefficients sum to e_C(P) | **PROVEN + audited** ([AudQ]) (corollary of Q′); **KNOWN IN SUBSTANCE** (Stanley–Gessel fundamental lemma, anchor labelled last; Verdict); COMPUTED on all 3107 pairs n ≤ 7 `[Fpos-all-T]` |
| H | Principal specialisation of Q′ is Theorem H for the labelling λ_T, proved without the telescoping Lemma 1 | **PROVEN + audited** ([AudQ]) (§3.4), for λ_T only; Theorem H for every separated labelling still needs [H]'s Lemma 1 |
| B | Bijective form: under (E*_T), an order-preserving f is T-anchored iff its Stanley word has T's piece last | **PROVEN + audited** ([AudQ]) (§3.2); COMPUTED by listing every map into [3], n ≤ 5 (8600 maps) `[bij]` |
| ✗1 | Lemma 1 lifted: under a separated labelling, each class contributes a single F_D to D_q | **FALSE** (refutation audited, [AudQ]): fails for 1805 of 6996 separated labelled pairs. The class contribution is not even F-positive in those cases `[ctl-perclass-sep]`, `[ctl-perclass-Fpos]` (§4) |
| ✗2 | One labelling for all T: under every fixed separated labelling, some choice of one rotation per class gives K_{C,T} for every T | **FALSE** (refutation audited, [AudQ]): the identity labelling of C_2 ⊔ C_1 fails for T = {0} (§4.2). The weak form is all that is refuted: for n ≤ 7, every disconnected poset (503) has some fixed separated labelling admitting a T-dependent rotation choice for every T ([AudQ] `[rot-choice]`) |
| ✗3 | D(κ) = Des of the lexicographically first min-des rotation under λ_0, any T | **FALSE** (audited, [AudQ]): 766 of 3107 pairs `[ctl-mindes]` (positive control) |
| ✗4 | D(κ) = Des of an arbitrary rotation (the first one listed), under λ_T | **FALSE** (audited, [AudQ]): 766 of 3107 pairs `[ctl-anyrep]` (positive control) |
| P | K_{C,T}(P) is not cyclically quasisymmetric ([PA] §1). It is an F-positive quasisymmetric function: the sub-sum of Gessel's K_P over the linear extensions with T's piece last. For the antichain it is K of A_{n−1} ⊕ 1 | **PROVEN + audited** ([AudQ]) (§5); prior art in §5 and the Verdict |

## 0. Conventions

Notation as in [H] §0. P is a finite poset on n ≥ 1 points with a natural
labelling by 0, …, n − 1. T is a fixed component. For w ∈ Lin P, a cut is
a p ∈ [1, n − 1] such that {w_1, …, w_p} is a union of components. The
cuts split w into pieces. The class κ(w) is the set of rotations of w at
its cuts. It has one member for each piece, and the pieces are rotated
cyclically ([H] §0). Exactly one member of κ has its last piece containing
T. Call it R_T(κ), and put

  L_T(P) = {w ∈ Lin P : the last piece of w contains T} = {R_T(κ) : κ ∈ Cyc(P)}.

C_T(w) = {cuts p : T ⊆ {w_1, …, w_p}} is the set of cuts after T's piece.
It is empty iff w ∈ L_T(P). When it is not empty, its least element is the
junction leaving T's piece.

Gessel's fundamental quasisymmetric function of degree n, for J ⊆ [n − 1],
is

  F_J = Σ x_{i_1} x_{i_2} ⋯ x_{i_n}, summed over i_1 ≤ i_2 ≤ ⋯ ≤ i_n with i_p < i_{p+1} for p ∈ J.

Its principal specialisation is F_J(1^m) = C(m + n − 1 − |J|, n).

## 1. K_{C,T} depends on T

**Example (PROVEN by direct count).** Let P = C_2 ⊔ C_1, with 0 isolated
and 1 < 2.
- *T = {0}.* The condition says f(0) ≥ f(1): otherwise the upper level
  set {1, 2} is a union of components that misses 0. This gives
  K_{C,{0}} = F_∅ + F_{2}.
- *T = {1, 2}.* The condition says f(0) ≤ f(2), and this gives
  K_{C,{1,2}} = F_∅ + F_{1}.

These differ, because F_{1} and F_{2} are linearly independent. Both are
checked against a brute-force sum of x^f in three variables
(`test_chain_count_matches_brute_force`). COMPUTED: K_{C,T} depends on T
for 492 of the 2450 posets with n ≤ 7 `[T-dep]`.

The principal specialisation K_{C,T}(1^m) counts the T-anchored maps into
[m]. By Theorem Ω, reproved in [H] §1 Steps 1–4 (HOLDS in [AudH]), this
count is Ω_C(P, m) for every T. COMPUTED against Ω_C from the Möbius
definition, for m = 0, …, n + 1 and all 3107 pairs (P, T) with n ≤ 7
`[spec]`.

The quantity [PA] computed as "K_C(P)" is K_{C,T} for the component T of
least label in its canonical labelling. Its F-positivity on n ≤ 7 is now a
special case of row F+.

## 2. The descent expansion lifted (Proposition D_q)

**Proposition D_q (PROVEN; COMPUTED `[propD-qsym]`).** For every natural
labelling and every T,

  K_{C,T}(P) = Σ_{w∈Lin P} G_T(w),
  G_T(w) = [C_T(w) ∩ Des w = ∅] Σ_{S ⊆ C_T(w)} (−1)^{|S|} F_{Des(w) ∪ S}.

Moreover, G_T(w) is the generating function Σ x^f of the T-anchored f
whose Stanley word is w.

*Proof.* By [H] §1 Step 5 (the direct argument is in [AudH] §1), every
order-preserving f has a unique word w ∈ Lin P such that f is weakly
increasing along w and strict at Des(w). Conversely, every such sequence
along w is an order-preserving f with Stanley word w. f is T-anchored iff
f(w_p) = f(w_{p+1}) for every p ∈ C_T(w). So the T-anchored f with word w
are the weakly increasing sequences (f(w_1), …, f(w_n)) that are strict
at Des(w) and equal at C_T(w), and x^f = Π_p x_{f(w_p)}.
- If the two sets meet, there are none.
- Otherwise, write "equal at p" as "not strict at p" and use
  inclusion–exclusion over C_T(w). The sequences that are strict at
  Des(w) ∪ S have generating function F_{Des(w)∪S}. ∎

Specialising gives N_T(w, m) of [H] Proposition D, by the Vandermonde-type
identity [H] uses. The unit test `test_inclusion_exclusion_word` checks
G_T(012) = F_∅ − F_{1} for C_2 ⊔ C_1 with T = {0}.

## 3. Theorem Q

### 3.1 Statement

Say that a natural labelling satisfies **(E*_T)** if both of the following
hold:
- a > b whenever a is a maximal element of a non-singleton component V,
  and b is a minimal element of a component U ∉ {T, V};
- if T = {t} is an isolated point, then t > b for every minimal element
  b ∉ T.

Isolated points count as minimal elements.

**Theorem Q (PROVEN; COMPUTED `[thmQ]`, `[thmQ-iff]`, `[E*]`).** For a
natural labelling of P and a component T, the following are equivalent.
- (i) K_{C,T}(P) = Σ_{w∈L_T(P)} F_{Des w} = Σ_{κ∈Cyc(P)} F_{Des R_T(κ)}.
- (ii) (X′_T): for every w ∉ L_T(P), C_T(w) ∩ Des(w) ≠ ∅.
- (iii) (X_T): for every w ∉ L_T(P), the junction leaving T's piece is a
  descent of w.
- (iv) (E*_T).

When they hold, each class contributes exactly one fundamental,
F_{Des R_T(κ)}.

### 3.2 Proof

*(i) ⇔ (ii).* By §0, G_T(w) = F_{Des w} for w ∈ L_T, since C_T(w) = ∅.
By Proposition D_q,

  K_{C,T}(P) − Σ_{w∈L_T} F_{Des w} = Σ_{w∉L_T} G_T(w).

Each G_T(w) is Σ x^f over a set of maps, so this difference is a sum of
monomials with nonnegative coefficients. It vanishes iff every one of these
sets is empty.

The set for w is empty iff C_T(w) ∩ Des(w) ≠ ∅. If the two sets are
disjoint, then f(w_p) = 1 + #{q ∈ Des w : q < p} is weakly increasing,
strict exactly at Des(w), and equal at C_T(w). The second equality in (i)
holds because L_T meets each class exactly once (§0).

*(iii) ⇒ (ii).* Trivial: the junction leaving T's piece is the least
element of C_T(w).

*(ii) ⇒ (iii).* Suppose w ∉ L_T and the junction leaving T's piece is an
ascent. Write w = A c B_1 B_2 ⋯ B_r. Here c is T's piece, the B_i are the
pieces after it (r ≥ 1), and A is the prefix before c. Put

  w′ = A B_2 ⋯ B_r c B_1.

Each block is a union of components written as a linear extension of
itself, so w′ ∈ Lin P.

The cuts of w′ are exactly the boundaries of the pieces of its blocks. A
prefix ending strictly inside a piece X would leave a proper prefix of X
that is a union of components. That is the argument of [H] §0. So c is
still T's piece, and C_T(w′) consists of the single junction from c to B_1.
That junction joins the same two letters as in w, so it is an ascent.
Hence C_T(w′) ∩ Des(w′) = ∅, and (ii) fails.

*Two facts about pieces.*
- (a) The first letter of a piece is minimal in P. It is not an isolated
  point unless the piece is that single point ([H] Lemma 2(a), HOLDS).
- (b) The last letter y of a piece of length ≥ 2 is a maximal element of a
  non-singleton component inside the piece. Anything above y is in y's
  component, hence in the piece, hence after y. And if {y} were a
  component, the piece minus y would be a proper prefix that is a union of
  components.

*(iv) ⇒ (iii).* Let w ∉ L_T. The junction leaving c runs from a = last(c)
to b = first(B_1). By (a), b is a minimal element of a component U that
does not meet c, so U ≠ T.
- If |c| = 1, then T = {t} is isolated and a = t.
- If |c| ≥ 2, then by (b), a is a maximal element of a non-singleton
  component V ⊆ c, so U ∉ {T, V}.

In both cases (E*_T) gives a > b.

*(iii) ⇒ (iv).* Suppose (E*_T) fails. We build a w ∉ L_T whose junction
leaving T's piece is an ascent. In every case, w starts with the
components other than T, V and U, each written as a linear extension. A
prefix of that kind is a union of components, so it ends at a cut.

- *Case V = T, U ≠ T, a ∈ max T, b ∈ min U, a < b.* Write
  w = (others) (T, ending in a) (U, starting with b). This works because
  a is maximal and b is minimal.
- *Case V ≠ T, |T| ≥ 2.* Take a minimal t_0 ∈ T. T's piece is
  c = t_0 (V ∖ a) (T ∖ t_0) a, with each part written as a linear
  extension. No proper prefix of c is a union of components:
  - before T is complete, the prefix contains t_0 but not all of T;
  - after that, a is still missing from V.
- *Case V ≠ T, T = {t}.* Pick a minimal v_0 ∈ V. Then v_0 ≠ a, because V
  is connected with at least two points, so a has something below it. Put
  c = v_0 t (V ∖ {v_0, a}) a. No proper prefix is a union of components:
  each one contains v_0 but not a.

  In both V ≠ T cases, w = (others) c (U, starting with b).
- *Case T = {t}, b ∉ T minimal, t < b.* Write
  w = (others) t (U, starting with b), where U is the component of b.

In each case the last piece of w is U, so w ∉ L_T. The junction leaving
T's piece is a → b (or t → b), and it is an ascent. ∎

*Bijective form (row B).* Under (i)–(iv), the T-anchored f are exactly
the order-preserving f whose Stanley word lies in L_T. Such an f has
G_T(w) ≠ 0 only if w ∈ L_T, and for w ∈ L_T the anchoring condition is
empty. COMPUTED: every order-preserving map into [3] under λ_T, n ≤ 5
(8600 maps) `[bij]`.

COMPUTED, all natural labellings, n ≤ 6:
- 8267 labelled pairs (P, T) in all;
- (E*_T) ⇔ (X_T) ⇔ (X′_T) ⇔ (i) on every one of them;
- (i) holds on 5894 and fails on 2373;
- the stronger and simpler condition (E_T) also suffices: every maximal
  element of a non-singleton component, and T itself if T is isolated, is
  labelled above every minimal element of P ∖ T. It holds on 5833 of them
  `[E=>X=>X']`.

### 3.3 Existence: the labelling λ_T

λ_T lists the elements in this order:
- the non-isolated minimal elements;
- the elements that are neither minimal nor maximal, in a linear extension;
- the isolated points other than T;
- the non-isolated maximal elements not in T;
- the maximal elements of T, or t itself if T = {t} is isolated.

This is [H]'s λ_0 with T's maxima moved to the end.

**Lemma 3 (PROVEN; COMPUTED `[lamT]`).** λ_T is natural, separated, and
satisfies (E*_T).

*Proof.*
- *Natural.* λ_0 is a linear extension ([H] §2.3, HOLDS). Moving maximal
  elements, or an isolated point, to the end keeps it one, since nothing
  lies above them.
- *Separated.* The non-isolated minima come first, and the non-isolated
  maxima come after the middle elements.
- *(E*_T).* Every minimal element outside T is either a non-isolated
  minimum or an isolated point other than T. Both groups come before
  every non-isolated maximum, and before t. ∎

**Corollary Q′ (PROVEN).** Under λ_T, K_{C,T}(P) = Σ_κ F_{Des R_T(κ)},
and for n ≥ 2, |Des R_T(κ)| = cdes(κ) − 1.

*Proof.* The identity is Theorem Q with Lemma 3. For the size:
- *If κ has s ≥ 2 pieces,* R_T(κ) is broken at the junction leaving T's
  piece, which is a descent by (iii). By [H] §0,
  des = d + jd − δ = d + jd − 1 = cdes − 1.
- *If s = 1,* the word is a single piece of length n ≥ 2. Under a
  separated labelling w_1 < w_n ([H] Lemma 2(a)), so cdes = des + 1. ∎

So R_T(κ) is a min-des rotation of κ ([H] Lemma 1: min des = cdes − 1).
It is the particular min-des rotation that is broken where T's piece ends.
This makes precise the guess "Des of the min-des representative under a
separated labelling". The representative and the labelling must both be
tied to T. §4 shows that, in general, neither can be chosen
independently of T (for the representative, see the scope of §4.2).

**Corollary F+ (PROVEN + audited).** For every finite poset P and every
component T, K_{C,T}(P) is F-positive, with Σ_J [F_J] K_{C,T}(P) = e_C(P).

This settles the OPEN item of [PA] §3, for every T. It is KNOWN IN
SUBSTANCE: the Stanley–Gessel fundamental lemma with the anchor labelled
last (Verdict).

### 3.4 Specialisation recovers Theorem H

Apply F_J(1^m) = C(m + n − 1 − |J|, n) to Corollary Q′, and use the
specialisation statement of §1. Under λ_T this gives

  Ω_C(P, m) = Σ_{κ∈Cyc(P)} C(m + n − cdes(κ), n)   (n ≥ 2).

This is Theorem H for the separated labelling λ_T, and it gives
h_C(P) ≥ 0 again.

This proof does not use the per-class telescoping (Lemma 1 of [H]). The
only rotation that contributes is the one broken where T's piece ends. For
another separated labelling, Theorem H is [H]'s statement. That the cdes
distribution does not depend on the separated labelling is [H]'s
corollary, which does use Lemma 1.

For a separated labelling that violates (E*_T), Theorem H still holds, but
its quasisymmetric lift with R_T does not (§4).

## 4. What does not lift

### 4.1 Lemma 1 is a binomial identity, not a quasisymmetric one

Under an arbitrary natural labelling, a class contributes
Σ_{w∈κ} G_T(w) = Σ_{i=0}^{q} G_T(R_i) to Proposition D_q. Notation is as
in [H] Lemma 1: R_0 has T's piece last, and q is the first descent
junction after it. Specialised, this telescopes by Pascal's rule to one
binomial. Before specialisation, the R_i are different rotations, and their
descent sets are shifted against each other, and in general their sum is not one F.

*Example (PROVEN; `test_per_class_negative`).* Take the antichain on
{0, 1, 2}, with T = {1}. Every labelling of an antichain is separated, and
this one violates (E*_T), since 1 < 2. Every position is a cut. The class
{012, 120, 201} contributes:
- G_T(201) = F_{1}, because 1 is last;
- G_T(120) = 0, because C_T = {1, 2} contains the descent 2;
- G_T(012) = F_∅ − F_{2}, because C_T = {2} and Des = ∅.

In total, F_∅ + F_{1} − F_{2}. This specialises to C(m + 2, 3), one
binomial, as Lemma 1 says, but it is not F-positive. The other class,
{021, 210, 102}, contributes F_{2}: only 021 survives. So
K_{C,{1}}(A_3) = F_∅ + F_{1}, which is F-positive, while the class-by-class
split is not. The unit test checks the first class.

COMPUTED over separated labellings, n ≤ 6, every T: the class contribution
is a single F_D for every class on 5191 of 6996 labelled pairs. On the
other 1805 pairs, some class does not contribute a single F. Of the 317 680
classes, 23 117 do not contribute a single F, and every one of those 23 117
contributions has a negative F-coefficient `[ctl-perclass-sep]`, `[ctl-perclass-Fpos]`.

### 4.2 A fixed labelling with no rotation rule

*Example (PROVEN; `test_no_rotation_rule_under_fixed_separated_labelling`).*
Take C_2 ⊔ C_1, with 0 isolated and 1 < 2. This labelling is separated.
The classes are {012, 120} and {102}. By §1, K_{C,{0}} = F_∅ + F_{2}. The
singleton class {102} must contribute F_{Des 102} = F_{1} under any rule
that picks one rotation per class, and F_{1} does not occur in K_{C,{0}}.

So, for this labelling and T = {0}, no choice of D(κ) = Des(some rotation
of κ) works. The labelling satisfies (E*_T) for T = {1, 2} but not for
T = {0}.

This refutes only "every fixed separated labelling admits a rotation rule
for every T". It does not refute "some labelling, fixed in advance, admits
one". For C_2 ⊔ C_1, label the isolated point 1 and the chain 0 < 2. Then
(E*_T) holds for T = {1} (1 > 0) and for T = {0, 2} (2 > 1), so by
Theorem Q, R_T works for both components under one labelling ([AudQ] §2).
- (E*_T) can hold for every T at once only if P has at most one isolated
  point: with two isolated points s, t, the isolated-T clause demands both
  s > t and t > s.
- COMPUTED in [AudQ] `[rot-choice]`, all 503 disconnected posets with
  n ≤ 7: (E*_T) holds for every T under a single labelling on 415 of them,
  and on none of the 88 with two or more isolated points. Yet on all 503,
  some single separated natural labelling has the property that for every
  T, some choice of one rotation per class sums to K_{C,T}. The choice
  depends on T and is found by bipartite matching; it is not an explicit
  rule.

Controls, COMPUTED:
- Des of the lexicographically first min-des rotation, under λ_0, fails
  for 766 of 3107 pairs `[ctl-mindes]`.
- Des of an arbitrary rotation (the first one listed), even under λ_T,
  fails for 766 of 3107 pairs `[ctl-anyrep]`.

## 5. What K_{C,T} is, and prior art

- **Not cyclically quasisymmetric.** See [PA] §1 (smallest case A_3).
  Toric P-partition enumerators ([AGRR] Prop. 3.18) count every rotation
  of a total cyclic order. K_{C,T} counts one rotation per cut class.
- **What it is.** By Theorem Q, K_{C,T}(P) is an ordinary F-positive
  quasisymmetric function. It is the sub-sum of Gessel's K_P = Σ_{w∈Lin P}
  F_{Des w} over the set L_T(P) of linear extensions whose last piece
  contains T, under any labelling satisfying (E*_T). By the bijective form
  (§3.2), it is the enumerator of (P, λ_T)-partitions whose Stanley word
  lies in L_T(P).
  - For connected P, L_T = Lin P and K_{C,T} = K_P.
  - For the antichain with T = {t} and t labelled last, L_T is the set of
    permutations ending in t. So K_{C,{t}}(A_n) = K_{A_{n−1}⊕1} =
    Σ_{u∈S_{n−1}} F_{Des u} (degree n) (PROVEN; `test_antichain_is_ordinal_sum`).
    Directly: the condition says f(t) ≥ f(x) for all x.
  - In general, L_T(P) is not the set of linear extensions of a poset.
    Under λ_T it is one for 2257 of 3107 pairs. The first exception is
    the poset 0 < 2, 0 < 3 plus the isolated point 1, with T = {0, 2, 3}
    COMPUTED. Whether K_{C,T}(P) is always K_{P′} for some poset P′ is
    **OPEN**.
- **Prior art.**
  - The mechanism is Stanley's fundamental lemma and Gessel's expansion
    K_P = Σ_{w∈Lin P} F_{Des w} (Gessel 1984; EC2 §7.19). As in [PA], EC2
    was not re-read; Gessel's expansion is re-verified by [PA] `[qsym]`
    for connected P with n ≤ 7.
  - Theorem Q adds a labelling criterion, (E*_T), under which the
    T-anchoring condition becomes a restriction on the Stanley word.
  - The antichain case is the quasisymmetric form of [Pet] Prop. 1.1 (put
    the anchor last).
  - [PA] read [AGRR], [Pet], [ARR] and [DMR] and found no
    T-anchored or cut-class enumerator. This note did one further search
    (cyclic descents, P-partitions, fundamental expansions of disconnected
    posets) and found nothing closer.
  - Verdict (split, after [AudQ] §3): Corollary F+ is **KNOWN IN
    SUBSTANCE** (fundamental lemma with the anchor labelled last; the
    general disconnected-P anchored version was not found stated). The
    characterisation (i) ⇔ (E*_T) of Theorem Q, the T-dependence of
    K_{C,T}, and the failure of the Lemma 1 lift are **NOT FOUND**, and
    elementary.

## 6. Open points

- **OPEN.** Is there a symmetric or T-free refinement, for example
  Σ_T K_{C,T}(P), with a natural F-expansion over Cyc(P) × components?
- **OPEN.** Is K_{C,T}(P) = K_{P′} for some poset P′, as in the antichain
  case?
- **Not open (closed by row 0; [AudQ]).** Could a separated labelling fixed
  in advance admit a T-free rule D(κ) that is *not* a rotation's descent
  set? No, whenever K_{C,T} depends on T. A T-free D(κ) gives a T-free sum
  Σ_κ F_{D(κ)}, but by row 0, K_{C,T} depends on T for 492 of the 2450
  posets with n ≤ 7. So on those posets no T-free rule of any kind exists,
  under any labelling. The other 1958 posets are the 1947 connected ones,
  where the question is trivial, and 11 disconnected ones on which K_{C,T}
  happens not to depend on T.
- **OPEN.** An *explicit* T-dependent rotation rule under a labelling fixed
  in advance, for P with two or more isolated points. (With at most one
  isolated point, a labelling satisfying every (E*_T) exists on all 415
  such disconnected posets with n ≤ 7, [AudQ] `[rot-choice]`.)

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 95 s):

    python3 qsym_refinement_omega_c.py --nmax 7 --lmax 6 > output/qsym_refinement_omega_c.txt
    python3 -m unittest test_qsym_refinement_omega_c

The script exits 0 iff every claim line passes and every CONTROL line is
refuted somewhere. It imports no other module of the repository. The poset
enumeration and the Möbius computation of Ω_C are copied from
`h_vector_omega_c.py`. K_{C,T} is computed from its definition, by chains
of order ideals in the monomial basis, and converted to the F-basis.
Options:
- `--lmax k`: try every natural labelling for n ≤ k;
- `--specmax k`: the Möbius check for n ≤ k;
- `--bijmax k`: the brute-force map check for n ≤ k.
