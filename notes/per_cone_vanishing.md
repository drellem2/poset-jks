# Per-cone vanishing of χ_V(g): when the terms of Formula Z cancel

This note takes up the open item PC″ of `notes/vanishing_criterion.md`
("[VC]"): an exact criterion for χ_V(g) = 0 on a given cone. Formula Z
([VC] §2) writes

  χ_V(g) = Σ_{X ∈ Z\*(V,g)} μ_{L(A)^g}(0, X) · m_X(V),   m_X(V) ≥ 1,

so χ_V(g) = 0 either because Z\*(V,g) carries no nonzero μ, or because
nonzero terms cancel. Here the cancellation case is classified on the data,
explained for all chambers by Crapo's complementation theorem, and solved
exactly in type A on every cone.

Notation is that of [VC] §§1–2: A is a finite central essential arrangement
in R^d, V a top-cone with L = lin V, g a finite-order linear symmetry with
gA = A and gV = V, U = Fix(g), L(A)^g the g-stable flats ordered by
inclusion, and χ_V(g) = (−1)^d det(g) μ(Λ(V)^g).

Tags:
- **PROVEN**: a full proof is given here, with its inputs named. Every
  PROVEN claim of this note is independently audited in [AudPCV] =
  `notes/audit_per_cone_vanishing.md` (mg-58bc6), verdict HOLDS WITH FIXES:
  all hold, and its corrections F1–F6 and the §3.7 slip are applied here
  (mg-8d776).
- **COMPUTED**: checked by `compute/per_cone_vanishing.py` (see Reproduce).
- **CITED**.
- **CONJECTURED**.
- **REFUTED**: shown false, with a counterexample in the note cited.
- **OPEN**.

## Verdict

| # | Claim | Status | Inputs |
|---|---|---|---|
| M | **Lemma M.** For X ∈ Z\*(g), m_X(all chambers) = (−1)^{dim U} Σ_{Z ∈ L(A)^g, Z ⊇ X, Z ∩ U = 0} μ(Z, R^d) | **PROVEN** (§1); COMPUTED on every X ∈ Z\*(g) of every class of 11 arrangements (149 terms) | W″(c) of [AudW] on the localization at X; audited ([AudPCV] §1). Prior art: not found in the literature searched ([PAPCV]) |
| Cr | **All chambers = Crapo relative to U.** χ_all(g) = (−1)^{dim U} Σ_{X ⊆ Z, X, Z ∈ Z\*(g)} μ(0, X) μ(Z, R^d). When U is a flat, Z\*(g) is the set of complements of U in L(A)^g, and this is Crapo's complementation theorem for the element U. If the complements form an antichain, m_X = (−1)^{dim U} μ(X, R^d) (Hanlon's case) | **PROVEN** (§1), given Lemma M; Crapo CITED. "Z\*(g) = complements" COMPUTED on all 83 classes with U a flat. Audited ([AudPCV] §2). Prior art ([PAPCV] §2): for U a flat, (Cr) is Crapo's theorem (KNOWN); for U not a flat, it is the Björner–Walker split for the convex set Z\*(g), and the vanishing μ_{M∖Z\*}(0̂, 1̂) = 0 that Lemma M supplies was not found | Formula Z, Lemma M |
| Pal | **Lemma Pal.** An anti-automorphism t of a finite poset Q admits a linear extension w with t(w_i) = w_{n+1−i} iff t² = 1 and t has at most one fixed point | **PROVEN** (§2); audited with Lemmas Sh and E ([AudPCV] §3, §4). **KNOWN in substance** ([PAPCV] §1): it is the existence of type-B linear extensions of Chow's B_n posets, stated for Reiner's signed posets; the proof of §2 is a reproof | Chow 2001; Reiner 1993 |
| TA | **Type A, every cone, g = −τ.** Let n ≥ 3 and let τ be an anti-automorphism of the poset P, so that −τ preserves C_P. Then χ_{C_P}(−τ) ≠ 0 iff (TA1) the cycle lengths of τ lie in {m, 2m} for an odd squarefree m; (TA2) every component of P has a ⟨τ⟩-orbit of length m or 2m; (TA3) for every component K, K ∪ τ^m K contains at most one point of an odd cycle of τ; (TA4) if τ has both odd and even cycles, some odd cycle of τ does not consist of isolated points of P. There is an explicit positive formula for \|χ\| (§3) | **PROVEN** (§3); COMPUTED: the closed formula equals sgn(τ) μ(OP(P)^τ) on all 922 pairs with n ≤ 6, on 1,089 involution pairs with n = 7, on 2,736 random pairs with n = 8, 9, 12, and equals χ_V(g) from the face poset on all 1,992 pairs (V, −w) of A_3 and A_4 | CF of [FP] (audited), Hanlon's (H), Theorem A of [VC], Lemmas Pal, Sh, E. Audited ([AudPCV] §4). Prior art: not found in the literature searched ([PAPCV]) |
| TA± | Together with [Thm, eq. closed] for g = +w: an exact per-cone criterion for every element of ±S_n on every cone of the braid arrangement | **PROVEN** (TA here; +w in [Thm], audited) | — |
| TA-L | In type A, whether χ_V(g) = 0 depends only on (lin V, g); the sign of a nonzero χ_V(g) depends only on g | **PROVEN** (Cor. 3.5); audited, including (c) ([AudPCV] §5) | Theorem TA, [Thm] |
| L′ | Neither holds in general. Vanishing is not a function of (lin V, g) on generic 4 planes in R^3 (1 key) and generic 5 hyperplanes in R^4 (4 keys). Both signs occur for one g in B_3, generic 4 in R^3, generic 5 in R^4, B_3 ∖ {z = 0}, the 12- and 13-line hexagon arrangements | **COMPUTED** (§4) | — |
| CO | **Crapo obstruction.** If some element of Λ(V)^g has no complement in Λ(V)^g, then χ_V(g) = 0. In type A every zero from (TA4) is of this kind, with an explicit uncomplemented element | "if": **CITED** (Crapo; stated verbatim in EC1 Ex. 3.92, [PAPCV] §3.1). Type A element: **PROVEN** (§3.6), audited ([AudPCV] §6) | Crapo's complementation theorem |
| CR_V | **Conjecture CR_V.** χ_V(g) = 0 iff Λ(V)^g has an element without a complement. This is a Crapo-type converse on the cone lattice; it implies the CR of [VC] in the cases where [VC]'s lattices are cone lattices | **REFUTED (rank 4)** in [CRV] = `notes/conjecture_cr_v.md` §0: a 12-hyperplane arrangement in R^4 with a 9-element, complemented, non-modular Λ(V)^g and χ_V(g) = 0; independently audited in [AudCRV] = `notes/audit_conjecture_cr_v.md` (refutation holds). PROVEN there for d ≤ 3, for pointed cones, and for the Cor. V zeros of [VC]. COMPUTED here: no counterexample on 18,750 pairs (V, g) (§4), and on all 5,063 lattices OP(P)^{±τ} with n ≤ 6 (both automorphisms and anti-automorphisms); these counts are correct as counts, and the rank-4 pairs sampled here do not include the counterexample. Prior art: not found in the literature searched; the modular case is known (Knop, Lemma A.2), and the converse fails for general lattices (8-element example, [PAPCV] §3.2) | — |
| D | The classification of zeros by arrangement (Cor. V / no nonzero μ / cancellation), including D_4, H_3, F_4 | **COMPUTED** (§4) | — |
| B, D, H, F | An exact per-cone criterion for B_n (n ≥ 5), D_n, H_3, H_4, F_4 | **OPEN** (§5). On the data, no pair cancels in B_2–B_4, D_4 (with triality), H_3, so there PC(a) of [VC] is already an equivalence on every pair tested | — |

**In one line.** On all chambers, cancellation in Formula Z is Crapo's
complementation theorem read relative to the subspace Fix g. On cones of the
braid arrangement it is exactly the failure of four component conditions,
and the surviving value is a signed count of connected permutations, so it
never cancels further. In general, the conjectured criterion is: some element
of Λ(V)^g has no complement.

**Prior art** ([PAPCV] = `notes/prior_art_per_cone_vanishing.md`).
- *Lemma Pal* is known in substance. After labelling the two points of each
  t-orbit ±i and the fixed point 0 (adjoined if absent), (Q, t) is a B_n
  poset in Chow's sense, and its t-palindromic extensions are the type-B
  linear extensions. The "if" direction is the existence of one, which
  follows from Chow's fundamental lemma for type-B P-partitions (Chow 2001,
  Thm 2.1.4; secondary, via Kim–Searles 2026, Thm 2.8). For Reiner's signed
  posets it is stated (Reiner 1993, Thm 3.3, as quoted by Csar 2014 §3.3).
  The "only if" direction is folklore. The proof in §2 is a reproof, kept
  because it is shorter than the translation. Al-Agha–Greechie 2001
  (involutory linear extensions of involution posets) may state the lemma
  verbatim; it could not be accessed, so this was not checked.
- *Theorem Cr.* When U is a flat, (Cr) is Crapo's complementation theorem
  (Crapo 1966, Thm 3; EC1 Ex. 3.92). When U is not a flat, Z\*(g) is a
  convex subset of M = L(A)^g, and the Björner–Walker complementation
  formula for convex subsets (Björner–Walker 1983, used as stated by
  Gálvez-Carrillo–Kock–Tonks 2024) splits μ(M) as μ_{M∖Z\*}(0̂, 1̂) plus
  the double sum of (Cr). So (Cr) is equivalent to μ_{M∖Z\*}(0̂, 1̂) = 0.
  That vanishing, i.e. Lemma M, was not found in the literature searched.
- *Theorem TA, Lemma M, Conjecture CR_V*: not found in the literature
  searched ([PAPCV] §0). This is the result of a search, not a claim of
  novelty.
- *CR_V, known cases.* For a finite modular lattice, μ(0̂, z) ≠ 0 iff
  [0̂, z] is complemented (Knop, arXiv:2209.10337, Lemma A.2), and this
  applies to fixed sublattices Λ^g of a modular Λ (Knop, after (A.8)). The
  lattices Λ(V)^g are not modular in general, so this does not cover CR_V.
  For general finite lattices the converse of Crapo's corollary is false: the
  smallest complemented lattice with μ(0̂, 1̂) = 0 has 8 elements ([PAPCV]
  §3.2).

---

## 1. All chambers: Formula Z is Crapo's theorem relative to U

This answers the question left unchecked in
`notes/prior_art_vanishing_criterion.md` ("[PA]") §2.2.

**Lemma M (PROVEN; input W″(c) of [AudW, §2], audited in [AudW2]).** Let
X ∈ Z\*(g). Then

  m_X(all) = (−1)^{dim U} Σ_{Z ∈ L(A)^g, Z ⊇ X, Z ∩ U = 0} μ_{L(A)^g}(Z, R^d).

*Proof.*
- If X = R^d (possible only when U = 0), the only Z is R^d, and both sides
  are 1 by the rank-0 convention of [VC] §2 step 1. Assume X ≠ R^d, so
  A_X/X has rank codim X ≥ 1.
- Apply W″(c) to (A_X/X, all chambers, ḡ), exactly as in [VC] §2 steps 1–4.
- By [VC] §2 step 3, the index set is {Z ∈ L(A)^g : Z ⊇ X, Z ∩ U = 0}.
- By step 4, the right side is m_X(all), since X ∈ Z\*(g).
- The Z-term is χ of all chambers of A_Z/Z at ḡ, that is
  (−1)^{codim Z} det(ḡ | R^d/Z) μ([Z, R^d]^g). The flats of A_Z/Z are the
  flats containing Z.
- Fix(ḡ on R^d/Z) = (U + Z)/Z ([VC] §2 step 2) has dimension dim U, because
  Z ∩ U = 0.
- The sign rule ([AudFP] §A.1(i)) gives det(ḡ | R^d/Z) = (−1)^{codim Z − dim U}.
  So the Z-term is (−1)^{dim U} μ(Z, R^d). ∎

**Theorem Cr (PROVEN; inputs Formula Z, Lemma M).** Write Z\* = Z\*(g) and
M = L(A)^g. Then

  χ_all(g) = (−1)^{dim U} Σ_{X, Z ∈ Z\*, X ⊆ Z} μ_M(0, X) μ_M(Z, R^d).      (Cr)

Moreover:
- (a) If U is a flat, then U ∈ M, and Z\* is the set of complements of U in M.
  Since χ_all(g) = (−1)^d det(g) μ(M) = (−1)^{dim U} μ(M), (Cr) is then
  Crapo's complementation theorem ([PA] §2.2; Crapo 1966, as stated in
  Stanley 1982, §7) for the element U of M.
- (b) If no two elements of Z\* are comparable, then
  m_X(all) = (−1)^{dim U} μ_M(X, R^d) for every X ∈ Z\*.

*Proof.*
- (Cr) is Formula Z for V = all chambers, with Lemma M substituted. For
  Z ⊇ X ∈ Z\*, Z + U lies in no hyperplane, so the Z of Lemma M are exactly
  the Z ∈ Z\* with Z ⊇ X.
- (a) The meet of X and U in M is X ∩ U. It is 0̂ iff X ∩ U = 0.
- The join of X and U in M is the smallest g-stable flat containing X + U.
  This is R^d iff no hyperplane contains X + U. The smallest flat containing
  X + U is g-stable, since g permutes the hyperplanes containing X + U.
- So "X ∈ Z\*" is "X is a complement of U".
- (b) Only Z = X survives in Lemma M. ∎

Remarks.
- When U is not a flat, (Cr) is Crapo's formula for a "virtual" element: the
  subspace U is not in M, but "X ∩ U = 0" and "X + U in no hyperplane" still
  make sense. Crapo's theorem is pure lattice theory. Lemma M is geometric,
  and it is what Formula Z adds. Precisely ([PAPCV] §2): Z\* is convex in
  M, and the Björner–Walker formula for a convex subset gives
  μ(M) = μ_{M∖Z\*}(0̂, 1̂) + Σ_{X ≤ Z in Z\*} μ_M(0̂, X) μ_M(Z, R^d), so
  (Cr) is equivalent to μ_{M∖Z\*}(0̂, 1̂) = 0.
- Hanlon's case ([PA] §2.1): braid arrangement, w ∈ S_n. There U is the hinge
  flat, which is modular. Its complements form an antichain, and
  μ(X, R^d) = ±(m − 1)! for every complement. Stanley's modular factorization
  is the further collapse in which all the [X, R^d] are isomorphic to [0, U].
  Neither is needed for (Cr).
- COMPUTED (`[M]`): Lemma M on all 149 pairs (class, X ∈ Z\*(g)) of the 11
  arrangements of §4, and "Z\*(g) = complements of U" on all 83 classes whose
  U is a flat.

**What this suggests for cones.** Crapo's theorem has a corollary: an
element without a complement forces μ = 0. On all chambers this is the
mechanism of [FPM] case (a) and of CR in [VC]. Λ(V)^g is a finite lattice for
every cone, so the same corollary applies to it (CO below). The type A
theorem (§3) shows that all the type-A cancellations that are not explained
by an empty Z\*(V,g) are of this kind. That motivates Conjecture CR_V (§4).

## 2. Two lemmas on posets

Throughout, an *anti-automorphism* of a poset Q is a bijection t with
i <_Q j ⇒ t(j) <_Q t(i). A linear extension w = w_1 ⋯ w_n of Q is
*t-palindromic* if t(w_i) = w_{n+1−i} for all i. Write pal_t(Q) for their
number.

**Lemma Pal (PROVEN).** Q has a t-palindromic linear extension iff t² = 1 and
t has at most one fixed point.

*Proof.*
- *Only if.* Applying the identity twice gives t²(w_i) = w_i. A fixed point
  x = w_i satisfies w_i = w_{n+1−i}, so i is the middle position.
- *If*, by induction on |Q|. The cases |Q| ≤ 1 are clear. Let |Q| ≥ 2.
  - Some minimal element x has t(x) ≠ x. Otherwise every minimal element is
    fixed, so there is only one, x_0. Since t is an anti-automorphism, x_0
    is also the unique maximal element, which forces Q = {x_0}.
  - t(x) is maximal. Q′ = Q ∖ {x, t(x)} is t-stable, t|_{Q′} is an
    anti-automorphism with at most one fixed point, and by induction Q′ has
    a palindromic extension w′.
  - Then x w′ t(x) is a palindromic linear extension of Q. ∎

This is a reproof of a known fact: the "if" direction is the existence of
type-B linear extensions of Chow's B_n posets, stated for Reiner's signed
posets (see Prior art under the Verdict, and [PAPCV] §1).

**Lemma Sh (shuffle; PROVEN).** Let Q = Q_1 ⊔ ⋯ ⊔ Q_r be a disjoint union of
posets with no relations between the parts. Let t act on each Q_j as an
involutive anti-automorphism t_j. Put h_j = ⌊|Q_j|/2⌋. If at most one t_j
has a fixed point, then

  pal_t(Q) = (h_1 + ⋯ + h_r)! / (h_1! ⋯ h_r!) · Π_j pal_{t_j}(Q_j).

If two of the t_j have fixed points, pal_t(Q) = 0.

*Proof.*
- The second statement is Lemma Pal.
- Otherwise, t maps the set of positions of Q_j-letters in a palindromic w
  to itself, reversed. So the restriction of w to Q_j is t_j-palindromic.
- w is determined by its first ⌊n/2⌋ letters and its middle letter (the
  fixed point, if any). The first half restricts to the first halves of the
  w_j.
- Conversely, any shuffle of the first halves, completed palindromically, is
  a linear extension, since there are no relations between parts.
- The number of shuffles is the multinomial coefficient. ∎

**Lemma E (connected permutations; PROVEN).** Let 𝒢 be a finite set of
"units" u with weights h_u ≥ 0. For S ⊆ 𝒢, put H(S) = Σ_{u ∈ S} h_u. Let
c(S) be the number of permutations of a set of H(S) points, split into
labelled groups of sizes h_u (u ∈ S), whose *unit graph* is connected. In
the unit graph u and v are joined when some cycle meets both groups. Then:
- (i) H(S)! = Σ_{π ∈ Π(S)} Π_{B ∈ π} c(B), hence
  c(S) = Σ_{π ∈ Π(S)} μ_Π(π, 1̂) Π_{B ∈ π} H(B)!;
- (ii) c(S) > 0 iff |S| = 1 or every u ∈ S has h_u ≥ 1.

Let ℱ ⊆ 𝒢 be a set of marked units, 𝒯 = 𝒢 ∖ ℱ, and k = |ℱ|. Put
F̃(S) = H(S)! · [|S ∩ ℱ| ≤ 1]. Then
- (iii) Φ := Σ_{π ∈ Π(𝒢)} μ_Π(π, 1̂) Π_{B ∈ π} F̃(B) equals c(𝒢) if k = 0,
  and otherwise

    Φ = (−1)^{k−1} (k − 1)! Σ_{(S_f)_{f ∈ ℱ}} Π_{f ∈ ℱ} c({f} ∪ S_f),

  the sum running over the ordered set partitions of 𝒯 into k labelled,
  possibly empty, parts.

*Proof.*
- (i) Send a permutation to the partition of S into the components of its
  unit graph. This is a bijection from permutations to pairs (π, a
  connected permutation on each block). Möbius inversion in the partition
  lattice gives the second form (the exponential formula, Stanley EC2,
  Cor. 5.1.6).
- (ii) A unit with h_u = 0 has no points, so it is an isolated vertex. If
  all h_u ≥ 1, a single cycle through all points connects everything.
- (iii) For functions on finite subsets with value 1 at ∅, write
  exp(ψ)(S) = Σ_π Π_B ψ(B). Then exp and the logarithm
  log(f)(S) = Σ_π μ(π, 1̂) Π_B f(B) are inverse bijections (EC2 §5.1). So it
  suffices to show exp(ψ) = F̃ for the function ψ defined by the right side
  of (iii) on every subset. This means ψ(B) = c(B) if B ∩ ℱ = ∅, and the
  displayed formula, with ℱ replaced by B ∩ ℱ and 𝒯 by B ∩ 𝒯, otherwise.
  - Expand exp(ψ)(S). A term is: a partition of S into "c-blocks", namely
    T-only blocks and one block {f} ∪ S_f for each f ∈ S ∩ ℱ; together with
    a set partition σ of S ∩ ℱ recording which marked units shared a
    ψ-block. Its weight is Π c(c-blocks) times Π_{β ∈ σ}(−1)^{|β|−1}(|β|−1)!.
  - This correspondence is bijective.
  - Summing over σ for fixed c-blocks gives Σ_{σ ∈ Π(S ∩ ℱ)} μ(0̂, σ), which
    is 1 if |S ∩ ℱ| ≤ 1 and 0 otherwise.
  - So exp(ψ)(S) = [|S ∩ ℱ| ≤ 1] · Σ (partitions of S into c-blocks)
    = [|S ∩ ℱ| ≤ 1] · H(S)!, by (i).
  - When |S ∩ ℱ| ≤ 1, every partition of S has at most one marked unit per
    block, so the last sum is the whole of (i). ∎

## 3. Type A on every cone

### 3.1 Setting

Let A be the braid arrangement in R^n_0, n ≥ 3, with hyperplanes
H_ij = {x_i = x_j}. The top-cones are the poset cones
C_P = {x : x_i ≤ x_j for i <_P j} ([GT] §0, [FP]), and lin C_P = X_{comp(P)},
the functions constant on the connected components of P. Flats are X_π,
with X_π ⊆ X_ρ iff π is coarser than ρ.

For ε = ±1 and a permutation τ, the map g = ετ acts by (gx)_{τ(i)} = ε x_i.
- g = +τ preserves C_P iff τ ∈ Aut(P). That case is [Thm, eq. closed]:
  χ_{C_P}(τ) ≠ 0 iff μ(ord τ) ≠ 0 and ⟨τ⟩ acts freely on the components of
  P.
- g = −τ preserves C_P iff τ is an anti-automorphism of P. If x_i ≤ x_j,
  then (gx)_{τ(j)} ≤ (gx)_{τ(i)}.
- Λ(C_P) is dual to OP(P), the partitions with acyclic quotient, and
  −τ acts on flats as τ does. So χ_{C_P}(−τ) = sgn(τ) μ(OP(P)^τ). The sign
  is (−1)^{n−1} det(−τ | R^n_0) = sgn τ.

Fix g = −τ with τ an anti-automorphism of P. Call a point *odd* if it lies
on an odd cycle of τ, and let O be the set of odd points.

**Theorem TA (PROVEN).** χ_{C_P}(−τ) ≠ 0 if and only if:
- **(TA1)** the cycle lengths of τ lie in {m, 2m} for one odd squarefree m;
- **(TA2)** every component K of P has ⟨τ⟩-orbit {K, τK, …} of length m or
  2m;
- **(TA3)** for every component K, the set b(K) = K ∪ τ^m K contains at most
  one odd point;
- **(TA4)** if τ has both odd and even cycles, then some odd cycle of τ does
  not consist of isolated points of P.

Under (TA1)–(TA3) the value is given by (3.3)–(3.5) below. Its sign is
μ(m)(−1)^{k−1} if τ has k ≥ 1 odd cycles, and μ(m) if it has none.

The smallest instance is the cancelling pair of [VC] §5: A_2, all chambers,
g = −(1 2). P is an antichain, the fixed point 3 is isolated, and 1 2 is a
2-cycle, so (TA4) fails. Adding relations that put the fixed point into a
larger component revives χ. For example, for P = {0 < 1 < 2} ⊔ {3} ⊔ {4}
and τ = (0 2), χ = 2, although 3 and 4 are isolated fixed points (COMPUTED,
test `test_non_isolated_fixed_point_revives`).

### 3.2 The CF expansion

The proof uses Theorem CF of [FP] (PROVEN, audited in [AudFP]). For every
(A, V, g),

  χ_V(g) = Σ_{Y ∈ 𝓛^g} μ_{𝓛^g}(0, Y) · #{chambers K of A_Y in |V| with gK = K},

where 𝓛^g is the set of g-stable flats inside L.

*Necessity of (TA1).* If (TA1) fails, −τ vanishes on every cone by
Theorem A of [VC] (PROVEN, audited twice). Assume (TA1) from now on.

*Terms.* Let Y = X_ρ, with ρ a τ-stable partition coarser than comp(P), b
blocks, and τ̄ the induced permutation of the blocks.
- [0, X_ρ] in 𝓛^g is the lattice of τ-stable coarsenings of ρ, so
  μ(0, X_ρ) = μ(Π_b^{τ̄}). By Hanlon's formula ((H) of [VC] §4; [FPM] (ii)),
  this is 0 unless all τ̄-orbits have one length ℓ. Then it is
  (−1)^{r−1} μ(ℓ) ℓ^{r−1} (r − 1)!, with r = b/ℓ.
- A_Y = {H_ij : i, j in one block}. Its chambers are the tuples (w_B) of
  linear orders of the blocks. Since every relation of P lies inside a
  block, such a chamber lies in |C_P| iff each w_B ∈ Lin(P|_B).
- g sends the chamber (w_B) to the chamber whose order on τ̄B is the image
  of w_B under τ, reversed. So a fixed chamber is determined by one w_B per
  τ̄-orbit (B, …, τ̄^{ℓ−1}B), and that w_B must be fixed by (−τ)^ℓ. For ℓ odd
  this means w_B is τ^ℓ-palindromic. For ℓ even it means τ^ℓ(w_B) = w_B,
  which happens iff τ^ℓ is the identity on B.

*Which ℓ survive.* Let ℓ be the common orbit length, and let B be a block
with a nonzero count.
- If ℓ is odd, τ^ℓ is an involution on B (Lemma Pal). On a point of a cycle
  of length m or 2m this forces m | ℓ. Also ℓ divides the order of τ̄, which
  divides 2m. So ℓ = m.
- If ℓ is even, τ^ℓ = 1 on B forces m | ℓ | 2m, so ℓ = 2m.

Hence χ = S_m + S_{2m}, where S_ℓ collects the ρ whose τ̄-orbits all have
length ℓ.

*Necessity of (TA2).* Let K ⊆ B be a component with orbit length s, so
s | 2m. Then τ^s B ∩ B ⊇ K, so τ^s B = B and ℓ | s.
- ℓ = m forces s ∈ {m, 2m}.
- ℓ = 2m forces s = 2m.
- So if some s ∉ {m, 2m}, both sums are empty and χ = 0.

Assume (TA2). Two further facts:
- If some s = m, or if O ≠ ∅, then S_{2m} is empty. A block of orbit length
  2m cannot contain a component with τ^m K = K, nor an odd point, which τ^m
  fixes.
- In particular, if O ≠ ∅ then χ = S_m.

### 3.3 Reduction of S_m to Lemma E

*Units.*
- The sets b(K) = K ∪ τ^m K form a τ-stable partition ρ_0, because they are
  unions of ⟨τ^m⟩-orbits of components.
- Each b(K) has τ̄-orbit of length exactly m. Indeed τ^m b = b, and
  τ^j b = b with 0 < j < m would force τ^j K ∈ {K, τ^m K}, against (TA2).
- A *unit* is a τ̄-orbit of ρ_0-blocks, so it consists of m blocks. Let
  𝒢 be the set of units, N = |𝒢|, and b_u one block of the unit u.

*The ρ of S_m.*
- Every block B of such a ρ is τ^m-stable, so it is a union of ρ_0-blocks.
- It contains at most one ρ_0-block of each unit. Two would give τ^j B = B
  with 0 < j < m.
- So ρ is the same as a partition γ of 𝒢 into r groups, together with an
  alignment for each group G. There are m^{|G|−1} alignments, and b = mr.

*The count.* For a group G, a block B_G of ρ is a disjoint union of one
ρ_0-block from each unit of G, with τ^m acting on each part as an involutive
anti-automorphism.
- Each part is isomorphic to b_u, or to its dual, as a poset with involution
  (via a power of τ). So pal_{τ^m} of the part is pal_{τ^m}(b_u).
- The fixed points of τ^m on b_u are the odd points of b_u.
- By Lemma Sh, pal_{τ^m}(P|_{B_G}) is
  [at most one odd point in B_G] · H(G)! / Π_{u ∈ G} h_u! · Π_{u ∈ G} pal_u,
  where h_u = ⌊|b_u|/2⌋ and pal_u = pal_{τ^m}(P|_{b_u}).

Call u an *F-unit* if b_u contains an odd point, ℱ the set of F-units and
k = |ℱ|. Summing, and using m^{r−1} · m^{Σ_G(|G|−1)} = m^{N−1}:

  S_m = μ(m) m^{N−1} · Π_{u ∈ 𝒢} (pal_u / h_u!) · Φ,      (3.3)

with Φ the sum of Lemma E(iii) for these weights h_u and marked set ℱ.

Facts about the units:
- By Lemma Pal, pal_u > 0 iff b_u has at most one odd point. This is (TA3).
  So (TA3) is necessary, and is assumed from now on.
- Then each block of an F-unit holds exactly one odd point. The m odd points
  of the unit form a τ-stable set, so they are one odd cycle. Hence k is the
  number of odd cycles of τ.
- h_u = 0 iff b_u is a single point. That point is odd, since an even point
  x has τ^m x ≠ x in b_u. So h_u = 0 iff u is an odd cycle of isolated
  points of P. Units without odd points have h_u ≥ 1.

### 3.4 The three cases

**Case I: O ≠ ∅ (k ≥ 1).** Then χ = S_m. By Lemma E(iii),

  χ = μ(m) m^{N−1} Π_u (pal_u / h_u!) · (−1)^{k−1}(k − 1)! Σ_{(S_f)} Π_{f ∈ ℱ} c({f} ∪ S_f).      (3.4)

Every summand is ≥ 0. By Lemma E(ii), a summand is positive iff every f
with S_f ≠ ∅ has h_f ≥ 1.
- If 𝒯 = ∅, the summand with all S_f empty is positive.
- If 𝒯 ≠ ∅, a positive summand exists iff some F-unit has h_f ≥ 1: give all
  of 𝒯 to it.

𝒯 ≠ ∅ means there is a unit without odd points, hence an even cycle. And
"all F-units have h_f = 0" means every odd cycle consists of isolated
points. Conversely, if an even cycle exists but 𝒯 = ∅, an even point lies in
a block b(K) of an F-unit, together with an odd point p. Since τ^m p = p,
K = τ^m K contains both points, so p is not isolated and (TA4) holds. So
χ ≠ 0 iff (TA4), and the sign is μ(m)(−1)^{k−1}.

**Case IIa: O = ∅, and some component has orbit length m.** Then S_{2m} is
empty and ℱ = ∅. So

  χ = μ(m) m^{N−1} Π_u (pal_u / h_u!) · c(𝒢).

All h_u ≥ 1, and all pal_u > 0 by Lemma Pal (τ^m is fixed-point-free on
b_u). So χ ≠ 0, with sign μ(m).

**Case IIb: O = ∅, and every component has orbit length 2m.** Then each
unit is the ⟨τ⟩-orbit of one component K_u, b_u = K_u ⊔ τ^m K_u, and
h_u = |K_u|.
- The ρ of S_{2m} are the groupings of the units, with (2m)^{|G|−1}
  alignments per group G. A block contains at most one component of each
  orbit, or τ^j B = B with 0 < j < 2m.
- The counts are |Lin(⊔_{u ∈ G} K_u)| = H(G)!/Π h_u! · Π |Lin K_u|.
- The Möbius factor is (−1)^{r−1} μ(2m)(2m)^{r−1}(r−1)!, and μ(2m) = −μ(m).

So

  χ = μ(m) c(𝒢) Π_u (1/h_u!) · [ m^{N−1} Π_u pal_u − (2m)^{N−1} Π_u |Lin K_u| ].      (3.5)

pal_u ≥ 2|Lin K_u|. For w ∈ Lin(K_u), both w · rev(τ^m w) and
τ^m(w)-first variants (w′ · rev(τ^m w′) for w′ ∈ Lin(τ^m K_u)) are
palindromic extensions, and the two families are disjoint. So the bracket
is at least 2^{N−1} m^{N−1} Π |Lin K_u| > 0, and χ ≠ 0 with sign μ(m).

**Conclusion.** Under (TA1) and (TA2), χ ≠ 0 iff (TA3) and (TA4). (TA4) is
vacuous in Case II. Without (TA1) or (TA2), χ = 0 (§3.2). This proves
Theorem TA. ∎

### 3.5 Corollaries

**Cor. 3.5 (PROVEN).**
- (a) For g ∈ ±S_n and every cone C_P, whether χ_{C_P}(g) = 0 depends only
  on (comp(P), g), that is on (lin V, g). For +w this is [Thm, eq. closed].
  For −τ, (TA1)–(TA4) mention only τ and the partition into components;
  isolated points are the singleton blocks.
- (b) The sign of a nonzero χ_{C_P}(g) depends only on g:
  - μ(m)(−1)^{k−1}, or μ(m), for g = −τ;
  - sgn(w) μ(ord w) for g = +w. The Lie character there is
    μ(o) Σ e_C(·) ≥ 0, and χ is its det(w)-twist.
- (c) In type A, the terms of Formula Z cancel exactly when the pair
  satisfies (TA1)–(TA3) but not (TA4), and Z\*(C_P, −τ) carries a nonzero μ.
  On the data of [VC] §5 these are the −w with w an involution with a fixed
  point. By (TA4), a fixed point of w then lies in a component of size ≥ 2
  only if χ ≠ 0.

*Proof of (c).* Cancellation means χ = 0 while Z\*(C_P, −τ) carries a
nonzero μ. Under (TA1)–(TA3), χ = 0 iff (TA4) fails (Theorem TA), and if
(TA1) fails, Z\*(C_P, −τ) ⊆ Z\*(−τ) carries no nonzero μ (necessity part of
the proof of (A−) in [VC] Theorem A). It remains to show: *if (TA1) holds
and (TA2) or (TA3) fails, then no X ∈ Z\*(C_P, −τ) has μ(0, X) ≠ 0*
([AudPCV] §5).
- Let X = X_ρ ∈ Z\*(C_P, −τ) with μ(0, X) ≠ 0. By Hanlon, all τ̄-orbits of
  blocks have one length ℓ.
- ℓ is odd. If ℓ is even, the vector equal to (−1)^j on τ̄^j B, along one
  orbit, is nonzero, lies in R^n_0, and lies in X ∩ U. This contradicts
  X ∩ U = 0.
- So ℓ | m, and every block B is τ^m-stable.
- On a block B, every vector of X + U has x_i − x_j = u_i − u_j. Every
  u ∈ U vanishes on odd points and satisfies u_{τ^e i} = (−1)^e u_i. So
  "X + U in no hyperplane" forbids two odd points in one block, and two
  points i ≠ τ^{2a} i in one block.
- (TA3) holds: b(K) ⊆ B, since τ^m B = B, so b(K) has at most one odd point.
- (TA2) holds: let K ⊆ B have orbit length s ∉ {m, 2m}, so s | 2m and
  m ∤ s. Take x ∈ K. If x is odd, τ^s x ≠ x is a second odd point of
  K ⊆ B. If x is even, τ^{2s} x ≠ x (as 2s < 2m) lies in K ⊆ B. Either way
  this contradicts the previous bullet. ∎

COMPUTED in [AudPCV]: on n ≤ 6, all 121 cancelling pairs have (TA4) as the
failing condition, and every (TA4) zero has a nonzero μ on Z\*.

The "sign-reversing involution" suggested in [VC] §5 is not what happens.
In Formula Z the terms do not pair off. For example, −(1 2) on all chambers
of A_4 has terms 2, 2, 2, −6 with all m_X = 1. CF regroups them into Lemma
E, where the logarithm of a truncated exponential has one sign. The only
remaining source of zeros is a unit with no points that must be joined to
something: an isolated odd cycle in the presence of an even one.

### 3.6 The zeros of (TA4) are Crapo obstructions

Suppose (TA1)–(TA3) hold, but every odd cycle consists of isolated points
and an even cycle exists. Let A_0 be the set of odd points (all isolated),
and Q = [n] ∖ A_0 ≠ ∅. Let a ∈ OP(P)^τ be the partition with one block Q
and singletons on A_0. It is τ-stable and acyclic, since A_0 is isolated.

**Claim (PROVEN).** a has no complement in OP(P)^τ, so μ(OP(P)^τ) = 0 by
Crapo's theorem (CITED). This is a second proof of the zero direction of
(TA4).

*Proof.*
- Meets in OP(P)^τ are common refinements: OP(P) is meet-closed
  ([Thm, lem:interval]), and τ-stability is preserved.
- The partition join x ∨ a is τ-stable. Its quotient has edges only inside
  the block containing Q, so it is acyclic, and it is the join in OP(P)^τ.
- So x is a complement of a iff x separates the points of Q and every block
  of x meets Q.
- Then φ: A_0 → Q, sending a point to the unique Q-point of its block, is
  τ-equivariant.
- An odd point p has τ^m p = p, so τ^m φ(p) = φ(p). But every point of Q
  lies on a 2m-cycle, a contradiction. ∎

COMPUTED (test `test_crapo_obstruction_element`) on {0 < 1} ⊔ {2} ⊔ {3},
τ = (0 1).

### 3.7 Checks

All COMPUTED by `[TA]` and `[TAarr]`:
- the closed formula (3.3)–(3.5) equals sgn(τ) μ(OP(P)^τ), and the criterion
  and sign rule hold, on every anti-automorphism of every poset with
  3 ≤ n ≤ 6 (922 pairs, 258 nonzero; cases I/IIa/IIb all occur);
- the same for every involution with a fixed point and a 2-cycle on the
  posets with n = 7 obtained by adding a maximal element (1,089 pairs);
- the same on random τ-invariant posets: n = 8 with τ of types (2,2,2,1) and
  (2,2,2,2); n = 9 with (6,3); n = 12 with (6,3,3) and (6,6). This is 2,736
  pairs and covers m = 3;
- independently of the poset model, the closed formula equals χ_V(g)
  computed from the face poset of the braid arrangement, for every cone and
  every −w ∈ Stab(V), in A_3 and A_4 (1,992 pairs);
- negative controls: dropping (TA4) misclassifies pairs already at n = 3
  (4 pairs, including the A_2 pair of §3.1; [AudPCV] §4), and in Case IIb the ℓ = 2m correction of (3.5) is needed (tests).

## 4. Data on all arrangements: classification and Conjecture CR_V

**Crapo obstruction (CO; CITED).** Λ(V)^g is a finite lattice, bounded by
0 and R^d. Λ(V) is closed under the join of flats: if F, G are faces of V,
then the composition F ∘ G is a face of V (x + εy ∈ |V| for x ∈ F, y ∈ G
and small ε > 0), and its span is the smallest flat containing
span F + span G. With bottom 0 it is a finite lattice. g acts on it by
automorphisms, so Λ(V)^g is a lattice with the ambient join. Its meet is
in general *not* intersection: Λ(V) need not be closed under intersection
(P = {0 < 2, 1 < 3}: X_{03|1|2} and X_{12|0|3} are spans of faces, their
intersection X_{03|12} is not; [AudPCV] §6, F6). So if some element has no
complement in Λ(V)^g, μ(Λ(V)^g) = 0 and χ_V(g) = 0 (Crapo).

**Conjecture CR_V (REFUTED in rank 4, [CRV] §0; audited in [AudCRV]).**
χ_V(g) = 0 iff Λ(V)^g contains an element without a complement.

It is false in rank 4 and PROVEN in rank ≤ 3 and for pointed cones ([CRV]
Theorems 3 and P). [CRV] Theorem Q shows that the Cor. V zeros of [VC] are
Crapo zeros, with the explicit uncomplemented elements cl(L + U) and cl(U),
and [CRV] Lemma K extends Theorem Cr(a) from all chambers to every cone.

This would give an exact per-cone criterion that does not pass through the
signed sum. CR of [VC] (for the lattices [0, X] in L(A)^g, X ∈ Z\*(g)) is the
same statement for the special cones that are top-lunes. For a minimal top-lune
V♯ with lin V♯ = X, χ_{V♯}(g) = μ(0, X) ([VC] Thm S). Whether Λ(V♯)^g and
[0, X]^g have the same complementation behaviour was not checked.

COMPUTED (`[CRV]`, `[CRV-Cox]`). Pairs are (class representative g of G,
every g-stable top-cone V) for the arrangements built in
`audit2_vanishing_criterion.py`. For B_4, D_4, H_3 and F_4 they follow the
convention of [VC] §7 without witness cones: W-orbit representatives V,
classes of Stab_G(V), with F_4 sampled. Column meanings:
- "Cor. V": a hyperplane contains L + U;
- "no μ": Z\*(V,g) carries no nonzero μ;
- "canc.": cancellation;
- "mixed (L,g)": keys (lin V, g) on which some cones vanish and others do
  not;
- "±": classes with nonzero values of both signs.

| arrangement | pairs | χ ≠ 0 | Cor. V | no μ | canc. | CR_V | mixed (L,g) | ± |
|---|---|---|---|---|---|---|---|---|
| A_2 (±S_3) | 30 | 24 | 2 | 1 | 3 | holds | 0 | 0 |
| A_3 (±S_4) | 300 | 266 | 24 | 7 | 3 | holds | 0 | 0 |
| A_4 (±S_5) | 4,634 | 4,292 | 268 | 34 | 40 | holds | 0 | 0 |
| B_2 | 45 | 41 | 4 | 0 | 0 | holds | 0 | 0 |
| B_3 | 1,106 | 998 | 106 | 2 | 0 | holds | 0 | 1 |
| generic 4 in R^3 | 122 | 112 | 0 | 1 | 9 | holds | 1 | 1 |
| generic 5 in R^4 | 382 | 352 | 6 | 6 | 18 | holds | 4 | 1 |
| B_3 ∖ {z = 0} | 832 | 708 | 82 | 6 | 36 | holds | 0 | 1 |
| A_3 minus a plane | 192 | 172 | 12 | 1 | 7 | holds | 0 | 0 |
| hexagon, 12 lines | 3,780 | 3,472 | 224 | 8 | 76 | holds | 0 | 1 |
| hexagon, 13 lines | 5,096 | 4,650 | 446 | 0 | 0 | holds | 0 | 2 |
| B_4 | 647 | 358 | 283 | 6 | 0 | holds | — | — |
| D_4 (W ⋊ S_3) | 476 | 297 | 174 | 5 | 0 | holds | — | — |
| H_3 | 167 | 103 | 58 | 6 | 0 | holds | — | — |
| F_4 (sampled) | 144 | 36 | 104 | 2 | 2 | holds | — | — |

The pair totals of the first eleven rows count every g-stable cone, not
orbit representatives, so they differ from [VC] §7 and [AudVC2] §5. The
B_4, D_4 and H_3 totals are those of [VC] §7 minus its witness cones
(668 − 21, 503 − 27, 174 − 7). The cancellation and zero counts of those
rows agree with [VC] §7. The F_4 row (two cancelling pairs, all chambers,
the two classes of order 6 with (dim Fix g^k) = (1,2,1,4)) also agrees.
Totals: 18,750 pairs; CR_V holds on all, and on all 5,063 lattices
OP(P)^{±τ} with n ≤ 6 (type A, automorphisms and anti-automorphisms).
These counts are correct as counts. They are consistent with [CRV]: 11,428
of these pairs have rank 3, where CR_V is a theorem, and the rank-4 rows
(A_4, generic 5, B_4, D_4, F_4) do not contain the counterexample of [CRV]
§0.

**Classification (scope item 1).**
- *Type A*: exactly Theorem TA, (TA1)–(TA3) holding and (TA4) failing.
- *F_4*: the two order-6 classes on all chambers. There L(A)^g has an
  uncomplemented element (CR_V holds), so the zero is a Crapo zero of the
  fixed lattice.
- *B_2–B_4, D_4, H_3*: no cancelling pair.
- *The five non-Coxeter probes* of [AudVC2] (generic 4 in R^3, generic 5 in
  R^4, B_3 ∖ {z = 0}, A_3 minus a plane, the 12-line hexagon) all cancel.
  - Every cancelling pair there has an uncomplemented element of Λ(V)^g.
  - On the generic arrangements, cancellation can depend on the cone
    through m_X(V) and not only on lin V.
  - Example: on generic 4 in R^3 with the non-orthogonal involution of det
    −1 and dim U = 2 printed by the script, two cones with the same line L
    have terms (−1)·1 + 1·1 = 0 and (−1)·1 + 1·2 = 1 (m_0 = 1 vs 2).
  - So no criterion in terms of (lin V, g) alone exists in general. This is
    the counterexample to extending Cor. 3.5(a).

## 5. What remains open

- **CR_V in general (REFUTED in rank 4).** [CRV] §0 gives a counterexample
  in R^4 (audited in [AudCRV]). [CRV] proves CR_V in rank ≤ 3 (Theorem 3),
  including all chambers there (Lemma R3), and for pointed cones in every
  rank (Theorem P). An exact per-cone criterion in rank ≥ 4 is again
  **OPEN** ([CRV] §6). The remarks below are the original motivation. On
  all chambers CR_V says: μ(L(A)^g) = 0 iff L(A)^g has an uncomplemented
  element. For general finite lattices the
  converse of Crapo's corollary is false: a lattice can have μ = 0 with every
  element complemented. The smallest such lattice has 8 elements ([PAPCV]
  §3.2). The converse is known for finite modular lattices (Knop,
  arXiv:2209.10337, Lemma A.2), including fixed sublattices of modular
  lattices, but L(A)^g and Λ(V)^g are not modular in general. Any proof must therefore use the geometry of fixed
  lattices of arrangements. A proof for all chambers would also give the
  CR conjecture of [VC] (via Theorem S's top-lunes), but this implication
  was not written out.
- **Type B_n.** The data (B_2–B_4) show no cancellation, so on every tested
  pair χ_V(g) ≠ 0 iff Z\*(V,g) carries a nonzero μ. Cones of B_n are
  type-B posets (signed posets). The analogue of §3 needs the CF counts of
  fixed chambers of B-type localizations under signed permutations, and a
  B-analogue of Lemmas Pal and E. The prerequisite all-cone rule (the
  analogue of Theorem A) is itself only known through Theorem S. **OPEN.**
- **D_n, H_3, H_4.** No cancellation in D_4 (with triality) or H_3 on the
  full enumerations. H_4 and D_n (n ≥ 5) were not computed. **OPEN.**
- **F_4.** The only cancellations found are on all chambers (sampled cones
  only). An exact rule for F_4 cones is **OPEN**.
- **General arrangements.** Cancellation is common (§4). Theorem Cr settles
  all chambers when U is a flat, in the sense that the cancellation there is
  that of Crapo's formula. It gives no criterion simpler than μ(L(A)^g) = 0.

## 6. Corrections and remarks on other notes (not applied)

- [VC] §5, "Open (PC″)": the suggestion of a sign-reversing involution on
  Z\*(V, g) does not hold as stated. In −(1 2) on A_4 the terms 2, 2, 2, −6
  (all m_X = 1) do not pair off. The resolution in type A goes through CF and
  Lemma E (§3.5).
- [VC] Verdict row PC″ can point here: type A is settled (Theorem TA), and
  the general case is reduced to Conjecture CR_V (since refuted in rank 4,
  [CRV]).
- [PA] §2.2 ("whether Formula Z on all chambers … can be derived from
  Crapo's theorem was not checked"): Theorem Cr. Given Lemma M, Formula Z on
  all chambers is Crapo's theorem when U is a flat. The identity [PA] asked
  for, m_X(all) = ± Σ_{y ≥ X complement} μ(y, 1̂), is Lemma M, with sign
  (−1)^{dim U}.
- No claim of another note was found to be wrong.

## Reproduce

From `compute/` (plain Python 3, no third-party packages; single process):

    python3 per_cone_vanishing.py > output/per_cone_vanishing.txt   # ~75 s, ends "ALL CHECKS PASSED", exit 0
    python3 per_cone_vanishing.py --quick                           # ~11 s: n <= 5, smaller random families, A_3 link, no A_4 / generic 5 / hexagon 13 / F_4
    python3 -m unittest test_per_cone_vanishing                      # < 1 s, positive and negative controls

The script imports its arrangement infrastructure from
`audit2_vanishing_criterion.py` and `vanishing_criterion.py`. The type A
poset code (OP(P)^τ, palindromic counts, the closed formula) is
self-contained. The archived log is `compute/output/per_cone_vanishing.txt`.

References: [VC] = `notes/vanishing_criterion.md`; [PA] =
`notes/prior_art_vanishing_criterion.md`; [AudVC2] =
`notes/audit2_vanishing_criterion.md`; [FP] = `notes/fixed_point_formula.md`;
[AudFP] = `notes/audit_fixed_point_formula.md`; [AudW] =
`notes/audit_prop_w_prime.md`; [AudW2] = `notes/audit_theorem_w2.md`; [GT] =
`notes/general_theory.md`; [FPM] = `notes/fixed_point_mobius_identity.md`;
[Thm] = `notes/poset_jks_theorem.tex`; [AudPCV] =
`notes/audit_per_cone_vanishing.md`; [PAPCV] =
`notes/prior_art_per_cone_vanishing.md`; [CRV] = `notes/conjecture_cr_v.md`;
[AudCRV] = `notes/audit_conjecture_cr_v.md`. Crapo, *The Möbius function of a
lattice*, J. Combin. Theory 1 (1966), used as stated in Stanley, *Some
aspects of groups acting on finite posets*, JCTA 32 (1982), §7, and in
Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed. ("EC1"), Ex. 3.92.
Stanley, *Enumerative Combinatorics* vol. 2, §5.1 (exponential formula).
Chow, *Noncommutative symmetric functions of type B*, PhD thesis, MIT
(2001), Thm 2.1.4 (not accessed; via Kim–Searles, arXiv:2601.22926, Thm 2.8).
Reiner, *Signed posets*, J. Combin. Theory Ser. A 62 (1993), Thm 3.3; Csar,
arXiv:2311.06387, §3.3. Al-Agha–Greechie, *The involutory dimension of
involution posets*, Order 18 (2001) (not accessed). Björner–Walker, *A
homotopy complementation formula for partially ordered sets*, European J.
Combin. 4 (1983) (not accessed; via Gálvez-Carrillo–Kock–Tonks,
arXiv:2409.03742, §1). Knop, *Multiplicities and dimensions in enveloping
tensor categories*, arXiv:2209.10337, App. A, Lemma A.2.
