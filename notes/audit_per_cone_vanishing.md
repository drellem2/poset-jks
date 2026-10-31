# Audit of `notes/per_cone_vanishing.md`

**Verdict: HOLDS WITH FIXES.** Every PROVEN claim audited here is true. The
fixes are one wrong justification (the lattice property in CO), one
statement whose proof is incomplete (Cor. 3.5(c)), two small gaps in proofs,
a misnamed Möbius value in Lemma E(iii), and two slips (a citation year, an
n in §3.7). None of them changes a result.

The note is cited as [PCV]. The other references are those of [PCV]. This
audit was written from [PCV] and the notes it cites as inputs. It does not
use any other audit of [PCV] or any script of `compute/` except its own,
`compute/audit_per_cone_vanishing.py` ("[Aud]").

| # | Claim of [PCV] | Verdict | How checked |
|---|---|---|---|
| M | Lemma M: m_X(all) = (−1)^{dim U} Σ_{Z ⊇ X, Z ∩ U = 0} μ_{L(A)^g}(Z, R^d) | **HOLDS.** Proof re-derived (§1). One case left implicit: X = R^d (fix F1) | m_X computed from its definition on 1,727 terms (1,588 symmetries of 9 arrangements) |
| Cr | Theorem Cr, (a) Crapo identification when U is a flat, (b) antichain case | **HOLDS.** (a) is Crapo's complementation theorem in the form checked in §2. The year in Theorem Cr(a) should be 1966 (fix F2) | (Cr) on all 1,588 symmetries; "Z\* = complements of U" on the 1,090 with U a flat; Crapo's identity itself on 10,340 pairs (lattice, element) |
| Pal | Lemma Pal | **HOLDS.** Proof correct (§3) | every anti-automorphism of every poset with n ≤ 7: 6,847 pairs. Counts re-checked by listing all linear extensions for n ≤ 6 |
| Sh, E | Lemmas Sh and E | **HOLD.** In E(iii) the inner weight is μ(0̂, σ), not μ(σ, 1̂). The sum is the same (fix F3) | E(i), (ii) by brute force over permutations, E(iii) on 9,369 cases |
| TA | Theorem TA (TA1–TA4), closed formula (3.3)–(3.5), sign rule | **HOLDS.** Each condition re-derived as necessary, and their conjunction as sufficient (§4). One step of Case I needs one more sentence (fix F4) | own closed formula = χ_{C_P}(−τ) from the faces of C_P, on all 6,842 pairs (P, τ) with 3 ≤ n ≤ 7, and on 220 random pairs with n = 7, 8, 9 (m = 1, 3) |
| TA-L | Cor. 3.5 (a), (b) | **HOLDS** (immediate from TA) | all labelled posets with n ≤ 5: 2,010 pairs, 549 keys (comp P, τ), no inconsistency |
| 3.5(c) | "cancellation ⇔ (TA1)–(TA3) hold, (TA4) fails, Z\* carries a nonzero μ" | **HOLDS, but the proof is incomplete.** One direction needs "(TA2) or (TA3) fails ⇒ Z\*(C_P, −τ) carries no nonzero μ", which [PCV] does not prove. Proof supplied (§5, fix F5) | n ≤ 6: 121 cancelling pairs, all with (TA4) the failing condition. Every (TA4) zero has a nonzero μ on Z\* |
| CO (type A) | the element a of §3.6 has no complement in Λ(V)^g | **HOLDS** (§6) | complements searched in the lattice itself, on all 461 (TA4) zeros with n ≤ 7 |
| CO (general) | "Λ(V)^g is a lattice … closed under intersection, since Λ(V) is ([GT] Lemma 0.1)" | **The justification is wrong; the conclusion holds.** Λ(V) is not closed under intersection, and [GT] Lemma 0.1 does not say so. Λ(V) is closed under joins, so it is a lattice (fix F6) | 56 of the 86 posets with n ≤ 5 give a Λ(C_P) that is not closed under intersection. All 86 are join-closed |

COR. V, L′, CR_V, D and the §4 table are COMPUTED or CONJECTURED in [PCV].
They were not in scope.

---

## 1. Lemma M

*Re-derivation.* Let X ∈ Z\*(g) with X ≠ R^d.
- (A_X/X, all chambers, ḡ) is an essential arrangement of rank codim X ≥ 1,
  with a top-cone and a finite-order symmetry. The localization of "all
  chambers" at X is "all chambers" of A_X/X. Its lineality space is R^d/X.
- (W″c) for it, read through [VC] §2 steps 2–4, is
  Σ_{Z ∈ L(A)^g, Z ⊇ X, Z ∩ U = 0} χ_{all}(A_Z/Z, ḡ) = m_X(all). This is
  exactly [VC] §2 step 5 with V = all chambers.
- The flats of A_Z/Z are the Z′/Z with Z′ ⊇ Z a flat, and ḡ-stability is
  g-stability. So μ(L(A_Z/Z)^ḡ) = μ_{L(A)^g}(Z, R^d).
- Fix(ḡ on R^d/Z) = (U + Z)/Z ([VC] §2 step 2) has dimension dim U, because
  Z ∩ U = 0.
- For a real finite-order map h, det h = (−1)^{(number of eigenvalues −1)} =
  (−1)^{dim − dim Fix h}, since the non-real eigenvalues come in conjugate
  pairs. So det(ḡ) = (−1)^{codim Z − dim U}.
- The Z-term is (−1)^{codim Z} · (−1)^{codim Z − dim U} · μ(Z, R^d) =
  (−1)^{dim U} μ(Z, R^d). Every sign of [PCV] is right.

**F1 (gap, rank 0).** (W″c) is stated for rank ≥ 1. The case X = R^d occurs
when U = 0. Then the only Z is R^d, and both sides are 1 by the rank-0
convention. This is the convention of [VC] §2 step 1. [PCV] should say so.

*Check.* [Aud] computes m_X(all) from its definition, independently of
(W″c): m_X(all) = (−1)^{dim U} μ of the intersection lattice of
{H ∩ U : H ⊇ X} in U, with U, X and the restricted forms computed by exact
linear algebra. It compares this with the right side of Lemma M for every
X ∈ Z\*(g) and every symmetry g. The symmetries are all linear maps that
permute the given normals up to sign. The arrangements are A_2, B_2, A_3,
B_3, D_4, generic 4 planes in R^3, generic 5 hyperplanes in R^4, B_3 minus
z = 0, and A_3 minus one plane. That is 1,588 symmetries and 1,727 terms,
all equal, all with m_X ≥ 1. Formula Z for all chambers is checked on the
same data. Negative control (test): Lemma M fails on A_2 without the sign
(−1)^{dim U}, and it fails without the condition Z ∩ U = 0.

## 2. Theorem Cr and Crapo's theorem

**Crapo's complementation theorem.** H. H. Crapo, *The Möbius function of a
lattice*, J. Combinatorial Theory 1 (1966) 126–131. For a finite lattice L
and any t ∈ L, with t^⊥ the set of complements of t,

  μ(0̂, 1̂) = Σ_{u, v ∈ t^⊥, u ≤ v} μ(0̂, u) μ(v, 1̂).

I could not access the 1966 paper, so this wording was read from secondary
sources: the exercise form used with Stanley EC1, ch. 3, and the
Björner–Walker generalization. The Stanley 1982 §7 statement cited by [PCV]
was not read. To make the identification independent of the citation, [Aud]
checks the displayed identity directly: on every element of every fixed
lattice L(A)^g above, 10,340 pairs (lattice, element), with meets and joins
computed in the lattice.

*Identification.* Take L = M = L(A)^g and t = U. Meet is intersection, so
X ∧ U = 0̂ iff X ∩ U = 0. Join is the smallest flat containing X + U, which
is g-stable, so it is the join in M too. It is R^d iff no hyperplane
contains X + U. So U^⊥ = Z\*(g). Also (−1)^d det g = (−1)^d (−1)^{d − dim U}
= (−1)^{dim U}. So (Cr) is exactly the displayed identity. Its index set is
right: for X ∈ Z\*, a flat Z ⊇ X with Z ∩ U = 0 is automatically in Z\*,
since Z + U ⊇ X + U. The antichain case (b) is also right. [Aud] checks
(Cr) on all 1,588 symmetries, (a) on the 1,090 whose U is a flat, and (b)
wherever Z\* is an antichain.

**F2.** Theorem Cr(a) says "Crapo 1968". The paper is from 1966, as the
References of [PCV] say.

## 3. Lemma Pal (and Sh)

*Proof check.*
- *Definition.* [PCV] defines an anti-automorphism by one implication only:
  i < j ⇒ t(j) < t(i). For a bijection of a finite poset this is enough. It
  maps the set of strict relations injectively into itself, hence onto it,
  so the converse holds. The proof uses both directions.
- *Only if.* Correct.
- *If.* If every minimal element is fixed, then (≤ 1 fixed point) there is
  exactly one, x_0. Then t, which maps minimal elements bijectively to
  maximal ones, makes x_0 the unique maximal element too. So x_0 is a
  minimum and a maximum, and |Q| = 1. Otherwise take a minimal x with
  t(x) ≠ x. Since t² = 1, Q′ = Q ∖ {x, t x} is t-stable, and t|_{Q′} is an
  involutive anti-automorphism of the induced subposet with ≤ 1 fixed point.
  Then x w′ t(x) is a linear extension, because x is minimal and t(x) is
  maximal, and it is palindromic.

Lemma Pal holds.

*Check.* [Aud] enumerates the unlabelled posets with n ≤ 7. Its counts
1, 1, 2, 5, 16, 63, 318, 2,045 are the known ones, a positive control on
the enumeration. For each poset it finds every anti-automorphism by
backtracking, 6,847 pairs in all, 6,038 of them not involutions. For each
pair it counts palindromic extensions by an exhaustive recursion over every
possible first letter, not over the one the proof picks. For n ≤ 6 it
re-counts them by listing all linear extensions. Existence agrees with
"t² = 1 and ≤ 1 fixed point" on all 6,847 pairs. The first version of the
recursion enforced t(w_1) = w_n but not t(w_n) = w_1. The brute-force
cross-check caught it on the 4-cycle of the 4-antichain, which is now a
test.

Lemma Sh: the restriction, half-word and shuffle arguments are correct. An
involution on a part of odd size has a fixed point. So when at most one t_j
has a fixed point, at most one part has odd size, and the centre position is
consistent.

## 4. Theorem TA

All of §3.2–§3.4 was re-derived. The points that needed care:

- *Fixed chambers of A_Y in |C_P|.* g sends (w_B) to the chamber whose order
  on τ̄B is rev(τ w_B). Going once around an orbit of length ℓ, w_B must
  equal τ^ℓ w_B, reversed when ℓ is odd. Correct.
- *Which ℓ survive.* A point on a cycle of length c ∈ {m, 2m}, fixed by the
  involution τ^{2ℓ}, gives c | 2ℓ, so m | ℓ. Also ℓ | ord τ̄ | 2m. So
  ℓ ∈ {m, 2m}, with parity deciding which. Correct.
- *(TA2).* If s is the orbit length of a component K ⊆ B, then τ^s B = B, so
  ℓ | s. The divisors of 2m that are divisible by m are m and 2m. Correct.
- *Units.* ⟨τ^m⟩-orbits of components have size ≤ 2, because τ^{2m} = 1.
  Each b(K) has τ̄-orbit exactly m, by (TA2). A block of an S_m-partition
  holds at most one ρ_0-block per unit. The alignments number m^{|G|−1}.
  The exponent identity m^{r−1} m^{N−r} = m^{N−1} holds. Correct.
- *Case IIb.* The bound pal_u ≥ 2 |Lin K_u| is correct: the two families
  start with a letter of K_u or of τ^m K_u. So the bracket of (3.5) is
  ≥ (2m)^{N−1} Π |Lin K_u| > 0.

**F4 (gap, Case I).** [PCV] shows χ ≠ 0 ⇔ (𝒯 = ∅ or some F-unit has
h_f ≥ 1). It then identifies this with (TA4) through "𝒯 ≠ ∅ means … an even
cycle". The case "even cycles exist but 𝒯 = ∅" needs one more sentence.
There an even point lies in some F-unit block b(K) together with an odd
point p. Since τ^m p = p, the component K equals τ^m K and contains both
points, so p is not isolated, and (TA4) holds. With this sentence the
equivalence is complete.

**F3 (Lemma E(iii)).** In the proof, summing the weights
Π_{β ∈ σ}(−1)^{|β|−1}(|β|−1)! over σ ∈ Π(S ∩ ℱ) gives Σ_σ μ(0̂, σ), not
Σ_σ μ(σ, 1̂). Both sums equal [|S ∩ ℱ| ≤ 1], so the lemma stands.

*Edge cases asked for.*
- n = 3: 8 pairs, 4 zeros, all from (TA4). The smallest is the A_2 pair.
- n = 4: 37 pairs, with Cases I, IIa and IIb all present, and one zero from
  (TA3).
- (TA2) zeros first appear at n = 6, with 14 pairs.
- Over 3 ≤ n ≤ 7 there are 4,614 pairs with mixed odd and even cycles and
  4,081 with an isolated fixed point.

**§3.7 slip.** "Dropping (TA4) misclassifies pairs already at n = 4". It
does so already at n = 3, on 4 pairs, including the A_2 example of §3.1.

*Check (independent of OP(P)).* For each pair, [Aud] computes
χ_{C_P}(−τ) = (−1)^{n−1} det(−τ | R^n_0) μ(Λ(C_P)^g) with:
- the faces of |C_P| listed as ordered set partitions B_1 < ⋯ < B_k
  compatible with P;
- Λ the set of their spans;
- g acting on faces by (gx)_{τ(i)} = −x_i;
- gV = V verified on the faces;
- det(−τ) taken as the determinant of the matrix on a basis of R^n_0.

For n = 7 and the random families it uses the equivalent "τ-stable
partitions that are spans of a face" form. The two forms agree on every
pair with n ≤ 6.

Against this value, [Aud] checks three things: its own literal
implementation of (3.3)–(3.5), the conditions (TA1)–(TA4), and the sign
rule. These hold on all 6,842 pairs with 3 ≤ n ≤ 7. They also hold on 220
random τ-invariant posets of cycle types (2,2,2,1,1), (2,2,2,2),
(2,2,1,1,1,1), (6,1), (6,3), (3,3,3) and (2,2,2,2,1). The n ≤ 6 count of
922 pairs agrees with [PCV]. On every pair that reaches (3.3), Φ was compared with
the closed form of Lemma E(iii).

## 5. Cor. 3.5

(a) and (b) are immediate from Theorem TA and [Thm]. [Aud] checks them on
all labelled posets with n ≤ 5: the vanishing is constant on each key
(comp P, τ), and the sign is constant on each τ.

**F5 (Cor. 3.5(c)).** Read as an equivalence, (c) needs this statement,
which [PCV] does not prove: *if (TA1) holds and (TA2) or (TA3) fails, then
no X ∈ Z\*(C_P, −τ) has μ(0, X) ≠ 0.* A proof:
- Let X = X_ρ ∈ Z\*(C_P, −τ) with μ(0, X) ≠ 0. By Hanlon, all τ̄-orbits of
  blocks have one length ℓ.
- *ℓ is odd.* If ℓ is even, the vector equal to (−1)^j on τ̄^j B, along one
  orbit, is nonzero. It lies in X ∩ U and in R^n_0. This contradicts
  X ∩ U = 0.
- So ℓ | m, and every block B is τ^m-stable.
- On a block B, every vector of X + U has x_i − x_j = u_i − u_j. Every
  u ∈ U vanishes on odd points, and satisfies u_{τ^e i} = (−1)^e u_i. So
  "X + U in no hyperplane" forbids two odd points in one block. It also
  forbids two points i ≠ τ^{2a} i in one block.
- *(TA3).* b(K) ⊆ B, since τ^m B = B. So b(K) has at most one odd point.
- *(TA2).* Let K ⊆ B have orbit length s ∉ {m, 2m}, so s | 2m and m ∤ s.
  Take x ∈ K. If x is odd, τ^s x ≠ x is a second odd point of K ⊆ B. If x
  is even, then τ^{2s} x ≠ x (because 2s < 2m) lies in K ⊆ B. Either way
  this contradicts the previous bullet. ∎

On the data (n ≤ 6), all 121 cancelling pairs have (TA4) as the failing
condition. Every (TA4) zero has a nonzero μ on Z\*. So, on these data, the
type-A cancellations are exactly the (TA4) zeros.

## 6. The Crapo obstruction

*Type A element (§3.6).* Correct as written. a = {Q} ∪ singletons on A_0 is
τ-stable, and it is acyclic because A_0 is isolated. Meets in OP(P) are
common refinements: a cycle in the quotient by π ∧ ρ maps to closed walks
in both acyclic quotients, so it lies in one block of each. The partition
join x ∨ a is acyclic, so it is the join in OP(P)^τ. A complement x needs
exactly one Q-point per block. φ: A_0 → Q is then τ-equivariant. An odd
p has τ^m p = p, while Q consists of 2m-cycle points, which is a
contradiction. The argument uses only (TA1) and A_0 ≠ ∅, Q ≠ ∅.
Complementation is self-dual, so this is the same as having no complement
in Λ(V)^g ≅ (OP(P)^τ)^op. [Aud] searches the complements in the lattice
Λ(C_P)^g itself, with meets and joins found by search. There are none, on
all 461 pairs with n ≤ 7 where (TA1)–(TA3) hold and (TA4) fails. A test
shows that another τ-stable element of the same lattice does have a
complement.

**F6 (the lattice property, [PCV] §4 "CO").** [PCV] says Λ(V)^g "is closed
under intersection, since Λ(V) is ([GT] Lemma 0.1)". This is false, and
[GT] Lemma 0.1 does not state it.
- *Counterexample.* P = {0 < 2, 1 < 3}. X_p with p = {03 | 1 | 2} and X_q
  with q = {12 | 0 | 3} are spans of faces. Their intersection X_{03|12} is
  not: on it the constraints force x_0 ≤ x_2 = x_1 ≤ x_3 = x_0, so it meets
  |C_P| in a line. Of the 86 posets with n ≤ 5, 56 give a Λ(C_P) that is not
  closed under intersection.
- *Correct reason that Λ(V) is a lattice.* If F, G are faces of V, then
  F ∘ G is a face of V: for x ∈ F, y ∈ G and small ε > 0, x + εy lies in
  |V|. Its zero set is zero(F) ∩ zero(G), so its span is the smallest flat
  containing span F + span G. So Λ(V) is closed under joins in the lattice
  of flats. With bottom 0 it is a finite lattice.
- g acts on it by automorphisms, so Λ(V)^g is a lattice too, with the
  ambient join.
- The meet is not intersection in general.
- CO, Crapo's corollary for Λ(V)^g, then stands as stated.

[Aud] confirms the join-closure on all 86 posets with n ≤ 5.

## 7. Corrections to [PCV] (not applied)

- F1: in Lemma M, note the case X = R^d (U = 0), covered by the rank-0
  convention of [VC] §2 step 1.
- F2: in Theorem Cr(a), "Crapo 1968" should be "Crapo 1966".
- F3: in the proof of Lemma E(iii), "Σ_σ μ(σ, 1̂)" should be "Σ_σ μ(0̂, σ)".
- F4: in Case I of §3.4, add the case "even cycle, 𝒯 = ∅" (§4 above).
- F5: in Cor. 3.5(c), add the proof of §5 above, or state only the
  inclusion that is proven.
- F6: in §4 "CO", replace "closed under intersection" by "closed under the
  join of flats (face composition)".
- §3.7: "already at n = 4" should be "already at n = 3".

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 audit_per_cone_vanishing.py > output/audit_per_cone_vanishing.txt   # ~140 s, ends "ALL CHECKS PASSED", exit 0
    python3 audit_per_cone_vanishing.py --quick                                 # ~6 s: n <= 6, smaller random families, no B_3 / generic 5 / D_4
    python3 -m unittest test_audit_per_cone_vanishing                            # < 1 s, positive and negative controls

The archived log is `compute/output/audit_per_cone_vanishing.txt`. The
script imports nothing from the other scripts of `compute/`.

What is not verified here:
- the original wording of Crapo 1966 and of Stanley 1982 §7 (§2);
- the audited inputs (W″c), Theorem CF and Theorem A were used in the proof
  re-derivations, but not re-audited. The computations check Lemma M and
  Theorem TA end to end without them.
