# Audit of `notes/cyclic_compatible_posets_bn.md` (mg-beea5)

This is an independent check of the deliverable merged at 092c7b9 (mg-e5444):
`notes/cyclic_compatible_posets_bn.md` (the "bn note") and
`compute/cyclic_posets.py`. Each claim the bn note tags PROVEN was re-derived
from scratch. The numbers were recomputed with new code,
`compute/audit_cyclic_posets.py`, which does not import or adapt the original
script. It also enumerates posets differently: it builds *all* labeled posets
by inserting element n with an ideal and a filter, and finds the natural ones
by filtering.

Verdicts: CONFIRMED / BROKEN / OVERSTATED / UNCHECKED.

**Bottom line.** Nothing is BROKEN. Every PROVEN claim survives
re-derivation, and the numbers agree with independent code for n ≤ 6, and
for n ≤ 8 for the quantities that do not need all labeled posets. The
definition of B_n is the right one for (globalind); §A proves this outright,
with no conjecture used. Two things are OVERSTATED, both minor:
- the summary says b_8 was found "by brute force", but it comes from
  Lemma 1(c);
- the proof of Proposition 1 says S_n where it means C_n.

## Reproduce

    python3 compute/audit_cyclic_posets.py        # n ≤ 6, all checks, ~13 s
    python3 compute/audit_cyclic_posets.py --b8   # a_n and Lemma-1(c) b_n, n ≤ 8, a few minutes

Output of the first command (COMPUTED):

    #posets           : [1, 3, 19, 219, 4231, 130023]
    a_n (natural)     : [1, 2, 7, 40, 357, 4824]
    n[x^n] log A      : [1, 3, 16, 131, 1561, 26532]
    b_n = |B_n|       : [1, 3, 16, 131, 1561, 26532]
    Lemma 1(a)(b)(c)  : ok for n <= 6
    i_k (irreducible) : [1, 1, 4, 27, 275, 4070]
    Lemma 2 A=1/(1-I) : ok
    n=1..6: #cyclic factorizations = 1, 3, 16, 131, 1561, 26532; realization is a bijection onto B_n
    sum_P e_C(P)      : [1, 3, 32, 786, 37464, 3183840] = (n-1)! b_n
    n=6: #Fix(sigma^k) = [26532, 1, 3, 16, 3, 1]; free orbits = 4419
    n=1..5: character of (+)_P Lie(P) == (1/n) sum_d mu(d) b_(n/d) p_d^(n/d)
    ALL AUDIT CHECKS PASSED

Output of `--b8` (COMPUTED): a_n = 1, 2, 7, 40, 357, 4824, 96428, 2800472.
n Σ_{Q natural} 1/|C(Q)| = 1, 3, 16, 131, 1561, 26532, 637890, 21580043,
which equals n[x^n] log A for n ≤ 8. Here C(Q) is found by testing each
rotated word L_c directly, not with the formula of Lemma 1(b).

The bijection check catches errors (positive control). The first draft of
the audit script had an off-by-one in the labels of the arcs (s, s']. With
that bug the assertion `C(realization) == S` failed at n = 2. With the bug
fixed, every check passes.

`python3 compute/cyclic_posets.py 7` was also rerun unchanged. It prints
ALL CHECKS PASSED in 24 s, and its numbers equal the ones above.

## Definition of B_n (the likely failure point)

The bn note defines B_n as the labeled posets on [n] that have some
L_c = (c+1, …, n, 1, …, c) as a linear extension. The original script builds
the same set in two ways: as ⋃_c ρ_c(natural posets) (`relabel(Q, rho)`),
and by scanning all posets with `cuts(P)` nonempty. Both use the same
L_c (0-based `rot_word`). My script uses the same definition with 1-based
labels, and gets the same b_n.

**This is the set that (globalind) needs: CONFIRMED (PROVEN here, §A).**

## Claim-by-claim

| # | Claim (bn note) | Verdict | Reason |
|---|---|---|---|
| 1 | §1: C(σP) = C(P)+1; C_n acts on B_n | CONFIRMED | Applying σ letterwise to L_c gives L_{c+1}. Also w ∈ Lin(P) ⇔ σ∘w ∈ Lin(σP), straight from the definition of σP. |
| 2 | §1 COMPUTED: a_n for n ≤ 8, b_n for n ≤ 7 (explicit set), b_8 = 21580043 | CONFIRMED | Reproduced independently (above). a_n and A001035 match for n ≤ 6 by full enumeration. a_7 and a_8 match by natural-poset enumeration. |
| 3 | Summary: "values of a_n (n ≤ 8) and b_n (n ≤ 8) are reproduced by brute force" | OVERSTATED | b_8 is not a brute-force count of B_8. It is n Σ 1/\|C(Q)\|, which equals b_8 only through Lemma 1(c). The body of the note says this; the summary does not. Lemma 1(c) is proven (row 6), so the value stands. |
| 4 | Lemma 1(a): distinct cuts c, c' ∈ C(P) make the arcs (c,c'] and (c',c] incomparable | CONFIRMED | L_c puts the first arc before the second and L_{c'} puts it after, so no cross relation can exist. Brute-force checked, n ≤ 6. |
| 5 | Lemma 1(b): for natural P, C(P) = {0} ∪ {c : no relation i ≤ c < j} | CONFIRMED | L_c reverses exactly the value pairs i ≤ c < j, and every relation of a natural P is increasing. Checked, n ≤ 6. |
| 6 | Lemma 1(c): Σ_{B_n} \|C(P)\| = n a_n, so b_n = n Σ_{natural} 1/\|C\| | CONFIRMED | (P, c) ↦ (σ^{-c}P, c) is a bijection onto (natural, Z/n), because C(σ^{-c}P) = C(P) − c ∋ 0. Then sum 1/\|C\|, which is σ-invariant. Checked directly, n ≤ 6. b_8 rests on this lemma and it holds. |
| 7 | Lemma 2: A = 1/(1−I) | CONFIRMED | Standard decomposition at linear cuts. Both directions of the proof check. The irreducible counts i_k = 1, 1, 4, 27, 275, 4070 were enumerated *directly* (the bn note never did this) and satisfy A = 1/(1−I) for n ≤ 6. |
| 8 | Lemma 3: n[x^n] log A = #cyclic factorizations | CONFIRMED | log A = Σ I^m/m. The map (sequence, offset) → factorization has fibres of size exactly m, given by the choice of offset in S, even when the factorization is rotationally symmetric. The m = 1 case (whole circle) is fine. The explicit enumeration of factorizations gives 1, 3, 16, 131, 1561, 26532 = n[x^n] log A. |
| 9 | Lemma 4: L is an extension of a disjoint union iff each restriction is | CONFIRMED | Immediate. |
| 10 | **Theorem**: P ↦ (C(P), (P\|_α)) is a bijection B_n → cyclic factorizations, with realization as its inverse; b_n = n[x^n] log A | CONFIRMED | Re-derived (i) and (ii); see §B. The key step is the irreducibility in (i): L_c reads α_2, then the remaining arcs, then α_1, and this is an extension by Lemma 4. Also checked by brute force in both directions for n ≤ 6: realization is injective with image exactly B_n, C(realization) = S, and restricting to the arcs recovers the pieces. Hand checks for n = 3, 4 are in §B. |
| 11 | Recurrence n a_n = Σ b_k a_{n−k} | CONFIRMED | Take coefficients in xA' = x(log A)'·A. |
| 12 | Prop. 1: Σ_P e_C(P) = (n−1)! b_n | CONFIRMED (wording OVERSTATED) | The argument is right: C_n acts freely on the right, left multiplication permutes the (n−1)! right cosets transitively, and Lin(τP) = τ Lin(P). But the text says "**S_n** acts on words by right rotation"; it should be C_n. Brute force over all posets gives 1, 3, 32, 786, 37464, 3183840. |
| 13 | Prop. 2(a): #Fix(σ^k) = b_{gcd(k,n)} | CONFIRMED | ⟨σ^k⟩ = ⟨σ^g⟩. A g-periodic factorization of size n is the same as a factorization of size g. The proof leaves implicit that consecutive cuts are ≤ g apart, which holds since s, s+g ∈ S. Checked for n ≤ 6, e.g. [26532, 1, 3, 16, 3, 1] at n = 6. |
| 14 | Prop. 2(b): the antichain is the unique σ-fixed point | CONFIRMED | C(P) is σ-invariant and nonempty, so it is all of Z/n, so every arc is a singleton. Checked for n ≤ 6. |
| 15 | Prop. 2(c): #free = Σ μ(n/d) b_d ≡ 0 (mod n); b_p ≡ 1 (mod p) | CONFIRMED | Möbius inversion over the divisor lattice. Free orbits number 1, 1, 5, 32, 312, 4419 for n = 1..6; (b_7−1)/7 = 91127 (arithmetic). |
| 16 | §4: these match the note's 5 and 312 in H_p ≅ ((b_p−1)/p)C[S_p] ⊕ (sgn⊗Lie_p) | CONFIRMED, conditional | Given (globalind): C[B_p] is the trivial rep plus ((b_p−1)/p)·C[C_p]. ζ⊗C[C_p] ≅ C[C_p], and Ind takes it to C[S_p]; sgn⊗Reg ≅ Reg; Ind ζ = Lie_p. The bn note correctly calls this conditional. |
| 17 | Prop. 3: ch Ind_{C_n}^{S_n}(ζ⊗C[B_n]) = (1/n) Σ_{d\|n} μ(d) b_{n/d} p_d^{n/d}, and the generating function is Σ_d (μ(d)/d) log A(p_d) | CONFIRMED | Frobenius for induced class functions. The character at σ^k is ζ^k·b_{n/d}. Summing ζ^k over the k of order d gives the Ramanujan sum c_d(1) = μ(d), for any faithful ζ. The resummation with n = dm and Σ b_m x^m/m = log A is right. Also checked numerically for n ≤ 5 against a trace computed directly in C[S_n] (§A). |
| 18 | Prop. 3 sign: twisting by sgn multiplies the d-term by (−1)^{n−n/d}, so (globalind) ⇒ (frob) with H_n ≅ sgn⊗V_n, and (plethlog) is the untwisted series | CONFIRMED | ω(p_λ) = (−1)^{n−ℓ(λ)} p_λ with ℓ = n/d, and ch(sgn⊗V) = ω ch V. This is the sign in the note's (frob). The note's (plethlog) is explicitly the untwisted series, which is ch V_n. The bn note's (−1)^{(d−1)n/d} is the same exponent. |
| 19 | §5: "(globalind) … depends on the main poset JKS conjecture"; Prop. 1 gives only dimension agreement, given Jenča–Sarkoci | CONFIRMED, can be sharpened | The *only* conjectural input is H_n ≅ sgn ⊗ ⊕_P Lie(P). The other half, ⊕_P Lie(P) ≅ Ind(ζ⊗C[B_n]), is unconditional (§A). (globalind) is therefore implied by (mainconj) for one representative P of each S_n-orbit of posets. The dimension statement uses JS (CITED in the seed note, not re-checked here or in the bn note). |
| 20 | Remark: "standard cycle-of-irreducibles interpretation" | UNCHECKED (no citation) | Not tagged and no source given. The argument itself does not depend on it. |
| 21 | §3 COMPUTED: the recurrence holds with brute-force b_n (n ≤ 7) and the Lemma-1(c) b_8 | CONFIRMED | Implied by rows 2 and 11. Recomputed independently. |

## A. The B_n convention is the one (globalind) needs (PROVEN)

The seed note says "Fix one cyclic order and let B_n be the set of labeled
posets compatible with it." This section shows that the bn note's reading of
that sentence is the one that makes (globalind) the summed form of (mainconj).
It also proves the non-conjectural half of (globalind).

**Claim.** As S_n-modules under left multiplication,
⊕_{P on [n]} Lie(P) ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]). Here C_n = ⟨γ⟩ acts on
C[B_n] by relabeling (γ = σ), and B_n is exactly the bn note's set.

*Proof.* In each right coset O = wC_n, fix a representative w_O. Then
w_O γ^j e_ζ = ζ^j w_O e_ζ, because γ^j e_ζ = ζ^j e_ζ. So the vectors
{w_O e_ζ : O ∩ Lin(P) ≠ ∅} form a basis of Lie(P).

Take τ ∈ S_n. Then τ w_O = w_{τO} γ^j for some j, so τ maps the basis vector
of (P, O) to ζ^j times the basis vector of (τP, τO). Hence ⊕Lie(P) is a
monomial representation on the S_n-set X = {(P, O) : O ∩ Lin(P) ≠ ∅}.

The map X → S_n/C_n, (P, O) ↦ O, is equivariant, and S_n acts transitively
on the base. The stabilizer of the identity coset O_0 is C_n.

The fibre over O_0 is {P : O_0 ∩ Lin(P) ≠ ∅}. As words, O_0 = {γ^j}, and the
word of γ^j is (1+j, …, n, 1, …, j) = L_j. So the fibre is exactly B_n.
With w_{O_0} = id, γ^j acts on the fibre by e_ζ ∈ Lie(P) ↦ ζ^j e_ζ ∈ Lie(γ^j P).
That is the representation ζ ⊗ C[B_n]. A monomial representation over a
transitive base is induced from the stabilizer's action on the fibre. ∎

So (globalind) ⇔ H_n ≅ sgn ⊗ ⊕_P Lie(P). The conjecture enters at exactly
this one step.

That step follows from (mainconj) for one P in each S_n-orbit. On both sides,
the S_n-module is ⊕_{orbits} Ind_{Aut P}^{S_n}(·), because relabeling
permutes the summands. Also Ind_G(sgn|_G ⊗ M) ≅ sgn ⊗ Ind_G M.

Using the opposite cyclic order would replace B_n by {P : P^op ∈ B_n}, whose
cyclic group is generated by γ^{-1} rather than γ. The resulting
Ind(ζ^{±1}⊗·) has the same real character. The statement is therefore
insensitive to this choice, but the fibre must be taken over the coset of
the same γ that defines e_ζ.

COMPUTED check (n ≤ 5, `main()` section "Section 5 convention check"). For
every τ ∈ S_n, the script computes the trace of τ on ⊕_P Lie(P) directly:
for each τ-fixed P and each τ-fixed coset, it adds ζ^j where τ∘w = w∘γ^j.
This equals z_λ μ(d) b_{n/d}/n when τ has cycle type λ = (d^{n/d}), and 0
otherwise. That is the character read off from Prop. 3's formula.

## B. Hand checks of the bijection

**n = 3.** The rotation class of 123 is {123, 231, 312}. A chain a<b<c has the
single extension abc, so the chains 3<2<1, 2<1<3 and 1<3<2 are not in B_3.
Every other poset on [3] has extensions in both rotation classes:
- the antichain and the one-relation posets have 3 or 6 extensions;
- V and Λ shapes have two extensions differing by a transposition, which lie
  in classes of opposite parity.

So b_3 = 19 − 3 = 16.

The factorization side gives the same total, 1 + 3 + 12 = 16:
- S = Z/3: 1 (the antichain).
- |S| = 2: 3 choices of S, each with a 2-chain on the 2-arc. These are {1<2},
  {2<3}, {3<1}.
- |S| = 1: 3 offsets × i_3 = 4 irreducible natural posets on [3]. The four
  are the chain, 1<2 & 1<3, 1<3 & 2<3, and 1<3 alone; 1<2 alone and 2<3
  alone are reducible.

Inverse map, worked examples:
- P = {1<2}: L_0 ✓, L_1 = 231 ✗, L_2 = 312 ✓. So C = {0, 2}, with arcs
  {1,2} (a chain) and {3}. This matches the S = {0, 2} factorization.
- P = {1<3}: C = {0}, a single arc 1,2,3. The piece is irreducible: both
  interior cuts are crossed by 1<3.
- σP = {2<1}: C = {1}, with arc order 2,3,1, and the piece is irreducible.
  This matches C(σP) = C(P) + 1.

**n = 4.**
- P = {1<2, 3<4}: C = {0, 2}. The arcs are {1,2} and {3,4}, both chains.
- P = {2<3, 4<1}: C = {1, 3}. The arcs are (1,3] = {2,3} and (3,1] = {4,1}
  in order 4,1. Both are chains, and realizing them gives P back.
- P = {1<3}: C = {0, 3}. The arcs are {1,2,3}, with 1<3 irreducible, and {4}.
- P = {1<3, 2<4}: C = {0}. The cuts 1, 2, 3 are crossed by 1<3, 1<3 and 2<4
  respectively, so the piece is irreducible.
- P = {2<1, 4<3}: none of the four L_c is an extension, so P ∉ B_4. There is
  no factorization realizing it either, since realizations lie in B_4 by (ii).

All of these agree with the brute-force bijection check.

## Successor items suggested (for the PM; nothing was changed in the bn note)

1. Fix the summary bullet: b_8 comes from Lemma 1(c), not "brute force".
2. Prop. 1 proof: "S_n acts on words by right rotation" should be "C_n".
3. Optional: add the unconditional statement ⊕_P Lie(P) ≅ Ind(ζ⊗C[B_n])
   (§A) to §5. This pins down that the conjecture enters only through
   H_n ≅ sgn⊗⊕Lie(P).
4. Optional: cite a source for the "cycle of irreducibles" remark, or drop it.
