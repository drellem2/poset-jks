# Audit of `notes/linear_extensions.md`

**Verdict: HOLDS WITH FIXES.** Every PROVEN claim in scope is true, and
every proof in scope survives a re-derivation by hand. Every COMPUTED count
in scope was reproduced exactly by independent code. The fixes are
wording, scope and citation fixes (F1–F7 below). None of them changes a
result.

The note is cited as [LE]. Its other references are as in [LE]. This audit
was written from [LE] §§0–7, from `notes/poset_jks_theorem.tex` ([Thm]) for
the definitions of cuts, blocks, B_P, R_P and PLie(P), and from the primary
sources named below. It imports nothing from `compute/`: all code is in
`compute/audit_linear_extensions.py` ("[Aud]"). The verdict and §§1–8 were
written before [LE] §8 (its own audit record) was read. §9 compares the two
afterwards.

| # | Claim of [LE] | Verdict | How checked |
|---|---|---|---|
| P | Lemma P, Cor. P1, Cor. P2 | **HOLDS.** Proof re-derived (§1). One sentence of the proof needs a justification added (F1) | Lemma P on all 503 disconnected posets n ≤ 7, every w and every split A ⊔ B into unions of components: 1,417,710 checks. P1 for every d ≤ n, P2 for every cut, same posets |
| R | Theorem R, and that its hypothesis is needed | **HOLDS.** "The smallest example is V ⊔ V" should be "a smallest": V ⊔ V, V ⊔ Λ and Λ ⊔ Λ all have n = 6 (F2) | hypothesis on 102 of 503; refinement on all 102. Hypothesis fails on 401; refinement fails on exactly 6 |
| O | Prop. O, all finite P | **HOLDS**, connected case included (§3) | all 2,450 posets n ≤ 7, every choice of base component |
| E | Prop. E (both directions) | **HOLDS** (§4) | all 2,450 posets: equality on exactly the 13 chains and antichains |
| D | Prop. D (both directions) | **HOLDS** (§5). The side remark on R_P double-counts the 2-antichain (F3) | K_P computed as a kernel, ∂(K_P) tested numerically, all 2,450 posets; ∂(R_P) ⊆ R_P on 9 of 108 (n ≤ 6), exactly the two-chain posets |
| F | Prop. F | **HOLDS** (§6) | all 2,450 posets; the [Thm] cumulant formula on all 2,450 |
| U | Theorem U, "given [RSW]" | **HOLDS.** The cited input is [RSW] Prop. 4.4 (with a = 1) in the evaluated form (4.5); [LE] should say so and should note ∂^n = id (F4) | fixed-point product formula on all 503; Theorem U on all 45 qualifying posets; [RSW] count on 255 compositions m, n ≤ 8; sweep table reproduced exactly |
| M | Theorem M, B_P | **HOLDS.** The Aut(P)-action should be called diagonal (F5) | R_P built from its generators, rank mod p, all 108 disconnected posets n ≤ 6: homogeneity, every graded piece, B_P on every piece |
| N1 | "No q-analogue comes from the theory" | **HOLDS as a scoped observation, not a theorem.** The verdict table states it more strongly than §3.1 does (F6) | §8 |
| N2 | "R_P homogeneous for des/maj on 0 of 108" | **HOLDS with its stated scope**, and beyond it: 0 of 603 (P, natural labelling) pairs with n ≤ 5 (F7 asks for the labelling to be named) | [homog] |

Out of scope and not audited: the Weisner family, the Jenča–Sarkoci
recursion checks, the Burnside and fixed-class counts of §4 and §3.1, and
open problems 1–4 (except where they restate an audited claim).

---

## 0. Definitions used

*Promotion* is taken from the primary definition, Schützenberger's, as
restated verbatim in Stanley [St09, §2] (arXiv:0806.4717): for a linear
extension f : P → [p], remove the label 1 from t_1 = f^{-1}(1), slide the
smallest label among the elements covering t_1 down, repeat until a maximal
element t_k is reached, label t_k by p + 1, then subtract 1 from every
label. [Aud] implements this (`promote_jdt`) and, separately, the toggle
product τ_{n−1} ∘ ⋯ ∘ τ_1 of [LE] §0 (`promote_tog`). They agree on every
linear extension of every poset with n ≤ 7 (2,450 posets) [jdt]. Every other
check uses `promote_jdt`. The negative control (toggles applied in the
reverse order) differs already on C_2 ⊔ C_1.

*Posets.* [Aud] generates unlabelled posets by adding a maximal element
above an order ideal and taking a canonical form. Counts 1, 2, 5, 16, 63,
318, 2045 for n = 1, …, 7 (OEIS A000112), 503 of them disconnected.

---

## 1. Lemma P and Corollaries P1, P2

*Re-derivation.* Write the toggle pass as a carried letter c moving right.
Before τ_i, the current word is a linear extension, because τ_1, …, τ_{i−1}
only swapped incomparable adjacent letters. If c ∥ w_{i+1}, the swap moves
w_{i+1} left and c is carried on. If not, then c < w_{i+1}, because c stands
to the left of w_{i+1} in a linear extension; nothing moves and w_{i+1} is
carried. So the carried letter changes only along a relation c < c′ and
stays in the component of w_1, say in A. Every B-letter is incomparable to
every A-letter, so each B-letter is swapped exactly once, one place left.
The A-letters see exactly the toggle pass of ∂_A on w|_A, because
comparability between A-letters is that of P|_A and B-letters are passed
transparently. The A-positions go from S to ((S ∖ {1}) − 1) ∪ {n} and the
B-positions from S^c to S^c − 1: the pattern rotates by one. This is [LE]'s
proof.

**F1.** [LE] writes "c < w_{i+1}, since c precedes w_{i+1} in a linear
extension". The word in question is the partially toggled word, not w. It
is a linear extension for the reason above, which should be stated.

P1: after j − 1 steps the pattern is rot_{j−1} p, whose first letter is
p_j, so step j applies ∂ to the component T_{p_j}. Hence a_i = #{j ≤ d :
p_j = i}, and a_i = m_i when d = n. P2: with A the cut prefix the pattern is
A^k B^{n−k}, so the first k steps all promote A. Both correct.

*Computed.* [P] checks Lemma P literally (pattern of ∂w, both restrictions)
for every disconnected P with n ≤ 7, every w ∈ Lin P and every split into
two nonempty unions of components: 1,417,710 triples, no failure. [P1]
checks P1 for every d = 1, …, n and [P2] checks P2 at every cut, on the
same 503 posets. No failure.

## 2. Theorem R

Proof re-derived: at a cut k with prefix A, P2 gives ∂^k(w) = w_{k+1} ⋯ w_n ·
∂_A^{|A|}(w_1 ⋯ w_k), and P1 applied to the poset P|_A gives ∂_A^{|A|} =
∏_{T ⊆ A} ∂_T^{|T|}, which is the identity under the hypothesis. So
∂^k(w) = wγ^k. Correct.

*Necessity.* [R]: the hypothesis holds on 102 of the 503 disconnected
posets with n ≤ 7, and refinement holds on all 102. It fails on 401, and
refinement fails on exactly 6 of those: V ⊔ V, V ⊔ Λ and Λ ⊔ Λ (Λ = V^op)
at n = 6, and the same three plus an isolated point at n = 7. For V ⊔ V,
e = 80, e_C = 76, 8 orbits of sizes 4, 4 and six of 12, and some class meets
two orbits. These are [LE]'s numbers (102, 401, 6, and the §2 table row).

**F2.** "The smallest example is V ⊔ V" — there are three smallest
examples. Say "a smallest example".

## 3. Proposition O

Disconnected case: by Lemma P the pattern rotates one place per step, so
within n steps the first letter lies in the base component P_1. If w_1 ∈
P_1, the first block of w is a union of components containing w_1, hence
contains P_1, so w ∈ B_P. Distinct orbits give distinct such words, and
|B_P| = e_C(P) ([Thm] Thm `thm:S`(a)). Correct.

*Connected case.* B_P = Lin P (the only union-prefixes are ∅ and P), P_1 = P,
and e_C = e ([Thm] Lemma `lem:rot`), so the bound is #orbits ≤ e, which is
trivial. No gap. The statement is true but carries no information for
connected P; [LE] says as much ("nothing to prove").

*Computed.* [O]: on all 2,450 posets n ≤ 7 and for **every** choice of base
component, every orbit meets {w : w_1 ∈ P_1}, |B_P| = e_C, and #orbits ≤ e_C.
[LE] checked one base component; the claim is for any.

## 4. Proposition E

Re-derived, both directions.
- (⇐) Antichain: ∂ = γ and every k is a cut, so orbits = cosets ∩ Lin P =
  classes. Chain: one extension.
- (⇒), connected P: classes are singletons, so equality means ∂ = id. If
  ∂(w) = w then w_1 < w_2 (else ∂(w)_1 = w_2), the carried letter is then
  w_2, and inductively w_i < w_{i+1} for all i, so P is a chain.
- (⇒), disconnected non-antichain: A a component with a ≥ 2, w = x·y. Cuts of
  w are 0 and a + j (0 ≤ j < b), so the other class members begin with a
  B-letter, w ends with one, and ∂(w) has pattern A^{a−1}B^bA. Correct.

*Computed.* [E]: equality holds on exactly 13 of the 2,450 posets: the
chains and antichains for n = 1, …, 7 (the 1-element poset is both).

## 5. Proposition D

Re-derived. γ^k e_ζ = ζ^k e_ζ, so wγ^k − ζ^k w ∈ K_P; the vectors we_ζ for
distinct classes have disjoint supports and are nonzero, so
dim PLie(P) = e_C and those differences span K_P. φ(∂v) is a difference of
two nonzero vectors each on one coset, so it vanishes iff
∂(wγ^k) = ∂(w)γ^k. Antichain: ∂ is right multiplication by γ, which commutes
with γ^k. Disconnected non-antichain: w = y·x, k = b; ∂(w) has pattern
B^{b−1}A^aB, its length-b prefix contains exactly one of the a ≥ 2 letters
of the component A, so ∂(w)γ^b ∉ Lin P while ∂(wγ^b) ∈ Lin P. Correct.

*Computed, without [LE]'s reduction.* [D] computes K_P directly as the kernel
of w ↦ we_ζ (images computed in C[S_n] in floating point; on each coset they
are checked to be proportional), applies ∂ to a kernel basis and tests
whether the image is still killed by e_ζ. On all 2,450 posets n ≤ 7 the
result is "preserved" iff P is connected or an antichain (6 disconnected
antichains, n = 2, …, 7). The eigen-relation wγ^k e_ζ = ζ^k we_ζ is also
checked numerically.

*The R_P remark.* [descR]: ∂(R_P) ⊆ R_P on 9 of the 108 disconnected posets
with n ≤ 6, namely C_a ⊔ C_b for (a, b) = (1,1), (1,2), (2,2), (1,3), (2,3),
(1,4), (3,3), (2,4), (1,5). The "if" proof (R_P = C·Σ_{Lin P} w) is correct.

**F3.** [LE] §2 says the 9 are "the two-component posets whose components
are both chains, together with the 2-antichain". The 2-antichain is C_1 ⊔
C_1, already one of the two-chain posets, and the two-chain posets with
n ≤ 6 are exactly 9. Delete "together with the 2-antichain". Also, the
identification C[Lin P]/R_P ≅ H_P ⊗ sgn ([Thm] Thm `thm:S`(d)) needs n ≥ 3,
so for C_1 ⊔ C_1 only the C[Lin P]/R_P side makes sense.

## 6. Proposition F

Re-derived. A cut depends only on the pattern p(w), and rotation at a cut
rotates p and fixes every w|_T. So the classes are (classes of patterns) ×
(restriction tuples), and patterns of content m are Lin(⊔ C_{m_i}).
Correct.

*Computed.* [F] on all 2,450 posets n ≤ 7. [Aud] also evaluates the
[Thm] Cor. `cor:eC` cumulant formula from its statement on all 2,450
posets; it agrees with e_C counted as cosets. So [LE]'s remark that
`cor:eC` is now computed through n = 7 is confirmed independently.

## 7. Theorem U and the [RSW] input

*The cited theorem.* [RSW] = V. Reiner, D. Stanton, D. White, *The cyclic
sieving phenomenon*, J. Combin. Theory Ser. A 108 (2004) 17–50 (checked
against the published paper). Its definition (Definition–Proposition (i),
p. 18): fix an embedding ω : C ↪ C^×; (X, X(q), C) exhibits the CSP if
[X(q)]_{q=ω(c)} = |{x : c(x) = x}| for every c ∈ C. The input Theorem U
needs is that words of content m under rotation sieve with the q-multinomial.
In [RSW] this is **Proposition 4.4** (C_n acting freely on [an], X the
k-flags of subsets, X(q) the q-multinomial), taken with a = 1 (a word p
corresponds to the flag S^{(j)} = {positions holding a letter ≤ j}, and
rotation of positions is the C_n-action), proved via the evaluation (4.5):
[an; k_1, …, k_m]_{q=ω} = (an/d; k_1/d, …, k_m/d) for ω a primitive d-th
root of unity, d | n, zero for non-integer arguments (convention stated on
p. 25). [LE] uses exactly this, at q = ω_n^d with ∂ ↦ ω_n. Theorem 1.1 of
[RSW] is only the binomial case.

*Proof re-derived.* By P1, ∂^d fixes (p; x) iff rot_d p = p and
∂_{T_i}^{a_i} x_i = x_i. If rot_d p = p then p has period e = gcd(d, n), so
a_i = (d/e)(m_i e/n) = d m_i/n. Hence |Fix ∂^d| = #{p : rot_d p = p} ·
∏_i |Fix ∂_{T_i}^{d m_i/n}|. When the first factor is nonzero, n/e divides
every m_i and ω_{m_i}^{d m_i/n} = ω_n^d, so the component CSPs give the
second factor. Correct. MacMahon–Stanley: by Garsia–Gessel, maj over a
shuffle of words on disjoint alphabets is maj(u) + maj(v) plus the
q-binomial statistic, for any labelling, so the shifted maj polynomial of
P is [n; m]_q ∏ X_i(q).

**F4.** (a) Cite [RSW] Prop. 4.4 with a = 1, or eq. (4.5), rather than
[RSW] unspecified. (b) Theorem U asserts a C_n-action, i.e. ∂^n = id on
Lin P. That follows from P1 (∂^n = ∏ ∂_{T_i}^{m_i} = id, since each
component carries a C_{m_i}-action), but the proof does not say so.

*Computed.* [RSW]: fixed patterns of rot_d on Pat(m) equal the
q-multinomial at e^{2πid/n}, for all 255 compositions m with n ≤ 8 and
≤ 50,000 words. [U]: the fixed-point product formula holds on all 503
disconnected posets n ≤ 7 (no CSP hypothesis needed for it); 45 of them
qualify (every component sieves with its shifted maj polynomial), and on
all 45 the product polynomial sieves and equals the shifted maj polynomial
of P. [LE]: 45.

*Controls and sweep.* [rh]: for the rectangles 2×2, 2×3, 2×4, 3×3, 2×5,
3×4, 2×6 the q-hook formula [n]_q!/∏[h]_q equals the shifted maj
polynomial, sieves, and q·(q-hook) is rejected. [sweep] reproduces the
§3.2 table exactly:

| n | posets | ∂ order ∤ n | CSP holds | CSP fails |
|---|---|---|---|---|
| 3 | 5 | 2 | 3 | 0 |
| 4 | 16 | 7 | 6 | 3 |
| 5 | 63 | 52 | 11 | 0 |
| 6 | 318 | 258 | 18 | 42 |
| 7 | 2045 | 1971 | 70 | 4 |

The three n = 4 failures are A_2 ⊕ A_2, {a, b} < c < d, and a < b < {c, d},
as [LE] says. Since the maj polynomial is the same for every natural
labelling (Stanley's P-partition theory), the sweep does not depend on the
labelling. [stair]: promotion orders 12 on SYT(3,2,1), 20 on SYT(4,3,2,1),
and 1, 2, 10 on the shifted staircases with 3, 6, 10 cells, as stated.

## 8. Theorem M and the negative claims

*Theorem M re-derived.* Every word of a generator s ⧢ t has the same
restriction tuple, since each component lies wholly in S or in S^c.
Interleavings are determined by the set of S-positions, which the pattern
records, so in pattern coordinates s ⧢ t = (pattern(s) ⧢ pattern(t)) ⊗ e_x,
with the shuffle of pattern words taken over position sets. For fixed x,
pattern(s) runs over all words of the S-content. So R_P = ⊕_x R_{Q(m)} ⊗ e_x
and every piece of the quotient is Q(m); dim Q(m) = e_C(⊔ C_{m_i}) by
[Thm] Thm `thm:S`(b) applied to ⊔ C_{m_i}. B_P is defined by the first block,
which depends only on the pattern, so B_P = ∏ Lin T × B_{⊔C}. Correct.

**F5.** "Aut(P) acts through its action on components: it permutes
isomorphic components and acts by Aut(T) inside each one." The action on
C[∏ Lin T] ⊗ Q(m) is diagonal: g relabels the restriction tuple and permutes
the pattern letters by the permutation it induces on components. It is not
a product of separate actions on the two factors. Say "diagonally".

*Computed.* [M] builds R_P from its generators (rank over GF(2^31 − 1)) for
all 108 disconnected posets with n ≤ 6 and checks: dim R_P = e − e_C; R_P is
homogeneous for the restriction tuple; every piece has quotient dimension
e_C(⊔ C_{m_i}); B_P ∩ (piece) has that many elements and is independent
modulo R_P ∩ (piece). All 108 pass. e_C(C_2^{⊔3}) = 74.

*N2, the homogeneity table.* [homog] tests homogeneity directly (every
statistic-piece of every generator lies in R_P), not via Ree's theorem:

| statistic | [LE] | [Aud] |
|---|---|---|
| restriction tuple | 108 | 108 |
| number of blocks | 5 | 5 |
| jumps | 5 | 5 |
| des (one natural labelling) | 0 | 0 |
| maj (one natural labelling) | 0 | 0 |
| first letter | 0 | 0 |
| random 2-colouring (control) | 1 | 2 |

The random control differs because the colouring is random (both
"homogeneous" cases are posets with tiny pieces); it is a control, not a
claim. **Beyond the stated scope:** des and maj were tested for **every**
natural labelling of every disconnected poset with n ≤ 5, 603 pairs: R_P is
homogeneous on none. So the negative claim does not depend on the choice of
natural labelling, at least for n ≤ 5.

**F7.** [LE] writes "des (natural labelling)" as if the labelling were
unique. Des and maj of individual words depend on which natural labelling
is chosen. State that one natural labelling per poset was tested (and,
optionally, cite the all-labellings check above for n ≤ 5).

*N1, "no q-analogue comes from the theory".* The facts listed in §3.1 are
correct: H_P is one homology group; C_n acts on Lin(P)C_n freely by right
multiplication, so C[Lin(P)C_n] is free of rank e_C and every PLie_j has
dimension e_C; the only CSP from that action is the trivial one of a free
action. The body states the conclusion with the right scope ("we found no
q-analogue coming from H_P or PLie(P)").

**F6.** The verdict table says "The theory gives no q-analogue". That is an
absence claim over an unspecified class of constructions, and it was not
(and cannot be) tested. It should be scoped as in the body: "neither H_P nor
PLie(P) carries a grading or a cyclic action that yields a q-analogue; we
found none". The verdict table should also say that the maj-CSP failures
are for n ≤ 7 and among posets with ∂^n = id, as the §3.2 table does.

*Citations.* [St09] is Electron. J. Combin. 16(2) (2009) #R9 (DOI
10.37236/75 resolves to v16i2r9). [Rh] is J. Combin. Theory Ser. A 117
(2010) 38–76. [RSW] is as above. [LE]'s "from memory; verify" caveat can be
dropped for these three.

---

## Reproduce

```
cd compute
python3 audit_linear_extensions.py            # full run, n <= 7 (~75 s, one core)
python3 audit_linear_extensions.py --quick    # n <= 5 (~4 s)
python3 -m unittest test_audit_linear_extensions
```

Pure Python 3, standard library only. The full output is in
`compute/output/audit_linear_extensions.txt`. Tags in brackets ([P], [R],
[O], …) are the labels printed by the script.

The code is `compute/audit_linear_extensions.py`; the unit tests, with
positive and negative controls (reverse-order toggles, q·X in place of X,
V ⊔ V for Theorem R, C_2 ⊔ C_1 for Props. E and D, des on C_2 ⊔ C_2), are in
`compute/test_audit_linear_extensions.py`.
