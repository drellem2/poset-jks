# Audit: proof of Conjecture S via shuffle-preserving contractions

Work item: mg-8c10c. This is an independent adversarial audit of
`notes/conjecture_s_splitting_cycles_span.md` (the "S-note") and
`compute/conjecture_s.py`, both merged in 4183257 (mg-3de87). Every step was
re-derived by hand. The audit code is `compute/audit_conjecture_s.py`. It
imports nothing from the repository: posets, shuffles, Lie combs, splitting
cycles, order complexes and ranks are all re-implemented. Nothing in the
original was changed.

Tags: PROVEN (with proof), COMPUTED (script + command), CITED, CONJECTURED.

## Verdict

**PROOF HOLDS**, with its dependencies stated precisely.

- **Purely combinatorial results (PROVEN, re-derived).** These are Lemma 1
  (both proofs), Lemmas 2–6, Theorem A (B_P is independent mod Sh_n),
  Theorem B (W_P ∩ Sh_n = R_P, W_P = span B_P ⊕ R_P), Lemma 4
  (|B_P| = e_C(P), including disconnected P) and Corollary 5.4. Their only
  external input is Ree's theorem, and only in Lemma 1's second proof and in
  Cor. 5.4. They do **not** depend on Prop. Φ or on Jenča–Sarkoci.
- **Homological results (PROVEN given the inputs).** These are Theorem C
  (Conjecture S and the basis {ρ_w : w ∈ B_P}), Cor. 5.5 and §6. They are
  correct deductions from three inputs: Prop. Φ (only the direction
  "ρ-relation ⇒ signed shuffle" for Theorem C), Lemma D, and J–S Thm 4.5.
  §C below says exactly which claims fall if Φ falls.
- **Chain-level check (COMPUTED, here for n ≤ 6).** At chain level, without
  Φ and without J–S, all of Theorem C and Cor. 5.5 hold for every unlabeled
  poset with 3 ≤ n ≤ 6. This covers:
  - the basis claim;
  - the kernel statement;
  - the explicit isomorphism, signs included;
  - Aut(P)-equivariance.

  This check extends the S-note's chain-level check from n ≤ 5 to n ≤ 6. It
  also computes dim H_P directly, so it re-checks J–S Thm 4.5 rather than
  citing it.

No step is broken. There are no mathematical gaps. Only small wording and
bookkeeping issues were found (§E). The novelty search found no prior
statement of Theorem A or B for general P (§F).

## A. Claim table

| # | Claim (S-note) | Status | Reason |
|---|---|---|---|
| 1 | Lemma 1, exact formula for E_{a,x}(u ш v) | CONFIRMED | Re-derived (§B.1). COMPUTED: exact for every proper shuffle and every (a, x), n ≤ 6 (118 540 cases in total). Also checked Ree-free: E(Sh_n) ⊆ Sh_{n−1} by rank against the shuffle generators, n ≤ 5. |
| 2 | Lemma 1, second proof (adjoint of a ↦ [x, a]) | CONFIRMED | Adjoint computed by hand. Sign convention: x before a gives +, which matches xa − ax = [x, a] (§B.1). COMPUTED: ⟨E w, w′⟩ = ⟨w, w′[a→xa] − w′[a→ax]⟩ for all words, n ≤ 5. Every right comb on A∖x is sent to an element orthogonal to every proper shuffle, n ≤ 5. |
| 3 | Lemma 2(a)–(d) (quotient P/{a,x}) | CONFIRMED | Re-derived. COMPUTED for every poset with n ≤ 6 and every pair adjacent in some extension: the quotient is acyclic, w∖x ∈ Lin Q, and (b) holds in both directions. |
| 4 | (★) and its support on Lin Q | CONFIRMED | Re-derived (§B.2). COMPUTED: E_{a,x}(X) is supported on B_Q for X supported on B_P. |
| 5 | Lemma 3 (adjacent incomparable swaps connect Lin P) | CONFIRMED | Classical. The proof given is correct. COMPUTED: the swap graph is connected, n ≤ 6. |
| 6 | Use of Lemma 3 inside Theorem A, with the first-block condition | CONFIRMED | §B.3. The swap identity is derived for **every** w ∈ Lin P, not only good ones, with c extended by 0 off B_P. The first-block condition enters only (i) through the induction hypothesis, via support on B_Q, and (ii) through the anchor word where c = 0. The two cases do not interact badly. |
| 7 | Lemma 4: \|B_P\| = e_C(P), via blocks and rotations | CONFIRMED | §B.4, including disconnected P. COMPUTED: a rotation is in Lin P iff the cut is a union-prefix, and each C_n-orbit meeting Lin P contains exactly one good word, for every base component, n ≤ 6. |
| 8 | Lemma 5 (good words contract to good words) | CONFIRMED | Re-derived, including the case P_1 = {x}. COMPUTED, n ≤ 6. |
| 9 | Theorem A (B_P independent mod Sh) | CONFIRMED | §B.3. COMPUTED for every base component of every poset, n ≤ 6. |
| 10 | Lemma 6 (W_P = span B_P + R_P) | CONFIRMED | Re-derived. The strict decrease of μ is asserted in the code at every reduction step. COMPUTED, n ≤ 6. |
| 11 | Theorem B (K_P = R_P, direct sum, dim K_P = \|Lin P\| − e_C) | CONFIRMED | Follows from Theorem A, Lemma 6 and Lemma 4. COMPUTED: rank(R_P gens) + \|B_P\| = \|Lin P\| = rank(R_P gens ∪ B_P), n ≤ 6. |
| 12 | Theorem C (Conjecture S; basis ρ_{B_P}) | CONFIRMED given Φ(⇒), D, J–S | Correct deduction. Uses only one direction of Φ (§C). COMPUTED at chain level without Φ or J–S, n ≤ 6. |
| 13 | Theorem C, kernel statement | CONFIRMED given Φ (both directions), D, J–S | COMPUTED at chain level, n ≤ 6: every R_P generator gives an exact integral relation, and rank{ρ_w} = e_C. |
| 14 | Remark: (Φ) + (D) + §4 give dim H_P ≥ e_C(P) | CONFIRMED | Only Φ(⇒) is needed. |
| 15 | Cor. 5.4 (Lie_n restricted to Lin P is R_P^⊥; onto for connected P) | CONFIRMED given Ree | Standard duality. Exact over Q, since the form is nondegenerate and finite-dimensional. |
| 16 | Cor. 5.5: H_P ⊗ sgn ≅ C[Lin P]/R_P, with ρ_w ⊗ 1 ↦ sgn(w) w | CONFIRMED given Φ, D, J–S | §B.5. The sign twist is right: g ρ_w = ρ_{gw} holds exactly, with no orientation sign, and sgn(gw) = sgn(g) sgn(w). COMPUTED at chain level, n ≤ 6: ρ_w = Σ_b sgn(w) sgn(b) N(w)_b ρ_b exactly, where N is the Lemma 6 normal form. g ρ_w = ρ_{gw} for all g ∈ Aut(P). |
| 17 | §6: eq. (mainconj) for connected P | CONFIRMED given Theorem C | Both sides are free C[Aut P]-modules of rank \|Lin P\|/\|Aut P\| (§B.6). |
| 18 | "The chain-level check (n ≤ 5) does not go through Φ" | CONFIRMED | §C.2. Top homology equals the top cycle space, so chain independence is homology independence. |
| 19 | "§2–§5.2 use none of these inputs" | OVERSTATED (wording) | There is no §5.2. The intended range is §2 to Theorem B/Lemma 6. Lemma 1's second proof uses (Ree). The first proof does not, so the claim holds for the proof route that matters. |
| 20 | Status line "(Φ) CITED / PROVEN in the literature note" | OVERSTATED pending mg-350d5 | Φ is under separate audit. Every homological claim in the S-note is conditional on it. See §C for what survives either way. |
| 21 | `conjecture_s.py` docstring: [La] "checked here for n ≤ 6" | Inconsistent with the note (n ≤ 7) | The docstring and the note disagree on the range. This is not a mathematical issue. The n = 7 run was not archived (the S-note says so). It was not re-run here. |
| 22 | n = 7 computations ([S], [B], [E]) | UNCHECKED | Not re-run. Pure Python is too slow at n = 7 without the original's shortcuts. My exhaustive range is n ≤ 6. |
| 23 | "May be folklore" (novelty) | Partially resolved | The antichain case is classical. Nothing was found for general P (§F). |

## B. Re-derivations

### B.1 Lemma 1 and the adjoint

*Case analysis.* Let a, x lie in the same factor u.
- If they are not adjacent in u, some letter of u separates them in every
  term, so the image is 0.
- If u = u_1 x a u_2, the terms with x immediately before a are in bijection
  with (u∖x) ш v. The bijection inserts x before a. All signs are +.
- The "ax" case gives the same with sign −.

Now let x ∈ u = u_1 x u_2 and a ∈ v = v_1 a v_2. In a term …xa…:
- the letters before x are u_1 together with the letters of v before x;
- the letters of v before x are those before a, namely v_1;
- so the term is p x a q with p ∈ u_1 ш v_1 and q ∈ u_2 ш v_2, and every
  pair (p, q) occurs.

The same is true for p a x q. Both families contract to p a q with opposite
signs, so they cancel. In the surviving case u∖x ∋ a is nonempty, so the
image is a *proper* shuffle on A∖x.

*Adjoint.* ⟨E_{a,x} w, w′⟩ = [w = w′[a→xa]] − [w = w′[a→ax]]. So
E* w′ = w′[a→xa] − w′[a→ax], the image of w′ under the algebra map
a ↦ xa − ax = [x, a] (other letters fixed), restricted to multilinear words.

That map is an associative-algebra morphism C⟨A∖x⟩ → C⟨A⟩ sending
generators to Lie elements, so it maps Lie polynomials to Lie polynomials.
For s ∈ Sh_A and ℓ ∈ Lie_{A∖x}, ⟨E s, ℓ⟩ = ⟨s, E*ℓ⟩ = 0. By Ree,
Lie_{A∖x}^⊥ = Sh_{A∖x} in the multilinear component, so E s ∈ Sh_{A∖x}.

The signs in the S-note are right. A sign-flipped E fails both the formula
and E(Sh) ⊆ Sh. This is a positive control in [CTL]: in case 2 the flipped
image of x ш av is nonzero.

### B.2 Lemma 2, (★), Lemma 5

*Lemma 2(a).* Let y <_P x with y ≠ a. In w, y precedes x. Since a and x
are adjacent and y ≠ a, y also precedes a. So w∖x respects the image
relation y < a. The same argument covers x <_P z. Hence w∖x is a linear
order respecting every generator, so the transitive closure is acyclic.

*Lemma 2(b).* Only the a–x relation can fail.

*(★).* The coefficient of w′ in E(X) collects exactly the two preimages
w′[a→xa] (sign +) and w′[a→ax] (sign −). If either preimage lies in
Lin P, then w′ ∈ Lin Q by (a). Words outside Lin P have c = 0. So E(X) is
supported on Lin Q, and on B_Q by Lemma 5.

*Lemma 5.* Let π′ be a union-prefix of w∖x for Q. It pulls back to a prefix
of w that does not separate a and x. If π′ omits a and x sits just before
a, the pull-back is π′ itself, which is still a prefix of w. Q-components
pull back to unions of P-components, so the pull-back is a union-prefix of
w. It therefore contains b_1 ⊇ P_1. So the first block of w∖x contains the
image of P_1, and hence its Q-component Q_1.

The degenerate case P_1 = {x} works: the pull-back contains x, hence a, so
the first block of w∖x contains a = image(x). This case is COMPUTED.

### B.3 Theorem A: the induction and the swap step

The proof is an induction on n over **all** posets and **all** choices of
base component at once. The hypothesis is applied to Q with base Q_1. This
is legitimate because Lemma 5 is stated for that base.

Fix X = Σ_{w∈B_P} c_w w ∈ Sh, and extend c by 0 to all words.
1. For **any** w ∈ Lin P (good or not) and any adjacent pair (x, a) = (w_i,
   w_{i+1}), the induction gives E_{a,x}(X) = 0.
2. Hence the coefficient of w∖x in (★) vanishes:
   c(w) = c(w with w_i, w_{i+1} swapped).
3. If w_i <_P w_{i+1}, the swapped word is not in Lin P, so c(w) = 0.

So c, viewed as a function on Lin P that is 0 off B_P, is invariant under
adjacent incomparable swaps. By Lemma 3 it is constant on Lin P.

This is the point the ticket asked about. Lemma 3 is applied to Lin P, not
to B_P, and c is a function on Lin P. B_P need not be swap-connected (for an
antichain it is not closed under swaps), and the argument does not need it
to be.

The first-block condition is used only twice:
- in the induction hypothesis, via support on B_Q;
- in the choice of an anchor word w_0 ∈ Lin P with c(w_0) = 0.

The anchor exists in both cases:
- **k ≥ 2 components.** Take a linear extension of P_2 followed by one of
  P∖P_2. Its first block is exactly P_2, because no proper nonempty subset of
  a connected component is a union of components. So the word is not good.
- **Connected, n ≥ 2.** List ↓q∖{q} with p last, then q, then the rest, for
  a cover p ⋖ q. Here p is maximal in ↓q∖{q}, since an element strictly
  between p and q would contradict the cover. The result is a linear
  extension with the comparable pair p, q adjacent, so c = 0 there by step 3.

The base case n = 1 is trivial. At n = 2 the quotient has one letter and
Sh = 0. No gap.

### B.4 Lemma 4: the cyclic structure

J–S Def. 4.1 defines f ∼ g by ⊕_f = ⊕_g. ⊕_f depends only on the cyclic
order of f, so ∼-classes are the C_n-orbits that meet Lin P. The literature
note §2.2 says the same. In the audit code, e_C is counted directly as the
number of C_n-orbits meeting Lin P, not via blocks.

The S-note's argument:
- A rotation at cut j is in Lin P iff the prefix w_1⋯w_j is a union of
  components.
  - (⇐) No relation crosses the cut.
  - (⇒) If the prefix is not a union of components, some component meets
    both sides. Connectedness of its comparability graph gives a comparable
    pair across the cut. In w that pair is ordered prefix-first, so the
    rotation reverses it.
- Each block is a union of components, as a difference of two unions.
- A union-prefix of a rotation cannot end inside a block. If it did, the
  part of that block before the end would itself be a union of components,
  creating a union-prefix of w inside the block.
- So a class is the set of m distinct block rotations of w. They are
  distinct because they start with letters from disjoint blocks.
- P_1 is a component, so it lies in exactly one block. Exactly one rotation
  puts that block first.

This is correct for disconnected P; there it is the whole content. For
connected P, m = 1 and B_P = Lin P.

Positive control: "words beginning with a letter of P_1" is a natural but
wrong variant. For P = {0<1} ⊔ {2<3} it gives 3 words against e_C = 5. The
good word 2031 is classified correctly.

### B.5 Cor. 5.5 and the sign twist

- **Aut(P) preserves the structure.** Aut(P) permutes components, so it
  preserves Lin P, B-structures up to base change, and R_P:
  g(s ш t) = gs ш gt.
- **Exact equivariance of the cycles.** g maps Π_w onto Π_{gw} and the chain
  with cut order π to the chain with the same cut order. So g ρ_w = ρ_{gw}
  exactly, with no orientation sign. COMPUTED for every g ∈ Aut(P) and
  w ∈ Lin P, n ≤ 6.
- **Defining the isomorphism.** Define F : C[Lin P]/R_P → H_P by
  F(w) = sgn(w) ρ_w.
  - F is well defined iff every R_P generator gives a relation
    Σ_{z ∈ s ш t} sgn(z) ρ_z = 0. This is Φ(⇐) restricted to R_P.
  - F is onto by Theorem C.
  - Both sides have dimension e_C, so F is an isomorphism.
- **The twist.** F(g w) = sgn(gw) ρ_{gw} = sgn(g) · g F(w). So F intertwines
  the permutation action on C[Lin P]/R_P with sgn ⊗ (action on H_P). That is
  H_P ⊗ sgn ≅ C[Lin P]/R_P.
- **Chain-level check.** COMPUTED at chain level, n ≤ 6: for every w ∈ Lin P
  and every base component,
  ρ_w = Σ_{b∈B_P} sgn(w) sgn(b) N(w)_b ρ_b
  holds exactly over Z, where N(w) is the Lemma 6 normal form. Positive
  control: dropping the signs breaks this for P = {0<1} ⊔ {2<3}, w = 2301.

### B.6 §6, connected P

- **H_P.** For connected P, B_P = Lin P and |Lin P| = e_C. So
  {ρ_w : w ∈ Lin P} is a basis of H_P, permuted by Aut(P) via
  g ρ_w = ρ_{gw}. The action on Lin P is free: gw = w forces g to fix every
  letter. So H_P is free, and so is H_P ⊗ sgn.
- **Lie(P).** Lie(P) = span{w e_ζ} has basis {w e_ζ}. The w e_ζ are nonzero
  and supported on pairwise distinct C_n-orbits, since for connected P no
  nontrivial rotation of w is in Lin P. This basis is permuted freely.
- Same rank, so the modules are isomorphic. The argument is correct.

## C. Dependence on Prop. Φ (audited separately, mg-350d5)

Write Φ(⇐) for "Σ a_σ sgn(σ) σ ∈ Sh_n ⇒ Σ a_σ ρ_σ = 0" (well-definedness).
Write Φ(⇒) for the converse (injectivity).

### C.1 What stands or falls

| Claim | Needs Φ? |
|---|---|
| Lemma 1–6, Theorem A, Theorem B, Lemma 4, Cor. 5.4 | **No.** Pure word combinatorics (+ Ree for Cor. 5.4). Survive any outcome of mg-350d5. |
| Theorem C, basis / spanning; Remark dim H_P ≥ e_C | **Φ(⇒) only** (plus D, J–S) |
| Theorem C, kernel statement | Φ(⇒) and Φ(⇐) (the latter only on R_P generators, plus dimension count) |
| Cor. 5.5 (H_P ⊗ sgn ≅ C[Lin P]/R_P) | Theorem C basis + Φ(⇐) on R_P generators |
| §6 (mainconj for connected P) | Theorem C basis only, i.e. Φ(⇒) |

One observation for mg-350d5. Φ(⇒) follows from Φ(⇐) by counting:
- Wachs's basis theorem says {ρ_σ : σ(n) = n} is a basis, so
  σ ↦ sgn(σ) ρ_σ maps C[S_n] onto H̃_{n−3}(Π̄_n) of dimension (n−1)!.
- dim Sh_n = n! − (n−1)!.
- So Sh_n ⊆ kernel forces Sh_n = kernel.

So for the whole homological half, what must be secured is the single family
of chain identities Σ_{z ∈ u ш v} sgn(z) ρ_z = 0, together with the CITED
basis theorem. If Φ fell entirely, Theorem C would revert to CONJECTURED.
Theorems A and B would remain.

### C.2 The chain-level check avoids Φ

Δ(Ô(P)) has dimension n − 3, so it has no (n−2)-simplices. Hence
H̃_{n−3} = Z_{n−3}, a subspace of the chain group. Linear independence of
the chains ρ_w is therefore literally linear independence in H_P. The check
needs no Φ: it computes ρ_w as explicit chains and ranks them. CONFIRMED by
reading `compute/conjecture_s.py` ([rho] ranks explicit chains) and by my
own re-implementation.

I went further, for n ≤ 6 (every unlabeled poset with 3 ≤ n ≤ 6, all base
components), with no Φ and no J–S:
- **Lemma D:** every chain of ρ_w lies in Δ(Ô(P)).
- **Cycles:** ∂ρ_w = 0 exactly over Z.
- **The rank sandwich:** rank_p{ρ_b : b ∈ B_P} = |B_P| = e_C(P) =
  dim_p Z_{n−3}(Δ(Ô(P))). Since
  rank_p ≤ rank_Q ≤ dim_Q Z ≤ dim_p Z,
  this proves over Q that ρ_{B_P} is a basis of H_P. It also proves that
  dim H_P = e_C, independently of J–S Thm 4.5.
- **The relations:** each R_P generator gives an exact integral relation.
  Together with rank{ρ_w : w ∈ Lin P} = e_C and dim R_P = |Lin P| − e_C
  ([AB]), the relations among the ρ_w are exactly R_P (sign-twisted).
- **Cor. 5.5** and equivariance hold as in §B.5.

## D. Computations (COMPUTED)

Script: `compute/audit_conjecture_s.py`, plain Python 3. It does not import
`conjecture_s.py`, `splitting_cycles.py` or any other repository module.
Command, from `compute/`:

    python3 audit_conjecture_s.py --nmax 6 --ne 6 --nlem 6 --nchn 6 --nree 6 \
        > output/audit_conjecture_s.txt

Output is archived at `compute/output/audit_conjecture_s.txt`. The run ends
with `ALL CHECKS PASSED` (exit 0), after about 16 min of single-core CPU time.
Most of that is the n = 6 chain-level check. The script also prints the case
counts: 9124 (poset, adjacent pair) cases for the lemmas, 402 posets at chain
level, and 404 posets for the shuffle-instrument cross-check.

- **Posets** are generated independently: add a maximal element above every
  down-set, then deduplicate by a canonical form. The counts
  1, 2, 5, 16, 63, 318 (n = 1..6) match OEIS A000112. This is a control.
- **Shuffle membership** uses two instruments:
  - comb coordinates: pair against the right combs [w_1,[…,[w_{n−1}, n]]],
    whose kernel is Sh_n by Ree;
  - Ree-free: reduce against an echelon basis of the span of all proper
    shuffle generators.

  [REE] checks that both give the same rank on Lin P for every poset with
  n ≤ 6, and that rank Sh_n = n! − (n−1)!.
- **Rigour.** Ranks are mod p = 2^31 − 1.
  - Independence conclusions have the form rank_p = count, so they hold
    over Q.
  - K_P = R_P uses dim_p R ≤ dim_Q R ≤ dim_Q K ≤ |Lin P| − rank_p, with the
    two ends equal.
  - Lemma 6 and the Cor. 5.5 identity are exact over Z.
- **Positive controls [CTL]**, all firing:
  - a sign-flipped E;
  - Lin P of {0<1} ⊔ {2<3} is dependent mod Sh (rank 5 < 6);
  - the wrong variant "starts with a P_1 letter";
  - Lin P of the 3-antichain has rank 2 < 6;
  - a single chain is not a cycle;
  - dim Z for the 4-antichain is 3! = 6;
  - the unsigned shuffle relation for ρ fails;
  - the iso check without signs fails.

## E. Minor issues (no effect on correctness)

1. The S-note's "§2–§5.2" refers to a nonexistent subsection. Lemma 1's
   *second* proof uses Ree; the first proof is elementary.
2. The S-note lists Φ as "CITED / PROVEN". Until mg-350d5 reports, every
   homological claim should read "PROVEN given Φ(⇒)" (Theorem C basis, §6)
   or "given Φ" (kernel statement, Cor. 5.5). The table in §C.1 is the exact
   dependency.
3. The `conjecture_s.py` docstring says the [La] kernel check is for
   n ≤ 6. The note's §8 says n ≤ 7. The n = 7 run was not archived. I did
   not re-run n = 7.
4. The heuristic link between E_{a,x} and the link of ρ_w at the atom
   π_{a,x} is flagged as unchecked in the S-note, and nothing uses it.
   Making it precise would give a fully Φ-free proof of Theorem C: run the
   §4 induction directly on chains. This is a suggestion, not a gap.

## F. Novelty

- **Classical cases.**
  - The antichain case of Theorem A says the words beginning with a fixed
    letter are a basis of C[S_n]/Sh_n. This is classical. It is the
    multilinear part of "Lyndon words are a basis of the shuffle algebra
    modulo products" (Radford 1979; Reutenauer, *Free Lie Algebras*, Ch. 6),
    equivalently the duality with the comb basis of Lie_n.
  - Ree's criterion (Lie = (proper shuffles)^⊥) is restated, for example, by
    Patras–Reutenauer–Schocker, *On the Garsia Lie idempotent*, Canad. Math.
    Bull. (2005). CITED, read only via the search abstract.
- **Search result for general P.** Searches for "linear extensions … modulo
  shuffles", "Lie elements … linear extensions", Malvenuto–Reutenauer
  primitives and Schocker found no statement of Theorem A, Theorem B or
  Cor. 5.4 for general posets.
  - The closest hit is Gessel-type work: e.g. arXiv:math/0509125,
    *P-partitions and a multi-parameter Klyachko idempotent*, which realizes
    u ш v as Lin of a poset P_{u,v} in order to pair Lie elements with
    shuffles. That goes in the opposite direction: shuffles as extensions,
    not extensions modulo shuffles.
  - Related context: Cor. 5.4 implies that two distinct linear extensions of
    a connected poset are never twins or anti-twins in the sense of
    Schützenberger's problem (Duchamp–Laugerotte–Luque, arXiv:0807.3519).
    This is consistent with the known fact that a multilinear w and rev(w)
    are anti-twins (up to the sign (−1)^{n−1}): w and rev(w) are never both
    extensions of a connected poset with n ≥ 2.
- **Verdict:** NOT FOUND, which is not proof of novelty. The S-note's
  "may be folklore" caveat remains appropriate. The natural experts to ask
  are those on free Lie algebras and shuffle algebras (Reutenauer,
  Schocker's coauthors, Duchamp) and on P-partitions (Gessel).
