# Audit of `notes/cyclic_sieving_cyc.md`

**Verdict: HOLDS WITH FIXES.** I re-derived every PROVEN claim by hand and
every proof survives. Independent code reproduces every COMPUTED number,
with one exception: the inv(B_P) counts of the §6 sweep depend on the
labelling (F4). The fixes concern how the evidence is counted, citations
and wording (F1–F6). None of them changes a theorem. Two of them strengthen
the note. First, clause (a) of Theorem C is **necessary whenever
gcd(k_i) = 1** (proof in §3). Second, [RSW] Thm 8.2 is now checked against
the published paper, so the regular case of §4 is a corollary of a cited
theorem (§4).

The note is cited as [CSC]. Its other references are as in [CSC]. This
audit was written from [CSC], from [LE] §§0 and 4 (for the definitions of
Cyc(P), cuts, B_P and Proposition F), and from the primary source [RSW].
It imports nothing from `compute/`. All code is in
`compute/audit_cyclic_sieving_cyc.py` ("[Aud]"). Only after the verdict and
the tables below were fixed did I open `compute/output/cyclic_sieving_cyc.txt`.
I opened it only to locate the origin of two counts (F1, F4). I did not read
`compute/cyclic_sieving_cyc.py`.

| # | Claim of [CSC] | Verdict | How checked |
|---|---|---|---|
| L1 | Lemma 1 (fixed class ⇒ all cycles of length o(g)) | **HOLDS** | re-derived (§1); F = 0 off the types d^{k/d} on all 23 T^{⊔k}, and on all 206 classes conjugate into W |
| P2 | Prop. 2, F(w) = φ(d) d^{k/d−1} c_{k/d} | **HOLDS.** I give a self-contained proof (§1), which does not route through [LE §4] | brute-force F on every cycle type of all 23 T^{⊔k}. The multi-type form F(w_d) = φ(d) d^{#cycles−1} e_C(one copy per cycle) holds on all 206 classes in W |
| A | Theorem A (X_P ∈ N[q], X_P(1) = e_C, X_P(0) = #orbits) | **HOLDS** | re-derived (§2); integrality, nonnegativity and X(1) on every polynomial computed |
| ★ | closed form (★); the k = 2 formula | **HOLDS** | (★) equals the Molien sum with brute-force F on 23/23. All 23 rows of the §5 table reproduced: e(T), e_C, fix, X mod q^k − 1, and the full X_P where printed |
| B | Theorem B (i), (ii) | **HOLDS** | re-derived (§2) |
| C-suff | Theorem C, sufficiency | **HOLDS** | re-derived (§2); criterion equals the CSP on 206/206 classes |
| C-b | necessity of (b) | **HOLDS** | re-derived, including F(w_e) > 0 for several types |
| C-a | necessity of (a): "COMPUTED on 249 classes … OPEN" | **HOLDS as stated, with two corrections.** "249" counts 43 classes twice: 206 classes are distinct (F1). Only 8 of them have (a) failing, and only 6 have (a) as the *sole* failing clause. **New: (a) is necessary whenever gcd(k_i) = 1** (§3). In general it is still OPEN; symbolic evidence is in §3 (F2) | §3 |
| T | Corollary T (σ, ⟨σ^j⟩, (k−1)-cycle, Springer-regular elements of W) | **HOLDS** | re-derived (§2); σ 23/23, (k−1)-cycle 8/8 |
| T′ | "(6, 2) in A_8 is not regular in any reflection subgroup of S_8" | **Imprecise.** I verified that it is not regular in S_8 = W, which is also its G. "Any reflection subgroup" is neither defined nor checked (F5). The rest of that paragraph (F(g³) = 48, X_P sieves ⟨g⟩, it is the only such class) **HOLDS** | [tk-allg] |
| PC | Pattern × component: the product with the RSW word polynomial sieves σ; it agrees with X_P mod q^k − 1 but not as a polynomial; the naive product sieves 12/23 | **HOLDS** | 23/23; equal mod q^k − 1 on 23/23, as polynomials on 12/23; naive product 12/23 |
| G | §4, the G(r,1,k) / Springer version | **HOLDS.** Every count in the §4 table is reproduced exactly: 1/3/11/44/216/1315 posets; 1/4/17/76/413/2637 regular classes; 0/0/1/5/27/122 non-regular classes; 3148/3148 regular classes sieved; 114 of 155 non-regular classes sieved, all of them free. **[RSW] Thm 8.2 is correctly numbered and correctly stated** (checked in the published paper). The note can upgrade the regular case to "PROVEN given [RSW] Thm 8.2 (CITED)" (F3). Nowhere does [CSC] present it as proven | §4 |
| O′ | Prop. O′: A_4 is an obstruction, none exists for n ≤ 3, and A_4 is the only one at n = 4 | **HOLDS** | by hand (§5); every poset with n ≤ 6: obstructions number 0, 0, 1, 0, 4 for n = 2, …, 6 |
| N | "Natural candidates all fail", with the §6 counts | **HOLDS.** Every candidate fails on some σ. Every §6 count is reproduced exactly except inv(B_P) on the sweep (labelling-dependent, F4) | [tk-cand], [cand] |
| X1 | No nonnegative-coefficient obstruction exists for one ⟨g⟩ | **HOLDS** (trivial: canonical polynomial) | — |
| X2 | "e_C(C_m^{⊔k}) is a necklace count only for m = 1": e_C(C_2 ⊔ C_2) = 5, but content (2, 2) has 2 necklaces | **HOLDS** | [ctl-eC], test |

---

## 0. Conventions and controls

Cyc(P) is the set of rotation classes of words that contain a linear
extension. [Aud] keys each class by its lexicographically least rotation.
Aut(P) acts by relabelling letters. **All fixed-point counts are computed by
brute force from this action, never from a formula.**

The CSP test for ⟨g⟩, with N = o(g), compares X mod q^N − 1 with the
canonical polynomial m_t = #{orbits O : (N/|O|) divides t}. This is the
multiplicity of the character g ↦ ω^t in C[O] = Ind_{⟨g^{|O|}⟩} 1, so the
test is equivalent to X(ω^j) = F(g^j) for all j.

Positive controls, all passing:
- **[RSW] Thm 1.1:** words of content μ under rotation, with the
  q-multinomial, for 11 contents (n ≤ 6). The negative control moves one
  unit of coefficient from q^1 to q^0; it is rejected 11/11 times.
- **The fake-degree engine:** on j-subsets of [k] it returns [k; j]_q in all
  35 cases with k ≤ 7.
- **Kraśkiewicz–Weyman:** the fake degree of S_k/C_k equals
  Σ_{maj w ≡ 0 (k)} q^{maj(w^{−1})} for k = 2, …, 7.
- **Poset enumeration:** 1, 2, 5, 16, 63, 318, 2045 unlabelled posets for
  n ≤ 7.
- **e_C(⊔ chains):** the exponential formula (§3) agrees with brute force
  on 9 contents.

For these controls I wrote the CSP instrument myself, before I applied it to
[CSC].

## 1. Lemma 1 and Proposition 2

**Lemma 1.** The proof is correct. One point is implicit. Write gw = wγ^r.
Then r is the same for every word of the class, because
g(wγ^t) = (wγ^t)γ^r.

**Proposition 2: a self-contained proof.** Let g ∈ Aut(P) fix a class C,
and let d = o(g). Then gL = Lγ^r for every L ∈ C. Since γ^r is conjugate to
g, it has order d, so r = s·n/d with gcd(s, d) = 1. That gives the φ(d).

Cut a linear extension L ∈ C into d blocks of length n/d. Then g maps block
j to block j + s. Let b(x) be the block index of x. For x < y in one
component, b(x) ≤ b(y). Applying g^t gives
(b(x) + ts mod d) ≤ (b(y) + ts mod d) for every t. If b(x) < b(y), choose t
with b(y) + ts ≡ 0. This contradicts the inequality, so b(x) = b(y). Hence
b is constant on each component, and **every block of L is a union of
components**, containing one copy from each cycle of components.

Conversely, take any u that is a linear extension of such a union. Then
u g^{s'}(u) g^{2s'}(u) ⋯, with s' = s^{−1} mod d, is a linear extension of P
fixed up to rotation. Fix s. Every lift of a linear extension of the
quotient T^{⊔k/d} is obtained by choosing one copy per cycle: d^{k/d}
choices. Rotating by one block permutes these lifts in orbits of size d, so
each class over a given class of the quotient is counted d times. Hence
F = φ(d) · d^{k/d−1} · c_{k/d}.

[Aud] confirms this on every cycle type of all 23 T^{⊔k} [tk-prop2]. It
also confirms the multi-type form F(w_d) = φ(d) d^{#cycles−1}
e_C(one copy per cycle) on all 206 classes conjugate into W [thmC-F].

## 2. Theorems A, B, C and Corollary T

**Theorem A.** I re-derived it via Molien and Chevalley. F is a permutation
character, hence real, and the S_k-modules R_t are self-dual. So
dim (R_t ⊗ M)^W = ⟨M, R_t⟩. The degrees are 1, …, k_i. Since R is the
regular representation, X(1) = e_C(P). Since R_0 is the trivial
representation, X(0) = #orbits.

**(★).** The class of type d^{k/d} has k!/(d^{k/d}(k/d)!) elements, and the
factor φ(d) d^{k/d−1} c_{k/d} comes from Proposition 2. Together they give
(★). The k = 2 case reduces to ((c_2 + c_1) + (c_2 − c_1)q)/2.

**Theorem B.** The order of vanishing of ∏(q;q)_{k_i} at ζ is Σ⌊k_i/e⌋. The
denominator vanishes to order Σ k_i/d if e | d, and to order 0 otherwise.
Every inequality in the proof checks.

In case (i), the surviving term evaluates to e^{k/e}(k/e)!, because
∏_{a=1}^{e−1}(1 − ζ^a) = (x^e − 1)/(x − 1) at x = 1, which is e, and
[t]_{q^e} → t. This cancels
the class size exactly.

**Theorem C.**
- *Sufficiency.* g^j and g^{N/e} generate the same group, and a power prime
  to e keeps e-cycles e-cycles. In the other case, Lemma 1 gives F = 0 and
  B(ii) gives X = 0.
- *Necessity of (b).* Let g^{N/e} have order e and a copy-cycle of length
  ≠ e. Then F(g^{N/e}) = 0. But X(ω^{N/e}) = F(w_e), and F(w_e) > 0 by the
  concatenation u w_e(u) ⋯ w_e^{e−1}(u), which is a linear extension fixed
  up to rotation by n/e.

[Aud] compared the criterion with the actual CSP on every class conjugate
into W [thmC]:
- all P with n ≤ 7: 171 classes;
- T^{⊔k} with n = 8: 35 classes.

It agrees on 206/206.

**Corollary T.** Regular elements of the permutation representation of
∏S_{k_i} have type e^{f_i}1^{r_i} with r_i ∈ {0, 1}; for r_i = 1 the zero
coordinates sit in different factors. The two clauses then follow:
- (a): every divisor of e is ≤ e ≤ max k_i.
- (b): if e′ | e divides every k_i, then each r_i = 0, since
  e′ | f_i e + 1 forces e′ = 1. So g^{e/e′} has type e′^{k_i/e′}.

[Aud] also confirms X_P sieves σ on 23/23 and the (k−1)-cycle on 8/8.

## 3. Necessity of clause (a)

**Where "249" comes from (F1).** The archived output of [CSC] has two lines:
- [tk-W]: 78 classes, the T^{⊔k} with n ≤ 8;
- [sweep-W]: 171 classes, all P with n ≤ 7.

78 + 171 = 249. But the 43 classes of T^{⊔k} with n ≤ 7 appear in both
lines (computed by [Aud]), so there are **206 distinct classes**.

More important is how many of them say anything about (a). In only **8**
classes does (a) fail. In only **6** of those does (b) hold, so that (a) is
tested alone. They are:

| P | (k_i) | cycle type of g on copies | gcd(k_i) |
|---|---|---|---|
| A_5 | (5) | (2, 3) | 5 |
| A_7 | (7) | (2, 5) | 7 |
| A_7 | (7) | (3, 4) | 7 |
| A_5 ⊔ C_2 | (5, 1) | (2, 3), (1) | 1 |
| A_3 ⊔ C_2 ⊔ C_2 | (3, 2) | (3), (2) | 1 |
| A_8 | (8) | (3, 5) | 8 |

The last row is the one with n = 8. The other two classes where (a) fails
are (1, 2, 5) and (1, 3, 4) in A_8, and (b) fails there too. The CSP fails
in all 8 classes.
So the phrase "necessary in all 249 computed cases" overstates the
evidence. The note should say "in all 6 computed cases where (a)
is the only failing clause".

**Proposition (new, PROVEN): if gcd(k_i) = 1, then (a) is necessary.**

*Proof.* Let e | N with e > max k_i. By Lemma 1, only types with all parts
equal to a common d dividing every k_i have F ≠ 0. Here that means d = 1,
so

  X_P = e_C(P) · ∏_i [k_i]_q! / k_i!.

Since e > k_i, no factor [j]_ζ with j ≤ k_i vanishes. So X_P(ζ_e) ≠ 0. But
g^{N/e} has order e > max k_i, so its cycles are not all of length e, and
F(g^{N/e}) = 0 by Lemma 1. ∎

This covers 2 of the 6 informative classes.

**Two facts that bound any general proof.**
- (i) *The bad e are never prime powers.* An element of ∏S_{k_i} whose
  order is divisible by ℓ^b has a cycle of length divisible by ℓ^b, so
  ℓ^b ≤ max k_i. So every e that violates (a) has a unit 1 − ζ_e. Norm
  arguments alone do not finish the proof.
- (ii) *Positivity of the coefficients of (★) is not enough.* Write
  y = ∏ e(T_i)^{k_i/g} with g = gcd(k_i). By Proposition F of [LE], X_P
  depends on the T_i only through their sizes m_i and through y.
  Consider two types with k = (4, 4) and e = 6. Then X_P(ζ_6), as a
  polynomial in y, has a real root with 0 < y < 1, for every (m_1, m_2)
  ∈ [3]². For example, with m = (1, 2) it is a root of
  1048410y³ + 50y − 12 ≈ 0 at y ≈ 0.02183 (corrected from "≈ 0.0225"
  by `notes/cyclic_sieving_gcd.md` and re-derived in
  `notes/audit_cyclic_sieving_gcd.md` §3; the root lies in (0, 1) either way). So a proof must use y ≥ 1, the
  actual size of the c_j.

**Symbolic evidence (COMPUTED, [neca]).** For fixed sizes (m_i) and
multiplicities (k_i), [Aud] reduces X_P mod Φ_e, keeping y as an
indeterminate. Each coordinate is a polynomial in y with rational
coefficients. A Sturm count shows their gcd has no root y ≥ 1. The pattern
factors e_C(⊔C_m^{⊔j}) come from the exponential formula
Σ e_C x^n/n! = log Σ (Σmn_m)!/∏m!^{n_m} · x^n/n!, checked against brute
force. The search found no failure:
- **single type**, k = 3, …, 16, |T| = 1, …, 6: 84 pairs (k, m) and 690
  triples (k, m, e). X_P(ζ_e) ≠ 0 for every T with these sizes, whatever
  e(T) is;
- **two types**, gcd(k_1, k_2) > 1, k_1 + k_2 ≤ 10, m_i ≤ 3: 81 cases and
  207 bad e. Again no root y ≥ 1.

This covers far more posets than the 6 classes above. Necessity of (a) in
general remains **OPEN**.

## 4. The G(r, 1, k) version and [RSW] Thm 8.2

**The citation, checked in the published paper.** [RSW] = V. Reiner,
D. Stanton, D. White, *The cyclic sieving phenomenon*, J. Combin. Theory
Ser. A 108 (2004) 17–50. §8 is titled "Springer's theorem on regular
elements". On p. 37:

> **Theorem 8.2.** Let c be a regular element of order n in a finite
> reflection group W. Let C = ⟨c⟩, and let W′ be any subgroup of W. Let
> A^{W′} be the W′-invariant subalgebra of the coinvariant algebra A. Then
> setting X := W/W′ and X(q) = Hilb(A^{W′}; q), one obtains a triple
> (X, X(q), C) that exhibits the cyclic sieving phenomenon.

The paper defines "finite reflection group" as a subgroup of GL_N(C)
generated by (pseudo-)reflections. It defines "regular" as having an
eigenvector off every reflecting hyperplane. Its proof uses Springer's
Proposition 4.5, through Theorem 8.1. So the number, the hypotheses and the
coset-space form are all as [CSC] says, and complex reflection groups such
as ∏G(r_i, 1, k_i) are covered.

**This makes the regular case a corollary, not only a prediction (F3).**
Cyc(P) is a disjoint union of G-orbits G/G_x. By Molien and
Shephard–Todd–Chevalley, as in Theorem A,

  X_P^G = Σ_orbits Σ_t ⟨Ind_{G_x}^G 1, A_t⟩ q^t = Σ_orbits Hilb(A^{G_x}; q).

Two remarks on this step:
- Replacing V by V* changes nothing, because F(h) = F(h^{−1}).
- A disjoint union of CSPs for the same C is a CSP.

So for every g whose normal form g′ is regular in G, X_P^G sieves ⟨g⟩, by
[RSW] Thm 8.2 applied orbit by orbit. Since g and g′ are conjugate in
Aut(P), they have the same fixed-point data. [Aud] checks this
[springer-nf].

[CSC] tags §4 COMPUTED and CITED, and §9 problem 3 asks for a proof
independent of [RSW]. Nothing in [CSC] presents §4 as proven. The caveats
"(Thm 8.2 as cited by secondary sources; not checked against the paper)"
and "The exact statement number in [RSW] was not checked" can now be
removed.

**Computation [springer].** [Aud] builds G = ∏⟨c_i⟩ ≀ S_{k_i} as a
permutation group. For c_i it takes the cycle product of largest order and
checks that every cycle product is Aut(T_i)-conjugate to a power of c_i. It
computes X^G by summing over **all** h ∈ G. For every h with F(h) ≠ 0 it
asserts that all cycle products are trivial, which [CSC] uses without
comment; the assertion never fired. When every c_i = 1, it uses X^G = X_P.

Regularity is tested exactly, against the hyperplanes x_i = 0 (r ≥ 2) and
x_i = ζ^a x_j. The results, all matching [CSC]:
- the per-n table of [CSC] §4, reproduced exactly (header of this note);
- the eigenvalue order equals o(g) on every regular class;
- for connected P, X^G = (e(P)/r)[r]_q;
- the T^{⊔k} table of [CSC] §5, n ≤ 8, reproduced exactly:

| | free | not free |
|---|---|---|
| regular | 33/33 | 31/31 |
| not regular | 25/49 | 1/1, the (6, 2) in A_8, with F(g^j) = (5040, 0, 0, 48, 0, 0) |
| mixed | 5, all free | — |

## 5. The A_4 obstruction and the candidates

**A_4 by hand.** Cyc(A_4) is the set of 6 cyclic orders of {1, 2, 3, 4}.
- (12) has cycles of different lengths, so F((12)) = 0 by Lemma 1.
- A cyclic order fixed by (12)(34) must read a b g(a) g(b). With a = 1 and
  b ∈ {3, 4} this gives (1 3 2 4) and (1 4 2 3), so F((12)(34)) = 2. This
  also equals Proposition 2: φ(2) · 2 · c_1 = 2.

Both elements have order 2, so X(−1) cannot equal both values.

A single X serves all of Aut(P) only if F is a function of o(g) alone,
because X(ζ_e) must equal F(x) for every x of order e. [Aud] searched all
posets with n ≤ 6 for a failure of this condition. It found 0, 0, 1, 0, 4
posets for n = 2, …, 6, and the single poset at n = 4 is A_4 [obst]. So
"A_4 is the smallest, and the only one at n = 4" **HOLDS**.

**Candidates.** For the 23 rotations σ, using the labelling of each T^{⊔k}
with consecutive copies and the base component containing the label 0,
[Aud] reproduces exactly:
- maj(B_P) 4, shifted 4, inv(B_P) 4, lex-minimal maj 5, block q-cumulant 4;
- naive product 12, pattern product 23.

On the sweep of disconnected P with n ≤ 7 there are 889 classes: 874 free
and 15 non-free, as in [CSC]. [Aud] reproduces exactly:
- fake degree: 15/15 non-free and 290/874 free;
- maj(B_P), plain and shifted: 4/15 non-free and 604/874 free;
- lex-minimal maj: 3/15 and 537/874;
- block q-cumulant: 2/15 and 351/874.

**inv(B_P)** gives 1/15 and 815/874 under [Aud]'s natural labelling (the
lexicographically first linear extension of a canonical form). [CSC] has
3/15 and 814/874. Both maj and inv depend on the labelling, and inv also
depends on the base component. The claim that every candidate fails holds
under both labellings (F4). "Each sieves at most 5" (on σ) and "at most 4"
(non-free) hold.

## 6. Fixes

- **F1** (§3). Replace "249 classes" by "206 distinct classes": 171 with
  n ≤ 7, plus 35 T^{⊔k} with n = 8, since the 43 T^{⊔k} with n ≤ 7 were
  counted twice. State that clause (a) is the sole failing clause in only 6
  of them. The phrase "necessary in all 249 computed cases" (§9 problem 2,
  and the verdict table) should be corrected accordingly.
- **F2** (§3). Add the gcd(k_i) = 1 case of the necessity of (a) as
  PROVEN, and record that the bad e are never prime powers. Optionally cite
  the symbolic check for single type k ≤ 16, |T| ≤ 6, and for two types,
  together with the remark that (★) alone does not force nonvanishing.
- **F3** (§4). [RSW] Thm 8.2 is checked: J. Combin. Theory Ser. A 108
  (2004), p. 37, §8. Drop both "not checked" caveats. The regular case of
  §4 may be tagged "PROVEN given [RSW] Thm 8.2 (CITED)", by the orbit
  decomposition above. §9 problem 3, a citation-free proof, stays open.
- **F4** (§6). State the labelling and the base component used in the
  sweep, and note that the inv(B_P) and maj(B_P) counts depend on them.
  Under another natural labelling inv(B_P) gives 1/15 and 815/874.
- **F5** (§3). Replace "not regular in any reflection subgroup of S_8" by
  "not regular in S_8 (= W = G here)", or define and check the stronger
  claim.
- **F6** (optional, §2). Prop. 2 can be given the self-contained proof of
  §1 above, instead of routing through [LE §4] and [FPM].

## Reproduce

From `compute/` (plain Python 3, no dependencies). It runs in about 18 s
on one core; `--jobs=3` runs the sweeps on three processes.

    python3 audit_cyclic_sieving_cyc.py > output/audit_cyclic_sieving_cyc.txt
    python3 -m unittest test_audit_cyclic_sieving_cyc

The script exits 0 iff every check passes, and it ends with
`[done] 0 failures`. `--nmax=` bounds the sweep (default 7), and `--tkmax=`
bounds |T^{⊔k}| (default 8), and `--jobs=` sets the number of processes
(default 1). The section tags of the output are listed in
the module docstring.
