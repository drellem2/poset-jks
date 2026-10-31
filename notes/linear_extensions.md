# What the poset Lie theory says about linear extensions

This note asks whether the poset Lie theory of [Thm] helps us count linear
extensions, or helps us understand their structure and dynamics. It treats
four questions: cyclic sieving, promotion against rotation classes, counting
identities, and the structure of C[Lin P]/R_P. Every claim is tagged
**PROVEN**, **COMPUTED**, **CONJECTURED**, **CITED** or **OPEN**. The new
PROVEN claims (§§1–5) were audited independently, by re-derivation, before
this note was finalised. §8 records that audit and a second, later one,
[AudLE].

## Verdict

| # | Question | Verdict | Main results |
|---|---|---|---|
| 1 | Cyclic sieving with a q-analogue from the theory | **NO.** Neither H_P nor PLie(P) carries a grading or a cyclic action that yields a q-analogue; we found none (§3.1). One CSP result comes out of its cut structure. | H_P sits in one degree and PLie(P) has no grading (§3.1). Theorem U (**PROVEN**): promotion CSPs are closed under disjoint union, with polynomial [n; m]_q · ∏ X_T(q). Rhoades and RSW positive controls pass. A sweep of all posets with n ≤ 7 and ∂^n = id (**COMPUTED**) shows that the maj polynomial is not a CSP polynomial in general there: it fails on 49 of them. |
| 2 | Rotation classes and promotion | **PARTIAL.** The classes and the promotion orbits are tightly linked. The Lie module does not see promotion. | Lemma P (**PROVEN**): on a disjoint union, promotion rotates the shuffle pattern. Theorem R (**PROVEN**): if ∂_T^{\|T\|} = id on every component T, each cyclic class lies inside one promotion orbit. Proposition O (**PROVEN**): #promotion orbits ≤ e_C(P) for every P. Proposition E (**PROVEN**): orbits equal classes iff P is a chain or an antichain. Proposition D (**PROVEN**): promotion descends to PLie(P) iff P is connected or an antichain. No equivariant bijection exists in general (the counts differ). |
| 3 | New identities, recursions or bounds for e(P), e_C(P) | **NO** for e(P). For e_C(P), every identity reduces to known or elementary facts. | Proposition F (**PROVEN**): e_C(P) = ∏_T e(T) · e_C(⊔_T C_{\|T\|}), so e_C carries no information beyond the e(T) and the component sizes. The Jenča–Sarkoci contraction recursion is, for connected P, the elementary "successor of a minimal element" count. Weisner identities hold (**COMPUTED** on 43,767 pairs) but cost more than counting Lin P. Fixed-class counts and the Burnside orbit count are **PROVEN** and **COMPUTED**; they are not new counts of e(P). |
| 4 | Basis, filtration or grading of C[Lin P]/R_P with combinatorial meaning | **YES** for one multigrading (restriction to components). **NO** for descents, major index, number of blocks and jumps. | Theorem M (**PROVEN**): C[Lin P]/R_P ≅ C[∏_T Lin T] ⊗ Q(m), where Q(m) is the shuffle quotient of the pattern words. B_P is the set of canonical rotation representatives. R_P is homogeneous for des or maj on 0 of 108 disconnected posets with n ≤ 6 (**COMPUTED**). |

**Does this theory help count or understand linear extensions?**
For **counting e(P)**, no. All of the theory's numerical content lives in
e_C(P), and e_C(P) equals e(P) for connected P. For disconnected P it is
determined by the e(T) of the components and their sizes (Proposition F).
The identity μ(OP(P)) = ±e_C(P) and the closed formula give no recursion
that is better than the standard ones. For **structure and dynamics**, the
answer is a modest yes. The objects the theory is built on, cuts, blocks
and rotation classes, give an exact description of promotion on disjoint
unions (Lemma P). That description yields a closure theorem for cyclic
sieving (Theorem U), an inclusion of rotation classes in promotion orbits
(Theorem R), the bound #orbits ≤ e_C(P) (Proposition O), and a canonical
multigrading of the Lie model (Theorem M). These results use only the
combinatorics of cuts. None of them uses the homology H_P or the Lie module
in an essential way. Promotion does not descend to the Lie module except in
the trivial cases (Proposition D). We found no q-analogue coming from H_P or
PLie(P).

Tags: [Thm] = `notes/poset_jks_theorem.tex`; [ME] =
`notes/mu_op_elementary.md`; [Glob] =
`notes/global_module_operations_plethlog.md`; [FPM] =
`notes/fixed_point_mobius_identity.md`; [Nat] =
`notes/natural_isomorphism.md`; [St09] = R. P. Stanley, *Promotion and
evacuation*, Electron. J. Combin. 16(2) (2009) R9; [Rh] = B. Rhoades,
*Cyclic sieving, promotion, and representation theory*, JCTA 117 (2010)
38–76; [RSW] = V. Reiner, D. Stanton, D. White, *The cyclic sieving
phenomenon*, JCTA 108 (2004) 17–50; [JS] = Jenča–Sarkoci, JCTA 122 (2014);
[AudLE] = `notes/audit_linear_extensions.md` (mg-5dbdd), the independent
audit of this note, verdict HOLDS WITH FIXES. [AudLE] verified the
bibliographic details of [St09], [Rh] and [RSW].

## 0. Conventions

P is a poset on [n], and words are written w = w_1 ⋯ w_n with
w ∈ Lin P. We follow [Thm, §1]. A *cut* of w is a k ∈ {0, …, n−1} such that
{w_1, …, w_k} is a union of components. The cyclic class of w is
{wγ^k : k a cut} ([Thm] Lemma `lem:rot`: wγ^k ∈ Lin P iff k is a cut).
Blocks, B_P (the words whose first block contains the base component P_1),
R_P and PLie(P) = span{we_ζ} are as in [Thm, §§1, 6].

*Promotion.* ∂ = τ_{n−1} ∘ ⋯ ∘ τ_1, with τ_1 applied first. Here τ_i swaps
the letters in positions i and i+1 when they are incomparable. This is the
usual promotion of the labelling f = w^{-1}. It agrees with the
jeu-de-taquin description of [St09] (**COMPUTED** on all 405 posets with
n ≤ 6, `[jdt]`). On the antichain, ∂(w) = wγ, the rotation.

*Pattern coordinates.* Let T_1, …, T_k be the components, m_i = |T_i|, and
m = (m_1, …, m_k). The map

  w ↦ (p(w); w|_{T_1}, …, w|_{T_k}),   p(w) = (c(w_1), …, c(w_n)), c(x) = index of the component of x,

is a bijection Lin P → Pat(m) × ∏_i Lin T_i. Here Pat(m) is the set of words
with m_i letters i. It is a bijection because there are no relations between
components. A cut of w depends only on p(w). Rotation at a cut rotates p and
leaves every restriction w|_T unchanged.

## 1. Promotion on disjoint unions

**Lemma P (PROVEN; COMPUTED `[lemmaP]` on all 503 disconnected posets with
n ≤ 7).** Let A be a union of components and B = [n] ∖ A, both nonempty.
Record w by its two-letter pattern in {A, B}^n together with w|_A and w|_B.
Then ∂(w) has pattern rot_1(p) = p_2 ⋯ p_n p_1. If w_1 ∈ A, then
∂(w)|_A = ∂_A(w|_A) and ∂(w)|_B = w|_B. If w_1 ∈ B, the same holds with A
and B exchanged.

*Proof.* Run the toggles in order. Just before τ_i, position i holds a
"carried" letter c, and position i+1 holds w_{i+1}. At the start, c = w_1.
If c ∥ w_{i+1}, then τ_i swaps them: w_{i+1} moves to position i, and c is
carried on. Otherwise c < w_{i+1}. Indeed, the partially toggled word
τ_{i−1} ∘ ⋯ ∘ τ_1(w) is a linear extension, because τ_1, …, τ_{i−1} only
swapped incomparable adjacent letters, and c precedes w_{i+1} in it. Then nothing moves, c stays in position i, and w_{i+1} becomes
the carried letter. The carried letter changes only to a letter comparable
to it, so it stays in the component of w_1. Suppose w_1 ∈ A. Every B-letter
is incomparable to the carried letter, so each one moves one position to
the left. The carried letter finishes in position n. Now delete the
B-letters. The process on the A-letters is then exactly the toggle process
of ∂_A on w|_A, since comparabilities inside A are those of P|_A. So
∂(w)|_A = ∂_A(w|_A). The positions occupied by A move from S to
(S ∖ {1}) − 1 ∪ {n}, and the B-positions move from S^c to S^c − 1. That is
the rotation of the pattern. The case w_1 ∈ B is symmetric. ∎

The special case of two disjoint chains, where promotion is rotation of a
binary word, is Stanley's [St09]. A quick search found no statement of the
general lemma, which may be folklore.

**Corollary P1 (PROVEN).** In pattern coordinates, ∂^d acts as
(p; x_1, …, x_k) ↦ (rot_d p; ∂_{T_1}^{a_1} x_1, …, ∂_{T_k}^{a_k} x_k),
where a_i = #{j ≤ d : p_j = i}. In particular ∂^n = ∏_i ∂_{T_i}^{m_i},
acting coordinatewise.

*Proof.* Apply Lemma P with A = T_{p_1} at each step. ∎

**Corollary P2 (PROVEN; COMPUTED `[corP2]`).** Let k be a cut of w, and put
A = {w_1, …, w_k}. Then ∂^k(w) = w_{k+1} ⋯ w_n · ∂_A^{|A|}(w_1 ⋯ w_k). That
is, ∂^k(w) is the rotation wγ^k with its A-part replaced by ∂_A^{|A|} of it.

*Proof.* Use the two-letter form of P1 for A ⊔ B. The first k pattern
letters are all A. ∎

## 2. Question 2: promotion against rotation classes

**Theorem R (PROVEN; COMPUTED on all 102 disconnected posets with n ≤ 7
that satisfy the hypothesis).** Suppose ∂_T^{|T|} = id on Lin T for every
component T. Then every cyclic class lies inside a single promotion orbit.

*Proof.* Let k be a cut of w, and let A be the corresponding prefix. By P1
applied to the poset A, ∂_A^{|A|} = ∏_{T ⊆ A} ∂_T^{|T|} = id. By P2,
∂^k(w) = wγ^k. ∎

The hypothesis holds for chains, antichains, rectangles [Rh], and every
poset whose promotion has order dividing its size. It cannot be dropped:
refinement fails on 6 of the 401 disconnected posets with n ≤ 7 that violate
it (**COMPUTED**). A smallest example is V ⊔ V, with V = {0 < 1, 0 < 2},
where ∂_V has order 2 ∤ 3. V ⊔ Λ and Λ ⊔ Λ, with Λ = V^op, are also
smallest (n = 6) [AudLE §2]. When the hypothesis holds, each orbit is a union
of classes.

**Proposition O (PROVEN for every finite P; COMPUTED `[propO]` on all 2450
posets with n ≤ 7).** Every promotion orbit contains a word whose first
letter lies in P_1. Hence #(∂-orbits on Lin P) ≤ |B_P| = e_C(P).

*Proof.* If P is connected, e_C = e and there is nothing to prove.
Otherwise, by Lemma P the pattern rotates by one place at each step. Within
n steps, the first letter therefore comes from P_1. A word whose first
letter lies in P_1 has first block containing P_1, so it lies in B_P. The
orbits are disjoint, and |B_P| = e_C(P) by [Thm] Thm `thm:S`(a). ∎

**Proposition E (PROVEN; COMPUTED: exactly the chains and antichains with
n ≤ 7, `[orbit=class]`).** The promotion orbits coincide with the cyclic
classes iff P is a chain or an antichain.

*Proof.*
- Antichain: ∂ = γ, and every k is a cut.
- Connected P: the classes are singletons, so the condition is ∂ = id.
  Suppose ∂(w) = w. Position 1 of ∂(w) is w_2 if w_1 ∥ w_2, so w_1 < w_2.
  The carried letter is then w_2, and the same argument at each position
  gives w_1 < w_2 < ⋯ < w_n. If this holds for one w, then P is a chain.
- Disconnected P that is not an antichain: take a component A with
  |A| = a ≥ 2, put B = [n] ∖ A with |B| = b ≥ 1, and let w = x·y with
  x ∈ Lin A and y ∈ Lin B. A prefix of length 0 < k < a is not a cut. So
  every word of the class other than w is y[j:] x y[:j] with j < b, and it
  begins with a B-letter. The word w itself ends with a B-letter. By
  Lemma P, ∂(w) has pattern A^{a−1}B^bA, so it begins and ends with
  A-letters. Hence ∂(w) is in the orbit of w but not in its class. ∎

**Proposition D (PROVEN; COMPUTED: among disconnected posets with n ≤ 7,
exactly the antichains, `[descend-PLie]`).** Let K_P be the kernel of
C[Lin P] → PLie(P), w ↦ we_ζ, so that PLie(P) = C[Lin P]/K_P. Then
∂(K_P) ⊆ K_P iff P is connected or an antichain.

*Proof.* Since wγ^k e_ζ = ζ^k we_ζ, K_P is spanned by v = wγ^k − ζ^k w for
k a cut of w. These vectors span it because they cut each class down to one
dimension, and dim K_P = e − e_C. Now φ(∂v) = ∂(wγ^k)e_ζ − ζ^k ∂(w)e_ζ.
Each term is a nonzero vector supported on one coset. So φ(∂v) = 0 iff
∂(wγ^k) = ∂(w)γ^j with ζ^j = ζ^k, i.e. j ≡ k. Hence ∂ descends iff ∂
commutes with every cut rotation.
- Connected P: K_P = 0.
- Antichain: ∂ is right multiplication by γ, which commutes with γ^k.
- Otherwise take A, B as in Proposition E and w = y·x with y ∈ Lin B first,
  and put k = b. Then wγ^b = xy ∈ Lin P, so ∂(wγ^b) ∈ Lin P. But ∂(w) has
  pattern B^{b−1}A^aB (Lemma P, with B in the role of A). Its length-b
  prefix contains exactly one of the a ≥ 2 letters of A, so b is not a cut
  of ∂(w), and ∂(w)γ^b ∉ Lin P. ∎

So **the Lie module does not see promotion.** On connected P it is the free
module C[Lin P] (Cor. `cor:connected`), on which promotion acts but carries
no Lie information. On disconnected non-antichain P, promotion does not act.

*The other model.* Promotion preserves R_P, and so acts on
C[Lin P]/R_P, on 9 of the 108 disconnected posets with n ≤ 6. These 9 are
the two-component posets whose components are both chains
(**COMPUTED** `[descend-R]`); the 2-antichain C_1 ⊔ C_1 is one of them. The
identification C[Lin P]/R_P ≅ H_P ⊗ sgn ([Thm] Thm `thm:S`(d)) needs
n ≥ 3, so for C_1 ⊔ C_1 only the C[Lin P]/R_P side makes sense. The "if"
direction is **PROVEN**: for two chains, R_P = C · Σ_{w ∈ Lin P} w, and ∂
permutes Lin P. The "only if" direction is **CONJECTURED** beyond n ≤ 6.
Note that ∂ = γ does *not* preserve Sh_3 = R_{A_3}.

*Equivariant bijection?* None exists in general, because the counts differ:

| P | e | e_C | #∂-orbits (sizes) | refinement |
|---|---|---|---|---|
| antichain A_3 | 6 | 2 | 2 (3, 3) | yes (equal) |
| C_2 ⊔ C_1 | 3 | 2 | 1 (3) | yes |
| C_2 ⊔ C_2 | 6 | 5 | 2 (2, 4) | yes |
| C_2 ⊔ C_2 ⊔ C_2 | 90 | 74 | 16 | yes |
| (2×2) ⊔ C_1 | 10 | 8 | 2 (5, 5) | yes |
| V ⊔ V | 80 | 76 | 8 | **no** |
| 2×3 (connected) | 5 | 5 | 2 (2, 3) | trivially |

## 3. Question 1: cyclic sieving

### 3.1 No q-analogue comes from the theory

These are structural facts (**PROVEN**):
- H_P is a single reduced homology group, in degree n−3 ([Thm] input (A)).
  It carries no grading.
- PLie(P) = span{we_ζ} ⊂ C[S_n] is homogeneous, and the theory has no
  q-deformation of it.
- The only cyclic group in the theory is C_n acting by position rotation.
  It acts on Lin P only at cuts, and freely on Lin(P) · C_n. The
  decomposition C[Lin(P)C_n] = ⊕_j PLie_j(P), with PLie_j = span{we_{ζ^j}}
  and every dim PLie_j = e_C(P), is a free C_n-module. Any CSP built from it
  is the trivial CSP of a free action.
- The Aut(P)-character Σ_{gC=C} ζ^{r_g(C)} = μ(o)·S(g), with
  S(g) = Σ_{x ∈ F(P,g)} e_C(P|_{B_0(x)}), is a character of the
  automorphism group, not of a cyclic action on Lin P.
- For connected P, which includes the rectangles and staircases with known
  promotion CSPs, PLie(P) ≅ C[Lin P] is free over Aut(P). It contains no
  information about promotion (Proposition D).

The fixed-point form of the closed formula is a sieving-type statement for
Aut(P) acting on classes, refined by rotation. The number of g-fixed classes
with rotation r is S(g) when gcd(n, r) = n/o(g), and 0 otherwise
([FPM, Prop. 6], restated in [Thm] Remark `rem:proofII`). Summing over r
gives #{C : gC = C} = φ(o(g))·S(g). This is **PROVEN** there and
**COMPUTED** here on 17,004 pairs (P, g) with n ≤ 7, `[fixed]`. It is a
count of fixed classes, not a CSP for a cyclic action on Lin P.

### 3.2 A CSP result from the cut structure

**Theorem U (PROVEN given [RSW] Prop. 4.4; COMPUTED on all 45 qualifying
disconnected posets with n ≤ 7, `[union]`).** Let P have components
T_1, …, T_k with |T_i| = m_i. Suppose each (Lin T_i, C_{m_i} = ⟨∂_{T_i}⟩,
X_i(q)) exhibits the CSP. Then (Lin P, C_n = ⟨∂⟩, X(q)) exhibits the CSP,
where

  X(q) = [n; m_1, …, m_k]_q · ∏_i X_i(q).

If every X_i is the shifted maj polynomial q^{−min maj} Σ_{u ∈ Lin T_i} q^{maj(u)},
then so is X. This is MacMahon–Stanley for disjoint unions, checked
`[union maj factorisation]`.

*Proof.* First, ∂^n = id on Lin P, so C_n = ⟨∂⟩ acts: by P1,
∂^n = ∏_i ∂_{T_i}^{m_i}, and each factor is the identity because
C_{m_i} = ⟨∂_{T_i}⟩ acts on Lin T_i. By P1, ∂^d fixes (p; x) iff rot_d p = p and ∂_{T_i}^{a_i} x_i = x_i
for all i. If p has period dividing e = gcd(d, n), then a_i = d m_i / n,
which is an integer when such p exist. So

  |Fix ∂^d| = #{p ∈ Pat(m) : rot_d p = p} · ∏_i |Fix ∂_{T_i}^{d m_i / n}|.

The first factor is [n; m]_q at q = ω_n^d ([RSW] Prop. 4.4 with a = 1,
equivalently eq. (4.5); **CITED**). When it is
nonzero, n/e divides every m_i, and ω_{m_i}^{d m_i/n} = ω_n^d. So the second
factor is ∏ X_i(ω_n^d). When the first factor is zero, the identity holds
trivially. ∎

Positive controls (**COMPUTED**, `[ctl-rhoades]`, `[ctl-rsw]`):
- Rhoades's CSP [Rh] for SYT of the rectangles 2×2, 2×3, 2×4, 3×3, 2×5, 3×4
  and 2×6, with the q-hook formula, which equals the shifted maj polynomial.
  The negative control q·(q-hook) is rejected each time.
- The RSW q-binomial CSP for Lin(C_a ⊔ C_b), the binary words, for seven
  (a, b).

So Theorem U gives, for example, a CSP for any disjoint union of rectangles.

*Sweep (COMPUTED, `[sweep]`).* We tested every unlabeled P with n ≤ 7 for
which ∂^n = id, using X = shifted maj polynomial:

| n | posets | ∂ order ∤ n | CSP holds | CSP fails |
|---|---|---|---|---|
| 3 | 5 | 2 | 3 | 0 |
| 4 | 16 | 7 | 6 | 3 |
| 5 | 63 | 52 | 11 | 0 |
| 6 | 318 | 258 | 18 | 42 |
| 7 | 2045 | 1971 | 70 | 4 |

The smallest failures are A_2 ⊕ A_2, the chain-then-V poset, and V^op with a
top added (n = 4). So "∂^n = id" does not imply a maj-CSP.

*Staircases (COMPUTED only).* Promotion on SYT of shape (3,2,1) has order 12
(n = 6), and on (4,3,2,1) order 20 (n = 10). On the shifted staircases with
3, 6 and 10 cells it has orders 1, 2 and 10. So a C_n-CSP is impossible for
the unshifted staircase. We did not test the staircase CSPs of the
literature.

## 4. Question 3: counting

**Proposition F (PROVEN; COMPUTED on all 2450 posets with n ≤ 7,
`[cumulant]`).**

  e_C(P) = ∏_i e(T_i) · e_C(C_{m_1} ⊔ ⋯ ⊔ C_{m_k}).

*Proof.* In pattern coordinates (§0), cut rotation acts on p alone and
leaves the restrictions fixed. So Cyc(P) ≅ Cyc(⊔ C_{m_i}) × ∏ Lin T_i. ∎

This also re-derives [Thm] Cor. `cor:eC` (the component cumulant formula)
in a second way. [Thm] marks that corollary as not independently audited;
the factorisation gives an independent derivation, and the cumulant formula
is now **COMPUTED** through n = 7 (2450 posets; [Thm] had n ≤ 6).

Consequences:
- For connected P, e_C = e (Fact 0 of [ME]). μ(OP(P)) = (−1)^{n−1} e(P) is
  then Jenča–Sarkoci's theorem read at the level of Möbius numbers.
- For disconnected P, e_C contains nothing beyond the e(T_i) and the sizes.
- Elementary bounds: e/k ≤ e_C ≤ e, since a class meets Lin P in at most k
  words (checked).

**Recursions (PROVEN in [ME]; COMPUTED here).**
- The Jenča–Sarkoci recursion e_C(P) = Σ_b e_C(P/π_ab), for a minimal and
  b ∥ a or b ⋗ a, holds for every minimal a: 5,928 pairs (P, a) with n ≤ 7,
  `[JS-rec]`. Dropping the covers b ⋗ a is rejected on every pair that has
  such a cover.
- For connected P it reads e(P) = Σ_b e(P/{a, b}). This is the count of
  linear extensions by the successor of a: merging the adjacent letters a, b
  gives a bijection. It is elementary, and no better than the standard
  e(P) = Σ_{a minimal} e(P − a), which we checked as a control (`[std-rec]`).

**Weisner family (PROVEN from [ME] Theorem A + Weisner; COMPUTED).** For
every c ∈ OP(P) with c ≠ 1̂ and n ≥ 2,

  Σ_{x ∈ OP(P), x ∧ c = 0̂} (−1)^{|x|} e_C(Q_x) = 0.

We checked 43,767 pairs (P, c): all c for n ≤ 6, all c at n = 7 when
|OP| ≤ 120, otherwise c = 0̂. The control c = 1̂ is rejected 430 times. For
c = 0̂ this is the defining recursion of μ, so it determines e_C
recursively. The cost is a sum over OP(P), which is larger than Lin P.

Two interpretations are open:
- A sign-reversing-involution proof of the c = 0̂ identity would be a third
  homology-free proof of Theorem A. **OPEN.**
- For c = {D, P ∖ D}, with D a down-set, the x are the order-preserving
  partial matchings between D and its complement. The identity becomes
  Σ_M (−1)^{|M|} e_C(P/M) = 0. **OPEN** as a statement with independent
  meaning.

**Fixed classes and Burnside (PROVEN; COMPUTED on 17,004 pairs (P, g) and
2450 posets, `[fixed]`, `[burnside]`).** Two consequences:
- The number of Aut(P)-orbits on Cyc(P) is
  (1/|Aut P|) Σ_g φ(o(g)) S(g).
- The multiplicity of the trivial character in PLie(P),
  (1/|Aut P|) Σ_g μ(o(g)) S(g), is a nonnegative integer.

Both follow from the closed formula. They count symmetry classes of
cyclic classes, not e(P). The integrality also follows from elementary orbit
counting on the ⟨g⟩ × C_n-set Lin(P)C_n.

**Ordinal sums, series-parallel posets.** P ⊕ Q is connected, so the theory
returns e(P)e(Q). Disjoint unions are covered by Proposition F. So on
series-parallel posets the theory reproduces the usual recursions and adds
nothing.

## 5. Question 4: structure of C[Lin P]/R_P

**Theorem M (PROVEN; COMPUTED: every graded piece has the predicted
dimension on all 108 disconnected posets with n ≤ 6, `[pieces]`).** Grade
C[Lin P] by the restriction tuple x = (w|_{T_1}, …, w|_{T_k}). Then R_P is
homogeneous, and every piece of the quotient is the same space:

  C[Lin P]/R_P ≅ C[∏_i Lin T_i] ⊗ Q(m),   Q(m) = C[Pat(m)] / span{u ⧢ v},

where u, v run over the pattern words on complementary nonempty sets of
letters. Each letter keeps all its copies on one side. Aut(P) acts through
its action on components: it permutes isomorphic components and acts by
Aut(T) inside each one. The action on C[∏_i Lin T_i] ⊗ Q(m) is diagonal:
g relabels the restriction tuple and permutes the pattern letters by the
permutation it induces on components. It is not a product of separate
actions on the two factors. dim Q(m) = e_C(⊔ C_{m_i}). For m = (1^k), Q is
C[S_k]/Sh_k ≅ Lie_k.

*Proof.* A generator s ⧢ t of R_P, with S a union of components,
s ∈ Lin P|_S and t ∈ Lin P|_{S^c}, has every word with the same
restriction tuple. Its interleavings are distinct words, because u and v
use disjoint letter sets. In pattern coordinates it becomes
(pattern(s) ⧢ pattern(t)) ⊗ e_x. As s and t range over the linear
extensions with restriction tuple x, pattern(s) and pattern(t) range over
all patterns of the S-content and the S^c-content. For the dimension, take
P = ⊔ C_{m_i}: then Lin P = Pat(m), R_P is exactly the span defining Q(m), and
[Thm] Thm `thm:S`(b) gives dim C[Lin P]/R_P = e_C(P). ∎

For k copies of a chain C_t, this makes PLie(C_t^{⊔k}) ≅ Q(t^k) an S_k-module.
It is a multiset analogue of Lie_k, with dimension e_C(C_t^{⊔k}), which is
74 for t = 2, k = 3.

*Other statistics (COMPUTED, `[homog]`).* R_P is homogeneous for a
statistic f iff Σ_v rank(Lie_n restricted to {w : f(w) = v}) = e_C(P). We
used Ree's theorem, Sh_n = Lie_n^⊥ (**CITED**). The positive control,
rank = e_C on all 108 posets, checks it against [Thm] Thm `thm:S`(b). Of the
108 disconnected posets with n ≤ 6:

| statistic | posets with R_P homogeneous |
|---|---|
| restriction tuple | 108 |
| number of blocks | 5 (the antichains, where it is constant) |
| jumps (adjacent incomparable pairs) | 5 (the antichains, where it is constant) |
| des (one natural labelling per poset) | 0 |
| maj (one natural labelling per poset) | 0 |
| first letter | 0 |
| a random 2-colouring (control) | 1 |

Des and maj were tested for one natural labelling per poset; the des and
maj of an individual word depend on which natural labelling is chosen.
[AudLE §8] tested every natural labelling of every disconnected poset with
n ≤ 5 (603 pairs) and found R_P homogeneous on none. So there is **no
grading by descents or major index**. The only natural
grading found is Theorem M.

*Basis.* B_P is the set of canonical rotation representatives: the unique
rotation of each class whose first block contains P_1 ([Thm] Thm `thm:S`(a)).
It is the poset analogue of the multilinear Lyndon-type basis of words
starting with the letter 1. Under Theorem M it splits as
∏ Lin T_i × B_{⊔ C_{m_i}}. We found no filtration with a further
combinatorial meaning.

## 6. Open problems

1. Does ∂(R_P) ⊆ R_P hold only for n ≤ 2, for connected P and for two chains
   (§2)? **CONJECTURED**; computed for n ≤ 6.
2. Is there a q-analogue of e_C(P), for example a polynomial in q with
   X(1) = e_C(P), that sieves Aut(P) acting on Cyc(P), at least for
   P = T^{⊔k}? **OPEN.** Nothing in the theory points to one.
3. Find a combinatorial proof of the Weisner family (§4). **OPEN.**
4. Is Lemma P in the literature beyond [St09]'s two-chain case? Is
   Theorem U? **OPEN** (one quick search).

## 7. Corrections and remarks on existing notes

- We found no errors in [Thm], [ME], [Glob] or [Nat].
- [Thm] Cor. `cor:eC` ("not independently audited") now has a second
  derivation, via Proposition F, and is computed through n = 7.

## 8. Audit

The new PROVEN claims are Lemma P, P1, P2, Theorem R, Propositions O, E,
D and F, Theorem U, Theorem M and the two-chain case of §2. They were
audited independently by a reader who saw only the statements and
conventions, not the proofs above. The reader re-proved each claim and ran
separate code (exact linear algebra over GF(p)).

**Verdict: every claim HOLDS, with no counterexample.**

- **Where the audit was checked.**
  - All 405 posets with n ≤ 6: Lemma P on 87,066 (word, union) pairs, P1,
    P2, O over 555 choices of P_1, and E, D and F.
  - D: tested directly as ker φ ⊆ ker φ∂.
  - Theorem U: 68 unions with n ≤ 8, including rectangle components with
    the q-hook polynomial. The 2×3 Rhoades control passed, and an altered
    polynomial was rejected.
  - dim Q(m) = e_C(chains): 53 partitions with n ≤ 8, for example
    2118 = 2118 for m = (2,2,2,2).
- **The one gap.** The audit left one gap: the dimension statement in
  Theorem M, which the reader confirmed only numerically. It is closed by
  the last sentence of the proof of Theorem M, which applies Thm `thm:S`(b)
  to the disjoint union of chains.
- **A further finding.** For three or more chains, for example m = (2,1,1),
  ∂ does not preserve R_P. This agrees with the conjecture in §6.1.
- **Second audit.** [AudLE] re-derived every PROVEN claim and recomputed
  them with its own code (n ≤ 7, and n ≤ 6 for the R_P linear algebra).
  Verdict HOLDS WITH FIXES. Its fixes F1–F7 are wording, scope and
  citation, none of which changes a result, and they are applied here:
  F1 (Lemma P proof), F2 (Theorem R), F3 (§2, the other model), F4
  (Theorem U: [RSW] Prop. 4.4, and ∂^n = id from P1), F5 (Theorem M, the
  diagonal action), F6 (verdict table scope) and F7 (the homogeneity
  table's labelling).

## Reproduce

From `compute/` (plain Python 3, no dependencies; about 40 s on one core):

    python3 linear_extensions.py --nmax 7 --rnmax 6 > output/linear_extensions.txt
    python3 -m unittest test_linear_extensions

The script exits with status 0 iff every check holds and every positive
control behaves as intended. The archived output is
`compute/output/linear_extensions.txt`. The bracketed tags in this note,
such as `[union]` and `[propO]`, are the line labels in that output.
Options:
- `--sections csp,promo,count,burnside,struct` runs a subset.
- `--wnmax` bounds the Weisner sweep.
- `--rnmax` bounds the R_P linear algebra, whose cost grows like (n−1)! · e.
