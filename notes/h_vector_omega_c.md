# The h-vector of the cyclic order polynomial is the cyclic-descent distribution

Question ([LS] §2.2, §7 item 1(ii)): the cyclic order polynomial Ω_C(P, m)
has an h-vector h_C(P). Its entries sum to e_C(P), and they are nonnegative
on all 2450 posets with n ≤ 7. Prove nonnegativity by finding a statistic
on e_C(P) objects that realises h_C, the way des on Lin P realises the
order polynomial.

Tags: **PROVEN** means proved here; **COMPUTED** means checked by
`compute/h_vector_omega_c.py`, with bracketed line labels from
`compute/output/h_vector_omega_c.txt`. **OPEN** means not settled.

Sources: [LS] = `notes/linext_statistics.md`; [ME] = `notes/mu_op_elementary.md`;
[AudME] = `notes/audit_mu_op_elementary.md`; [LE] = `notes/linear_extensions.md`;
EC1 = Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed.

## Verdict

**Lead 1 (cyclic descents) works.** Choose a *separated* natural labelling:
every minimal element of a non-singleton component gets a smaller label
than every maximal element of a non-singleton component. Such labellings
always exist. Then, for n ≥ 2,

  Ω_C(P, m) = Σ_{κ ∈ Cyc(P)} C(m + n − cdes(κ), n),
  so h_C(P)_j = #{κ ∈ Cyc(P) : cdes(κ) = j + 1}.

Here Cyc(P) is the set of cyclic classes of Lin P, and cdes is the number
of cyclic descents of the cyclic word. cdes is constant on a class.

Two consequences:
- **h_C(P) ≥ 0 is PROVEN** (Theorem H).
- The distribution of cdes on Cyc(P) is the same for every separated
  labelling, because h_C(P) is defined without a labelling.

| # | Statement | Status |
|---|---|---|
| H | Separated labelling, n ≥ 2: h_C(P)_j = #{κ ∈ Cyc(P) : cdes κ = j + 1}. Equivalently, the statistic is min_{w∈κ} des(w) | **PROVEN** (§2); COMPUTED on all 2450 posets n ≤ 7 against the Möbius definition `[sep-cdes]`, `[sep-mindes]`, and on every separated labelling for n ≤ 6 (4443 labelled posets) `[sep-all]` |
| L1 | Per-class lemma: if a class is not all-ascent, its rotations contribute exactly C(m+n−1−min des, n) to the descent expansion of Ω_C, for every component T | **PROVEN** (§2.2); COMPUTED on 2 457 467 (class, T, m) cases `[perclass]` |
| H′ | Any natural labelling with no all-ascent class: min-des on Cyc(P) realises h_C | **PROVEN** (same proof); COMPUTED on 5182 labelled posets n ≤ 6 `[mindes-all]` |
| H″ | Converse of H′: an all-ascent class makes min-des fail | COMPUTED on all 48 such labelled posets n ≤ 6 `[ctl-mindes-asc]`; **OPEN** in general |
| B | Under the labelling λ_0 (§3), des on B_P realises h_C. Here B_P is the set of rotations whose last piece contains the component of label n − 1; the first-piece convention (piece of label 0 first) also works | **PROVEN** (§3); COMPUTED on 2450 posets `[lambda0-BP]` |
| ✗ | cdes − 1 for an arbitrary natural labelling | **FALSE**: refuted on 787 of 5230 labelled posets n ≤ 6 `[ctl-cdes-any]` (positive control) |
| ✗ | des on B_P (last or first convention) for an arbitrary separated labelling | **FALSE**: refuted on 346 of 4443 `[ctl-BP-last]`, `[ctl-BP-first]` |
| ✗ | des on all of Lin P | **FALSE** on exactly the 503 disconnected posets `[ctl-lin]` |

Lead 2 is answered by row B. The B_P convention is not wrong in itself.
Its failures in [LS] §2.2 come from the labelling: the representative must
be broken at a descent junction (§3). Lead 3, a shelling, was not needed
for nonnegativity. Whether Theorem H comes from a shelling of the upper
intervals of OP(P) is **OPEN**.

**Dependence.** The proof uses two inputs:
- Lemma U and Theorem A of [ME], both audited in [AudME];
- Theorem Ω of [LS] §2.1 (PROVEN, audit pending).

So that Theorem H does not rest on that audit, §1 reproves the part of
Theorem Ω that we use, starting from the Möbius definition. All
computations compute Ω_C from the Möbius sum, not from Theorem Ω.

## 0. Conventions

P is a poset on n ≥ 1 points with a natural labelling by 0, …, n − 1
(x <_P y ⇒ x < y). OP(P) is the lattice of order-preserving set partitions
under refinement, and Q_π is the quotient poset ([ME] §0). The definition is

  Ω_C(P, m) := Σ_{π ∈ OP(P)} (−1)^{|π|−1} μ_{OP(P)}(π, 1̂) C(m, |π|),

and h_C(P) is defined by Ω_C(P, m) = Σ_j h_j C(m + n − 1 − j, n). It exists
because Ω_C has degree ≤ n and Ω_C(P, 0) = 0. Equivalently,
Σ_m Ω_C(P, m) x^m = Σ_j h_j x^{j+1}/(1 − x)^{n+1}.

*Words.* For w ∈ Lin P, a **cut** is a p ∈ [1, n − 1] such that
{w_1, …, w_p} is a union of components. The cuts split w into **pieces**
w = c_1 c_2 ⋯ c_s, with s = 1 + #cuts. Each piece is nonempty, its letter
set is a union of components, and no proper prefix of a piece is a union of
components. The **cyclic class** κ(w) is the set of rotations of w at its
cuts ([LE] §0). Equivalently, κ(w) = wC_n ∩ Lin P, the C_n-orbit of w
intersected with Lin P (Fact 0 of [ME]).

*The rotations of a class.* Let p be a cut and write w = c_1 ⋯ c_i | c_{i+1} ⋯ c_s.
The rotation c_{i+1} ⋯ c_s c_1 ⋯ c_i has the same pieces, rotated
cyclically. To see this, suppose a prefix of the rotation ended strictly
inside some piece c_j. Removing whole pieces from a union of components
leaves a union of components, so a proper prefix of c_j would be a union
of components. That contradicts the definition of a piece. Since the
pieces have disjoint nonempty letter sets, the s rotations are distinct,
and |κ| = s.

*Junction statistics.* Index the pieces of a class cyclically, c_1, …, c_s.
For s ≥ 2, junction J_k runs from c_k to c_{k+1} (indices mod s), and
δ_k = [last(c_k) > first(c_{k+1})]. Put

  d(κ) = Σ_k des(c_k),  jd(κ) = Σ_{k=1}^{s} δ_k  (jd = 0 if s = 1).

Both depend only on κ. The rotation broken at junction J_i has
des = d + jd − δ_i. For s ≥ 2, every w ∈ κ has

  cdes(w) := des(w) + [w_n > w_1] = d + jd,

since the wrap-around pair (w_n, w_1) is the broken junction. So cdes is a
class statistic. A class is **all-ascent** if s ≥ 2 and jd = 0.

## 1. The descent expansion, from the definition

This section reproves Theorem Ω of [LS] and its Corollary Ω-des from the
definition, using only [ME] Lemma U and Theorem A. Readers who accept
Theorem Ω can skip to Proposition D.

**Step 1.** By [ME] Lemma U, [π, 1̂] ≅ OP(Q_π). By [ME] Theorem A applied to
Q_π, (−1)^{|π|−1} μ(π, 1̂) = e_C(Q_π). Hence
Ω_C(P, m) = Σ_σ e_C(Q_σ) C(m, |σ|). The sign is checked on every π of every
poset with n ≤ 7 `[mu-sign]`.

**Step 2 (triples).** Order-preserving maps f : P → [m] are in bijection
with triples (σ, u, S):
- σ ∈ OP(P) is the partition of P into nonempty fibres of f;
- S ⊆ [m] is the image, with |S| = |σ|;
- u = (F_1, …, F_k) ∈ Lin Q_σ lists the fibres in increasing value.

**Step 3 (cuts).** For 0 < j < k, F_1 ∪ ⋯ ∪ F_j is a union of components
of Q_σ iff it is a union of components of P, since a P-relation across the
boundary is a Q_σ-relation and conversely. Each component T of P lies in a
single component of Q_σ, because the relations inside T connect its blocks.
So T lies in a single piece of u. The pieces of u correspond to the
**clumps** of f: the differences of consecutive nonempty upper level sets
f^{−1}([v, m]) that are unions of components.

**Step 4 (one rotation per class).** Fix a component T. By §0, applied to
Q_σ, the class of u has one member for each piece, and exactly one member
has the piece containing T last. Rotating u while keeping S fixed rotates
the clumps of f. So e_C(Q_σ) C(m, |σ|) is the number of f with fibre
partition σ whose top clump contains T. Summing over σ:

  Ω_C(P, m) = #{f : every nonempty upper level set of f that is a union of components contains T}.

This is the statement of Theorem Ω.

**Step 5 (Stanley's word).** Each order-preserving f has a unique
w ∈ Lin P such that f is weakly increasing along w and strictly increasing
at every descent of w (sort by (f(x), x); EC1 Lemma 3.15.3). A nonempty
upper level set is the suffix after a position p (or all of P, for p = 0)
with f(w_p) < f(w_{p+1}). It is a union of components iff p is a cut. It
misses T iff T ⊆ {w_1, …, w_p}. Put

  C_T(w) = {cuts p : T ⊆ {w_1, …, w_p}}, c = |C_T(w)|.

Then the condition of Step 4 says that f(w_p) = f(w_{p+1}) for every
p ∈ C_T(w).

**Proposition D (PROVEN; this is Corollary Ω-des of [LS]).** For every
natural labelling and every component T,

  Ω_C(P, m) = Σ_{w ∈ Lin P} N_T(w, m),
  N_T(w, m) = [C_T(w) ∩ Des(w) = ∅] · C(m + n − 1 − des(w) − c, n − c).

*Proof.* Count, for each w, the weakly increasing sequences that are strict
at Des(w) and equal at C_T(w). There are none if the two sets meet.
Otherwise, merge the c forced equalities. That leaves n − c positions, with
des(w) of the n − c − 1 gaps strict, giving C(m + (n − c) − 1 − des(w), n − c)
sequences. ∎

## 2. Theorem H

### 2.1 Statement

**Theorem H (PROVEN; COMPUTED `[sep-cdes]`, `[sep-mindes]`, `[sep-all]`).**
Let n ≥ 2, and let P carry a separated natural labelling. Then no class is
all-ascent, min_{w∈κ} des(w) = cdes(κ) − 1 for every κ ∈ Cyc(P), and

  Ω_C(P, m) = Σ_{κ ∈ Cyc(P)} C(m + n − cdes(κ), n).

Hence h_C(P)_j = #{κ ∈ Cyc(P) : cdes κ = j + 1} ≥ 0, and Σ_j h_j = e_C(P).
For n = 1, h_C = (1).

More generally, for any natural labelling with no all-ascent class,
h_C(P)_j = #{κ : min_{w∈κ} des w = j} (H′).

### 2.2 The per-class lemma

**Lemma 1 (PROVEN; COMPUTED `[perclass]`).** Fix any natural labelling and
any component T. Let κ be a class that is not all-ascent, and put
stat(κ) = min_{w∈κ} des(w). Then

  Σ_{w ∈ κ} N_T(w, m) = C(m + n − 1 − stat(κ), n),

and stat(κ) = d if s = 1, and stat(κ) = d + jd − 1 if s ≥ 2.

*Proof.* If s = 1, then κ = {w} with no cuts, so N_T = C(m + n − 1 − d, n).

Let s ≥ 2. Index the pieces so that T ⊆ c_s, and let R_i be the rotation
c_{i+1} ⋯ c_s c_1 ⋯ c_i, for 0 ≤ i ≤ s − 1. R_i is broken at J_i (read J_0
as J_s). Its cuts are the other junctions, and the ones after c_s are
J_s, J_1, …, J_{i−1}, so |C_T(R_i)| = i. Thus R_i contributes only if
δ_s = δ_1 = ⋯ = δ_{i−1} = 0, and then

  N_T(R_i, m) = C(m + n − 1 − (d + jd − δ_i) − i, n − i).

Since jd ≥ 1, some junction is a descent, so stat = d + jd − 1.
- *Case δ_s = 1.* Only R_0 contributes, with des(R_0) = d + jd − 1.
- *Case δ_s = 0.* Let q = min{k ≥ 1 : δ_k = 1}. It exists and q ≤ s − 1.
  Exactly R_0, …, R_q contribute. Put M = m + n − 1 − d − jd. Then
  N_T(R_i) = C(M − i, n − i) for i < q, and N_T(R_q) = C(M + 1 − q, n − q).
  Pascal's rule C(a, b) + C(a, b + 1) = C(a + 1, b + 1) gives, by downward
  induction on j, Σ_{i=j}^{q} N_T(R_i) = C(M + 1 − j, n − j). At j = 0 this
  is C(m + n − 1 − (d + jd − 1), n). ∎

So each class contributes a single binomial, whichever T is chosen. Only
the representative carrying the contribution moves.

### 2.3 Separated labellings

**Lemma 2 (PROVEN).** Let n ≥ 2. Suppose the labelling is separated:
x < y whenever x is minimal and y is maximal, each in a non-singleton
component. Then:
- (a) every piece c of every w ∈ Lin P has first(c) ≤ last(c);
- (b) no class is all-ascent;
- (c) stat(κ) = cdes(κ) − 1 for every κ.

*Proof.*
- (a) A piece of length 1 is trivial. The first letter of a piece is
  minimal in P: anything below it lies in its component, hence in the same
  piece, hence before it. A piece of length ≥ 2 cannot start with an
  isolated point x, because then {x} would be a proper prefix that
  is a union of components. So it starts with a minimal element of a
  non-singleton component. Dually, it ends with a maximal element of a
  non-singleton component. Separation gives first < last.
- (b) If every junction were an ascent, then
  first(c_1) ≤ last(c_1) < first(c_2) ≤ ⋯ ≤ last(c_s) < first(c_1),
  a contradiction.
- (c) For s ≥ 2, stat = d + jd − 1 = cdes − 1 by Lemma 1 and §0. For s = 1,
  w is one piece of length n ≥ 2, so w_1 < w_n by (a), and
  cdes(w) = des(w) + 1. ∎

*Existence.* λ_0 lists the non-isolated minimal elements first, then the
elements that are neither minimal nor maximal in a linear extension of
their subposet, then the isolated points, then the non-isolated maximal
elements. λ_0 is a linear extension of P, hence a natural labelling, and it
is separated. (Everything below a middle element is minimal or middle, and
everything above it is middle or maximal; isolated points are unrelated to
everything.)

*Proof of Theorem H.* The classes partition Lin P. Sum Lemma 1 over
classes in Proposition D, and use Lemma 2. Theorem H′ is the same argument
without Lemma 2. ∎

### 2.4 Checks and small values

Data from `[sep-cdes]` and the unit tests. Here e is the des-distribution
on Lin P.

| P | h_C | e_C | e |
|---|---|---|---|
| A_n (antichain) | Eulerian numbers A(n−1, ·) (n ≤ 5, unit test) | (n−1)! | A(n, ·) |
| connected P | des-distribution on Lin P (Stanley) | e(P) | the same |
| C_2 ⊔ C_1 | 1, 1 | 2 | 1, 2 |
| C_2 ⊔ C_2 | 1, 3, 1 | 5 | 1, 4, 1 |
| C_3 ⊔ C_1 | 1, 2 | 3 | 1, 3 |
| A_4 | 1, 4, 1 | 6 | 1, 11, 11, 1 |

- *Antichain.* Every labelling is separated. Cyc(A_n) is the set of cyclic
  permutations, and cdes − 1 on it is the Eulerian distribution of S_{n−1}.
  This is the known identity Σ_k S(n, k)(k − 1)! C(m, k) = Σ_{j≤m} j^{n−1}
  of [LS] §2.3.
- *Connected P.* A separated labelling has w_1 < w_n for every w, so
  cdes − 1 = des and Theorem H is Stanley's theorem.
- *h_0 = 1 always*, since Ω_C(P, 1) = 1: the constant map is the only map
  to [1], and it satisfies Step 4. Theorem H says that exactly one class has
  cdes = 1.

*Positive control.* C_2 ⊔ C_2 labelled 0 < 1, 2 < 3 is not separated. The
classes {0123, 2301}, {0213}, {0231}, {2013}, {2031} have cdes − 1 equal to
0, 1, 1, 1, 1, so the distribution is (1, 4) ≠ h_C = (1, 3, 1). Over n ≤ 6,
cdes − 1 fails on 787 of 5230 labelled posets `[ctl-cdes-any]`.

*All-ascent example.* Take 0 < 1, 3 < 4, and 2 isolated. The class of
3041 | 2 has pieces 3041 and 2. Both junctions, 1 → 2 and 2 → 3, are
ascents. Min-des gives (1, 9, 8, 2) ≠ h_C = (1, 9, 9, 1). All 48 labelled
posets with n ≤ 6 that have an all-ascent class fail `[ctl-mindes-asc]`.
That the failure is forced in general is **OPEN** (H″). An all-ascent class
contributes Σ_{i=0}^{s−1} C(M − i, n − i), which is not a single binomial,
but the other classes could in principle compensate.

## 3. Why des on B_P failed, and when it works

B_P chooses, in each class, the rotation R_0 whose last piece contains T.
By §0, des(R_0) = d + jd − δ_s. That equals stat(κ) exactly when the junction
J_s, which wraps from T's piece back to the first piece, is a descent. When
J_s is an ascent, B_P counts the class one degree too high. Proposition D
explains the extra terms: the rotations R_1, …, R_q telescope onto R_0 and
raise its binomial by one step.

In [LS]'s example, P = {0<2} ⊔ {1<4} ⊔ {3} with T = {1, 4}, the labelling is
separated. The class {3|0142, 0142|3} has cdes = 2. B_P takes 30142, with
des 2, but stat = 1, which is des(01423). The junction 2 → 3 out of T's
piece is an ascent.

**Proposition B (PROVEN; COMPUTED `[lambda0-BP]`, 2450 posets).** Under
λ_0, des on B_P realises h_C(P). Here T is the component containing label
n − 1, put in the last piece. So does des on the rotations whose first
piece contains label 0.

*Proof.* Under λ_0, the possible first letters of pieces (non-isolated
minima, and isolated points) are all smaller than the possible last
letters of non-singleton pieces (non-isolated maxima).
- If P is not an antichain, then n − 1 is a non-isolated maximum. So T's
  piece is a non-singleton piece, and the junction leaving it is a descent:
  δ_s = 1.
- Dually, label 0 is a non-isolated minimum. So the junction entering its
  piece is a descent.
- For the antichain, the pieces are letters, and both statements are
  trivial.

In every case the chosen rotation is broken at a descent junction, so its
des is stat(κ). Apply Theorem H. ∎

Under other separated labellings, an isolated point labelled above some
maximum can follow T's piece with an ascent. Both conventions then fail,
on 346 of 4443 separated labelled posets with n ≤ 6 `[ctl-BP-last]`,
`[ctl-BP-first]`. The general rule: **any rule that picks, in each class,
a rotation broken at a descent junction realises h_C**, provided no class
is all-ascent.

## 4. Remarks and open points

- *Form of the identity.* Theorem H reads

    Ω_C(P, m) = Σ_{O ∈ S_n/C_n, O ∩ Lin P ≠ ∅} C(m + n − cdes(O), n),

  next to Stanley's Ω(P, m) = Σ_{w ∈ Lin P} C(m + n − 1 − des(w), n). The
  statistic lives on the C_n-orbits of words that meet Lin P. These are
  the objects e_C counts ([ME] §0).
- *Adin–Reiner–Roichman.* This is not a cyclic descent extension in their
  sense, since C_n does not act on Cyc(P). It is the classical cyclic
  descent number of a cyclic word. The labelling hypothesis plays the role
  that their non-Escher condition plays. Prior art is being checked
  separately and was not searched here.
- *Labelling invariance (corollary).* For n ≥ 2, the distribution of cdes
  on Cyc(P) is the same for every separated natural labelling. Separation
  is needed: the positive control above shows the distribution changes
  without it.
- **OPEN.** The converse H″. A shelling of the upper intervals of OP(P), or
  of the cone C_P read from 1̂, that realises h_C (lead 3). Symmetry or
  unimodality of h_C (A_4 gives 1, 4, 1, but C_3 ⊔ C_1 gives 1, 2). A
  reciprocity law ([LS] §2.3).

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 70 s):

    python3 h_vector_omega_c.py --nmax 7 --lmax 6 > output/h_vector_omega_c.txt
    python3 -m unittest test_h_vector_omega_c

The script exits with status 0 iff every claim holds and every CONTROL line
is refuted somewhere. It imports no other module of the repository. It
enumerates the posets up to isomorphism itself (1, 2, 5, 16, 63, 318, 2045
for n = 1, …, 7) and computes Ω_C from the Möbius recursion on OP(P).
`--lmax` sets the largest n at which every natural labelling is tested.
