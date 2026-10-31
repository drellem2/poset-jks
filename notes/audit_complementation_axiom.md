# Audit: the complementation axiom (C) of quotient_categories.md §1.5

**Object of audit.** `notes/quotient_categories.md` §1.5 ([QC]), which comes from
`notes/audit_quotient_categories.md` §1.3 ([AudQC]):

> **Axiom (C).** For every object X with Q̄(X) ≠ ∅ there is a t ∈ Q̄(X) such that its
> complements in Q(X) form an antichain, every complement is an atom a, and
> [a, 1̂] ≅ Q(X/a) for an object X/a of the class.
>
> **Claim (PROVEN, given Björner–Walker, cited from memory).** In a class satisfying (Q1),
> (Q2) and (C), every Q̄(X) is a wedge of spheres. The wedge is pure when all the X/a have
> the same length.

**Verdict: FIXABLE.**
- The wedge statement **HOLDS**. The Björner–Walker formula is quoted correctly. I checked
  it against four published statements, not against the 1983 original (§1).
- Heredity is built into the axiom as written, and it is necessary (§1.2).
- The antichain clause is redundant but harmless (§1.3).
- (Q1) and (Q2) are used only in a weak form (§1.4).
- The **purity clause FAILS as stated**. It needs the equal-length hypothesis at every
  level, not only at the top. With that hypothesis, or when every Q(X) is graded, it holds
  (§1.5).
- In subgroup lattices, (C) is **not hereditary in general**. It holds on every interval
  of L(G) for ten groups up to S_5, including A_5 and S_5. It fails on exactly one interval
  of L(PSL(2,7)), namely [1, G], where no element at all has an antichain of complements
  (§2).
- Prior art: **KNOWN IN SUBSTANCE**. The induction is Björner–Walker's own argument for
  Π_n, and its dual is the Kratzer–Thévenaz argument for solvable groups. I did not find
  the class-level packaging as a named axiom (§3).

Tags:
- **CHECKED**: computed by `compute/audit_complementation_axiom.py`. The output is
  archived in `compute/output/audit_complementation_axiom.txt`. The code is new and
  imports nothing from the repo.
- **READ**: I read the cited source, saying which part.
- **CITED**: not read; I say where the citation comes from.

---

## 1. The claim

### 1.1 The Björner–Walker formula

**Statement (READ, four secondary sources that agree):**
- Živaljević, *Combinatorics of topological posets: homotopy complementation formulas*,
  arXiv math/9801147, Thm 4.1;
- Živaljević, arXiv 1603.08175, eqs. (15)–(17);
- Babson–Björner–Linusson–Shareshian–Welker, arXiv math/9705219, Prop. 10.3;
- Kramarev–Lokutsievskiy, arXiv 0911.4136, Thm 2.1.

Let L be a finite bounded lattice, z ∈ L̄, and Co(z) = {x : x ∧ z = 0̂, x ∨ z = 1̂}. Then:
1. L̄ ∖ Co(z) is contractible.
2. If Co(z) is an antichain, then Δ(L̄) ≃ ⋁_{y ∈ Co(z)} Σ(Δ(L̄_{<y}) ∗ Δ(L̄_{>y})).

The original (European J. Combin. 4 (1983) 11–19) was **not read**. Its statement is
quoted the same way in all four sources.

The proof in [Ži98] has two steps:
- the contractibility in part 1;
- the identity Δ(P)/Δ(P ∖ A) ≃ ⋁_{y∈A} Σ(Δ(P_{<y}) ∗ Δ(P_{>y})) for any antichain A
  ([Ži16] eq. (16)). The open stars of the elements of A are disjoint because A is an
  antichain.

**This is where the antichain is used.**

[QC]'s use of the formula is correct. For an atom a, L̄_{<a} = ∅, so ∅ ∗ Y = Y and the
summand is ΣΔ((a, 1̂)) = ΣQ̄(X/a).

**CHECKED.** The formula was compared with direct homology in 51,216 cases
(interval, z, p) with p = 2, 3, where Co(z) is an antichain. The cases range over:
- every interval of length ≥ 2 of Π_3, Π_4 and Π_5;
- OP(P) for all 84 posets with 3 ≤ n ≤ 5, up to isomorphism;
- 150 random lattices of closure systems (3–22 elements).

Another 960 cases come from the subgroup lattices of §2. **There are 0 mismatches.**

**Control, must fail and does.** Take N_5 = {0̂ < a < b < 1̂, 0̂ < t < 1̂}. Then
Co(t) = {a, b} is a chain. The naive sum gives H̃ = 0, but the actual answer is
H̃_0 = 𝔽. The instrument refuses this case.

### 1.2 Heredity is needed, and the axiom already asks for it

The induction applies (C) to every X/a, then to every (X/a)/a′, and so on.
- The axiom is stated "for every object X", and it requires X/a to be an object of the
  class. So the class is closed under the passage X ↦ X/a, and (C) holds at every level.
  **As written, the axiom is hereditary**, and the proof is correct.
- Heredity is essential. **CHECKED, control:** take L = R̂ × 2, where R̂ is the face lattice
  of the 6-vertex RP² with 0̂ and 1̂ adjoined.
  - t = (1̂, 0) has exactly one complement, the atom (0̂, 1), and [a, 1̂] ≅ R̂. So (C)
    holds at the top.
  - It fails in R̂, which has no certificate, primal or dual.
  - L̄ ≃ ΣR̄ has mod-2 Betti numbers {2: 1, 3: 1} and none mod 3. This is torsion, so L̄ is
    not a wedge.

  So "(C) at the top level" proves nothing.
- The **base case** is fine. Length 1 gives Q̄ = ∅ = S^{−1}, and Σ∅ = S^0.
- **Vacuous case.** If Co(t) = ∅, then "every complement is an atom" holds vacuously, and
  part 1 of the formula makes L̄ contractible, which is the empty wedge. So (C) is
  automatic for every lattice with an uncomplemented element of L̄. This is correct, but
  it should be said, because it makes (C) weaker than it looks. CHECKED: all 150 random
  lattices carry a certificate. Of them, 84 are contractible and 66 are not. So the random
  corpus tests the formula, not the strength of (C).

### 1.3 The antichain clause

- **The clause is redundant.** Distinct atoms are incomparable, so "every complement is an
  atom" already implies "the complements form an antichain".
- **The formula itself does need an antichain** (control in §1.1). Without the atom
  clause, the honest axiom is: "Co(t) is an antichain, and the closed intervals [0̂, y] and
  [y, 1̂] are again objects of the class." That version needs the class to be closed under
  lower intervals too. This is where (Q3) would enter.

### 1.4 What (Q1) and (Q2) contribute

- (Q1) is used only as "Q(X) is a finite lattice". The formula needs meets and joins to
  define complements.
- (Q2) is used only at the atoms a ∈ Co(t), and (C) already states that case. So the claim
  holds for any class of finite lattices closed under the chosen X ↦ X/a.
- However, if (Q2) is assumed in full, every upper interval [π, 1̂] becomes an object.
  Then (C) must hold on **every** upper interval, which is stronger than the induction
  needs. Recommended wording: "(Q1) and (C)", or "(C) along the recursion".

### 1.5 The purity clause: FAILS as stated, FIXABLE

**Counterexample (CHECKED).**
- Let M = B_3 ∪ {p}, where p is a new element with 0̂ < p < 1̂, incomparable to the rest.
  Then M̄ is a hexagon plus a point, so M̄ ≃ S^1 ∨ S^0.
- Let L = M × 2, which has 18 elements.
- Every upper interval of L satisfies (C).
- t = (1̂_M, 0) has the single complement a = (0̂, 1), which is an atom, and [a, 1̂] ≅ M.
  So "all X/a have the same length" holds at the top, because there is only one X/a.
- But L̄ ≃ ΣM̄ ≃ S^2 ∨ S^1. This is not pure: the Betti numbers are {1: 1, 2: 1} at
  p = 2, 3, 5 and 2^31 − 1.
- The non-purity comes from one level down. In M, every (C)-witness has complements whose
  upper intervals have lengths 1 and 2. CHECKED.

**Correct statement (PROVEN by the same induction).** Unwind the recursion. The spheres
are indexed by the *complement chains* 0̂ ⋖ a_1 < a_2 < … < a_k ⋖ 1̂, where:
- a_1 is a complement of t;
- a_2 is a complement of t′ in [a_1, 1̂];
- and so on.

The sphere for a complement chain has dimension k − 1, and the k elements a_i are atoms of
the successive upper intervals. So:
- Q̄(X) is a wedge of S^{d} with d = ℓ(Q(X)) − 2 if, at every level of the recursion, all
  the X/a have length ℓ − 1. This holds in particular when every Q(X) in the class is
  graded.
- It is a pure wedge of some dimension d if all complement chains have the same length,
  that is, if "all X/a have the same length" holds hereditarily.

CHECKED: all 84 lattices OP(P) with n ≤ 5, and Π_3 to Π_5, are graded and certified, and
their homology lies in the single degree ℓ − 2.

**Recommended replacement for [QC] §1.5:**

> The wedge is pure, of dimension ℓ(Q(X)) − 2, when every Q(Y) in the class is graded,
> and more generally when all X/a have the same length at every level of the recursion.
> The top-level condition alone is not enough.

---

## 2. Where (C) holds: subgroup lattices

### 2.1 Census

CHECKED, `[GRP]` and `[GRP+]`. The table lists every interval [H, K] of L(G) of length
≥ 2. The columns are:
- **(C) top:** some t at the top of L(G) has all its complements atoms (|t| = possible
  orders of t).
- **(C) all:** the same holds on every interval of length ≥ 2.
- **dual:** the same with complements equal to coatoms, recursing on [0̂, c].
- **mixed:** at each interval, either form may be used.

Intervals of intervals are intervals, so the mixed certificate proves the wedge property
for every interval it certifies. Homology was computed at p = 2, 3, 5, 2^31 − 1, plus
p = 7 for the larger groups.

| G | #L(G) | H̃(L̄(G)) | (C) top (\|t\|) | intervals failing (C) | failing dual | no mixed certificate |
|---|---|---|---|---|---|---|
| C_2² | 5 | {0: 2} | yes (2) | 0/1 | 0 | 0 |
| S_3 | 6 | {0: 3} | yes (2, 3) | 0/1 | 0 | 0 |
| D_8 | 10 | 0 | yes (2, 4) | 0/9 | 0 | 0 |
| Q_8 | 6 | 0 | yes (2, 4) | 0/5 | 0 | 0 |
| C_2³ | 16 | {1: 8} | yes (4) | 0/15 | 0 | 0 |
| A_4 | 10 | {0: 4} | yes (2, 4) | 0/5 | 0 | 0 |
| D_12 | 16 | {1: 6} | yes (4, 6) | 0/15 | 0 | 0 |
| S_4 | 30 | {1: 12} | yes (8, 12) | 0/54 | 0 | 0 |
| A_5 | 59 | {1: 60} | yes (10) | 0/78 | 1 (the top) | 0 |
| S_5 | 156 | {2: 60} | yes (60) | 0/588 | 12 | 0 |
| PSL(2,7) | 179 | {1: 48, 2: 48} | **no** | **1/703 (the top)** | 1 (the top) | **1: [1, G]** |

- Wherever a certificate exists, its predicted wedge matches the direct homology at every
  prime, on every certified interval.
- No interval of any of these lattices shows p-torsion for p = 2, 3, 5.
- The subgroup counts 30, 59, 156 and 179 are the known ones.
- The reduced Euler characteristics are −12, −60, 60 and 0. These agree with the known
  Möbius values μ(S_4) = −12, μ(A_5) = −60, μ(S_5) = 60 and μ(PSL(2,7)) = 0. These values
  are CITED from memory, as the pattern μ(S_n) = (−1)^{n−1} n!/2 for small n and Hall's
  values.

### 2.2 Observations

1. **[AudQC]'s top-level findings are confirmed.** In L(A_4), L(S_4) and L(A_5), (C) holds
   at the top. For S_4, t = A_4 works, with the six transposition subgroups as complements.
   For A_5, t = D_10. They are also extended: for these groups and S_5, (C) holds on
   *every* interval, so the claim of §1 applies hereditarily and proves directly that
   every interval of L(G) is a wedge.
2. **L(A_4).**
   - H̃_0 = ℤ^4 is the wedge of four S^0, which (C) gives directly: t = V_4, whose
     complements are the four C_3, and each [C_3, A_4] has length 1.
   - This wedge is pure in the sense "all spheres of one dimension", but its dimension 0 is
     below ℓ − 2 = 1, because L(A_4) is not graded.
   - So [QC]'s statement "⇒ wedge of top-dimensional spheres is false (A_4)" is right,
     and it agrees with §1.5.
3. **(C) does not hold hereditarily in subgroup lattices.**
   - In L(PSL(2,7)), every interval except [1, G] carries a (C)- or dual certificate.
   - At [1, G] there is **no z at all** whose complements form an antichain. The census
     covers all 177 elements of L̄, and every one has two comparable complements. Grouped
     by (|z|, multiset of complement orders), they fall into 10 types; that grouping was
     an ad hoc run, and the archived output records only the count 0. So Björner–Walker
     gives nothing there in any form.
   - L̄(PSL(2,7)) is a non-pure wedge, ⋁_{48} S^1 ∨ ⋁_{48} S^2. This is
     Kramarev–Lokutsievskiy, arXiv 0911.4136, main theorem (READ: abstract, §1, Thm 2.1
     and the statement of the result). Our Betti numbers {1: 48, 2: 48} at five primes
     agree.
   - So the failure of (C) at PSL(2,7) is **not** a failure of the wedge property. It is a
     failure of the mechanism.
4. **On simple groups.** Kramarev–Lokutsievskiy say that the Björner–Walker method
   "depend[s] on the existence of a normal subgroup and therefore cannot be used" for
   simple groups. The census refines this.
   - For A_5, the primal (atom) form *does* work at the top, with t = D_10, which is not
     normal.
   - The dual (Kratzer–Thévenaz) form, which is the one that uses normal subgroups,
     fails there.
   - For PSL(2,7), both forms fail.

### 2.3 What this means for Shareshian's conjecture

Shareshian's conjecture says that every open interval in a subgroup lattice is a wedge of
spheres. It is Conjecture 1.4.2 in Wachs, *Poset topology: tools and applications*
(arXiv math/0602226), READ at §1.4. Wachs says it holds for solvable groups by
Kratzer–Thévenaz.

- **Sufficient.** If (C), in primal, dual or mixed form, held on every interval of every
  subgroup lattice, the claim of §1 would prove Shareshian's conjecture. Group by group,
  it does prove the conjecture for C_2², S_3, D_8, Q_8, C_2³, A_4, D_12, S_4, A_5 and S_5.
  These cases are already known: the solvable ones by Kratzer–Thévenaz, and A_5 because
  L̄(A_5) is a wedge of 60 circles (Shareshian, as reported in [KL] §1). So this is
  consistency, not news.
- **Not available.** The hypothesis fails at [1, PSL(2,7)], the smallest case outside
  the groups above, and there no complementation formula of Björner–Walker type applies.
  So a "(C) ⇒ wedge" theorem cannot prove the conjecture in general. This sharpens [QC]
  §1.5, item 3 ("for G-sets, the induction needs (C) on every interval"): that requirement
  is **false** for PSL(2,7).
- **Purity cannot be forced.** PSL(2,7) is a non-pure wedge, so no axiom system that
  covers G-sets can conclude purity. This is consistent with §1.5: certificates give
  non-pure wedges whenever complement chains have different lengths.
- **No change to STOP.** [QC] §4 asks for a mechanism outside complementation, Kozlov and
  Arone–Brantner. (C) is complementation, and the PSL(2,7) case shows exactly where it
  runs out.

---

## 3. Prior art (search result, not a proof of absence)

**Verdict: KNOWN IN SUBSTANCE.** The induction "complements of t are atoms, recurse on
[a, 1̂]" is:
1. **Björner–Walker's own application to Π_n.** With t = {n} | rest, the complements are
   the n − 1 atoms {i, n}, and Π̄_n ≃ ⋁ ΣΠ̄_{n−1}, which gives (n − 1)! spheres S^{n−3}.
   Živaljević attributes this recurrence to [BW83] (READ: [Ži98] §2, eq. (1);
   [Ži16] eq. (18)). CHECKED: Π_3, Π_4 and Π_5 give {0: 2}, {1: 6} and {2: 24}.
2. **Kratzer–Thévenaz 1985** (Comment. Math. Helv. 60, 86–106) for solvable groups, in
   dual form. The complements of an abelian minimal normal subgroup N are maximal
   subgroups (coatoms), and one recurses into L(H). Thévenaz identifies the spheres with
   chains of complements to a chief series. These are the "complement chains" of §1.5.
   CITED: via Wachs 2007 §1.4 (READ) and Woodroofe arXiv 0708.3539 (search snippet only);
   the paper itself was not read.
3. **Kramarev–Lokutsievskiy 2009** use the formula on subposets of L(PSL(2,7)) (READ in
   part).

**Not found:** a statement of (C) as a *class-level axiom*, meaning "every object has a t
whose complements are atoms, and the upper intervals are objects of the class", under
any name.

**Related, but a different mechanism:**
- Björner's EL-shellability and Björner–Wachs recursive atom orderings (Wachs 2007,
  Lecture 3, READ as headings and theorem statements). These are a shelling mechanism and
  give purity directly.
- Björner–Wachs nonpure shellability, which Shareshian 2001 uses to show that L(G) is
  shellable iff G is solvable (Wachs 2007, Thm 3.1.13, READ).
- Not checked: Kozlov, *Combinatorial Algebraic Topology*, which states the formula, and
  Björner, *A general homotopy complementation formula* (Discrete Math. 1998), which is
  the non-antichain version. Also CITED from memory, not checked: in a lattice with a
  modular coatom, the complements of that coatom are atoms (the supersolvable case).
  This is the source of the Π_n example.

**Searched (2026-10-31):**
- "Björner Walker homotopy complementation formula complements antichain";
- "Wachs Poset topology homotopy complementation formula partition lattice";
- "Shareshian topology of order complexes of intervals in subgroup lattices";
- "homotopy type subgroup lattice PSL(2,7) wedge of spheres".

**Read:** the four statements of §1.1, and Wachs 2007 §1.4 and §3.1.

---

## 4. Recommended edits to [QC] §1.5 (not applied here)

1. Purity clause: replace it with the corrected statement of §1.5.
2. Say that the antichain clause is implied by the atom clause.
3. Say that Co(t) = ∅ is allowed and gives contractibility.
4. Say that (Q2) is used only at the atoms in Co(t).
5. "Where (C) holds", subgroup lattices:
   - (C) holds on every interval for the groups of §2.1 through S_5;
   - it fails at [1, PSL(2,7)], which is nevertheless a non-pure wedge
     (Kramarev–Lokutsievskiy).
6. Item 3 of "Why it does not reverse STOP": add the PSL(2,7) failure as the concrete
   witness.
7. The claim can stay PROVEN, with the formula citation upgraded from "from memory" to
   "statement checked in four secondary sources; original not read".

---

## Reproduce

```
cd compute
python3 audit_complementation_axiom.py --nmax 5 > output/audit_complementation_axiom.txt   # ~26 s, single core
python3 -m unittest test_audit_complementation_axiom
```

The run ends `== done: 0 failure(s)`.

Controls that must fail, and do (`[CTL]`):
- N_5: the formula mispredicts when Co(z) is a chain, and the instrument refuses the case.
- Π_4, t = 01|23: the (C) test rejects it, because the complements include non-atoms.
- RP²: mod 2 and mod 3 differ, so the torsion detector fires.
- RP²: there is no certificate.
- R̂ × 2: (C) holds at the top, but L̄ has torsion.

Unit test: an earlier draft cached chain lengths by `id(lattice)`. That was unsound,
because Python reuses ids, and it gave wrong interval counts. It is fixed, and a test
covers it.

References:
- [Ži98] R. Živaljević, arXiv math/9801147.
- [Ži16] R. Živaljević, arXiv 1603.08175.
- [BBLSW] Babson, Björner, Linusson, Shareshian, Welker, arXiv math/9705219.
- [KL] I. P. Kramarev, L. V. Lokutsievskiy, arXiv 0911.4136.
- [W07] M. Wachs, arXiv math/0602226.
