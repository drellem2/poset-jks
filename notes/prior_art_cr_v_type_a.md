# Prior art for cr_v_type_a.md (Theorem TA-CR, Lemma C, Lemma K_A)

This note checks the claims of `notes/cr_v_type_a.md` ("[CVA]") against the
literature:
- **Theorem TA-CR**: for every poset P on [n], n ≥ 3, and every g = ετ ∈ ±S_n
  with g C_P = C_P, χ_{C_P}(g) = 0 iff M = OP(P)^τ has an uncomplemented
  element. This is a converse of Crapo's corollary on the fixed sublattice of
  an automorphism (ε = +1) or anti-automorphism (ε = −1).
- **Lemma C**: the gcd criterion for complements of the orbit partition of
  ⟨σ^h⟩ among σ-stable partitions coarser than κ.
- **Lemma K_A**: every complement of an element below cl(Fix g) is coarser
  than the component partition κ = comp(P).

Verdicts are used as in `notes/prior_art_per_cone_vanishing.md` ("[PAPCV]"):
- **KNOWN**: stated in a source read here, with the exact reference.
- **PARTLY KNOWN**: a special case, or one direction, is stated in a source
  read here.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is never counted as
  evidence either way. A statement about it that comes from another paper is
  marked "(secondary, via …)".

## Verdict

| Claim of [CVA] | Verdict | Closest prior art (read) |
|---|---|---|
| **TA-CR, "if" direction** (an uncomplemented element forces χ = 0) | **KNOWN.** This is Crapo's corollary: "Deduce that if μ(0̂, 1̂) ≠ 0, then L is complemented" (EC1 Ex. 3.92; the solution names Crapo 1966, Thm 3). It has topological strengthenings: a noncomplemented finite lattice is Z-acyclic (Baclawski 1977, Cor. 6.3), contractible (Björner 1981, Thm 3.3), and nonevasive (Kozlov 1998). These three are secondary, via Kozlov's introduction | EC1 Ex. 3.92 and its solution; Kozlov 1998 §1 |
| **TA-CR, "only if" direction**, general P and ±τ | **NOT FOUND.** The converse is false for general finite lattices ([PAPCV] §3.2: there is an 8-element complemented lattice with μ = 0). The converse is known for *modular* lattices and their fixed sublattices (Knop, Lemma A.2 and the paragraph after (A.8)), and for distributive lattices (EC1 §3.4, Ex. 3.9.6). M = OP(P)^τ is not modular in general. Already Π_4 = OP(antichain on 4 points) is not modular. No source read treats OP(P), its fixed sublattices, or anti-automorphisms | Knop App. A; EC1 §§3.4, 3.9; [PAPCV] §3.3 |
| **TA-CR, special case P = antichain, g = +w** (Π_n^w, all chambers) | **KNOWN in substance**, with one elementary step that the sources do not state (§2.2). Stanley (1982, Remark after Lemma 7.1) shows that μ(Π_n^w) = 0 exactly when 0̂ is not a meet of coatoms, using Hanlon's Lemma 2 and EC1 Cor. 3.9.5. When 0̂ is not a meet of coatoms, the meet of all coatoms has no complement. That is one line, and it is ours. Hanlon gives the complements of the hinge in the nonvanishing case (Lemma 6) | Stanley 1982 §7; Hanlon 1981 Lemmas 1, 2, 6, Thm 4; EC1 Cor. 3.9.5 |
| **TA-CR, special case g = −τ on the antichain** (Π_n^τ for −τ) | **PARTLY KNOWN.** Π_n^{−τ} = Π_n^τ as a lattice, so the all-chambers case reduces to the previous row. On a single cone, −τ has not been treated in any source read ([PAPCV], Theorem TA row) | Stanley 1982 §7; [PAPCV] |
| **Lemma C**, h = 1 and κ = 0̂, "(ii) ⇒ (i)": the cycle partition of σ has a complement when all cycles have one length | **KNOWN.** In Hanlon's Lemma 6, the partitions c(f) are complements of the hinge h = cyc(σ) "in Π(N) hence … in L", and there are j^{m−1} of them. The proof assumes all m cycles have length j. On our reading, it does not use that j is squarefree. Hanlon's Lemma 1 is the block-orbit structure that Lemma C, Steps 2 and 4, rederive | Hanlon 1981 Lemma 1, Lemma 6 and its proof |
| **Lemma C**, h = 1 and κ = 0̂, "(i) ⇒ (ii)": unequal cycle lengths leave cyc(σ) uncomplemented | **NOT FOUND as stated.** Hanlon's last paragraph of the proof of Lemma 6 classifies the complements of h, but it works inside the meet sublattice 𝓜 and assumes equal lengths. The vanishing for unequal lengths is proved through the meet of coatoms (Stanley's Remark), not through the hinge | Hanlon 1981 Lemma 6; Stanley 1982 Remark after Lemma 7.1 |
| **Lemma C**, general h and κ: the condition gcd(s, h) = 1, s divides every λ_K, and ℓ/gcd(ℓ, h) = s | **NOT FOUND.** Every gcd in Hanlon is the gcd of the cycle lengths of σ, or the Π(x ∨ y) of his Lemma 9. None involves a power σ^h or a σ-stable lower bound κ. No source read considers complements of the orbit partition of a power of σ | Hanlon 1981 (grep "gcd", §0.3) |
| **Lemma K_A** (fixed-point averaging; complements of w ≤ cl(Fix g) are ≥ κ) | **NOT FOUND** in the sources read. The averaging step itself (the ⟨g⟩-average of a point of a g-stable convex set is fixed) is standard. It was not searched for separately | — |
| **Observation CC** (new, first COMPUTED here, not claimed in [CVA]): every zero is a zero of EC1 Cor. 3.9.5 type. That is, 0̂ is not a meet of coatoms of M, or 1̂ is not a join of atoms of M | **Not a literature claim**; recorded as a remark for [CVA] (§2.3). **Now PROVEN for every n** (Theorem CC of `notes/observation_cc.md`), independently audited (`notes/audit_observation_cc.md`: every step HOLDS); its prior art is checked in `notes/prior_art_observation_cc.md`. It holds on all 3,519 zeros of the 6,154 pairs with n ≤ 7, and fails on none of the 2,635 nonzero pairs; n = 8 is added in those notes. It is a strictly stronger property than "uncomplemented element": EC1 Ex. 3.28 (Rival's example) is a noncomplemented lattice that is atomic and coatomic | `compute/prior_art_cr_v_type_a.py`; EC1 Cor. 3.9.5, Ex. 3.28 |

**Bottom line.**
- The "if" half of TA-CR is Crapo's corollary (KNOWN).
- The "only if" half was NOT FOUND for any class that contains the lattices
  OP(P)^τ. For the antichain with g = +w, it follows from Hanlon and Stanley
  plus one elementary line (§2.2), so [CVA] should cite them for that case.
- Lemma C is PARTLY KNOWN. Its h = 1, κ = 0̂ existence half is Hanlon's
  Lemma 6 construction. The gcd(s, h) = 1 criterion for powers σ^h, and the
  κ-relative version, were NOT FOUND.
- New remark: on n ≤ 7, every zero is already explained by EC1 Cor. 3.9.5
  (§2.3). If this held for all n, it would give a uniform witness: the meet
  of the coatoms, or the join of the atoms. It is COMPUTED only, for n ≤ 7.

---

## 0. Sources

### 0.1 Read

Full text. PDFs were fetched with `curl` and converted with
`pdftotext -layout`, then grepped. The listed sections were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981) 319–341 | msp.org, `pjm/1981/96-2/pjm-v96-n2-p04-s.pdf` | Abstract; §1; §2 (Lemma 1, Lemma 2 and its proof, coatoms of types a and b); Lemmas 3–4; §5 to the end of Lemma 6 (the hinge, Lemma 5, Lemma 6 and its whole proof, Example 2); Lemma 14, Theorem 4 and its proof, Theorem 4A; references |
| Stanley, *Some aspects of groups acting on finite posets*, J. Combin. Theory Ser. A 32 (1982) 132–161 | math.mit.edu/~rstan/pubs/pubfiles/50.pdf | Theorem 1.1 and its proof (the Hopf–Lefschetz formula, attributed to Baclawski–Björner); §7 opening, Lemma 7.1 and the Remark after it, Lemma 7.2 |
| Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., author's online version ("EC1") | math.mit.edu/~rstan/ec/ec1.pdf | Cor. 3.9.3, Cor. 3.9.4 (Crosscut), Cor. 3.9.5, Example 3.9.6; §3.10 opening and Prop. 3.10.1; Exercises 3.28, 3.92, 3.93 and the solutions of 3.28 and 3.92 |
| Kozlov, *Order complexes of noncomplemented lattices are nonevasive*, Proc. AMS 126 (1998) 3461–3465 | arXiv:math/9704225 | §1 in full (the history Crapo → Baclawski → Björner → Björner–Walker); references |
| Wachs, *Poset topology: tools and applications*, IAS/Park City lecture notes | arXiv:math/0602226 | §4.6 in full (Theorem 4.6.1: χ_P(g) = μ(P̂^g), attributed to Baclawski–Björner [13]); reference [13] |
| Knop, *Multiplicities and dimensions in enveloping tensor categories* | arXiv:2209.10337 | Appendix A: Lemma A.2, (A.8) and the paragraph after it |
| Farley, *A conjecture of Kozlov from the 1998 Proceedings …* | arXiv:2201.01491 | Final section and references (the history of the fixed-point property of noncomplemented lattices) |

### 0.2 Web searches

- Baclawski Björner "Fixed points in partially ordered sets" Advances 1979,
  complemented lattice automorphism;
- Möbius function fixed point sublattice automorphism complement vanishing
  partition lattice orbit partition gcd cycle lengths (extended);
- Björner "On complements in lattices of finite length" Discrete Math. 1981;
- Stanley "Some aspects of groups acting on finite posets" fixed point
  Möbius Lefschetz;
- "fixed point" sublattice group action Möbius nonzero complemented
  equivariant converse Crapo partition lattice Smith theory (extended);
- Baclawski Björner "Fixed points and complements in finite lattices" JCTA
  30 (1981) (extended);
- Baclawski "A combinatorial proof of a fixed point property";
- lattice of acyclic partitions, order-preserving partitions, Möbius
  function, complemented, poset cone, braid arrangement, automorphism
  (extended).

None returned a converse of Crapo's corollary for fixed sublattices of
partition lattices, for OP(P), or for any non-modular class. None returned
complements of orbit partitions of a power of σ. The searches did return the
two Baclawski–Björner papers, Knop's appendix and Kozlov's note.

### 0.3 Greps, with positive controls

Every negative grep is paired with the same instrument (case-insensitive
`grep -c` on the same text file) firing on a term that is known to be
present. Counts are lines.

| Text | Negative term → count | Positive control → count |
|---|---|---|
| Hanlon | "uncomplemented / noncomplemented / non-complemented" → 0 | "complement" → 11 (Lemma 6, its proof, Example 2) |
| Hanlon | "acyclic" → 0; "cone" → 0 | "partition" → 50 |
| Hanlon | "anti-automorph / antiautomorph / order-reversing" → 0 | the same pattern in EC1 → 12 (Ex. 3.8, Fig. 3.69) |
| Hanlon | "orbit" → 0 (Hanlon says "cycle") | "orbit" in Stanley 1982 → 9 |
| Hanlon | "gcd" with a power σ^h: none among the 19 "gcd / greatest common divisor" hits (lines read: the abstract, Lemma 2, the count of type-b coatoms, Lemma 4, Lemma 9) | "gcd" → 19, so gcd statements are found when present |
| Stanley 1982 | "complemented" → 0; "acyclic" → 0; anti pattern → 0 | "partition" → 21; "complement" → 1 (set complement, §1) |
| EC1 | "uncomplemented / noncomplemented" → 0 | "not complemented" → Ex. 3.28; "no complement" → its solution; index "non-complemented lattice, 474" |
| Kozlov 1998 | "fixed" → 0 | "noncomplemented" → 11 |

### 0.4 NOT ACCESSIBLE

- **Baclawski–Björner, *Fixed points and complements in finite lattices*,
  J. Combin. Theory Ser. A 30 (1981) 335–338** (doi
  10.1016/0097-3165(81)90030-3). ScienceDirect and the Elsevier text-mining
  API returned 403 or a Cloudflare page. Baclawski's publication list has
  no PDF for it. This is the source whose title is closest to the question.
  Content (secondary, via Wachs §4.6 and Stanley 1982 Thm 1.1): the
  Hopf–Lefschetz form χ_P(g) = μ(P̂^g) for a G-poset. Whether it also
  states a complementation criterion for fixed sublattices could not be
  checked. *This is the most likely place for a statement close to TA-CR*,
  and a reader with access should check it.
- **Baclawski–Björner, *Fixed points in partially ordered sets*, Adv. Math.
  31 (1979) 263–287.** Same paywall. Content (secondary, via the search
  summaries and Farley): a finite noncomplemented lattice L has L ∖ {0̂, 1̂}
  with the fixed-point property. That is a strengthening of the "if"
  direction, not a converse.
- **Björner, *On complements in lattices of finite length*, Discrete Math. 36
  (1981) 325–326**, and **Björner, *Homotopy type of posets and lattice
  complementation*, JCTA 30 (1981) 90–100.** Same paywall. Content
  (secondary, via Kozlov and EC1 solution 3.92): noncomplemented ⇒
  contractible.
- **Crapo 1966**, **Baclawski 1977**, **Björner–Walker 1983**: not opened,
  as in [PAPCV] §0.3. They are used as stated by EC1 and Kozlov.

## 1. TA-CR, the "if" direction

EC1 Ex. 3.92: "Show that μ(0̂, 1̂) = Σ μ(0̂, u) ζ(u, v) μ(v, 1̂), where u, v
range over all pairs of complements of t. Deduce that if μ(0̂, 1̂) ≠ 0, then L
is complemented." The solution calls it "the Crapo complementation theorem"
(Crapo 1966, Thm 3) and points to Björner 1981 for topology. [CVA] S3 cites
this correctly.

The fixed-sublattice frame is also KNOWN. For a group acting on a poset,
χ_P(g) = μ(P̂^g) (Wachs Thm 4.6.1; Stanley 1982 eq. (4), attributing the
general statement to Baclawski–Björner). This is the role that [VC]'s
identity χ_{C_P}(g) = ± μ(Λ(C_P)^g) plays in [CVA] S1. So "Crapo applied to
a fixed sublattice" is the standard way to get vanishing of a Lefschetz
character. Knop uses it (after (A.8)): "h_Λ(g) = 0 unless the action of g is
'semisimple', i.e., every g-stable a ∈ Λ has a g-stable complement". For
modular Λ, Knop's Lemma A.2 makes it an iff.

## 2. TA-CR, the "only if" direction

### 2.1 No converse for a class containing OP(P)^τ

The converse of Crapo's corollary is false in general. EC1 does not state a
converse anywhere. Its Cor. 3.9.5 (0̂ not a meet of coatoms ⇒ μ = 0) is a
sufficient condition of a different kind. Knop's iff needs modularity. Π_n
is not modular for n ≥ 4 ([PAPCV] §3.3), and OP(antichain) = Π_n, so the
lattices of TA-CR are outside every class with a known converse. No source
read mentions acyclic (order-preserving) partitions together with group
actions (§0.3; [PAPCV] for Dorpalen-Barry–Kim–Reiner and
Dorpalen-Barry–Proudfoot–Wang).

### 2.2 The antichain with g = +w

For the antichain on [n], OP(P)^w = Π_n^w. Here CR_V follows from the
literature plus one elementary step.
- **Stanley 1982, Lemma 7.1**: μ(Π_n^π) = (−1)^{d−1} μ(n/d)(d−1)!(n/d)^{d−1}
  if π is a product of d cycles of length n/d, and 0 otherwise. The Remark
  after it: "Hanlon actually computes μ(x_π, 1̂), where x_π is the meet of
  the coatoms of Π_n^π. It is easy to see (alternatively, this follows from
  [Hanlon, Lemma 2]) that x_π = 0̂ if and only if all cycles of π have the
  same length. Since in any (finite) lattice μ(0̂, 1̂) = 0 unless 0̂ is a meet
  of coatoms …, Lemma 7.1 follows." Read literally, the middle sentence
  does not hold for σ = (1234) (Π_4^σ = {0̂, 13|24, 1̂}, so x_σ = 13|24 ≠ 0̂);
  the correct form (same squarefree length) is in the proof of Hanlon's
  Lemma 4, and Lemma 7.1 is unaffected (`notes/prior_art_observation_cc.md`
  §2.2). The next bullet uses only the correct form.
- So μ(Π_n^w) = 0 iff x_w ≠ 0̂ or μ(o) = 0 for the common length o. In the
  second case Hanlon's Lemma 2 still applies: the type-b coatoms have prime
  period p | o. With Lemma 1, their meet with the type-a coatoms splits each
  o-cycle into j blocks, where j is the squarefree part of o, so x_w ≠ 0̂
  again. Hence **μ(Π_n^w) = 0 iff 0̂ is not a meet of coatoms.** This is our
  combination of the cited facts, and COMPUTED below (antichain, +w,
  41 pairs with n ≤ 7, 0 mismatches).
- **The elementary step (ours, not found stated).** If x := ⋀ coatoms ≠ 0̂,
  then x has no complement. A complement y has y ≠ 1̂, since x ∧ 1̂ = x ≠ 0̂.
  So y ≤ c for some coatom c, and x ≤ c too. Then x ∨ y ≤ c < 1̂. Dually, if
  the join of all atoms is not 1̂, it has no complement.

So, for the antichain with g = +w, TA-CR is KNOWN in substance, with the
uncomplemented witness x_w. [CVA]'s witness for this case is different
(cyc(w), or cyc(w^{o/p})).

### 2.3 Observation CC on all cones (COMPUTED, n ≤ 7)

`compute/prior_art_cr_v_type_a.py` imports the enumeration and lattice code
of `compute/cr_v_type_a.py`, so the pairs are the same 6,154 pairs (P, ±τ)
up to isomorphism. For each pair it tests CC: "0̂ is not the meet of the
coatoms of M, or 1̂ is not the join of the atoms of M".

| n | pairs | zeros | CC | CC with μ ≠ 0 | CC witness not uncomplemented | zeros without CC | CC sides: coatom meet only / atom join only / both |
|---|---|---|---|---|---|---|---|
| 3 | 14 | 5 | 5 | 0 | 0 | 0 | 0 / 0 / 5 |
| 4 | 50 | 22 | 22 | 0 | 0 | 0 | 0 / 0 / 22 |
| 5 | 174 | 99 | 99 | 0 | 0 | 0 | 4 / 3 / 92 |
| 6 | 866 | 481 | 481 | 0 | 0 | 0 | 64 / 3 / 414 |
| 7 | 5,050 | 2,912 | 2,912 | 0 | 0 | 0 | 558 / 36 / 2,318 |

The pair counts per n equal the sums of the "pairs +w" and "pairs −τ"
columns of [CVA] §4 (9 + 5, 34 + 16, 144 + 30, 758 + 108, 4,804 + 246), and
the total of zeros, 3,519, equals [CVA]'s.

- **Controls.** Π_4^{(1234)}, a 3-element chain: CC holds and μ = 0.
  Π_4: CC fails and μ = −6. The "CC with μ ≠ 0" column is EC1 Cor. 3.9.5
  checked on the data. The "witness" column checks §2.2's step on every CC
  pair.
- **Both sides are needed.** On 42 zeros only the atom-join side fires, and
  on 626 only the coatom-meet side fires.
- **Not a tautology.** CC is strictly stronger than "has an uncomplemented
  element" in general. EC1 Ex. 3.28 (Rival's lattice: a sub-meet-semilattice
  of B_6 with 1̂ adjoined) is atomic and coatomic but has the uncomplemented
  element {1, 2}.
- **Status.** First recorded here as a COMPUTED pattern for n ≤ 7 (not a
  claim of [CVA]). It is now PROVEN for every n: Theorem CC of
  `notes/observation_cc.md`, independently audited in
  `notes/audit_observation_cc.md` (every step HOLDS; the n ≤ 7 counts above
  are reproduced and n = 8 is added). Its Corollary U gives TA-CR's "only
  if" half again, with the uniform witnesses c ∧ D and O | Q, by a shorter
  route than table W.

A bug found while writing the script, kept for the record: the first
version treated the two-element lattice {0̂, 1̂} as having atom 0̂. It
reported 5 false "CC with μ ≠ 0" pairs at n = 3 and 5. After the fix (the
atom of {0̂, 1̂} is 1̂) all columns are as above.

## 3. Lemma C

### 3.1 What Hanlon has

- **Lemma 1** (stated without proof): if β ∈ Π_n^σ and an element of the
  cycle C_s lies in the block B_{i_0}, then some d | l_s and some distinct
  blocks B_{i_0}, …, B_{i_{d−1}} split C_s evenly, by the rule "m_{s,t} ∈ B_{i_r}
  iff u − t ≡ r mod (l_s/d)". This is the block-orbit structure used in
  [CVA] Lemma C, Steps 2 and 4.
- **Lemma 2**: the coatoms of Π_n^σ are of two types. Type (a) has two
  σ-stable blocks. Type (b) has p cyclically permuted blocks, with p a prime
  dividing gcd(l_1, …, l_m).
- **Lemma 6**: with all m cycles of length j, the hinge h = cyc(σ) has
  j^{m−1} complements c(f), f : [m−1] → [j]. "So c(f) is a complement to h
  in Π(N) hence c(f) will be a complement to h in L." The last paragraph
  shows every complement of h in 𝓜 is some c(f). It uses only h ∧ c = 0̂,
  h ∨ c = 1̂ and σ-invariance, but it is stated for 𝓜 and for equal lengths.

### 3.2 What is not there

[CVA] Lemma C with h = 1 and κ = 0̂ reads: cyc(σ) has a complement in Π_n^σ
iff all cycles of σ have one length. The "if" half is Hanlon's c(f). The
"only if" half is not stated by Hanlon or Stanley. Stanley gets the vanishing
from the coatom meet instead (§2.2). For h > 1, the orbit partitions of ⟨σ^h⟩
and the condition gcd(s, h) = 1 do not appear in any source read. Neither
does the relative version with x ≥ κ. The only gcds in Hanlon are of cycle
lengths (§0.3). So: **h = 1 existence KNOWN (Hanlon Lemma 6); the rest NOT
FOUND.**

## 4. Remarks for [CVA] (not applied)

- §1 S3 and the references: add Stanley 1982 §7 (Lemma 7.1 and the Remark)
  for the all-chambers +w case. That case of TA-CR follows from it by §2.2.
- Lemma C: credit the h = 1, κ = 0̂ existence half and the block-orbit
  structure (Steps 2 and 4) to Hanlon 1981, Lemmas 1 and 6.
- Observation CC (§2.3): done. Proven for every n in
  `notes/observation_cc.md` (Theorem CC), audited in
  `notes/audit_observation_cc.md`; every zero has an uncomplemented witness
  below ⋀ coatoms or above ⋁ atoms (c ∧ D or O | Q).
- Baclawski–Björner 1981, "Fixed points and complements in finite
  lattices", should be read by someone with access before any novelty claim
  for TA-CR is made (§0.4).
- No claim of [CVA] was found to be wrong.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 prior_art_cr_v_type_a.py --nmax 7 > output/prior_art_cr_v_type_a.txt   # ~45 s, ends "ALL CHECKS PASSED", exit 0
    python3 prior_art_cr_v_type_a.py --nmax 6                                       # ~1 s

The archived log is `compute/output/prior_art_cr_v_type_a.txt`.

References: [CVA] = `notes/cr_v_type_a.md`; [PAPCV] =
`notes/prior_art_per_cone_vanishing.md`; [VC] =
`notes/vanishing_criterion.md`; Hanlon, Stanley 1982, EC1, Kozlov, Wachs,
Knop, Farley as in §0.1.
