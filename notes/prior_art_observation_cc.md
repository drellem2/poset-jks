# Prior art for observation_cc.md (Theorem CC, Lemma CK, Prop. B, Cor. U)

This note checks four claims of `notes/observation_cc.md` ("[OCC]") against
the literature:
- **Theorem CC**: for every poset P on [n], n ≥ 3, and every g = ετ ∈ ±S_n
  with g C_P = C_P, μ(M) = 0 for M = OP(P)^τ iff 0̂ ≠ ⋀ coatoms of M (LOW)
  or 1̂ ≠ ⋁ atoms of M (HIGH).
- **Lemma CK**: every coatom x ≥ κ = comp(P) of M satisfies x ≥ D, where D
  is the partition into ⟨τ^r⟩-orbits of components and
  r = rad(gcd_K λ_K) ([OCC] calls this "Hanlon's Lemma 2, relative to κ").
- **Proposition B**: in row W−4 (g = −τ, (TA1)–(TA3) hold, odd points
  isolated, O ≠ ∅ ≠ Q), every atom of M is below Q | singletons or below
  O | singletons, so ⋁ atoms ≤ O | Q < 1̂.
- **Corollary U**: c ∧ D (when ≠ 0̂), and O | Q in row W−4, are
  uncomplemented elements of M.

Verdicts are used as in `notes/prior_art_cr_v_type_a.md` ("[PACVA]"):
- **KNOWN**: stated in a source read here, with the exact reference.
- **KNOWN IN SUBSTANCE**: follows from a stated result of a source read here
  by a step that the source does not write down but that needs no new idea.
  The step is named.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.
- **NOT ACCESSIBLE**: the source could not be opened. It is not counted as
  evidence either way.

## Verdict

| Claim of [OCC] | Verdict | Closest prior art (read) |
|---|---|---|
| **Theorem CC, "if"** (LOW or HIGH ⇒ μ(M) = 0) | **KNOWN.** EC1 Cor. 3.9.5, for every finite lattice. [OCC] cites it so | EC1 Cor. 3.9.5 |
| **Theorem CC, "only if", P = antichain, g = +w** (M = Π_n^w) | **KNOWN IN SUBSTANCE.** Stanley 1982, Lemma 7.1 and the Remark after it, read together with Hanlon 1981, Lemma 2 and the proof of Lemma 4 (§2.1). Stanley's Remark, read literally, says that the meet x_π of the coatoms of Π_n^π is 0̂ iff all cycles have one length. That is false for one cycle of length 4 (§2.2). The correct statement, x_π = orbit partition of π^j with j the squarefree part of the gcd of the cycle lengths, is in Hanlon's proof of Lemma 4. With it, μ(Π_n^w) = 0 iff x_w ≠ 0̂ follows from Lemma 7.1 | Stanley 1982 §7; Hanlon 1981 Lemmas 2, 4 |
| **Theorem CC, "only if", P = antichain, g = −τ** | **KNOWN IN SUBSTANCE**, by the same route: on the antichain, OP(P)^τ = Π_n^τ as a lattice, whatever the sign ([PACVA] Verdict) | as above |
| **Theorem CC, "only if", general P** | **NOT FOUND.** The converse of Cor. 3.9.5 is false for general finite lattices (Rival's lattice, EC1 Ex. 3.28, is atomic and coatomic; [PACVA] §2.3 and [PAPCV] §3.2 give complemented lattices with μ = 0). It is stated in the sources read only for distributive lattices (EC1 Ex. 3.9.6), geometric lattices (EC1 Ex. 3.100(a), where μ never vanishes and 0̂ is always a meet of coatoms) and Π_n^σ (previous rows). No source read treats OP(P) together with a group action, or any fixed sublattice under an anti-automorphism | EC1 §3.9, Ex. 3.28, 3.100; Hanlon 1981; Stanley 1982; Jenča–Sarkoci |
| **Theorem CC, the predicate c ∧ D ≠ 0̂ and Cor. X** (the zeros of χ_{C_P}(+w) are exactly the pairs with a cycle longer than rad(gcd_K λ_K)) | **NOT FOUND** for general P. For P = antichain, every λ_K is a cycle length, so this is Lemma 7.1 of Stanley 1982 in Hanlon's form (§2.1) | Stanley 1982 Lemma 7.1; Hanlon 1981 Lemma 4 |
| **Lemma CK** | **KNOWN IN SUBSTANCE.** The interval [κ, 1̂] of M is the set of τ-stable partitions ≥ κ (this uses [OCC]'s step S2: every τ-stable partition ≥ κ is acyclic, which is not in the literature but is proven in `notes/cr_v_type_a.md`). Under the standard isomorphism [κ, 1̂]_{Π_n} ≅ Π(blocks of κ), it is Π_k^{τ̄}, with τ̄ the permutation of the k components induced by τ; its cycle lengths are the λ_K. Hanlon's Lemma 2 classifies the coatoms of Π_k^{τ̄}, and the proof of his Lemma 4 states that "c_{i,k}, c_{i,k+j}, c_{i,k+2j}, …" (the ⟨σ^j⟩-orbits, j = rad gcd) "are in the same block of every coatom". Read on components, that is exactly "every coatom ≥ D". [OCC]'s own description ("Hanlon's Lemma 2 applied to the interval [κ, 1̂]") is accurate; the attribution should name Lemma 4's proof as well | Hanlon 1981 Lemma 2, proof of Lemma 4 |
| **Proposition B** | **NOT FOUND.** It is about atoms of the fixed lattice of an anti-automorphism τ, with odd and even cycles of τ treated differently. Hanlon has no statement about atoms of Π_n^σ (his atoms are those of the meet sublattice 𝓜, Lemma 12), and no source read treats anti-automorphisms of P (§0.3) | Hanlon 1981 Lemma 12 (atoms of 𝓜, not of L) |
| **Corollary U, the lattice step** (an element 0̂ ≠ z below every coatom, or 1̂ ≠ z above every atom, has no complement) | **NOT FOUND stated**, as in [PACVA] §2.2. It is one line. EC1 Ex. 3.28 ("give an example of a finite atomic and coatomic lattice that is not complemented") presupposes the contrapositive (complemented ⇒ atomic and coatomic) without stating it. Björner 1981 (Discrete Math. 36) is the likely place for a statement and was NOT ACCESSIBLE | EC1 Ex. 3.28; [PACVA] §2.2 |
| **Corollary U, the witnesses** c ∧ D and O \| Q | **NOT FOUND.** For P = antichain and g = +w, c ∧ D is cyc(w) ∧ (orbits of w^r) = orbits of w^r = Hanlon's x_w (D is the orbit partition of w^r there, and it refines cyc(w)), so the witness is Hanlon's meet of coatoms in that case. Elsewhere: not found | Hanlon 1981 Lemma 4 (antichain only) |

**Bottom line.**
- The "if" half of Theorem CC is EC1 Cor. 3.9.5 (KNOWN). The "only if"
  half is KNOWN IN SUBSTANCE for the antichain (Hanlon plus Stanley, with
  the corrected reading of Stanley's Remark) and NOT FOUND for any other P.
- Lemma CK is Hanlon's coatom classification (Lemma 2) together with the
  orbit statement in the proof of his Lemma 4, transported to the interval
  [κ, 1̂] ≅ Π_k^{τ̄}: KNOWN IN SUBSTANCE, given step S2.
- Proposition B and the witnesses of Corollary U outside the antichain
  case: NOT FOUND in the sources of §0.
- Side finding: Stanley's Remark after Lemma 7.1, read literally, has the
  counterexample σ = (1234) (§2.2). Lemma 7.1 itself is unaffected.

---

## 0. Sources

### 0.1 Read

PDFs were fetched with `curl` and converted with `pdftotext -layout`, then
grepped. The listed parts were read in full.

| Source | Obtained from | What was read |
|---|---|---|
| Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981) 319–341 | msp.org, `pjm/1981/96-2/pjm-v96-n2-p04-s.pdf` | Abstract; §1; Lemma 2 and its proof and the count of type-a/type-b coatoms; Lemma 3; Lemma 4 and its proof; Lemma 5; the statement of Lemma 6; the statement of Lemma 12 |
| Stanley, *Some aspects of groups acting on finite posets*, J. Combin. Theory Ser. A 32 (1982) 132–161 | math.mit.edu/~rstan/pubs/pubfiles/50.pdf | §7 opening, Lemma 7.1 and the Remark after it |
| Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., author's online version ("EC1") | math.mit.edu/~rstan/ec/ec1.pdf | §3.4, the list of equivalent conditions after FTFDL (boolean ⇔ complemented ⇔ atomic ⇔ 1̂ a join of atoms, for finite distributive L); Cor. 3.9.4–3.9.5 and the paragraph before them; Example 3.9.6; Exercises 3.28, 3.92, 3.100 and the solutions of 3.28 and 3.100(a) |
| Jenča, Sarkoci, *Linear extensions and order-preserving poset partitions* (the lattice of order congruences of a finite poset) | arXiv:1112.5782 | Abstract, introduction, definitions; grep for automorphisms and fixed points (§0.3) |
| Sagan, Sundaram, *Ordered set partition posets* | arXiv:2506.23355 (v3) | Abstract; grep for coatoms, fixed points, automorphisms and Hanlon (§0.3) |
| Kozlov, *Order complexes of noncomplemented lattices are nonevasive*, Proc. AMS 126 (1998) | arXiv:math/9704225 | §1 and the proof (cases on atoms and coatoms comparable to x) |
| Farley, *A conjecture of Kozlov …* | arXiv:2201.01491 | Final section and references |

The sources of [PACVA] §0.1 (Wachs, Knop) were not reread; they are cited
only through [PACVA].

### 0.2 Web searches

- Björner "On complements in lattices of finite length" complement join of
  atoms meet of coatoms;
- fixed point sublattice partition lattice Möbius function zero meet of
  coatoms automorphism poset Sundaram Hopf trace fixed-point (extended);
- lattice of order-preserving partitions poset automorphism fixed sublattice
  Möbius function coatoms;
- "complements in lattices of finite length" Björner abstract "join of
  atoms" (extended);
- Möbius function vanishes "meet of coatoms" fixed points group action
  lattice characterization iff partition lattice.

None returned a characterization "μ = 0 iff 0̂ not a meet of coatoms or 1̂
not a join of atoms" for a class of fixed sublattices other than Π_n^σ, a
fixed-point statement for OP(P) or for order congruences, or a statement
about atoms of fixed lattices of anti-automorphisms. They returned, among
others: Hanlon 1981; Sagan–Sundaram (ordered set partitions with restricted
block sizes, no fixed sublattices); Jenča–Sarkoci (no group action); the
normal-subgroup analogue (μ vanishes unless the bottom is an intersection of
maximal normal subgroups, a modular lattice, secondary via a search
summary, not read); and a semimodular statement attributed to Stern
(complemented semimodular of finite length ⇒ every element a meet of
coatoms; secondary, not read).

### 0.3 Greps, with positive controls

Counts are lines, case-insensitive, on the `pdftotext` output.

| Text | Negative term → count | Positive control (same instrument) → count |
|---|---|---|
| Hanlon | "anti-automorph / antiautomorph / order-revers" → 0 | same pattern in EC1 → 12 |
| Hanlon | "acyclic" → 0 | "acyclic" in Jenča–Sarkoci → 12; "coatom" in Hanlon → 32 |
| Hanlon | atoms of L itself: every "atom(s)" hit (lines 29, 74, 156, 228, 612–622) is about 𝓜, its geometry G, or the title of §2 on coatoms | "coatom" → 32 |
| Stanley 1982 | anti pattern → 0; "acyclic" → 0 | "coatom" → 2 (the Remark); "fixed" → 12 |
| Jenča–Sarkoci | anti pattern → 0; "coatom" → 0; "automorph" → 0 | "acyclic" → 12 |
| Sagan–Sundaram | anti pattern → 0; "coatom" → 1 (recursive coatom ordering, BW83) | "automorph" → several (group of automorphisms of P, §§2–4); "Hanlon" → 5 |

### 0.4 NOT ACCESSIBLE

- **Björner, *On complements in lattices of finite length*, Discrete Math.
  36 (1981) 325–326.** ScienceDirect returned 403. Its title and the
  secondary mentions (Kozlov §1; a search summary attributing to Björner
  "finite relatively complemented lattices are atomic") make it the most
  likely place for an explicit form of Corollary U's lattice step.
- **Baclawski–Björner 1979 and 1981**, **Björner, JCTA 30 (1981)**: as in
  [PACVA] §0.4.
- **Sundaram, *Applications of the Hopf trace formula to computing homology
  representations* (1994)**: not obtained. It computes homology
  representations of subposets of Π_n through fixed-point subposets; a
  reader with access should check it for fixed sublattices of subposets of
  Π_n that contain OP(P) as a special case.

## 1. Theorem CC, "if"

EC1 Cor. 3.9.5: "If L is a finite lattice for which 0̂ is not a meet of
coatoms, then µ(0̂, 1̂) = 0. Dually, if 1̂ is not a join of atoms, then again
µ(0̂, 1̂) = 0." M is a finite lattice ([OCC] S2), so this applies directly.
KNOWN.

## 2. Theorem CC, "only if", and Lemma CK

### 2.1 The antichain

For P the antichain on [n], OP(P)^τ = Π_n^τ. The relevant statements:
- **Hanlon, Lemma 2**: the coatoms of L = Π(N)^σ are (a) two σ-stable
  blocks, or (b) p blocks cyclically permuted by σ, p a prime dividing
  gcd(l_1, …, l_m), each cycle divided evenly among the blocks.
- **Hanlon, proof of Lemma 4**: with j the product of the distinct primes
  dividing gcd(l_1, …, l_m), "c_{1,1}, c_{1,1+j}, c_{1,1+2j}, … are in the
  same block of every coatom in L, and hence they are in the same block of
  every partition in 𝓜. The same is true of c_{i,k}, c_{i,k+j}, c_{i,k+2j},
  … as i ranges from 1 to m and k ranges from 1 to j." So the meet x_σ of
  the coatoms is ≥ the orbit partition of σ^j. Lemma 5 ([0̂_𝓜, h] ≅ D_j,
  with τ(j) the bottom of 𝓜 realized as a meet of coatoms) gives equality.
- **Stanley 1982, Lemma 7.1**: μ(Π_n^π) = (−1)^{d−1} μ(n/d)(d−1)!(n/d)^{d−1}
  if π is a product of d cycles of length n/d, and 0 otherwise.

Together: μ(Π_n^σ) ≠ 0 iff all cycles have one squarefree length j iff the
orbit partition of σ^j is 0̂ iff x_σ = 0̂. That is the "only if" of
Theorem CC for the antichain (LOW alone suffices there). This is the
combination [PACVA] §2.2 already made; it is COMPUTED again below, without
using any code of the repository other than this note's script.

Lemma CK is the same orbit statement one level up. [κ, 1̂] in Π_n is
isomorphic to Π(blocks of κ) by the standard map, and the map commutes with
τ. Its τ-fixed part is Π_k^{τ̄}, whose cycle lengths are the λ_K, so Hanlon's
j becomes r = rad(gcd λ_K), and the orbit partition of τ̄^r pulls back to D.
The only input not in the literature is that this fixed part lies in M,
i.e. that every τ-stable partition ≥ κ is acyclic ([OCC] S2, proven in
`notes/cr_v_type_a.md`). [OCC]'s self-contained proof of CK reproves
Hanlon's Lemma 2 argument (merging an orbit, or merging blocks mod a proper
divisor) on components.

### 2.2 Stanley's Remark, read literally

Stanley's Remark: "x_π = 0̂ if and only if all cycles of π have the same
length". For σ = (1234), Π_4^σ = {0̂, 13|24, 1̂} (a 3-element chain), its
only coatom is 13|24, so x_σ = 13|24 ≠ 0̂, though σ has one cycle. Hanlon's
j is the squarefree part, so the correct condition is "all cycles have the
same squarefree length". Lemma 7.1 is unaffected (μ(4) = 0). COMPUTED
(§3): for n ≤ 8 the literal reading fails exactly on the cycle types (4),
(8), (4,4), all equal lengths with a non-squarefree length, and Hanlon's
form holds on all 66 cycle types.

### 2.3 General P

No source read gives a converse of Cor. 3.9.5 for a class containing the
lattices OP(P)^τ. The known converses read here: distributive lattices
(EC1 §3.4, the list after FTFDL, with Ex. 3.9.6: μ(I, I′) ≠ 0 iff [I, I′] is boolean),
geometric lattices (EC1 Ex. 3.100: μ never vanishes and every element is a
meet of coatoms), and Π_n^σ (§2.1). OP(P)^τ is none of these in general:
it contains Π_n^σ (P antichain) and is not modular already for Π_4
([PACVA] §2.1). So the "only if" half for general P is NOT FOUND. The
reduction of [OCC] goes through the arithmetic predicate c ∧ D ≠ 0̂
(Prop. Z±, Cor. X), which uses the components of P; nothing in the sources
read involves components of a poset together with an automorphism.

## 3. Computation (standalone)

`compute/prior_art_observation_cc.py` builds Π_n^σ from scratch for one σ of
each cycle type, n ≤ 8 (it imports nothing from the repository), and
checks:
- **[H4]** x_σ (the meet of all coatoms) equals the orbit partition of σ^r,
  r = rad(gcd of cycle lengths): Hanlon, proof of Lemma 4; Lemma CK for
  κ = 0̂. 0 failures on 66 cycle types.
- **[S71]** μ(Π_n^σ) = 0 iff x_σ ≠ 0̂. 0 failures.
- **[LIT]** Stanley's literal Remark: fails on (4), (8), (4,4) only.

Controls, all passing:
- Π_4^{(1234)}: a 3-element chain, μ = 0, x ≠ 0̂. Π_4: μ = −6, x = 0̂.
- Injected fault: with r replaced by 1 (cycle partition instead of the
  orbit partition of σ^r), [H4] fails on 15 cycle types, so the comparison
  can fire.
- [LIT] fires (3 failures), so the "iff" comparison against a wrong
  statement is detected.

## 4. Remarks for [OCC] (not applied)

- Lemma CK: cite Hanlon 1981, Lemma 2 **and the proof of Lemma 4** (the
  orbit statement), via [κ, 1̂] ≅ Π_k^{τ̄}. The current wording ("Hanlon's
  Lemma 2, relative to κ") is accurate but Lemma 2 alone gives only the
  coatom types; the step "p | every λ_K ⇒ D-blocks stay in a block" is the
  one Hanlon writes in Lemma 4's proof.
- Theorem CC: record that the antichain case is Hanlon–Stanley (§2.1), and
  that Cor. X for +w on the antichain is Stanley's Lemma 7.1 in Hanlon's
  form. Note the literal reading of Stanley's Remark (§2.2) if it is quoted.
- Corollary U: the witness c ∧ D equals Hanlon's x_w on the antichain with
  g = +w.
- No claim of [OCC] was found to be wrong.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 prior_art_observation_cc.py --nmax 8 > output/prior_art_observation_cc.txt   # ~20 s, ends "ALL CHECKS PASSED", exit 0
    python3 prior_art_observation_cc.py --nmax 7                                          # < 1 s

The archived log is `compute/output/prior_art_observation_cc.txt`. The
sources of §0.1 were fetched with `curl -sL -o <file>.pdf <url>` and
converted with `pdftotext -layout`; the counts of §0.3 are `grep -ci` on
those text files.

References: [OCC] = `notes/observation_cc.md`; [PACVA] =
`notes/prior_art_cr_v_type_a.md`; [PAPCV] =
`notes/prior_art_per_cone_vanishing.md`; Hanlon 1981, Stanley 1982, EC1,
Jenča–Sarkoci, Sagan–Sundaram, Kozlov 1998, Farley as in §0.1.
