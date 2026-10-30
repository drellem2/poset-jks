# Fidelity audit of `notes/poset_jks_theorem.tex` against the audited sources

Work item: mg-87d65. Subject: `notes/poset_jks_theorem.tex` (the "write-up"),
merged in 477fa24 (mg-22462). The write-up restates results from the notes
files below and their audits. This audit checks each restatement against its
source, including hypotheses, quantifiers and the epistemic status attached to
it. It also checks the one new deduction in the write-up, the prime-degree
corollary, from scratch. Finally it checks the computational-record table
against `compute/output/` and the bibliography against
`notes/literature_novelty_jks_maps.md` §5.

Grades:
- **MATCHES**: the statement, its hypotheses and its status agree with the
  source and its audit.
- **DRIFTED**: it differs from the source in some way, with details given.
- **NEW-UNAUDITED**: it has no source statement and no audit.
- **STALE**: it was accurate when written and has since been overtaken by a
  later merge.

Tags on this file's own claims: PROVEN (proof given here), COMPUTED (command
given), CITED. Source abbreviations are the write-up's own ([Glob], [FPM],
[AudChar], [Lit], [AudLit], [S], [AudS], [Cone], [Bn], [AudBn], [Repro],
[N7]). [AudCone] is `notes/audit_cone_lune_lie_theory.md` (0ef7274, mg-52a16).
That audit merged *after* the write-up.

## Verdict

- **Nothing is presented as audited when it is not.** Every \st{audited} tag
  in the write-up traces to a verdict of CONFIRMED or PROOF HOLDS in an audit
  file. The places where the write-up's status differs from the sources
  *understate* the status (rows 9, 26 and 49).
- **No sign or quantifier error in any restated theorem.** The re-derived
  Proof I (§3) agrees step by step with [Glob, §2] and with [AudChar, I1–I11],
  and it writes in the two expository slips of [AudChar, §2] correctly.
- **The prime-degree corollary (`cor:prime`) is correct for odd
  primes p** (PROVEN below, two ways). As stated ("for p prime") it also covers
  p = 2, which lies outside the n ≥ 3 range of the main theorem that the proof
  goes through. The formula does hold at p = 2 (checked here by hand), but not
  by the cited chain of results. Reported, not changed (row 51).
- **Cone/lune remark (row 44): DRIFTED and STALE.** It drops the hypothesis
  "essential" from the pointed-cone theorem. [AudCone] flags this as an
  overstatement in [Cone] itself, and the write-up inherited it. The remark
  also says the [Cone] results have not been audited, which was true when
  written. [AudCone] has since audited them. The same staleness affects open
  problem 4 and the computational table, which has no row for
  `audit_cone_lune.py`. Reported, not changed, because the ticket requires
  this remark to say unaudited and because updating it is a status change.
- **Computational table: numbers match the archived outputs.** One clerical
  fix: the n = 4, 5 homology runs are not archived. Two rows point to scripts
  with no archived output (§4).
- **Bibliography: matches the corrections of [Lit, §5].** This includes the
  Klyachko DOI 10.1007/BF00966559 and pages 914–920. One clerical fix: the
  `AguiarMahajan` entry was never `\cite`d.
- **Build: not run.** `./build.sh` found no TeX toolchain on this host
  (`build.sh: no TeX toolchain (latexmk/pdflatex) found; skipping`). As a
  substitute, a script checked that every `\ref`/`\eqref` has a `\label`,
  every `\cite` has a `\bibitem`, environments are balanced, and braces
  balance. This is not a LaTeX compile.

## 1. Statement-by-statement table

Line numbers refer to `notes/poset_jks_theorem.tex` after this item's three
clerical edits. Those edits do not change the line count.

| # | Write-up statement (line) | Source / audit | Grade | Details |
|---|---|---|---|---|
| 1 | Status-tag definitions, §1 (66–77) | — | MATCHES (after fix F1) | The "computed" tag said the reproduce command was in §`sec:computations`, but that section only says the commands are in `compute/README.md`. Fixed (F1). |
| 2 | Cited input (A), Jenča–Sarkoci Thm 4.5, no connectivity hypothesis (145–151) | [Lit §2.1–2.2], [AudChar S6], [FPM §1] | MATCHES | Same theorem number and arXiv v2 caveat. The order-congruence identification is flagged UNCHECKED in [AudChar S6], and open problem 5 records this. |
| 3 | Cited input (B), P. Hall, EC1 Prop. 3.8.5 "number not re-checked" (152–155) | [FPM §1] | MATCHES | |
| 4 | Cited input (C), Hopf trace formula, Munkres Thm 22.1 (156–162) | [FPM §1] | MATCHES | |
| 5 | Crapo used only by Proof II (163–164) | [AudChar II1, R4] | MATCHES | |
| 6 | **Theorem `thm:main`** (168–188): (characterconj) for n ≥ 3; (mainconj); closed formula with F(P,g) | [Glob Thm 2.8, Prop 2.5, 2.7], [FPM Thm], [AudChar verdict, R1] | MATCHES | Hypotheses (A)–(C), n ≥ 3, abstract isomorphism, μ(o), and "F empty unless ⟨g⟩ free on components" all agree. [AudChar] states the closed formula with the same sign. |
| 7 | Status of thm:main (190–196): proven, audited; (characterconj) computed for all posets n ≤ 7; closed formula checked through n = 10 examples | [AudChar], [Repro], [N7], `audit_character_identity_n10.txt` | MATCHES | n ≤ 6: [Repro] (758 pairs at n = 6) and [AudChar] check A. n = 7: `n7_summary.txt` (2045 posets, 4804 pairs, 0 failures). n = 10: one family, 9 pairs, non-identity classes only. |
| 8 | Remark `rem:abstract`, abstract vs natural isomorphism (198–207) | [AudChar §5 (i)–(ii)] | MATCHES | |
| 9 | Lemma `lem:homchar` (216–233) | [AudChar S5], [FPM §1] | MATCHES | Tagged proven, not audited. S5 is CONFIRMED, so this understates. |
| 10 | Lemma `lem:liechar` (235–249) | [AudChar S1] | MATCHES | Same convention (gw)_i = g(w_i), (wγ^r)_i = w_{i+r}. |
| 11 | Remark on ζ conventions (251–256) | [AudChar S2] | MATCHES | |
| 12 | Lemma `lem:orbitquot` (266–277) | [Glob L2.1], [AudChar I1] | MATCHES | |
| 13 | Lemma `lem:lattice` (i)–(iv) (279–313) | [Glob L2.2], [AudChar I2–I4] | MATCHES | |
| 14 | Lemma `lem:weisner` (315–328) | [Glob L2.3], [AudChar I5] | MATCHES | The EC1 Cor. 3.9.3 number is listed as unchecked in open problem 5, as in [Glob]. |
| 15 | Lemma `lem:interval` (334–354) | [Glob L2.4], [AudChar I6, S8] | MATCHES | |
| 16 | Lemma `lem:small` (base case, n ≤ 2) (361–375) | [AudChar S7, slip (a)] | MATCHES | This is the hand computation that [AudChar §2(a)] asked to be written in. Values re-checked here: \|Q\| = 1 gives μ = 1 and M̃ = (−1)^{−2} = 1; \|Q\| = 2 gives μ = −1 and M̃ = (−1)^{−1}(−1) = 1; e_C = 1 in both cases. |
| 17 | Prop. `prop:Mside` (377–448) | [Glob Prop 2.5], [AudChar I7–I11, slip (b)] | MATCHES | Recursion (W), the bijection of I7, the inversion, "which x contribute" (now argued as m \| o, as [AudChar §2(b)] suggested), and μ_X(x, 1̂) = μ(o) all agree. The inversion direction f(1̂) = Σ_x μ_X(x,1̂)Φ(x) is correct. |
| 18 | Lemma `lem:rot` (452–462) | [FPM L6a], [Glob L2.6] | MATCHES | |
| 19 | Prop. `prop:Lside` (464–534) | [Glob Prop 2.7], [AudChar S3–S4] | MATCHES | Checked here: q = (r/k)^{−1} mod o; gW = Wγ^{kq^{−1}} (piece j goes to piece j + q^{−1} at the same offset); the weight \|K(w)\|/o = \|K_{B_0}(u)\|. |
| 20 | Proof of thm:main (536–545) | [Glob Thm 2.8] | MATCHES | |
| 21 | Remark `rem:proofII` (547–574): Proof II via Crapo; proven given (A)–(C) + Crapo; audited | [FPM Props 4–6, L2], [AudChar II1–II8, §3, R4] | MATCHES | The case split (unequal lengths / type d^k with k ≥ 2), the antichain z^⊥ = {y_T}, and N_r = Σ_T e_C(T) iff gcd(n,r) = k all agree. The Björner–Walker strengthening is correctly tagged cited and not needed. |
| 22 | Cor. `cor:connected` (578–590): μ(OP(P)^g) = 0 for g ≠ 1; free of rank \|Lin P\|/\|Aut P\|; proven, audited | [Glob §3.1], [FPM Cor 7], [AudChar II7] | MATCHES | II7 audits the vanishing. Freeness follows from it in two lines, both re-derived in the proof. |
| 23 | Paragraph after cor:connected: ordinal sums, products, crowns, substitutions (592–595) | [Glob §3.1], [FPM §6.3] | MATCHES | |
| 24 | Cor. `cor:examples` (a) antichain (600–605) | [FPM §6.1] | MATCHES | The Stanley/Hanlon attribution is "from memory" in [FPM]. The write-up records this in the note after the bibliography. |
| 25 | Cor. `cor:examples` (b), three 2-chains, χ = −1, also computed (606–609) | [FPM §6.2], `n6_homology_discriminating.txt` | MATCHES | The archived homology line `3x2chain … g=(1 3 5)(2 4 6) … trace_H=-1` confirms the computed claim. |
| 26 | Cor. `cor:examples` (c), m equal chains, χ = (−1)^{(m−1)ℓ}μ(m) (610–611) | [FPM §6.2], [AudChar II8] | MATCHES | Chains are rigid, which [FPM] needs. Tagged proven. It is also audited (II8), so this understates. |
| 27 | Cor. `cor:eC`, e_C over components; proven; computed for all 405 posets n ≤ 6; not independently audited (615–620) | [Glob §3.3] | MATCHES | 405 = 1+2+5+16+63+318. (−1)^{\|π\|−1}(\|π\|−1)! = μ_Π(π, 1̂). [AudChar] covered only [Glob §2], so "not audited" is correct. |
| 28 | §4 setup: seed note's J and (restrictionlemma), "second formulation", (homembed) (625–640) | [AudLit §1.1], seed §§"Embedding…", "A second formulation…", "Potential proof via splitting spheres" | MATCHES | The section and lemma titles exist in the seed note. |
| 29 | Lemma `lem:op` (Lemma B); proven, audited (642–650) | [Lit §3.3], [AudLit row 1] | MATCHES | |
| 30 | Prop. `prop:C`; proven, audited (652–666) | [Lit §3.3], [AudLit rows 2–3] | MATCHES | The quantifiers are the seed note's: one J for all P ([AudLit §1.1]). |
| 31 | Prop. `prop:Cprime` (C′): proven given the signed relation for 1 ш 2⋯n; that relation is computed n ≤ 6 and cited for all n (674–693) | [AudLit §1.2] | MATCHES (provenance note) | Statement, hypothesis and proof agree with [AudLit §1.2]. Note that C′ *originates in* an audit file. No second audit has re-checked it. The write-up does not claim one, so this is not a drift. I re-derived step 5 here: the identity word arises only from u = id (j = 0) and u = γ (j = n−1), so its coefficient is (1+ζ)/n. |
| 32 | Remark "Variants" (695–713) | [AudLit §1.2–1.4, rows 8, 30] | MATCHES | Each of the four bullets matches, including "κ_n P-dependent version computed only n ≤ 5". The phrase "so it is true by Theorem thm:main" is a one-line consequence of [AudLit §1.3]'s equivalence and is correct. |
| 33 | Paragraph "What replaces (restrictionlemma)" (715–721) | [Lit §3.4 (S1)], [AudLit rows 9, 16] | MATCHES (wording loose) | "…which is Theorem `thm:S` below" is shorthand. The identity Φ(H_P⊗sgn) = (W_P+Sh_n)/Sh_n is Theorem S(c) *combined with* Prop. Φ, and so inherits S(c)'s conditional status ([AudLit row 16]: "given Conjecture S"). Not changed: rewording would touch the mathematical claim. |
| 34 | §5 definitions: Π_w, ρ_w with Wachs's normalisation, Sh_n, W_P (728–735) | [AudLit §2.1, §5 row "Prop. 2.3"] | MATCHES | |
| 35 | Prop. `prop:Phi` and its status (737–757): cited for general n (Wachs Lemma 3.1, Thms 4.2–4.3, preprint) + Ree; computed and proven for n ≤ 6; Φ(⇒) from Φ(⇐) by counting | [Lit §3.2], [AudLit rows 10–12, §2], [AudS §C.1] | MATCHES | |
| 36 | Lemma `lem:D`; proven, audited (759–769) | [Lit §3.4], [AudLit row 13] | MATCHES | |
| 37 | Definitions of base component, union-prefix, blocks, B_P, R_P (773–781) | [S §3, §5] | MATCHES | |
| 38 | **Theorem `thm:S`** (a)–(d) (783–799) | [S Thms A, B, C, Cor 5.5, Cor A′, Lemma 4], [AudS rows 7–16] | MATCHES | (a) also bundles Lemma 4 (\|B_P\| = e_C) and Cor. A′ (connected: W_P ∩ Sh_n = 0). Both are in [S] and audited. (c) and (d) carry n ≥ 3 as in [S]. |
| 39 | Status list for thm:S (801–817) | [AudS verdict, §C.1, §C.2] | MATCHES | The dependency map agrees with [AudS §C.1] row by row: (a),(b) need no Φ or JS; (c) basis needs Φ(⇒), D, JS; the kernel statement also needs Φ(⇐) on R_P generators; (d) needs (c) + Φ(⇐) on R_P generators. The chain-level check for 3 ≤ n ≤ 6 matches `audit_conjecture_s.txt` ("[CHN] chain level (no Phi, no J-S) for 402 posets"). |
| 40 | "Key tool" paragraph, E_{a,x} and Lemma 1 (819–825) | [S Lemma 1], [AudS rows 1–2, §B.1] | MATCHES | Sign: x immediately before a gives +, as in [AudS §B.1]. |
| 41 | Proof sketch of thm:S(a); deductions of (b), (c) (827–845) | [S §4–5], [AudS §B.3–B.4] | MATCHES | |
| 42 | Remark "Relation to thm:main" (847–857) | [S §6], [AudLit row 19], [AudS row 17] | MATCHES (status implicit) | "a second, independent proof of (mainconj)" for connected P is conditional on Φ(⇒) and JS, through Theorem S(c). The status list 15 lines earlier states that dependency; this remark does not repeat it. "Independent" is in the sense of [S §6]: independent of the character-identity proof. JS is shared. |
| 43 | Remark "Novelty of thm:S" (859–865) | [AudS §F], [S §7] | MATCHES | |
| 44 | **Remark "Cone/lune form; not audited"** (867–883) | [Cone Thm 4.1, Lemma E, Thm 5.2, Conj. G, §7], [AudCone] | **DRIFTED + STALE** | (i) **Hypothesis dropped:** "for every real central arrangement, … chambers of a *pointed* top-cone are linearly independent modulo top-lunes". [AudCone row 8, row 9, §B.5]: the theorem holds for *essential* arrangements. Without essentiality, "pointed" (lin V = 0) never holds, so the statement is vacuous. The [Cone] section headings carry the same overstatement, and [AudCone] grades it OVERSTATED. The repair is "essential", or "pointed" read as lin V = ∩A. (ii) **Stale status:** "have *not* been independently audited". [AudCone] (0ef7274) now audits [Cone]: Lemma E and Thm 5.2 are CONFIRMED (essential A), the corrected Ex. 10.9 is CONFIRMED, and Thm 4.1(c) is OVERSTATED (label only) because it is Theorem S(c), conditional on Φ, D, JS. The remark's "These results are proven in [Cone]" inherits that unconditional label for the (c) half. (iii) The rest matches: Γ_{C_P} ∩ Lune = span of lunes in C_P is [Cone Thm 4.1(a)] = Theorem S(b) ([AudCone row 11]); Conjecture G is conjectured and computed on A_2–A_4, B_2, B_3 and samples; the Ex. 10.9 correction "non-singleton → non-pointed" is [AudCone row 16]. **Not changed:** the ticket requires the remark to say unaudited, and updating it is a status change. Suggested replacement is in §3. |
| 45 | §6 setup: HH_n, V_n, B_n via rotations L_c, a_n, A(x) (887–893) | [Bn §1], [AudBn §A] | MATCHES | |
| 46 | Prop. `prop:Ind`, V_n ≅ Ind(ζ⊗C[B_n]); proven unconditionally; audited by a second read (895–911) | [AudBn §A, §C] | MATCHES | §A is itself an audit-authored proof. §C is its independent second read, verdict CONFIRMED. |
| 47 | Cor. `cor:globalind`; proven, audited (913–926) | [Glob §1(a)], [AudChar R3], [AudBn §C] | MATCHES | R3 confirmed the HH_n ≅ sgn⊗V_n half. [AudBn §C] confirmed the V_n ≅ Ind half and the orbit argument. |
| 48 | Theorem `thm:bn`, b_n = n[x^n] log A and the recurrence; proven, audited (928–945) | [Bn §3], [AudBn rows 4–11] | MATCHES | |
| 49 | Prop. `prop:frob` (a)–(d) and its status (947–967) | [Bn Props 1–3], [AudBn rows 12–18], [Glob §1(b)] | MATCHES (d understated) | (a)–(c) agree, and (c) is labelled the untwisted series as in [AudBn row 18]. For (d) the write-up says "no separate audit". In fact [AudBn row 18] CONFIRMED the sign rule "⊗ sgn multiplies the d-term by (−1)^{n−n/d}", which is the (d) Frobenius formula given (globalind). Only the twisted generating function Σ_d (μ(d)/d) log A((−1)^{d−1}p_d) is unaudited. This understates, which is the safe direction. |
| 50 | Paragraph after prop:frob: (d) computed by direct homology for n ≤ 6; class (6): −1 vs +1; class (2,2,2): +128 vs −128 (969–974) | [Glob §1(c)] | MATCHES | |
| 51 | **Cor. `cor:prime`, prime degree** (976–992) | none (new deduction); [Bn §4], [AudBn row 16] for the conditional version | **NEW-UNAUDITED; checked here; hypothesis issue at p = 2** | The deduction is correct for every **odd** prime (PROVEN, §2). At p = 2 the proof cites Cor. `cor:globalind`, which rests on thm:main (n ≥ 3), so the cited chain does not cover p = 2. The identity is true at p = 2 by direct check (§2), with the convention H_P = H̃_{−1}(∅) = C. Suggested fix: say "odd prime p", or add the one-line p = 2 check. Not changed (a hypothesis). The numbers are right: (16−1)/3 = 5 and (1561−1)/5 = 312; dimensions 5·6+2 = 32 and 312·120+24 = 37464 = (n−1)! b_n. The note after it ("[Bn §4] had recorded this as conditional on (globalind)") matches [Bn §4] and [AudBn row 16]. |
| 52 | Remark "Why a plethystic logarithm; not independently audited" (998–1014) | [Glob §4] | MATCHES | Computed n ≤ 4, primitives not P-homogeneous at n = 2, CMM/PBW cited with numbers unchecked: all as in [Glob §4.2–4.3]. |
| 53 | §7 computational table and its notes (1016–1070) | `compute/output/*` | MATCHES (after fix F2), with notes | See §4. |
| 54 | §8 open problems 1–3, 5–7 (1074–1137) | [AudChar §5], [Glob §3.4, §4.3], [AudS §E.4], [AudLit rows 8, 24, 28–30, §5], [Lit §1], [AudS §F] | MATCHES | |
| 55 | §8 open problem 4: "The results of [Cone] themselves still await an independent audit" (1102–1104) | [AudCone] | STALE | [AudCone] (0ef7274) is that audit. Not changed (same reason as row 44). |
| 56 | Abstract (45–60) | — | MATCHES | "proved, conditional on a cited theorem of Wachs" for the basis matches row 39. |

## 2. The prime-degree corollary, checked from scratch (PROVEN)

**Claim.** For p prime, HH_p ≅ ((b_p−1)/p)·C[S_p] ⊕ (sgn ⊗ Lie_p).

**Proof for odd p.**
1. By Cor. `cor:globalind` (thm:main, which needs n = p ≥ 3),
   HH_p ≅ sgn ⊗ Ind_{C_p}^{S_p}(ζ ⊗ C[B_p]). Here γ^j acts on the fibre by
   ζ^j times relabelling ([AudBn §A]).
2. C_p has prime order, so every orbit on B_p is either a fixed point or
   free. By Prop. `prop:frob`(b) (= [Bn Prop 2(b)], [AudBn row 14]) the
   antichain is the only γ-fixed poset. A fixed point of γ^k with
   0 < k < p is a fixed point of γ, since ⟨γ^k⟩ = C_p. So
   C[B_p] ≅ triv ⊕ ((b_p−1)/p)·C[C_p] as a permutation module, and
   ζ ⊗ C[B_p] ≅ ζ ⊕ ((b_p−1)/p)·(ζ ⊗ C[C_p]).
3. ζ ⊗ C[C_p] ≅ C[C_p], because a regular representation tensored with a
   character is regular. So Ind_{C_p}^{S_p} of it is C[S_p].
4. Ind_{C_p}^{S_p} ζ ≅ Lie_p, by Klyachko (CITED, the write-up's `\cite{Klyachko}`).
5. Tensor with sgn: sgn ⊗ C[S_p] ≅ C[S_p]. ∎

The write-up's proof follows exactly these steps. It leaves step 2's
"every non-fixed orbit is free, since p is prime" implicit. That is not a gap.

**Cross-check against (frob) (PROVEN).** For odd p, (frob) gives
ch HH_p = (1/p)(b_p p_1^p + (−1)^{p−1}μ(p) b_1 p_p) = (b_p p_1^p − p_p)/p.
On the right-hand side, ch C[S_p] = p_1^p and ch Lie_p = (p_1^p − p_p)/p.
Applying ω fixes both p_1^p and p_p (since (−1)^{p−1} = 1). So the right-hand
side is ((b_p−1)/p) p_1^p + (p_1^p − p_p)/p = (b_p p_1^p − p_p)/p. The two
sides agree.

**p = 2.** The write-up's proof routes through thm:main, which assumes
n ≥ 3, so it does not prove the case p = 2. A direct check: the posets on
[2] are the antichain and the two chains, and H_P = H̃_{−1}(∅) = C for each,
with every automorphism acting trivially. The swap fixes the antichain and
exchanges the two chains, so HH_2 ≅ triv ⊕ C[S_2]. On the right-hand side,
(3−1)/2 = 1 and Lie_2 = sgn, so sgn ⊗ Lie_2 = triv and the right-hand side
is C[S_2] ⊕ triv. The two agree. The (frob) formula agrees too:
(3p_1^2 + p_2)/2 on both sides. So the statement is true at p = 2, but only
under that convention for H̃_{−1}, and not by the cited argument.

**Numbers.** b_3 = 16 and b_5 = 1561 are COMPUTED in [AudBn]
("b_n = |B_n| : [1, 3, 16, 131, 1561, 26532]"), and they also follow from
b_n = n[x^n] log A (PROVEN, thm:bn). Then (b_p−1)/p = 5 and 312, matching
[Bn §4]. The dimension checks 5·3! + 2! = 32 and 312·5! + 4! = 37464 match
Σ_P e_C(P) = (n−1)! b_n (`poset_lie_structure.txt`, [AudBn]).

## 3. Suggested replacement for the cone/lune remark (not applied)

> **Remark (Cone/lune form; [Cone], audited in [AudCone]).** [Cone] restates
> Theorem S(b)–(c) in the language of Aguiar–Mahajan's top-lunes. … [Cone,
> Lemma E, Thm 5.2] proves, for every real central **essential**
> arrangement, that the chambers of a pointed top-cone are linearly
> independent modulo top-lunes (proven, audited [AudCone row 8]). The lune
> form of Theorem S(c) ([Cone, Thm 4.1(c)]) is proven *given* Prop. Φ,
> Lemma D and (A), exactly as Theorem S(c) is ([AudCone row 12]). …

To go with it: drop open problem 4's last sentence, and add a table row
`audit_cone_lune.py | 6 arrangements outside [Cone]'s list (A_1×A_2,
resonance R^3, A_2×A_2, generic 6 in R^5, non-generic 7 in R^4, H_3) |
[AudCone]`. These counts are taken from `compute/output/audit_cone_lune.txt`
and [AudCone §C].

## 4. Computational-record table vs `compute/output/`

| Row (script) | Write-up range | Archived evidence | Grade |
|---|---|---|---|
| `poset_jks_check.py` | all n ≤ 6, 758 pairs at n = 6 | `character_table.tsv`: 784 rows at n = 6 = 758 unlabeled pairs + 26 named-example rows ([N7] l. 33); [Repro] l. 113 says "758" | MATCHES |
| `n7_sweep.py` | 2045 posets, 4804 pairs | `n7_summary.txt`: "n=7: 2045 posets, 4804 … pairs"; `n7_character_table.tsv`: 4804 rows | MATCHES |
| `equivariant_homology.py` | every pair n = 4, 5, 6, 7 | `n6_homology_all.txt` (784, 0 disagreements); `n7_homology_all.txt` (1613+1585+1606 = 4804 AGREE); n = 4, 5 **not archived** ([N7] results table) | MATCHES after fix F2. Note: the n = 7 traces are exact over C *given JS* ([N7] "Why the mod-p answer…"). That is the "sandwich" of the table's preamble with JS as one bound. |
| `poset_lie_structure.py` | n ≤ 6 (+7, 8 examples); Q: n ≤ 4; bracket n ≤ 5 | `poset_lie_structure.txt` headers | MATCHES |
| `fixed_point_mobius.py` | n ≤ 6; 194 families at n = 7, 8, 9 | `fixed_point_mobius.txt` (596 = 402 + 194 posets) | MATCHES |
| `audit_character_identity.py` | n ≤ 6; 19 families at 7, 8, 9; one at n = 10 | `audit_character_identity.txt` (424 = 405 + 19), `…_n10.txt` (1 poset, 9 pairs) | MATCHES |
| `splitting_cycles.py` | Φ: n ≤ 5; S: n ≤ 6 | `splitting_cycles.txt` (shuffle relations n = 3..5; span = e_C at n = 6) | MATCHES |
| `audit_jks_maps.py` | n ≤ 6 (C, κ_n, Ex 10.9: n ≤ 5) | `audit_jks_maps.txt`; [AudLit §6] | MATCHES |
| `conjecture_s.py` | n ≤ 6 archived; n ≤ 7 not archived; ρ n ≤ 5 | `conjecture_s.txt` ([S] to n = 6, [rho] to n = 5) | MATCHES |
| `audit_conjecture_s.py` | n ≤ 6 | `audit_conjecture_s.txt` | MATCHES |
| `cyclic_posets.py` | n ≤ 7 (a_8, b_8 via Lemma 1(c)) | **no archived output** in `compute/output/`; [AudBn] reports re-running it at n = 7 | MATCHES as to range; the preamble's "archived outputs are in compute/output/" does not hold for this row |
| `audit_cyclic_posets.py` | n ≤ 6 (`--b8`: n ≤ 8) | **no archived output**; the output is quoted in full in [AudBn] | as above |
| `second_read_globalind.py` | n ≤ 5 | `second_read_globalind.txt` (2 ≤ n ≤ 5) | MATCHES |
| `cone_lie.py` | A_2, A_3, A_4, B_2, B_3; samples of D_4, B_4 | `cone_lie.txt` | MATCHES (also omits the non-reflection arrangements; harmless) |
| (missing) `audit_cone_lune.py` | — | `audit_cone_lune.txt` | STALE (merged after the write-up) |

The note "No check in the table failed" agrees with every archived output:
each ends in `ALL CHECKS PASS(ED)` or reports 0 disagreements.

## 5. Bibliography vs [Lit §5]

| Entry | [Lit §5] proposal | Write-up | Grade |
|---|---|---|---|
| Klyachko | Sibirsk. Mat. Zh. 15 (1974) no. 6, 1296–1304; Siberian Math. J. 15 (1974) 914–920, doi:10.1007/BF00966559 | identical | MATCHES |
| Jenča–Sarkoci | JCTA 122 (2014) 28–38, add arXiv:1112.5782, arXiv v2 numbering | identical, plus doi:10.1016/j.jcta.2013.09.010 (as in the seed note's entry) | MATCHES |
| Wachs 1998 | Discrete Math. 193 (1998) 287–319; numbers are preprint numbers | identical, with the preprint date | MATCHES (the seed note's DOI 10.1016/S0012-365X(98)00147-2 is not repeated; optional) |
| Ree, Reutenauer | add | present, identical | MATCHES |
| Stanley 1982, Hanlon 1981, Joyal 1986 | add, "from memory; verify" | present, and the caveat is repeated after the bibliography | MATCHES |
| Aguiar–Mahajan | add EMA 173 and *Topics*, MSM 226 | present | MATCHES; was uncited, fixed (F3) |
| Crapo | (from [FPM §1]) JCT 1 (1966) 126–131 | identical | MATCHES |
| Barcelo; Wachs, *Poset topology* | proposed in [Lit §5] items 3–4 | absent | fine: the write-up cites neither |

## 6. Clerical fixes applied to the write-up

- **F1** (§1, l. 70–71): the "computed" tag pointed to §`sec:computations`
  for the reproduce command. That section only refers to
  `compute/README.md`. Reworded to "listed in §…, with the reproduce
  command in `compute/README.md`".
- **F2** (table, `equivariant_homology.py` row): added "(n = 4, 5 not
  archived)", as the [N7] results table records.
- **F3** (cone/lune remark): added `\cite{AguiarMahajan}` after "*Topics*".
  The bibliography entry was otherwise never cited.

No mathematics was changed. The items reported but not changed are rows 33,
42, 44, 49, 51 and 55.

## Reproduce

Run from the repository root:

    ./build.sh      # on this host: "no TeX toolchain (latexmk/pdflatex) found; skipping"

Reference and citation consistency check (the substitute for the build):

    python3 - <<'EOF'
    import re
    s = open('notes/poset_jks_theorem.tex').read()
    labels = set(re.findall(r'\\label\{([^}]*)\}', s))
    refs = set(re.findall(r'\\(?:eq)?ref\{([^}]*)\}', s))
    keys = set(re.findall(r'\\bibitem\{([^}]*)\}', s))
    cites = {k.strip() for c in re.findall(r'\\cite\{([^}]*)\}', s) for k in c.split(',')}
    print('undefined refs', refs - labels, 'undefined cites', cites - keys, 'uncited', keys - cites)
    EOF

After F3 this prints three empty sets.

The pair counts in §4 were read with:

    awk -F'\t' 'NR>1{c[$2]++} END{for(k in c) print k, c[k]}' compute/output/character_table.tsv
    awk -F'\t' 'NR>1{c[$2]++} END{for(k in c) print k, c[k]}' compute/output/n7_character_table.tsv
    grep -c AGREE compute/output/n7_homology_all.txt     # 4804
    tail -n 3 compute/output/*.txt                       # every run ends in a pass line
