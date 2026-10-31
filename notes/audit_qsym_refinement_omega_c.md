# Audit of qsym_refinement_omega_c.md: the quasisymmetric refinement of Theorem H

This is an independent, adversarial audit of `notes/qsym_refinement_omega_c.md`
([Q] below, merged in 54c7603), with a prior-art section. I re-derived every
proof by hand. I recomputed every claim with my own script,
`compute/audit_qsym_refinement_omega_c.py`. It imports nothing from the
repository and was written without reading the author's script. Its one
contact with the author's script: I grepped the author's print statements to learn what "3107 pairs"
counts, which is every component of every poset, not Aut(P)-orbits.
Bracketed labels such as `[thmQ-iff]` refer to lines of
`compute/output/audit_qsym_refinement_omega_c.txt`. The label `[rot-choice]` refers to
`compute/output/audit_qsym_refinement_omega_c_rotchoice.txt`.

Sources: [H] = `notes/h_vector_omega_c.md`; [AudH] =
`notes/audit_h_vector_omega_c.md`; [PA] = `notes/prior_art_linext_statistics.md`.

## Bottom line

**Every PROVEN claim of [Q] HOLDS. Every count of [Q] that I recomputed with the same definition reproduces exactly; the two controls I defined differently give different counts.**

**Is Theorem Q just Gessel's lemma restricted by bijection B? Yes, for the
direction that matters.**
- The fundamental lemma of P-partitions (Stanley; Gessel 1984) splits the
  order-preserving maps as A(P) = ⊔_{w∈Lin P} A(w), where A(w) is the cell
  of maps with Stanley word w and contributes F_{Des w}.
- K_{C,T} is the generating function of a subset Anch_T ⊆ A(P).
- Theorem Q(i) says exactly that Anch_T is the union of the cells A(w) with
  w ∈ L_T. That is bijection B, and then (i) is a sum over those cells.
- Half of B needs no labelling hypothesis at all. If w ∈ L_T, then every
  upper level set of f that is a union of components is a suffix of w
  starting at a cut, so it contains the last piece, so it contains T.
- The other half is the only step that is not a restriction. If w ∉ L_T,
  every f in A(w) must be strict at the junction leaving T's piece. This
  holds iff that junction is always a descent (Q(iii)). The label condition
  (E*_T) is a characterisation of when this happens (Q(iii) ⇔ (iv)). It is
  an elementary lemma about which letters can meet at a piece boundary
  ([Q] §3.2, facts (a) and (b)).

For **F-positivity (F+) only one labelling is needed**: λ_T, in which T's
maxima, or t when T = {t}, come last and all minima come early. The
non-restriction step then takes five lines. So **F+ is KNOWN IN SUBSTANCE.** It is
an immediate corollary of the fundamental lemma, once the anchor is labelled
last. That is the same move as the "put n last" proof of Petersen's
Prop. 1.1, which is [Q]'s antichain case. It should be reported to Daniel
as an observation, not as a new positivity theorem.

The parts of Theorem Q that are not a restriction are:
- the converse (i) ⇒ (iv): (E*_T) is necessary;
- the exact form of (E*_T).

Both are correct, elementary, and NOT FOUND in the literature I checked.

## Verdicts

| # | Claim of [Q] | Verdict |
|---|---|---|
| Q | Theorem Q: for a natural labelling, K_{C,T}(P) = Σ_κ F_{Des R_T(κ)} ⇔ (ii) ⇔ (iii) ⇔ (E*_T) | **HOLDS.** Every implication was re-derived (§1). COMPUTED: all 8267 labelled pairs n ≤ 6 (deduplicated up to labelled isomorphism); (i) holds on 5894 and fails on 2373, and (i), (ii), (iii) and (E*_T) agree on every one `[thmQ-iff]` |
| Q′ | λ_T is natural, separated and satisfies (E*_T); \|Des R_T(κ)\| = cdes κ − 1 | **HOLDS.** COMPUTED: all 3107 pairs (P, T) n ≤ 7 `[lamT]`, `[thmQ-lamT]`, `[size]` |
| F+ | K_{C,T}(P) is F-positive for every P and T, with coefficient sum e_C(P) = #Cyc(P) | **HOLDS. KNOWN IN SUBSTANCE** (fundamental lemma + "anchor labelled last"; Bottom line, §3). COMPUTED: 3107 pairs `[F+]` |
| H | Specialising Q′ gives Theorem H for λ_T without Lemma 1 | **HOLDS, with the scope [Q] states.** The proof uses Theorem Ω (spec = Ω_C, [H] §1, audited in [AudH]) and needs only Lemma 2(a), not Lemma 1. It gives Theorem H for λ_T only, which is enough for h_C ≥ 0. Theorem H for every separated labelling still needs [H]'s Lemma 1. COMPUTED `[H-spec]` |
| D_q | K_{C,T} = Σ_w G_T(w), and G_T(w) is the generating function of the anchored maps with Stanley word w | **HOLDS.** This is the cell decomposition plus inclusion–exclusion over C_T(w), so routine. COMPUTED: 8267 labelled pairs `[propD-qsym]`. The per-word statement was checked against a literal enumeration of maps, for every word, on 687 labelled pairs n ≤ 5 `[G_T-word]` |
| B | Under (E*_T): f is T-anchored ⇔ its Stanley word lies in L_T | **HOLDS.** COMPUTED under λ_T on every order-preserving map into [3], n ≤ 5: 8600 maps, the author's count `[bij]` |
| 0 | K_{C,T} depends on T (492 of 2450 posets); its principal specialisation does not | **HOLDS.** COMPUTED: 492 of 2450 (by n: 0, 0, 1, 4, 18, 75, 394) `[T-dep]`. The specialisation is T-independent on all 2450 posets `[spec]`. Equality with the Möbius Ω_C is [Q]'s and [AudH]'s check; here it is checked against Σ_κ C(m+n−cdes κ, n), which is Theorem H, audited |
| ✗1 | Lemma 1 does not lift: 1805 of 6996 separated labelled pairs have a class whose contribution is not a single F; all 23 117 such classes (of 317 680) have a negative coefficient | **HOLDS as a refutation.** Every number reproduced `[perclass-sep]`, `[ctl-perclass]`. The hand example (A_3, T = {1}: F_∅ + F_{1} − F_{2}) was re-checked (unit test) |
| ✗2 | No rotation rule for a labelling fixed independently of T (C_2 ⊔ C_1) | **HOLDS as stated in §4.2. The verdict-line paraphrase is FIXABLE** (§2): it overstates. The example refutes "every fixed separated labelling admits a rotation rule for every T". It does not refute "some labelling, fixed in advance, admits a rotation rule for every T". For C_2 ⊔ C_1 the labelling with the isolated point labelled 1 satisfies (E*_T) for both components, so R_T works for both. COMPUTED: on all 503 disconnected posets n ≤ 7, some fixed separated labelling admits a (T-dependent) rotation choice for every T `[rot-choice]` |
| ✗3, ✗4 | Controls (min-des rep; arbitrary rep) fail | **HOLDS.** My own versions of the controls (lex-first rotation under λ_T; lex-first min-des rotation under the generation labelling) are refuted on 783 and 782 of 3107 pairs `[ctl-anyrep]`, `[ctl-mindes-id]`. These are different representatives from the author's, so the counts differ from [Q]'s 766 |
| P | Not cyclically quasisymmetric; = sub-sum of Gessel's K_P over L_T; antichain case = K_{A_{n−1}⊕1}; L_T is Lin of a poset for 2257 of 3107 | **HOLDS**, and 2257 of 3107 was reproduced, labelling-free `[LT-lin]`. The antichain case was re-derived by hand: the condition is f(t) ≥ f(x) for every x. "Not cyclically quasisymmetric" is [PA]'s check and was not recomputed here. The prior-art verdict "NOT FOUND … short consequence of Gessel–Stanley" should be split: **F+ KNOWN IN SUBSTANCE**, the iff characterisation (E*_T) NOT FOUND (§3) |
| §6 item 3 | OPEN: does a fixed separated labelling admit a T-free rule D(κ) that is not a rotation's descent set? | **FIXABLE: not open.** A T-free D(κ) gives a T-free sum Σ_κ F_{D(κ)}, but by row 0, K_{C,T} depends on T for 492 posets. So no T-free rule of any kind exists for those posets, under any labelling. The other 1958 posets are the 1947 connected ones, where the question is trivial, and 11 disconnected ones on which K_{C,T} happens not to depend on T |

**No claim FAILS.** There are two wording fixes, in rows ✗2 and §6 item 3.
The first matters: the strong reading of [Q]'s verdict line ("no rotation
rule for a T-independent labelling") is false on every disconnected poset
with n ≤ 7, by an existence computation (§2).

## 1. Re-derivation of Theorem Q

Conventions as in [Q] §0. A(w) is the set of order-preserving f whose
Stanley word is w. That word is the elements sorted by (f, label), and f is
weakly increasing along it and strict at Des w.

- **Anchoring is a condition on equalities along w ([Q] §2).** The upper
  level sets of f ∈ A(w) are the suffixes w_{p+1} … w_n at the positions p
  where f strictly increases, together with P itself. Such a suffix is a
  union of components iff p is a cut. It misses T iff p ∈ C_T(w). So f is
  anchored iff f is constant across every p ∈ C_T(w). Inclusion–exclusion
  over C_T(w) then gives G_T(w), which is Proposition D_q. Correct.
- **(i) ⇔ (ii).** For w ∈ L_T we have C_T(w) = ∅, so A(w) ⊆ Anch_T.
  Hence K_{C,T} − Σ_{L_T} F_{Des w} is the generating function of the
  anchored maps whose word is not in L_T. It is a nonnegative sum of
  monomials, and it is zero iff that set of maps is empty. The set for w is
  empty iff some p ∈ C_T(w) is forced strict, that is, iff C_T(w) ∩ Des w ≠ ∅.
  The witness f(w_p) = 1 + #{descents before p} is correct.
- **(ii) ⇒ (iii).** This is the swap w′ = A B_2 ⋯ B_r c B_1. I checked
  three things:
  - w′ ∈ Lin P, because every block is a union of components;
  - the pieces of w′ are the blocks' pieces, by [H] §0's argument that
    removing whole pieces from a union of components leaves one;
  - C_T(w′) is the single junction c → B_1, which is an ascent by
    hypothesis.

  Correct.
- **(iv) ⇒ (iii).** I checked fact (a), that the first letter of a piece is
  minimal in P, and fact (b), that the last letter of a piece of length ≥ 2
  is a maximum of a non-singleton component lying inside the piece. Then
  U ≠ T because U ∩ c = ∅. When |c| ≥ 2 we also have U ≠ V, because V ⊆ c.
  Correct.
- **(iii) ⇒ (iv).** The negation of (E*_T) is either clause 1 failing
  (V = T, or V ≠ T with |T| ≥ 2, or V ≠ T with T = {t}) or clause 2 failing.
  That is four cases, and [Q] covers all four.
  - The pieces c = t_0 (V∖a)(T∖t_0) a and c = v_0 t (V∖{v_0, a}) a are
    linear extensions, since removing a minimum or a maximum leaves a
    linear extension.
  - They have no proper prefix that is a union of components. Every prefix
    either contains t_0 but not all of T, or meets V without containing a.
    Here |V| ≥ 2 makes V ∖ a nonempty.
  - v_0 ≠ a holds because a is maximal in a connected V with |V| ≥ 2.
  - U is connected, so U forms a single last piece.

  Correct.

Lemma 3 (λ_T natural, separated, (E*_T)) and Corollary Q′ (|Des R_T| =
cdes − 1) were re-derived. The case s = 1 uses w_1 < w_n under a separated
labelling ([H] Lemma 2(a), HOLDS in [AudH]). The case s ≥ 2 uses des = d + jd − δ with δ = 1 at the
broken junction. Correct.

## 2. The "T-independent labelling" wording (✗2, §6)

[Q] §4.2 is correct as written. Under the identity labelling of C_2 ⊔ C_1
(0 isolated, 1 < 2) and T = {0}, the singleton class {102} forces F_{1},
and F_{1} is not in K_{C,{0}} = F_∅ + F_{2}.

The verdict paragraph instead says "No rotation rule works for a labelling
fixed independently of T". Read as "for every P, every labelling fails for
some T", this is false on the note's own example. Label the isolated point
1, with the chain 0 < 2. Then (E*_T) holds for T = {1}, since 1 > 0. It
also holds for T = {0, 2}, since 2 > 1. So by Theorem Q, R_T works for
both components under one fixed labelling.

What is true is the following:
- (E*_T) can hold for every T at once only if P has at most one isolated
  point. With two isolated points s, t, the isolated-T clause demands s > t
  and t > s.
- If K_{C,T} depends on T, which happens for 492 posets, no T-free D(κ) of
  any kind works. This makes §6 item 3 not open.

`[rot-choice]` gives the computed answer to the T-dependent version: whether
a labelling exists under which, for every T, some choice of one rotation per
class gives K_{C,T}.

COMPUTED `[rot-choice]`, all 503 disconnected posets with n ≤ 7:
- (E*_T) holds for every T under a single labelling on 415 of them, and on
  none of the 88 with two or more isolated points;
- yet on **all 503**, some single separated natural labelling has the
  property that for every T, some choice of one rotation per class sums to
  K_{C,T}.

The choice depends on T. It is found by bipartite matching, and it is not an
explicit rule. The matching is controlled by a unit test
(`test_rotation_choice_matching`): it fails for the identity labelling of
C_2 ⊔ C_1 with T = {0}, as §4.2 requires, and it succeeds for the labelling
with the isolated point labelled 1. So the strong reading of [Q]'s verdict
line is false for n ≤ 7. What remains open is an *explicit* rule for a
labelling fixed in advance, and only for posets with ≥ 2 isolated points
(otherwise λ-type labellings satisfying every (E*_T) exist on all 415 cases
here).

Suggested fixes:
- Replace "No rotation rule works for a labelling fixed independently of T"
  with: "Under some labellings fixed in advance (for example C_2 ⊔ C_1 with
  the isolated point labelled 0, and T the isolated point), no choice of
  rotations works. No rule D(κ) that ignores T can work when K_{C,T}
  depends on T (492 posets). For n ≤ 7, every poset has some fixed
  labelling under which a T-dependent choice of rotations works."
- In §6, delete item 3, or restate it as asking for an explicit
  T-dependent rule under a fixed labelling when P has ≥ 2 isolated points.

## 3. Prior art (search result)

| Item | Result |
|---|---|
| Fundamental lemma A(P) = ⊔ A(w), K_P = Σ_{w∈Lin P} F_{Des w} | **KNOWN**: Stanley (1972; EC1 §3.15, EC2 §7.19); Gessel, *Multipartite P-partitions and inner products of skew Schur functions*, Contemp. Math. 34 (1984). Petersen states and proves it as Thm 2.1 (FTPP) of *Cyclic descents and P-partitions*, J. Algebraic Combin. 22 (2005), arXiv:math/0405479, which I read. EC2 itself was not re-read |
| Any union of cells A(w) has an F-positive generating function Σ F_{Des w} | **KNOWN** (immediate from the above) |
| F+ for K_{C,T}: label the anchor's maxima last, then anchoring = "Stanley word has T's piece last" | **KNOWN IN SUBSTANCE.** Same mechanism as Petersen's proof of Prop. 1.1 (A^{(c)}_n(t) = n A_{n−1}(t), after Fulman): fix n in the last position and rotate. That is [Q]'s antichain case. The general disconnected-P anchored version was not found stated |
| Theorem Q's characterisation (i) ⇔ (E*_T) | **NOT FOUND.** Elementary |
| Prop. D_q | **KNOWN IN SUBSTANCE** (cell decomposition + inclusion–exclusion) |
| Cyclic quasisymmetric functions / toric P-partitions | Adin–Gessel–Reiner–Roichman, *Cyclic quasi-symmetric functions*, Israel J. Math. 243 (2021), arXiv:1811.05440. Toric enumerators sum over every rotation of a total cyclic order. K_{C,T} takes one rotation per cut class and is not in cQSym ([PA] §1). They are **not the same object**, which confirms [PA] |
| Petersen's "cyclic P-partitions" | Petersen's paper uses ordinary P-partitions plus rotation to put n first. I found no notion there of cut classes of a disconnected poset |

Search scope: web searches for Petersen cyclic P-partitions, AGRR, and
"P-partitions disconnected poset … prescribed last component", plus a reading
of the Petersen arXiv text (§1–2). No source states K_{C,T} or (E*_T).
The negative result is a search result, not a proof of absence.

**How to report it to Daniel.** "The T-anchored enumerator is F-positive" is
a two-line corollary of Stanley–Gessel once T's maxima are labelled last. It
is not a new positivity phenomenon. The new content is small and elementary:
- the exact criterion (E*_T);
- K_{C,T} depends on T, although its specialisation does not;
- the per-class (Lemma 1) contributions are not F-positive.

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 50 s):

    python3 audit_qsym_refinement_omega_c.py --nmax 7 --lmax 6 --litmax 6 --wordmax 5 > output/audit_qsym_refinement_omega_c.txt
    python3 -m unittest test_audit_qsym_refinement_omega_c

The script exits 0 iff every claim line is OK and every CONTROL is refuted
somewhere. What it computes:
- K_{C,T} by literal enumeration of maps f : P → [k] for n ≤ 6, checking
  order preservation and the anchoring condition on every upper level set.
  The result is cross-checked against a chain-of-ideals count, which is
  used for n = 7.
- The conversion to the F basis by Möbius inversion.
- Σ_κ F_{Des R_T(κ)} from explicitly built rotation classes.

Positive controls, all refuted as required:
- an arbitrary natural labelling (2373 of 8267);
- (E*_T) without its isolated-T clause (808);
- an arbitrary representative (783 of 3107);
- bijection B under a labelling that violates (E*_T) (16 of 16);
- the per-class lift (1805 of 6996).

The `[rot-choice]` search (§2, about 5 s) is

    python3 audit_qsym_refinement_omega_c.py --rotchoice 7 > output/audit_qsym_refinement_omega_c_rotchoice.txt
