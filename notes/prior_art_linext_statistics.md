# Prior art for the cyclic order polynomial (Theorem Ω, Corollary Ω-des, Theorem H)

This note checks the identities around the cyclic order polynomial against
the literature:
- **Theorem Ω** ([LS] §2.1): for a fixed component T of P,

    Ω_C(P, m) := Σ_{π∈OP(P)} |μ(π, 1̂)| C(m, |π|)
               = #{f : P → [m] order-preserving : every nonempty upper level
                  set that is a union of components contains T};

- **Corollary Ω-des** ([LS] §2.2): the descent expansion of Ω_C;
- **nonnegativity of the h-vector** h_C(P) ([LS] §2.2, row 2″), now
  **Theorem H** ([H]): under a *separated* natural labelling,
  h_C(P)_j = #{κ ∈ Cyc(P) : cdes κ = j + 1}, where Cyc(P) is the set of
  classes of Lin P under rotation at cuts.

Notation is that of [LS] and [H]. Verdicts are search results:
- **KNOWN**: stated in a source read here, with the exact reference.
- **KNOWN IN SUBSTANCE**: a special case, or the same mechanism, is in a
  source read here.
- **NOT FOUND**: not in the sources of §0. This is the result of a search,
  not a proof of novelty.

Computations are in `compute/prior_art_linext_statistics.py`, which imports
nothing from the repository. It regenerates the posets, computes Ω_C from
the counting side of Theorem Ω (chains of order ideals), and tests each
candidate from the literature. Bracketed tags such as `[toric]` are line
labels in `compute/output/prior_art_linext_statistics.txt`.

## Verdict

| Claim | Verdict | Closest prior art (read) |
|---|---|---|
| **Theorem Ω**, general P | **NOT FOUND.** It is not the toric order polynomial of a toric poset in the sense of [DMR] and [AGRR]. A toric order polynomial on n points has leading coefficient n·\|L^tor\|/n!, while Ω_C has e_C(P)/n!. So a match needs n \| e_C(P), and the toric poset would have only e_C/n total cyclic extensions, not e_C. Numerically, Ω_C(P, ·) is not even in the cone of toric order polynomials for any P with n ≤ 5 `[toric]`, and the quasisymmetric lift of Ω_C is not cyclically quasisymmetric `[qsym]` (§1) | [DMR] Thm 1.4, Def. 5.1; [AGRR] Def. 3.14, Lemma 3.15, Prop. 3.18 |
| Theorem Ω, antichain | **KNOWN.** Ω_C(A_n, m) = Σ_{j≤m} j^{n−1}. The bijection S_n/C_n ↔ S_{n−1}, which puts n last, is in [Pet] Prop. 1.1 (credited there to Fulman). It is the antichain case of the T-anchoring in Theorem Ω | [Pet] Prop. 1.1 and its proof |
| **Corollary Ω-des** | **NOT FOUND.** No source read has a descent expansion with merged positions at cuts. [AGRR] Prop. 2.15 and Lemma 3.15 expand toric enumerators over total cyclic orders, and every rotation counts there. In Ω-des, rotations count only at cuts, and the cut positions are forced to be equalities | [AGRR] §§2–3 |
| **h_C(P) ≥ 0 / Theorem H** | **NOT FOUND** for general P. The *statistic* is known: it is Cellini's cyclic descent number on cyclic words ([Pet] §1.1; [AGRR] (1.1); [ARR] (1.1)), restricted to the cut-rotation classes. The *identity* h_C = cdes − 1 on Cyc(P) was not found. **KNOWN** for the antichain: Cyc(A_n) is all of S_n/C_n, and [Pet] Prop. 1.1 gives A^{(c)}_n(t) = n A_{n−1}(t), so h_C(A_n) is the Eulerian distribution of S_{n−1}. Checked independently here under every separated labelling of every poset with n ≤ 7 `[sep]` (§2) | [Pet] Prop. 1.1; [AGRR] (1.1) |
| h_C as an ARR cyclic-descent distribution | **No.** A cyclic descent extension in the sense of [ARR] Def. 2.1 lives on Lin P. It has e(P) elements, and e(P) ≠ e_C(P) on every disconnected P. The cdes distribution that [ARR] Lemma 2.4 forces from des on Lin P equals n·t·h_C(t) on only 6 of 2449 posets `[arr]` (§2) | [ARR] Def. 2.1, Lemmas 2.2, 2.4 |
| F-positivity of the quasisymmetric lift K_C(P) | **NOT FOUND**; COMPUTED, OPEN. K_C(P) := Σ x^f over the T-anchored maps f. It is F-positive in Gessel's fundamental basis on all 2450 posets with n ≤ 7 `[qsym]`, which is stronger than h_C ≥ 0. For connected P it is Gessel's K_P (§3) | [AGRR] §2; Gessel's P-partition enumerator (EC2 §7.19, not re-read) |

**Bottom line.**
- The toric/cyclic literature (toric posets, toric P-partitions, cyclic
  quasisymmetric functions, cyclic descent extensions) is the right
  neighbourhood, but none of it contains Theorem Ω, Corollary Ω-des or
  Theorem H.
- The structural reason is the anchoring. Toric theory counts *all*
  rotations of a total cyclic order. Ω_C counts one representative per
  cut-rotation class, and its leading coefficient is e_C/n!, not a
  multiple of n/n!.
- The antichain case of all three statements is classical ([Pet], after
  Fulman), and the statistic in Theorem H is Cellini's cdes.
- A write-up should cite [Pet] Prop. 1.1 for the antichain, [AGRR] for
  the contrast with toric P-partitions, and [ARR] only to say why their
  framework does not apply.

## 0. Sources read

- **[DMR]** M. Develin, M. Macauley, V. Reiner, *Toric partial orders*,
  arXiv:1211.4247v1 (Trans. Amer. Math. Soc. 368 (2016) 2263–2287). Read in
  full (§§1–10).
- **[AGRR]** R. M. Adin, I. M. Gessel, V. Reiner, Y. Roichman, *Cyclic
  quasi-symmetric functions*, arXiv:1811.05440v5. Read: §§1–3 in full, §4
  through Thm 4.6, and §7 (open problems).
- **[Pet]** T. K. Petersen, *Cyclic descents and P-partitions*,
  arXiv:math/0405479v2. Read: §§1–2 in full; §3 (type B, augmented
  P-partitions) skimmed for any general-poset statement; there is none.
- **[ARR]** R. M. Adin, V. Reiner, Y. Roichman, *On cyclic descents for
  tableaux*, arXiv:1710.06664v2. Read: §§1–2 in full. §§3–7 concern SYT,
  ribbon Schur functions and Postnikov's toric Schur functions; they were
  searched for "poset", "linear extension" and "P-partition", and contain
  none of these beyond the bibliography.
- **[Lia]** J. Liang, *Enriched toric [D]-partitions*, arXiv:2209.00051v2.
  Read §§1 and 5.4. Its Ω^cyc([D], m) is the order polynomial of
  *enriched* toric partitions. It is the only source found that names an
  order polynomial for toric posets.
- **Searched, not found:** "toric order polynomial", "cyclic order
  polynomial", "cyclic descent" together with "linear extensions". The
  one hit, Ramassamy (arXiv:1706.03386), is about extensions of partial
  cyclic orders (Megiddo's ternary relations), which [DMR] Rem. 1.11
  distinguishes from toric posets.
- **Not read:** Stanley, EC2 §7.19 (no copy available to this check). Its
  content used here, K_P = Σ_{w∈L(P)} F_{Des w} (Gessel), is re-verified
  numerically for every connected P with n ≤ 7 `[qsym]`, and is also
  [AGRR] Lemma 3.3 in its DAG form. B. Huang's constructive cyclic descent
  map for skew SYT was not read, because it concerns SYT only.

**What the brief assumed and the sources do not have.** [DMR] defines no
toric order polynomial and no toric chromatic polynomial. Its only counts
are |Cham A^tor(G)| = |Acyc(G)/≡| = T_G(1, 0) (Thm 1.4 and §1.2) and
(n − 1)! toric total orders. The toric analogue of P-partitions is in
[AGRR] §3.2. The corresponding order polynomial, the number of toric
[D]-partitions with values in [m], is not named there. It is the principal
specialisation of the enumerator of [AGRR] Prop. 3.18, and [Lia] §5.4
names its enriched version. That is the object compared with Ω_C in §1.

## 1. Theorem Ω against toric posets

**Toric order polynomial.** For a DAG D on [n], a toric [D]-partition is a
D′-partition for some D′ in the flip class of D ([AGRR] Def. 3.14). By
[AGRR] Lemma 3.15, these partitions split over the total cyclic orders
[w] ∈ L^tor([D]), and A^tor([w]) is the disjoint union of A(w′) over the
n rotations w′ of w. A rotation has des = cdes − 1 when it is broken at a
cyclic descent, and des = cdes otherwise. So the number of toric
[D]-partitions with values in [m] is

  Ω^tor([D], m) = Σ_{[w] ∈ L^tor([D])} g_{cdes w}(m),
  g_d(m) = d·C(m + n − d, n) + (n − d)·C(m + n − 1 − d, n),  1 ≤ d ≤ n − 1.

The formula for g_d is unit-tested against brute force
(`test_g_formula_matches_bruteforce`).

**Obstruction (PROVEN).** Each g_d has leading coefficient n/n!. So Ω^tor
has leading coefficient n·|L^tor|/n!, while Ω_C(P, ·) has e_C(P)/n!. A
match forces n | e_C(P), with |L^tor| = e_C/n. Two cases fail at once:
- P connected with n ∤ e(P), for example every chain;
- the antichain, for n ∤ (n − 1)!, for example n prime.

When a match does happen, it pairs e_C cut-rotation classes with e_C/n
total cyclic orders. That is a numerical coincidence of polynomials, not an
identification of the objects. The normalised guess n·Ω_C = Ω^tor also
fails for the antichain: |L^tor| = (n − 1)! forces L^tor to contain every
class, so Ω^tor = m^n, whereas n·Σ_{j≤m} j^{n−1} ≠ m^n.

**Computation.** Any toric order polynomial on n points lies in the cone
N{g_1, …, g_{n−1}}. The script solves Ω_C = Σ a_d g_d exactly over Q.
- n ≤ 5: Ω_C(P, ·) is in the cone for **no** P `[toric]`.
- n ≤ 4, brute force: every DAG on [n] is enumerated, with its flip class
  and its toric partitions counted directly. All 15 distinct toric order
  polynomials lie in the cone (control), and none equals Ω_C(P, ·) or
  n·Ω_C(P, ·) `[toric-bf]`.
- n = 6, 7: 13 of the 2449 posets pass the cone test `[toric]`.
  - 11 of them are connected, so Ω_C = Ω, and the question becomes whether
    an ordinary order polynomial equals a toric one. That can happen. For
    P with down-sets (0, 0, 0, {2}, {0,1,2,3}, all), Ω(P, m) equals the
    toric order polynomial of the toric poset with toric chains [01234]
    and [01235]. Its L^tor is {[012345], [012354]}, and the values agree
    for m = 1, …, 6 `[toric]`.
  - The 2 disconnected ones, with down-sets (0,0,0,{2},{1},{0,2,3}) and
    (0,0,{1},{1},{1,3},{0}), have the same cone coordinates (1, 4, 2, 0, 0)
    as two connected posets. Whether some toric poset realises those
    coordinates was not decided.

**Quasisymmetric level.** [AGRR] Prop. 3.18 puts every toric enumerator
in cQSym⁻. The natural lift of Ω_C is

  K_C(P) = Σ_{f T-anchored} x^f.

It is quasisymmetric, because the anchoring condition depends only on the
relative order of the values. It is **not** cyclically quasisymmetric for
2440 of the 2449 posets with n ≥ 2 `[qsym]`. The smallest case is
A_3: [M_{(1,2)}] K_C = 2 but [M_{(2,1)}] K_C = 1
(`test_antichain_lift_not_cyclic`).

## 2. h_C against cyclic descents

**Theorem H, checked independently.** [H] proves that, for a separated
natural labelling (every minimal element of a non-singleton component
gets a smaller label than every maximal element of a non-singleton
component),

  h_C(P)_j = #{κ ∈ Cyc(P) : cdes κ = j + 1}.

Here Ω_C is computed from the ideal-chain count, not from the Möbius sum
used in [H]. The identity holds under every separated labelling of every
poset with 2 ≤ n ≤ 7, which is 188,354 (poset, labelling) pairs `[sep]`. Without
the separation hypothesis it fails:
- cdes − 1 on Cyc(P) realises h_C under every natural labelling for 1356
  of 2449 posets, and fails for some labelling on the other 1093
  (control, `[cdes]`);
- for every poset, at least one natural labelling works `[cdes]`, as
  Theorem H predicts.

The rival statistic des of the T-anchored representative is Petersen's
representative π̃ for the antichain. It fails for some labelling or some T
on exactly the 503 disconnected posets `[anchor]`. This matches [LS] §2.2
and [H] row B, where it works only under a special labelling.

**Prior art for Theorem H.**
- Cellini's cdes on cyclic words, and its rotation invariance, are
  standard ([Pet] §1.1; [AGRR] (1.1), Def. 3.12; [ARR] (1.1)–(1.4)).
- For the antichain, Cyc(A_n) = S_n/C_n, and [Pet] Prop. 1.1 (credited
  to Fulman) gives Σ_{π∈S_n} t^{cdes π} = n A_{n−1}(t). Equivalently,
  #{κ : cdes κ = j + 1} is the Eulerian number of S_{n−1} with j descents.
  This is Theorem H for A_n, and [Pet]'s proof is the same "put the
  anchor last" bijection. **KNOWN**.
- For general P, none of [DMR], [AGRR], [Pet] or [ARR] considers the cut
  classes Cyc(P) (rotation only at cuts, so a class has 1 + #cuts
  members rather than n). The identity was **NOT FOUND**.

**Is h_C an ARR cyclic-descent distribution?** No, in either reading.
1. A cyclic extension (cDes, p) of Des on T = Lin P ([ARR] Def. 2.1) has
   #T = e(P) elements, but Σ_j h_C(P)_j = e_C(P) < e(P) whenever P is
   disconnected. On connected P, h_C is the des distribution itself.
   That is not a cdes distribution in general: a chain has a single
   linear extension, which admits no non-Escher extension. Chains are
   connected ribbons in [ARR] Thm 1.1.
2. [ARR] Lemma 2.4 determines the cdes generating function of any cyclic
   extension from des: n T^des(t)/(1 − t)^{n+1} = d/dt[T^cdes(t)/(1 − t)^n].
   Computing that polynomial formally for every poset (canonical
   labelling) and comparing it with n·t·h_C(t), they agree on 6 of 2449
   posets `[arr]` (the antichains, where both are n t A_{n−1}(t)).

Theorem H is therefore *not* an instance of the ARR existence theory. Its
objects are the e_C cut classes, not Lin P, and its statistic needs a
labelling hypothesis that the ARR axioms do not have.

## 3. A quasisymmetric lift (EC2 §7.19 direction)

K_C(P) expands in monomial quasisymmetric functions as

  K_C(P) = Σ_{chains 0̂ = I_0 ⊂ ⋯ ⊂ I_k = P, anchored} M_{(|I_1|, |I_2 − I_1|, …)},

and its principal specialisation at 1^m is Ω_C(P, m). The script converts
this to Gessel's fundamental basis.
- **COMPUTED:** K_C(P) is F-positive on all 2450 posets with n ≤ 7
  `[qsym]`, and the specialisation of its F-expansion reproduces h_C.
- For connected P it equals Σ_{w∈Lin P} F_{Des w}. That is Gessel's
  theorem (EC2 Cor. 7.19.5, not re-read), and it doubles as a check of the
  M → F conversion.
- Control: M_{(2)} = F_{(2)} − F_{(1,1)} is flagged as not F-positive.

Since F_J(1^m) = C(m + n − 1 − |J|, n), F-positivity implies h_C ≥ 0. It
is stronger than Theorem H, because Theorem H is only the specialisation.
A combinatorial F-expansion, for example Σ_{κ∈Cyc(P)} F_{J(κ)} for some
descent-type set J(κ) of size cdes κ − 1, was **not found** in the
sources and is **OPEN**.

## Reproduce

From `compute/` (plain Python 3, no dependencies, one core, about 3 minutes):

    python3 prior_art_linext_statistics.py --nmax 7 > output/prior_art_linext_statistics.txt
    python3 -m unittest test_prior_art_linext_statistics

The script exits 0 iff every claim line passes and every CONTROL line is
refuted somewhere. Options:
- `--lab-nmax k` tries every natural labelling only for n ≤ k (default 7);
- `--bf-nmax k` sets the largest n for the brute-force toric enumeration
  (default 4).

References inside the repository: [LS] = `notes/linext_statistics.md`;
[H] = `notes/h_vector_omega_c.md`.
