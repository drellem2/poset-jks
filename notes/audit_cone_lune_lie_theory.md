# Audit: cone/lune Lie theory for C_P (pointed top-cone theorem)

Work item: mg-52a16. This is an independent adversarial audit of
`notes/cone_lune_lie_theory.md` (the "cone note") and `compute/cone_lie.py`,
both merged in 46dc1ae (mg-3ab4a). Every claim marked PROVEN in the cone note
was re-derived by hand. The audit code is `compute/audit_cone_lune.py`. It
imports nothing from the repository, and its method differs from
`cone_lie.py` (see "Method" below). Nothing in the original was changed.

Tags: PROVEN (with proof), COMPUTED (script + command), CITED, CONJECTURED.

## Verdict

**The general-arrangement theorem HOLDS.** If V is a pointed top-cone of a
finite, real, central, **essential** arrangement, then the chambers of V are
linearly independent modulo top-lunes. Lemmas L and E and the corrected
Ex. 10.9 also hold. No mathematical step is broken.

There are two overstated labels:

- **The section headings drop the hypothesis "essential".** They say "any
  real central arrangement", but essentiality is assumed in the cone note's
  §1 and used in Lemma E. Theorem 5.2 survives for a non-essential
  arrangement only vacuously. Prop. 7.1(a), read literally, is false there
  (§B.5).
- **Theorem 4.1(c), and the "(G3) PROVEN" status line in §5.3, are tagged
  PROVEN without conditions.** They are Theorem C of the Conjecture S note,
  which is PROVEN only *given* (Φ), (D) and (JS). The cone note's own text
  ("a restatement of Theorems B and C") shows the dependence, but the tag
  does not.

The intrinsic-Lie claim of §6 ("Lie^int(V) = 0 for proper cones") is labelled
honestly: PROVEN for the chain, COMPUTED otherwise, CONJECTURED in general.
The §0 verdict table states it more strongly than §6 does (§B.7).

## A. Claim table

| # | Claim (cone note) | Status | Reason |
|---|---|---|---|
| 1 | Prop. 2.1(a)–(c): F(P) = faces of the braid arrangement in C_P; a sub-LRB of the Tits monoid; chambers Lin(P) form an ideal | CONFIRMED | Re-derived (§B.1). |
| 2 | The same for any top-cone of any real arrangement (x + εy ∈ XY, convexity) | CONFIRMED | Standard argument, re-derived. |
| 3 | Prop. 2.2: the support semilattice of F(P) is OP(P) | CONFIRMED | Re-derived (§B.1). Note the orientation: bottom = one block, top = singletons, so this is OP(P) ordered by *reverse* refinement. That does not affect H̃. Brown's definition of support is CITED from memory, as the cone note says. |
| 4 | §1: every class {C : C\|_Z = D\|_Z} (Z ≠ A a flat) is a non-singleton top-lune | CONFIRMED | Re-derived. COMPUTED `[class]` on 6 new arrangements, with lunes built from the Tits product rather than from classes. |
| 5 | Lemma L: L(H,D) ⊆ V ⟺ D ∈ V and S_max(V) ⊆ z(H) | CONFIRMED | Re-derived (§B.2), including the use of the opposite face H̄. COMPUTED `[L]`. |
| 6 | Cor. 3.1: lin(C_P) = unions of components, so C_P is pointed ⟺ P is connected; the lunes in C_P span R_P | CONFIRMED | Here "pointed" means pointed in the essentialized braid arrangement, modulo (1,…,1). That is the convention of the cone note. |
| 7 | Lemma E: E_h(L(H,D)) = 0 if h ∉ z(H), and otherwise ±(a non-singleton lune of A^h) | CONFIRMED | Re-derived (§B.3), including the edge case z(H) = {h}, where the image is the full chamber sum of A^h. COMPUTED `[E]`: exact membership in Lune[A^h], with Lune[A^h] built independently from the faces of A in h. |
| 8 | **Theorem 5.2: V pointed ⇒ Γ_V ∩ Lune = 0** | **CONFIRMED**, with hypotheses finite, real, central, essential | Re-derived (§B.4). "Pointed" is used correctly: it is needed for (i) V^h to be pointed (lin(V^h) = lin(V) ∩ h) and (ii) V ≠ all chambers, which gives a boundary wall. COMPUTED on every top-cone of 6 arrangements outside the author's list (§C), including H_3 over Q(√5) and rank 5. |
| 9 | Hypothesis wording "any real central arrangement" (§§3, 5, 7 headings) | OVERSTATED (minor) | Essentiality is assumed in §1 and used in Lemma E ("A^h is again essential"). Without it, "pointed" in the literal sense lin(V) = 0 never holds. Theorem 5.2 is then vacuous and Prop. 7.1(a) is false (§B.5). Fix: say "essential", or define pointed as lin(V) = ∩A. |
| 10 | Thm 5.2 for braid = Cor. A′ of the Conjecture S note, "the same argument" | CONFIRMED | For connected P, B_P = Lin P. The S-note's (★) is E_h with h = {x_a = x_x}, and its "y <_P z ⇒ c = 0" step is the boundary-wall step. The sign convention of E_h vs. E_{a,x} matches up to the orientation of h. |
| 11 | Theorem 4.1(a)(b): Γ_{C_P} ∩ Lune = R_P, q(C_P) = e_C(P) | CONFIRMED | (a) is Theorem B (K_P = R_P), using Lune = Sh_n (k-block shuffles are sums of 2-block shuffles) and Cor. 3.1. (b) is Theorem B's dimension count. "= dim H_P" uses (JS), CITED, as stated. |
| 12 | Theorem 4.1(c): Φ restricts to H_P ⊗ sgn ≅ (Γ_{C_P} + Lune)/Lune | OVERSTATED (label only) | The mathematics is correct: it is Theorem C's kernel statement plus injectivity of H_P → H̃(Π̄_n) in top degree. But Theorem C is PROVEN *given* (Φ), (D) and (JS) (Conjecture S note §5; audit `notes/audit_conjecture_s.md` row 13). The tag "PROVEN" should carry that condition. |
| 13 | Theorem 4.1(d): connected P ⇒ Lie_n → C^{Lin P} is onto | CONFIRMED | This is Cor. 5.4 of the S-note (given Ree, CITED), or Thm 5.2 together with Lie = Lune^⊥. |
| 14 | Claimed equivalence of §4 with Theorems B/C of mg-3de87 | CONFIRMED | Same objects: W_P = Γ_{C_P}, Sh_n = Lune, K_P = Γ_{C_P} ∩ Lune, R_P = span of the lunes inside C_P. It is a restatement, not a new proof. |
| 15 | Prop. 7.1(a): the chamber sum of V is in Lune ⟺ V is not pointed | CONFIRMED (essential A) | Re-derived (§B.5). COMPUTED `[7.1a]` exactly, by integer orthogonality to an exact Lie basis, on every cone. |
| 16 | Prop. 7.1(b): z ∈ Lie ⟺ z sums to zero on every non-pointed top-cone; the printed "non-singleton" is false | CONFIRMED | Re-derived: every non-singleton lune is a non-pointed cone (by Lemma L applied to V = L). The printed text of Topics Ex. 10.9 is CITED from the literature-note audit (row 26, preliminary version p. 267), not re-read here. COMPUTED `[7.1b]`: on every tested arrangement, a pointed non-singleton cone has its sum outside Lune. |
| 17 | §1 rigour: rank_p arguments give rational conclusions | CONFIRMED | Each inequality chain in the cone note §8 was re-checked. This audit uses exact Q for Lie and Lune, and only rank_p ≤ rank_Q in the safe direction. |
| 18 | §6: Lie^int(V) = 0 for the chain | CONFIRMED (PROVEN) | Trivial: Hw = w for every H ∈ F(V). |
| 19 | §6: Lie^int(V) = 0 for every proper cone in the cone note's list | CONFIRMED as COMPUTED, and now independent of Brown | The cone note computed only m_⊥ and inferred dim Lie^int ≤ m_⊥ from Brown's theorem (CITED from memory). This audit computes dim Lie^int(V) directly as \|V\| − rank_p of the constraints Hz = 0. It is 0 on every proper cone tested (`[int]`, §C). It is **not** proven in general. The cone note says CONJECTURED in §6, which is correct. |
| 20 | §0 verdict table, step 3: "zero for every proper order cone" | OVERSTATED (minor) | The table cell does say "(PROVEN for the chain, COMPUTED in general)", but "every proper order cone" is computed only for n ≤ 5. §6 correctly says CONJECTURED. |
| 21 | Conjecture G evidence description | CONFIRMED honest | `compute/output/cone_lie.txt` matches §8. D_4 and B_4 are samples of 150 cones. For B_4, [q]-homology and [rho] were not run (said in §8, but not in the §0 summary line). (G4) is marked "not tested". The "(G1)–(G3) PROVEN" status for braid inherits row 12's conditionality for (G3). |
| 22 | Conjecture G1 itself | CONJECTURED (unchanged); new COMPUTED evidence | `[G1]` passes on all 10 368 top-cones of the 6 new arrangements (§C). |
| 23 | §8 positive controls and counts (A_2–A_4, B_2, B_3, D_4, B_4) | UNCHECKED here except by re-running | `python3 cone_lie.py --quick` re-ran: ALL CHECKS PASSED (6.9 s). `python3 -m unittest test_cone_lie`: 7 tests OK. The full run (A_4, D_4, B_4) was not re-run. |

## B. Re-derivations

### B.1 Steps 1–2
- **β_{FG} is isotone.** β_{FG}(i) is the lexicographic rank of
  (β_F(i), β_G(i)), and both coordinates are isotone.
- **The relation xy = x and yx = y.** In Σ_n, xy = x means that supp y is
  coarser than or equal to supp x. So the relation says that x and y have
  the same underlying set partition. A sub-LRB inherits this relation.
- **Kernels of isotone surjections are exactly the π with P/π acyclic.** If
  P/π is acyclic, a linear extension of P/π gives β. Conversely, β induces a
  linear order on the blocks that is compatible with <_P.

### B.2 Lemma L
- (⇐) The lune's conditions on z(H) ⊇ S_max force the signs of V.
- (⇒) If H_e = s_e ≠ 0 for some e ∈ S_max, put D′ = H̄D.
  - Then HD′ = HH̄D = HD = D, so D′ ∈ L(H, D).
  - But D′_e = −s_e, so D′ ∉ V.

### B.3 Lemma E
- **Case h ∉ z(H).** Membership in the lune ignores the sign at h. So
  partners C, C′ across a wall on h are both in L or both out, and they
  contribute C_h F + (−C_h) F = 0.
- **Case h ∈ z(H).** All C ∈ L have C_h = D_h. The facet F lies in the image
  iff its D_h-side neighbour satisfies the lune conditions on z(H) ∖ h.
  - Those conditions are conditions on the hyperplanes h ∩ e of A^h that
    contain s = span H. Several e may give the same h ∩ e; the conditions
    then coincide or are contradictory, in which case the image is 0.
  - s ⊆ h is a flat of A^h, and s ≠ 0 because H ≠ O and A is essential. So
    the set is a non-singleton lune of A^h.
  - The edge case z(H) = {h} gives s = h, so the image is the whole chamber
    sum of A^h. That is the lune of a chamber of A^h, and it is a
    non-singleton since rank A^h = d − 1 ≥ 1.

### B.4 Theorem 5.2
The induction is on d.
- **Support of E_h(X).** Let X ∈ Lune be supported on V. Then E_h(X) is
  supported on V^h, the chambers of A^h in |V| ∩ h.
- **V^h is a top-cone of A^h.** |V| ∩ h is cut out by the A^h half-spaces
  h ∩ {s_e x_e ≥ 0}.
- **V^h is pointed:** |V^h| = |V| ∩ h, so lin(V^h) = lin(V) ∩ h = 0.
- **Every F ∈ V^h has a neighbour in V.** A relative-interior point of F lies
  in some closed chamber of V, which must then be adjacent along F.
- **Conclusion of the step.** By induction E_h(X) = 0. Its coefficient at F
  is C_h(c_C − c_{C′}), so c_C = c_{C′} (with c := 0 off V).
- **Ending the argument.**
  - The chambers of the convex set |V| are gallery-connected, so c is
    constant on V.
  - V ≠ all chambers, because lin(all) = R^d ≠ 0 and d ≥ 1. So a gallery
    from V to its complement exits through a boundary wall, where c = 0.
- **Where the hypotheses enter.**
  - Pointedness is used exactly in the two places above.
  - Reality is used for sign vectors and convexity.
  - Centrality is used for the Tits product and for lunes.
  - Essentiality is used for "lune is a singleton ⟺ H = O" and for A^h being
    essential.

### B.5 Essential hypothesis (PROVEN)
- **Counterexample to the literal statement.** Take A non-essential with
  centre W ≠ 0, e.g. the braid arrangement A_2 in R^3.
  - Every top-cone V has lin(V) ⊇ W ≠ 0, so no V is pointed in the sense
    lin(V) = 0.
  - Faces, Tits product and lunes are those of the essentialization A/W,
    with O = W.
  - So a single chamber V has chamber sum ∉ Lune, by Thm 5.2 applied to A/W.
  - Hence Prop. 7.1(a) "sum ∈ Lune ⟺ V not pointed" fails literally.
- **Repair.** Replace "lin(V) = 0" by "lin(V) = ∩_{e∈A} h_e", or assume
  essential, as §1 of the cone note does. Every conclusion then holds.
- **Unit test.** `test_not_essential_rejected` documents that the audit code
  refuses non-essential input rather than silently testing it.

### B.6 Prop. 7.1
- **(a), non-pointed V.** Let Z = {e : h_e ⊇ lin V}. This is a flat ≠ A
  (A essential, lin V ≠ 0), and Z ⊇ S_max. So V is a union of Z-classes,
  each a non-singleton lune (row 4).
- **(a), pointed V.** Thm 5.2.
- **(b).** Lie = Lune^⊥, with Lune spanned by non-singleton lunes, and these
  are non-pointed cones. So the vanishing conditions on "non-singleton lunes"
  and on "non-pointed top-cones" are equivalent.
- **The printed condition is too strong.** "Every non-singleton top-cone"
  adds pointed cones such as {x_1 ≤ x_2, x_1 ≤ x_3}. Lie elements need not
  vanish there: [[1,2],3] has sum 1 on {123, 132}.

### B.7 §6 (intrinsic Lie part)
- **Status.** No proof for general proper V was found here. I tried
  boundary walls and facet faces; these give only the total-sum condition.
- **The direct computation** (row 19) removes the dependence on Brown's
  theorem for the tested cones. It does not upgrade the general claim, which
  stays CONJECTURED.
- **The step-3 conclusion survives without it.** "Intrinsic LRB theory
  cannot produce H_P" already follows from the chain example, which is
  PROVEN: H_P ≠ 0 there while Lie^int = 0.

## C. Independent computation (COMPUTED)

Script: `compute/audit_cone_lune.py` (plain Python 3, no dependencies).
Tests: `compute/test_audit_cone_lune.py`.

**Method.** It differs from `cone_lie.py`, which closes cocircuits under the
Tits product.
- Exact arithmetic is over Q, or over Q(√5) for H_3.
- **Faces.** Covectors are the sign vectors of sums of k signed rays
  (1-flats), for k ≤ d. This is complete, because every face contains a
  simplicial subcone on its extreme rays.
- **Completeness check.** It is certified against the exact Zaslavsky counts:
  #topes = Σ|μ(∅, X)| and #covectors = Σ_{X ≤ Y}|μ(X, Y)|.
- **Lunes** are L(H, D) = {C : HC = D}, built from the Tits product.
- **Lie := Lune^⊥** is an exact rational nullspace. No Ree or Aguiar–Mahajan
  input is used. Membership in Lune is tested exactly, as integer
  orthogonality to that basis.
- **Theorem 5.2.** rank_p(Lie|_V) = |V| implies rank_Q = |V|.
- **[G1] and [int]** use rank_p only in the direction that is rigorous over Q.

**Arrangements.** None of these is in the cone note's list.

| arrangement | d | hyperplanes | chambers | top-cones tested | pointed | Thm 5.2 |
|---|---|---|---|---|---|---|
| A_1 × A_2 (reducible) | 3 | 4 | 12 | 57 (all) | 24 | 24/24 |
| resonance, all 0/1 normals in R^3 | 3 | 7 | 32 | 397 (all) | 298 | 298/298 |
| A_2 × A_2 (reducible) | 4 | 6 | 36 | 361 (all) | 144 | 144/144 |
| generic 6 in R^5 | 5 | 6 | 62 | 715 (all) | 242 | 242/242 |
| non-generic 7 in R^4 | 4 | 7 | 68 | 1093 (all) | 704 | 704/704 |
| H_3 (non-crystallographic) | 3 | 15 | 120 | 7745 (all) | 7294 | 7294/7294 |

On every row, the following checks pass:
- [faces], [class] and [E];
- [L], on a seeded sample of up to 300 cones × all lunes;
- [7.1a] and [G1], on all cones;
- [7.1b];
- [int], on all proper cones, except H_3, where 1500 sampled proper cones
  were tested.

Further checks:
- dim Lune^⊥ = |μ| for every arrangement (5, 9, 4, 5, 13, 45). This
  reproduces dim Lie[A] = |μ(L(A))| without citing it.
- H_3 control: 31 lines (6 + 10 + 15), 120 chambers and 363 faces, which is
  the f-vector 1 + 62 + 180 + 120.

**Positive controls** (`[CTL]`, all fire):
- dropping one line breaks the Zaslavsky tope count;
- a half-plane of A_2 is non-pointed and dependent mod Lune;
- a lune with one chamber removed is caught by the exact E_h test;
- the full A_2 has dim Lie^int = dim Lie = 2, so the [int] instrument can
  return a nonzero answer.

## Reproduce

From `compute/`:

    python3 audit_cone_lune.py > output/audit_cone_lune.txt   # ~14 s, ends ALL CHECKS PASSED, exit 0
    python3 -m unittest test_audit_cone_lune                   # 6 tests, ~2 s
    python3 cone_lie.py --quick                                # the audited script, ~7 s
    python3 -m unittest test_cone_lie                          # the audited tests, 7 tests
