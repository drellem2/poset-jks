# compute/

Every script here is plain Python 3 and has no dependencies. Run each command
below **from this directory**. Each script exits with status 0 iff all its
checks pass, and each includes positive controls: deliberately wrong variants
that must fail. Archived outputs are in `output/`. Ranks are computed modulo a
large prime, and are used only in directions that are valid over Q.

The consolidated account of what these computations support is
`../notes/poset_jks_theorem.tex`, §8 ("Computational record"). Each entry
below names the notes file whose Reproduce section the command comes from.

Run all unit tests (the slow sweeps are not part of them):

    python3 -m unittest discover -p 'test_*.py'

## Index

One row per script (unit tests `test_*.py` omitted). The notes file is
the one whose Reproduce section the commands below come from.

| Script | Notes file |
|---|---|
| `poset_jks_check.py` | `../notes/reproduce_character_identity_n_le_5.md` |
| `n7_sweep.py` | `../notes/n7_character_sweep_and_homology_crosscheck.md` |
| `equivariant_homology.py` | `../notes/n7_character_sweep_and_homology_crosscheck.md` |
| `poset_lie_structure.py` | `../notes/global_module_operations_plethlog.md` |
| `fixed_point_mobius.py` | `../notes/fixed_point_mobius_identity.md` |
| `audit_character_identity.py` | `../notes/audit_character_identity_proof.md` |
| `mu_op_elementary.py` | `../notes/mu_op_elementary.md` |
| `audit_mu_op_elementary.py` | `../notes/audit_mu_op_elementary.md` |
| `splitting_cycles.py` | `../notes/literature_novelty_jks_maps.md` |
| `audit_jks_maps.py` | `../notes/audit_literature_novelty_jks_maps.md` |
| `conjecture_s.py` | `../notes/conjecture_s_splitting_cycles_span.md` |
| `audit_conjecture_s.py` | `../notes/audit_conjecture_s.md` |
| `cone_lie.py` | `../notes/cone_lune_lie_theory.md` |
| `audit_cone_lune.py` | `../notes/audit_cone_lune_lie_theory.md` |
| `general_theory.py` | `../notes/general_theory.md` |
| `audit_general_theory_cones.py` | `../notes/audit_general_theory_cones.md` |
| `audit_theorem_c.py` | `../notes/audit_theorem_c.md` |
| `audit_general_theory_hopf.py` | `../notes/audit_general_theory_hopf.md` |
| `oriented_matroid_cones.py` | `../notes/oriented_matroid_cones.md` |
| `audit_oriented_matroid_cones.py` | `../notes/audit_oriented_matroid_cones.md` |
| `fixed_point_formula.py` | `../notes/fixed_point_formula.md` |
| `audit_fixed_point_formula.py` | `../notes/audit_fixed_point_formula.md` |
| `audit_prop_w_prime.py` | `../notes/audit_prop_w_prime.md` |
| `audit_theorem_w2.py` | `../notes/audit_theorem_w2.md` |
| `vanishing_criterion.py` | `../notes/vanishing_criterion.md` |
| `audit_vanishing_criterion.py` | `../notes/audit_vanishing_criterion.md` |
| `audit2_vanishing_criterion.py` | `../notes/audit2_vanishing_criterion.md` |
| `prior_art_vanishing_criterion.py` | `../notes/prior_art_vanishing_criterion.md` |
| `per_cone_vanishing.py` | `../notes/per_cone_vanishing.md` |
| `audit_per_cone_vanishing.py` | `../notes/audit_per_cone_vanishing.md` |
| `prior_art_per_cone_vanishing.py` | `../notes/prior_art_per_cone_vanishing.md` |
| `conjecture_cr_v.py` | `../notes/conjecture_cr_v.md` |
| `natural_isomorphism.py` | `../notes/natural_isomorphism.md`, `../notes/wgt_check_fix.md` |
| `audit_natural_isomorphism.py` | `../notes/audit_natural_isomorphism.md` |
| `cyclic_posets.py` | `../notes/cyclic_compatible_posets_bn.md` |
| `audit_cyclic_posets.py` | `../notes/audit_cyclic_compatible_posets_bn.md` |
| `second_read_globalind.py` | `../notes/audit_cyclic_compatible_posets_bn.md`, §C |
| `linear_extensions.py` | `../notes/linear_extensions.md` |
| `audit_linear_extensions.py` | `../notes/audit_linear_extensions.md` |
| `cyclic_sieving_cyc.py` | `../notes/cyclic_sieving_cyc.md` |
| `audit_cyclic_sieving_cyc.py` | `../notes/audit_cyclic_sieving_cyc.md` |
| `moonshine_scoping.py` | `../notes/moonshine_scoping.md` |
| `moonshine_lookup.py` | `../notes/moonshine_scoping.md` (network; asserts nothing) |
| `audit_moonshine_scoping.py` | `../notes/audit_moonshine_scoping.md` |
| `moonshine_residual.py` | `../notes/moonshine_residual.md` |
| `lean_js_route.py` | `../notes/lean_js_route.md` |
| `audit_lean_js_route.py` | `../notes/audit_lean_js_route.md` |

## The character identity (eq. characterconj)

`poset_jks_check.py` checks the character identity for every unlabeled poset
with n <= NMAX, and for the seed note's n = 6 examples. F0 is the note's
identity. F1-F4 are the opposite convention and three deliberately wrong
formulas, reported as positive controls. Findings:
`../notes/reproduce_character_identity_n_le_5.md`.

    python3 poset_jks_check.py --nmax 6 --control-counts --examples \
        --tsv output/character_table.tsv > output/summary.txt          # ~5 s
    python3 -m unittest test_poset_jks_check

`n7_sweep.py` runs the same check on all 2045 unlabeled posets with n = 7.
It imports `poset_jks_check.analyse` and uses a faster canonical form.
`equivariant_homology.py` is a separate instrument for the left-hand side. It
computes the trace of g on ker(d: C_{n-3} -> C_{n-4}) of the order complex of
the proper part of OP(P). It uses neither Möbius numbers nor Lefschetz.
Findings: `../notes/n7_character_sweep_and_homology_crosscheck.md`.

    python3 n7_sweep.py --n 7 --jobs 3 --tsv output/n7_character_table.tsv \
        > output/n7_summary.txt                                        # ~70 s on 3 workers
    python3 equivariant_homology.py output/character_table.tsv --select all --n 6 \
        --out output/n6_homology_all.tsv > output/n6_homology_all.txt
    python3 equivariant_homology.py output/character_table.tsv --select discriminating \
        --n 6 --with-identity --out output/n6_homology_discriminating.tsv \
        > output/n6_homology_discriminating.txt
    # n = 7: ~38 CPU-min. output/n7_homology_all.* is the merge of three runs
    # with --shard 0/3, 1/3, 2/3 (rows sorted by poset id).
    python3 equivariant_homology.py output/n7_character_table.tsv --select all --n 7 \
        --out output/n7_homology_all.tsv > output/n7_homology_all.txt
    python3 -m unittest test_n7_and_homology

## Proofs of the character identity, and their audit

`poset_lie_structure.py` checks Proof I (Weisner) step by step: T1-T5 for
all posets with n <= 6, plus n = 7, 8 examples. It also checks the global
module HH_n by direct homology against eq. (frob) for n <= 6, which fixes the
sign twist; the primitives of the Hopf monoid of posets with a linear
extension (n <= 4); and the e_zeta-model bracket test. Findings:
`../notes/global_module_operations_plethlog.md`.

    python3 poset_lie_structure.py > output/poset_lie_structure.txt   # all sections, ~40 s
    python3 poset_lie_structure.py --theorem 6    # proof steps T1-T5, ~9 s
    python3 poset_lie_structure.py --homology 6   # HH_n vs (frob), ~31 s
    python3 poset_lie_structure.py --hopf 4       # primitives of Q
    python3 poset_lie_structure.py --bracket 5    # e_zeta-model bracket test
    python3 -m unittest test_poset_lie_structure

`fixed_point_mobius.py` brute-force checks every lemma of Proof II (Crapo
complementation) for all unlabeled posets with n <= 6, and for
repeated-component disjoint unions at n = 7, 8, 9. Findings:
`../notes/fixed_point_mobius_identity.md`.

    python3 fixed_point_mobius.py --nmax 6 --large 7 8 9 > output/fixed_point_mobius.txt   # ~2 min
    python3 -m unittest test_fixed_point_mobius

`audit_character_identity.py` is the independent audit of both proofs. It is
self-contained and imports no other script here. Findings:
`../notes/audit_character_identity_proof.md`.

    python3 audit_character_identity.py --nmax 6 --large 7 8 9 --homology 6 \
        > output/audit_character_identity.txt                          # ~5 min
    python3 audit_character_identity.py --nmax 0 --large 10 --skip-identity-large \
        > output/audit_character_identity_n10.txt                      # ~5 min
    # positive controls: each must exit 1
    for c in no_mu_o no_sgn trace_sign no_mu_X crapo_drop lin_not_ec; do
      python3 audit_character_identity.py --nmax 5 --large --homology 5 --control $c; done
    python3 -m unittest test_audit_character_identity

## Splitting cycles, Prop. Phi, Prop. C, Conjecture S

`splitting_cycles.py` checks Wachs's splitting cycles against the shuffle
relations (Prop. Phi, n <= 5), the e_zeta / Klyachko / adjoint-Dynkin
realizations (Prop. C), and whether the splitting cycles of linear extensions
span H_P (n <= 6). Findings: `../notes/literature_novelty_jks_maps.md`.

    python3 splitting_cycles.py --nmax 5 --nmax-comb 6 > output/splitting_cycles.txt   # ~4 s
    python3 -m unittest test_splitting_cycles

The Topics Ex. 10.9 counterexample count is the one-liner in §6 of that
note. It prints `3 4 2 / 4 15 9 / 5 62 43`.

`audit_jks_maps.py` is the independent audit of those findings. It re-checks
Prop. Phi at chain level (n <= 6), Lemma B and Prop. C, Lemma D, Conjecture S
with a direct dim H_P computation (all posets n <= 6), the criterion
mu(O(P)^g) = 0 for connected P (n <= 6), and the Topics Ex. 10.9 counts.
Findings: `../notes/audit_literature_novelty_jks_maps.md`.

    python3 audit_jks_maps.py > output/audit_jks_maps.txt   # ~40 s
    python3 -m unittest test_audit_jks_maps

`conjecture_s.py` checks the proof of Conjecture S: the contraction lemma
E_{a,x}(Sh) ⊆ Sh, ker L_a = Sh, W_P ∩ Sh_n = R_P, the first-block basis B_P,
and chain-level independence of {rho_w : w ∈ B_P} (n <= 5). Findings:
`../notes/conjecture_s_splitting_cycles_span.md`.

    python3 conjecture_s.py --nmax 6 --ne 6 --nrho 5 > output/conjecture_s.txt   # ~3 s
    python3 conjecture_s.py --nmax 7 --ne 7      # ~90 s; output not archived
    python3 -m unittest test_conjecture_s

`audit_conjecture_s.py` is the independent audit of the Conjecture S proof.
It imports no other module of this repository. It checks Lemma 1 and its
adjoint, Lemmas 2-6, Theorems A and B (every base component), the Ree-free
shuffle-membership cross-check, and Theorem C / Cor. 5.5 at chain level
without Prop. Phi or Jenča–Sarkoci (n <= 6). Findings:
`../notes/audit_conjecture_s.md`.

    python3 audit_conjecture_s.py --nmax 6 --ne 6 --nlem 6 --nchn 6 --nree 6 \
        > output/audit_conjecture_s.txt                                # ~16 min
    python3 -m unittest test_audit_conjecture_s

## Cone/lune Lie theory

`cone_lie.py` checks the cone/lune statements for the order cone C_P and for
other real arrangements: the lune form of Conjecture S, pointed top-cones,
and Conjecture G on A_2, A_3, A_4, B_2, B_3 and samples of D_4, B_4 (parts
(G1)–(G3) are now proved as Theorem G\*; see `general_theory.py` below).
Findings: `../notes/cone_lune_lie_theory.md`.

    python3 cone_lie.py --quick                  # ~7 s, skips A4, D4, B4
    python3 cone_lie.py > output/cone_lie.txt    # all arrangements
    python3 -m unittest test_cone_lie

`audit_cone_lune.py` is the independent audit of those findings. It imports
no module of this repo and uses exact arithmetic (over Q, and Q(sqrt5) for
H_3), on six arrangements outside the note's list. Findings:
`../notes/audit_cone_lune_lie_theory.md`.

    python3 audit_cone_lune.py > output/audit_cone_lune.txt
    python3 -m unittest test_audit_cone_lune

## The natural-isomorphism question

`natural_isomorphism.py` checks the findings of
`../notes/natural_isomorphism.md`: R_P e_zeta = 0 iff P is connected or
n <= 2, the witness coefficient, that the truncation map psi_P is an
isomorphism (Theorem Psi), phi_Sigma, Lie_n e_zeta, and the disjoint-sum
maps. Its `[wgt]` check is defective (it uses class representatives outside
LinExt P), so its lambda = 1 counts are wrong; see
`../notes/audit_natural_isomorphism.md`, section 5.

    python3 natural_isomorphism.py --nmax 6 > output/natural_isomorphism.txt   # ~6 s
    python3 natural_isomorphism.py --nmax 7 --only ext,psi > output/natural_isomorphism_n7.txt  # ~100 s
    python3 -m unittest test_natural_isomorphism

`audit_natural_isomorphism.py` is the independent audit. It imports no module
of this repo. Findings: `../notes/audit_natural_isomorphism.md`.

    python3 audit_natural_isomorphism.py --nmax 6 > output/audit_natural_isomorphism.txt   # ~40 s
    python3 -m unittest test_audit_natural_isomorphism

## Cyclic-compatible posets, b_n and the global module

`cyclic_posets.py` brute-force checks a_n, b_n = |B_n|, b_n = n[x^n] log A(x),
Σ_P e_C(P) = (n−1)! b_n and the C_n-action on B_n. Findings:
`../notes/cyclic_compatible_posets_bn.md`.

    python3 cyclic_posets.py 7     # all checks, ~25 s
    python3 cyclic_posets.py 8     # adds a_8, b_8 (b_8 via Lemma 1(c)), a few minutes

`audit_cyclic_posets.py` is the independent re-check. It uses all labeled
posets with n <= 6, an explicit cyclic-factorization bijection, and the
character of ⊕_P Lie(P). `--b8` adds a_n and b_n via Lemma 1(c) up to n = 8.
Findings: `../notes/audit_cyclic_compatible_posets_bn.md`.

    python3 audit_cyclic_posets.py         # n <= 6, ~13 s
    python3 audit_cyclic_posets.py --b8    # n <= 8, a few minutes

`second_read_globalind.py` checks the unconditional identity
⊕_P Lie(P) ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]) by direct linear algebra in C[S_n],
with two positive controls (n <= 5). Findings: §C of
`../notes/audit_cyclic_compatible_posets_bn.md`.

    python3 second_read_globalind.py 5 > output/second_read_globalind.txt   # ~2 s
    python3 -m unittest test_second_read_globalind

## The homology-free base case μ(OP(P)) = (−1)^{n−1} e_C(P)

`mu_op_elementary.py` checks Theorem A and Lemmas M, U, D, W, F, C of the
two homology-free proofs, with three negative controls. Findings:
`../notes/mu_op_elementary.md`.

    python3 mu_op_elementary.py            # n <= 6, about 16 s
    python3 -m unittest test_mu_op_elementary

`audit_mu_op_elementary.py` is the independent audit. Findings:
`../notes/audit_mu_op_elementary.md`.

    python3 audit_mu_op_elementary.py            # n <= 6 every check, n = 7 Theorem A, C, D, W; about 3 min
    python3 audit_mu_op_elementary.py --nmax 5   # about 1 s
    python3 -m unittest test_audit_mu_op_elementary

## General theory: cones of arrangements, Theorem G*, the Hopf side

`general_theory.py` checks the cone wedge theorem, cone Zaslavsky, the
Foata lemma, Prop. 3, Theorem G\* (`[q=m]`, `[eq]`) and the Hopf-side
Theorems 6–8. It imports `cone_lie.py` and `poset_jks_check.py`. Findings:
`../notes/general_theory.md`.

    python3 general_theory.py > output/general_theory.txt   # ~25 s, ALL CHECKS PASSED, exit 0
    python3 general_theory.py --quick                        # ~1 s: no A4/D4, posets n <= 4
    python3 -m unittest test_general_theory                  # < 1 s, includes the negative controls

`audit_general_theory_cones.py` audits §§0–1 and checks Theorem C (the
chamber cycles span) on 6,910 cones. Findings:
`../notes/audit_general_theory_cones.md`.

    python3 audit_general_theory_cones.py      # full run, about 2.5 min; prints the log
    python3 -m unittest test_audit_general_theory_cones

`audit_theorem_c.py` is the independent audit of Theorem C and Props. A, B.
Findings: `../notes/audit_theorem_c.md`.

    python3 audit_theorem_c.py            # full run, about 3 min; prints the log
    python3 audit_theorem_c.py --quick    # about 20 s
    python3 -m unittest test_audit_theorem_c

`audit_general_theory_hopf.py` audits §2 (Q′, Theorems 6–8). Findings:
`../notes/audit_general_theory_hopf.md`.

    python3 audit_general_theory_hopf.py > output/audit_general_theory_hopf.txt   # ~40 s, ALL CHECKS PASSED, exit 0
    python3 -m unittest test_audit_general_theory_hopf                           # < 1 s

## Oriented matroids

`oriented_matroid_cones.py` checks Theorems 1, 2 and C/G\* for T-convex sets
of topes, on realizable and non-realizable oriented matroids. Findings:
`../notes/oriented_matroid_cones.md`.

    python3 oriented_matroid_cones.py > output/oriented_matroid_cones.txt   # ~60 s, ends "ALL PASS", exit 0
    python3 oriented_matroid_cones.py --quick                                # ~30 s: A3, Pappus, one non-Pappus, subsampled [lem02]
    python3 -m unittest test_oriented_matroid_cones                          # ~15 s, includes the controls

`audit_oriented_matroid_cones.py` is the independent audit. It uses
`$AUDIT_WORKERS` worker processes (default 3). Findings:
`../notes/audit_oriented_matroid_cones.md`.

    python3 audit_oriented_matroid_cones.py > output/audit_oriented_matroid_cones.txt   # ~6 min, ends "ALL PASS", exit 0
    python3 audit_oriented_matroid_cones.py --quick     # ~8 s: A3, B3, non-Pappus, N on 400 cones
    python3 -m unittest test_audit_oriented_matroid_cones   # ~5 s

## The fixed-point formula for cones

`fixed_point_formula.py` checks EZ, EZ′, CF and Props. W, W′ on 7,200 pairs
(V, g). Findings: `../notes/fixed_point_formula.md`.

    python3 fixed_point_formula.py > output/fixed_point_formula.txt   # ~45 s, ALL CHECKS PASSED, exit 0
    python3 fixed_point_formula.py --quick                             # < 1 s: A2, A3, B2, B3
    python3 fixed_point_formula.py --types D4,H3                       # any subset
    python3 -m unittest test_fixed_point_formula                       # < 1 s, positive and negative controls

`audit_fixed_point_formula.py` is the independent audit. Findings:
`../notes/audit_fixed_point_formula.md`.

    python3 audit_fixed_point_formula.py            # full run, about 3 min; exit 0
    python3 audit_fixed_point_formula.py --quick    # A3, B3, tetra7, hex6, braid n <= 4; a few seconds
    python3 -m unittest test_audit_fixed_point_formula

`audit_prop_w_prime.py` audits Prop. W′ and G\* for g outside the reflection
group, and checks Theorem W″. Findings: `../notes/audit_prop_w_prime.md`.

    python3 audit_prop_w_prime.py > output/audit_prop_w_prime.txt   # ~30 s; ends "ALL CHECKS PASSED", exit 0
    python3 audit_prop_w_prime.py --quick                             # < 1 s: A3, B3, tetra7, hex7
    python3 -m unittest test_audit_prop_w_prime                       # < 1 s, positive and negative controls

`audit_theorem_w2.py` is the independent audit of Theorem W″. Findings:
`../notes/audit_theorem_w2.md`.

    python3 audit_theorem_w2.py > output/audit_theorem_w2.txt   # ~4 min; ends "ALL CHECKS PASSED", exit 0
    python3 audit_theorem_w2.py --quick                           # ~5 s: coord3, G2, A2xA1, coordsum3, cyc3
    python3 -m unittest test_audit_theorem_w2                     # ~1 s: FM, Betti, and theorem controls

## Vanishing of the cone Lie character

`vanishing_criterion.py` checks Formula Z, Theorem S and Theorem A.
Findings: `../notes/vanishing_criterion.md`.

    python3 vanishing_criterion.py --n9 > output/vanishing_criterion.txt   # ~35 s, ALL CHECKS PASSED, exit 0
    python3 vanishing_criterion.py --quick                                 # ~1 s: A2, A3, B2, B3; type A n <= 6
    python3 vanishing_criterion.py --types D4,H3                           # any subset; F4 is sampled (--samples k)
    python3 -m unittest test_vanishing_criterion                           # ~3 s, positive and negative controls

`audit_vanishing_criterion.py` is the first independent audit. Findings:
`../notes/audit_vanishing_criterion.md`.

    python3 audit_vanishing_criterion.py > output/audit_vanishing_criterion.txt   # ~75 s, ends "ALL CHECKS PASSED", exit 0
    python3 audit_vanishing_criterion.py --quick                                  # ~2 s: no A4, type A n <= 5, no Section 6 block
    python3 -m unittest test_audit_vanishing_criterion                            # ~1 s, positive and negative controls

`audit2_vanishing_criterion.py` is the second independent audit, with six
non-Coxeter arrangements. Findings: `../notes/audit2_vanishing_criterion.md`.

    python3 audit2_vanishing_criterion.py > output/audit2_vanishing_criterion.txt   # ~2 min, ends "ALL CHECKS PASSED", exit 0
    python3 audit2_vanishing_criterion.py --quick                                    # ~80 s: n <= 6 for Theorem A; A_4 and generic 5 in R^4 omitted
    python3 -m unittest test_audit2_vanishing_criterion                              # ~4 s, positive and negative controls

`prior_art_vanishing_criterion.py` checks the computations of the prior-art
note. Findings: `../notes/prior_art_vanishing_criterion.md`.

    python3 prior_art_vanishing_criterion.py > output/prior_art_vanishing_criterion.txt   # ~12 s, ALL CHECKS PASSED, exit 0
    python3 prior_art_vanishing_criterion.py --quick                                        # n <= 6, < 1 s
    python3 -m unittest test_prior_art_vanishing_criterion                                  # < 1 s, positive and negative controls

`per_cone_vanishing.py` checks Lemma M, Theorem Cr, Theorem TA and the
CR_V sweep of the per-cone note. It imports its arrangement code from
`audit2_vanishing_criterion.py` and `vanishing_criterion.py`. Findings:
`../notes/per_cone_vanishing.md`.

    python3 per_cone_vanishing.py > output/per_cone_vanishing.txt   # ~75 s, ends "ALL CHECKS PASSED", exit 0
    python3 per_cone_vanishing.py --quick                           # ~11 s: n <= 5, smaller random families, A_3 link, no A_4 / generic 5 / hexagon 13 / F_4
    python3 -m unittest test_per_cone_vanishing                      # < 1 s, positive and negative controls

`audit_per_cone_vanishing.py` is the independent audit; it imports nothing
from the other scripts. Findings: `../notes/audit_per_cone_vanishing.md`.

    python3 audit_per_cone_vanishing.py > output/audit_per_cone_vanishing.txt   # ~140 s, ends "ALL CHECKS PASSED", exit 0
    python3 audit_per_cone_vanishing.py --quick                                 # ~6 s: n <= 6, smaller random families, no B_3 / generic 5 / D_4
    python3 -m unittest test_audit_per_cone_vanishing                            # < 1 s, positive and negative controls

`prior_art_per_cone_vanishing.py` checks the Björner–Walker split for ±S_n
(3 <= n <= 6) and the smallest complemented lattice with μ = 0. Findings:
`../notes/prior_art_per_cone_vanishing.md`.

    python3 prior_art_per_cone_vanishing.py > output/prior_art_per_cone_vanishing.txt   # ~5 s, ends "ALL CHECKS PASSED", exit 0

`conjecture_cr_v.py` checks the rank-4 counterexample to Conjecture CR_V
(`[CX]`), Theorems P, Q, Lemma K and Proposition Ln on every swept pair, and
reproduces the per-cone sweep (`[REP]`). CR_V counterexamples are reported,
not counted as failures. The second-implementation check of that note's §0.4
is a loop run once by hand, not part of the script. Findings:
`../notes/conjecture_cr_v.md`.

    python3 conjecture_cr_v.py > output/conjecture_cr_v.txt   # ~45 min, ends "ALL CHECKS PASSED", exit 0
    python3 conjecture_cr_v.py --quick                         # ~90 s
    python3 -m unittest test_conjecture_cr_v                    # ~2 s, positive and negative controls, including the counterexample

## Linear extensions and cyclic sieving

`linear_extensions.py` checks the linear-extensions note: promotion CSPs on
disjoint unions, rotation classes against promotion orbits, counting, and
the structure of C[Lin P]/R_P. `--sections csp,promo,count,burnside,struct`
runs a subset. Findings: `../notes/linear_extensions.md`.

    python3 linear_extensions.py --nmax 7 --rnmax 6 > output/linear_extensions.txt   # about 40 s
    python3 -m unittest test_linear_extensions

`audit_linear_extensions.py` is the independent audit. Findings:
`../notes/audit_linear_extensions.md`.

    python3 audit_linear_extensions.py            # full run, n <= 7 (~75 s, one core)
    python3 audit_linear_extensions.py --quick    # n <= 5 (~4 s)
    python3 -m unittest test_audit_linear_extensions

`cyclic_sieving_cyc.py` checks cyclic sieving for Aut(P) on Cyc(P): the
fake degree on T^{⊔k}, the sweep, and the obstruction search.
`--sections ctl,tk,sweep,obst` runs a subset. Findings:
`../notes/cyclic_sieving_cyc.md`.

    python3 cyclic_sieving_cyc.py --nmax 7 --tkmax 8 > output/cyclic_sieving_cyc.txt   # about 9 s
    python3 -m unittest test_cyclic_sieving_cyc

`audit_cyclic_sieving_cyc.py` is the independent audit; `--jobs=3` runs the
sweeps on three processes. Findings: `../notes/audit_cyclic_sieving_cyc.md`.

    python3 audit_cyclic_sieving_cyc.py > output/audit_cyclic_sieving_cyc.txt   # about 18 s, ends "[done] 0 failures"
    python3 -m unittest test_audit_cyclic_sieving_cyc

## Moonshine

`moonshine_scoping.py` checks the four candidates of the scoping note. It
imports `poset_jks_check.py` and `poset_lie_structure.py`. Section flags
`--controls`, `--witt`, `--ppart`, `--infinite`, `--fock` run one part.
`moonshine_lookup.py` queries OEIS and LMFDB over the network; it is
informational and asserts nothing. Findings: `../notes/moonshine_scoping.md`.

    python3 moonshine_scoping.py > output/moonshine_scoping.txt    # all sections, ~2 s, exit 0 iff all 217 checks pass
    python3 -m unittest test_moonshine_scoping
    python3 moonshine_lookup.py > output/moonshine_lookup.txt      # network: OEIS + LMFDB, ~1-3 min

`audit_moonshine_scoping.py` is the independent, self-contained audit.
Section flags `--W`, `--H`, `--P`, `--I`, `--D`, `--F`, `--A`. Findings:
`../notes/audit_moonshine_scoping.md`.

    python3 audit_moonshine_scoping.py > output/audit_moonshine_scoping.txt   # ~25 s, exit 0 iff all 59 checks pass
    python3 -m unittest test_audit_moonshine_scoping

`moonshine_residual.py` checks the residual candidates. Section flags
`--U`, `--E`, `--S`, `--B`, `--G`, `--T`. Findings:
`../notes/moonshine_residual.md`.

    python3 moonshine_residual.py > output/moonshine_residual.txt   # ~35 s, exit 0 iff all 42 checks pass
    python3 -m unittest test_moonshine_residual

## Route C for the Lean input jencaSarkoci_homology

`lean_js_route.py` checks the combinatorial claims of Route C (Lemma K,
Proposition C, Theorem V) on all 405 posets with n <= 6, with four positive
controls. Findings: `../notes/lean_js_route.md`.

    python3 lean_js_route.py --nmax 6 --procs 3 > output/lean_js_route_n6.txt   # ~55 s
    python3 -m unittest test_lean_js_route

`audit_lean_js_route.py` is the independent audit, with exact ranks over Q.
Findings: `../notes/audit_lean_js_route.md`.

    python3 audit_lean_js_route.py --nmax 6 --procs 3 > output/audit_lean_js_route_n6.txt   # ~4 min
    python3 -m unittest test_audit_lean_js_route
