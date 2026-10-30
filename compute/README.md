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
and Conjecture G on A_2, A_3, A_4, B_2, B_3 and samples of D_4, B_4. Findings:
`../notes/cone_lune_lie_theory.md`.

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
