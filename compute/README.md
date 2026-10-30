# compute/

`poset_jks_check.py` checks the character identity (eq. characterconj of the
note) for every unlabeled poset with n <= NMAX and for the named n=6 examples.
It uses plain Python 3 and has no dependencies. Findings:
`../notes/reproduce_character_identity_n_le_5.md`.

Run from this directory:

    # reproduces output/summary.txt and output/character_table.tsv (~5 s)
    python3 poset_jks_check.py --nmax 6 --control-counts --examples \
        --tsv output/character_table.tsv > output/summary.txt
    # tests
    python3 -m unittest test_poset_jks_check

The program exits with status 0 iff the note's identity (F0) holds on every
case. F1-F4 are the opposite convention and three deliberately wrong formulas.
They are reported as positive controls.

`splitting_cycles.py` checks Wachs's splitting cycles against the shuffle
relations, the e_ζ / Klyachko / adjoint-Dynkin realizations, and whether the
splitting cycles of linear extensions span H_P (n ≤ 6). Findings:
`../notes/literature_novelty_jks_maps.md`. Run from this directory:

    python3 splitting_cycles.py --nmax 5 --nmax-comb 6 > output/splitting_cycles.txt   # ~4 s
    python3 -m unittest test_splitting_cycles

`poset_lie_structure.py` checks the steps of the proof of the character
identity in `../notes/global_module_operations_plethlog.md` (T1-T5 for all
posets n <= 6, and n = 7, 8 examples), the global module HH_n by direct
homology against eq. (frob) (n <= 6), the primitives of the Hopf monoid of
posets with a linear extension (n <= 4), and the e_zeta-model bracket test.
Exit status 0 iff every check passes. Run from this directory:

    python3 poset_lie_structure.py > output/poset_lie_structure.txt   # ~40 s
    python3 -m unittest test_poset_lie_structure

`fixed_point_mobius.py` brute-force checks every lemma of the direct proof of
eq. (characterconj) (complements of an orbit-merging element in OP(P)^g,
interval Möbius numbers, fixed-class counts), for all unlabeled posets with
n ≤ 6 and repeated-component disjoint unions at n = 7, 8, 9. Findings:
`../notes/fixed_point_mobius_identity.md`. Run from this directory:

    python3 fixed_point_mobius.py --nmax 6 --large 7 8 9 > output/fixed_point_mobius.txt
    python3 -m unittest test_fixed_point_mobius

## n = 7 sweep and the direct homology cross-check

`n7_sweep.py` runs the same check (it imports `poset_jks_check.analyse`) on
all 2045 unlabeled posets with n = 7. It adds a faster canonical form and tags
the named symmetric families. `equivariant_homology.py` is a second, separate
instrument for the left-hand side. It computes the trace of g directly on
ker(d: C_{n-3} -> C_{n-4}) of the order complex of the proper part of OP(P)
(this kernel equals H~_{n-3}). It works eigenspace by eigenspace over F_p,
with p = 1 mod ord(g), using two primes, and it does not use Moebius numbers.
Findings: `../notes/n7_character_sweep_and_homology_crosscheck.md`.

    # ~70 s on 3 workers
    python3 n7_sweep.py --n 7 --jobs 3 --tsv output/n7_character_table.tsv \
        > output/n7_summary.txt
    # homology trace vs mu side: every n=6 pair, the n=6 discriminating pairs, every n=7 pair
    python3 equivariant_homology.py output/character_table.tsv --select all --n 6 \
        --out output/n6_homology_all.tsv > output/n6_homology_all.txt
    python3 equivariant_homology.py output/character_table.tsv --select discriminating \
        --n 6 --with-identity --out output/n6_homology_discriminating.tsv \
        > output/n6_homology_discriminating.txt
    # n = 7: ~38 CPU-min; output/n7_homology_all.* is the merge of three runs with
    # --shard 0/3, 1/3, 2/3 (rows sorted by poset id)
    python3 equivariant_homology.py output/n7_character_table.tsv --select all --n 7 \
        --out output/n7_homology_all.tsv > output/n7_homology_all.txt
    # tests (includes the JKS closed-form positive control and a corrupted-boundary negative control)
    python3 -m unittest test_n7_and_homology

`conjecture_s.py` checks the proof of Conjecture S in
`../notes/conjecture_s_splitting_cycles_span.md`: the contraction lemma
E_{a,x}(Sh) ⊆ Sh, ker L_a = Sh, W_P ∩ Sh_n = R_P, the first-block basis B_P
(n ≤ 7 with `--nmax 7 --ne 7`), and chain-level independence of
{ρ_w : w ∈ B_P} (n ≤ 5). Exit status 0 iff every check passes. Run from this
directory:

    python3 conjecture_s.py --nmax 6 --ne 6 --nrho 5 > output/conjecture_s.txt   # ~3 s
    python3 -m unittest test_conjecture_s

`second_read_globalind.py` checks the unconditional identity
(+)_P Lie(P) ~= Ind_{C_n}^{S_n}(zeta (x) C[B_n]) by direct linear algebra in
C[S_n], with two positive controls (n <= 5). Findings: section C of
`../notes/audit_cyclic_compatible_posets_bn.md`. Run from this directory:

    python3 second_read_globalind.py 5 > output/second_read_globalind.txt   # ~2 s
    python3 -m unittest test_second_read_globalind
