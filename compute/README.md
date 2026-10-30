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
