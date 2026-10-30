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
