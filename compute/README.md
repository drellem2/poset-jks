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
