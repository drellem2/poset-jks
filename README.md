# poset-jks

Research program on a poset generalization of the Joyal–Klyachko–Stanley theorem.

**Conjecture.** For a finite poset P on [n], the top homology of the lattice of
order-preserving partitions of P is, as an Aut(P)-module, the sign twist of the
span of {w·e_ζ : w a linear extension of P} in C[S_n], where e_ζ is the
cyclic Fourier idempotent. For the antichain this is classical JKS; the
dimensions agree for every P by Jenča–Sarkoci. Checked by computer for all
posets with n ≤ 5.

The note: [`notes/poset_jks_research_note.tex`](notes/poset_jks_research_note.tex).
Open problems are in its sections "Status: proved, supported, and open" and
"Concrete next research steps".

Independent reproduction of the n ≤ 5 computation (extended to all n = 6):
[`notes/reproduce_character_identity_n_le_5.md`](notes/reproduce_character_identity_n_le_5.md),
code in [`compute/`](compute/) (`cd compute && python3 poset_jks_check.py --help`).

`./build.sh` builds the note to PDF if a TeX toolchain is present.

## Computations

- `python3 compute/cyclic_posets.py [NMAX]` (default 7; plain Python) — brute-force
  checks of a_n, b_n = |B_n| (cyclic-compatible posets), b_n = n[x^n] log A(x),
  Σ_P e_C(P) = (n−1)! b_n and the C_n-action on B_n. Findings and proof:
  [`notes/cyclic_compatible_posets_bn.md`](notes/cyclic_compatible_posets_bn.md).
- `python3 compute/audit_cyclic_posets.py [--b8]` — independent re-check of the above
  (all labeled posets n ≤ 6, explicit cyclic-factorization bijection, character of
  ⊕_P Lie(P); `--b8` adds a_n and b_n via Lemma 1(c) to n = 8). Audit:
  [`notes/audit_cyclic_compatible_posets_bn.md`](notes/audit_cyclic_compatible_posets_bn.md).
- `cd compute && python3 splitting_cycles.py --nmax 5 --nmax-comb 6` (plain Python, ~4 s) —
  splitting cycles vs shuffles (explicit JKS map), the counterexample to the
  note's restricted image identity, and the span of linear-extension splitting
  cycles for all posets n ≤ 6. Findings, literature/novelty check and
  bibliography corrections:
  [`notes/literature_novelty_jks_maps.md`](notes/literature_novelty_jks_maps.md).
- `cd compute && python3 poset_lie_structure.py` (plain Python, ~40 s) — checks every
  step of a proposed proof of the character identity for all posets (Weisner's
  theorem on the orbit partition; n ≤ 6 plus n = 7, 8 examples), direct homology of
  the global module HH_n against eq. (frob) for n ≤ 6 (fixes the sign twist), the
  primitives of the Hopf monoid of posets with a linear extension (n ≤ 4), and the
  e_ζ-model bracket test. Findings (proof pending independent audit):
  [`notes/global_module_operations_plethlog.md`](notes/global_module_operations_plethlog.md).
- `cd compute && python3 conjecture_s.py --nmax 6 --ne 6 --nrho 5` (plain Python, ~3 s;
  `--nmax 7 --ne 7` ~90 s) — linear extensions modulo proper shuffles: the
  contraction lemma, W_P ∩ Sh_n = R_P, the first-block basis, and Conjecture S
  for all posets n ≤ 7. Proof of Conjecture S for every finite poset (hence the
  main conjecture for connected P), pending independent audit:
  [`notes/conjecture_s_splitting_cycles_span.md`](notes/conjecture_s_splitting_cycles_span.md).
