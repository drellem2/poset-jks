# poset-jks

Research program on a poset generalization of the Joyal–Klyachko–Stanley theorem.

**Status (October 2026).** The seed note's main conjecture holds as an
abstract isomorphism. For every finite poset P on n ≥ 3 points, the top
homology H_P of the proper part of the lattice of order-preserving partitions
is isomorphic, as an Aut(P)-module, to the sign twist of
Lie(P) = span{w·e_ζ : w a linear extension of P}. There is also a closed
formula for the character. The result is proved twice: once via Weisner's
theorem and once via Crapo's complementation theorem. Both proofs assume
Jenča–Sarkoci Thm 4.5, P. Hall's theorem and the Hopf trace formula, and an
independent audit found that both hold. That isomorphism is abstract, but
there is also an explicit one, for every P: truncate an element of Lie(P) to
the linear extensions and read it modulo shuffles. This truncation map is an
Aut(P)-isomorphism onto C[LinExt P]/R_P, proved by elementary word
combinatorics ("Theorem Ψ"); composed with the splitting-cycle model below it
gives H_P ⊗ sgn ≅ Lie(P) with no choices, compatible with relabelling. In the
stronger sense of naturality along order extensions, an isomorphism exists
exactly on connected posets: for disconnected P with n ≥ 3, no family of maps
compatible with the inclusions into P's own linear extensions is injective.
Both results are independently audited. The seed note's "restricted JKS image
identity" (its eq. restrictionlemma) is **false**. In its place, the splitting
cycles of the linear extensions span H_P, with an explicit basis (formerly
"Conjecture S"). That result is proved and audited, conditional on a cited
theorem of Wachs; it is checked without that input for n ≤ 6. The global
induced-module formula and b_n = n[x^n] log A(x) are proved. The
consolidated, self-contained account, with the epistemic status of every
claim, is
[`notes/poset_jks_theorem.tex`](notes/poset_jks_theorem.tex).

`./build.sh` builds the two TeX notes to PDF if a TeX toolchain is present.

## Notes

- [`notes/poset_jks_theorem.tex`](notes/poset_jks_theorem.tex): the
  consolidated write-up (theorem, proof, corrections, computational record,
  open problems). Start here.
- [`notes/poset_jks_research_note.tex`](notes/poset_jks_research_note.tex):
  the original research note (the seed note), kept unedited. Its
  "open problems" are partly solved, and its eq. (restrictionlemma) is
  false. See the write-up above.

The character identity and the main theorem:
- [`notes/reproduce_character_identity_n_le_5.md`](notes/reproduce_character_identity_n_le_5.md):
  independent reproduction of the character identity, all posets n ≤ 6.
- [`notes/n7_character_sweep_and_homology_crosscheck.md`](notes/n7_character_sweep_and_homology_crosscheck.md):
  all 2045 posets at n = 7, and a direct equivariant-homology cross-check.
- [`notes/global_module_operations_plethlog.md`](notes/global_module_operations_plethlog.md):
  Proof I (Weisner), the global module HH_n, operations on posets, and the
  Hopf monoid behind the plethystic logarithm.
- [`notes/fixed_point_mobius_identity.md`](notes/fixed_point_mobius_identity.md):
  Proof II (Crapo complementation).
- [`notes/audit_character_identity_proof.md`](notes/audit_character_identity_proof.md):
  independent audit of both proofs.
- [`notes/citation_check.md`](notes/citation_check.md): check of the main
  theorem's cited inputs (Jenča–Sarkoci, P. Hall, Hopf trace formula) and of
  Crapo, Weisner, Ree, Wachs and Aguiar–Mahajan against the sources.

JKS maps, the correction, and the explicit basis:
- [`notes/literature_novelty_jks_maps.md`](notes/literature_novelty_jks_maps.md):
  literature and novelty search, explicit JKS maps (Prop. Φ), the
  counterexample to eq. (restrictionlemma) (Prop. C), and the statement of
  Conjecture S.
- [`notes/audit_literature_novelty_jks_maps.md`](notes/audit_literature_novelty_jks_maps.md):
  its audit, including the strengthening of Prop. C to poset-dependent maps.
- [`notes/conjecture_s_splitting_cycles_span.md`](notes/conjecture_s_splitting_cycles_span.md):
  proof of Conjecture S via shuffle-preserving contractions.
- [`notes/audit_conjecture_s.md`](notes/audit_conjecture_s.md): its audit.
- [`notes/cone_lune_lie_theory.md`](notes/cone_lune_lie_theory.md): cone/lune
  Lie theory for the order cone; a lune form of Conjecture S, and
  independence of the chambers of pointed cones for every finite real
  central essential arrangement (audited:
  notes/audit_cone_lune_lie_theory.md).

The natural-isomorphism question:
- [`notes/natural_isomorphism.md`](notes/natural_isomorphism.md): which
  notions of naturality hold; Theorem Ψ (twisted class sums are independent
  modulo shuffles) and the explicit isomorphism for every P; extension
  naturality exactly on connected posets; ordinal and disjoint sums.
- [`notes/audit_natural_isomorphism.md`](notes/audit_natural_isomorphism.md):
  its audit. Theorem Ψ holds; one check in the note's script is defective,
  and the count it gave is corrected.

Cyclic-compatible posets and b_n:
- [`notes/cyclic_compatible_posets_bn.md`](notes/cyclic_compatible_posets_bn.md):
  proof of b_n = n[x^n] log A(x).
- [`notes/audit_cyclic_compatible_posets_bn.md`](notes/audit_cyclic_compatible_posets_bn.md):
  its audit, and the unconditional proof of ⊕_P Lie(P) ≅ Ind_{C_n}^{S_n}(ζ ⊗ C[B_n]).

## Computations

All code is plain Python 3 in [`compute/`](compute/). Every script, with its
reproduce command, is listed in [`compute/README.md`](compute/README.md).
Unit tests: `cd compute && python3 -m unittest discover -p 'test_*.py'`.
