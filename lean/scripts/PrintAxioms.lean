import PosetJKS

-- Run from `lean/`:  lake env lean scripts/PrintAxioms.lean
#print axioms PosetJKS.character_identity
#print axioms PosetJKS.main_iso
#print axioms PosetJKS.closed_formula
#print axioms PosetJKS.trace_HP
#print axioms PosetJKS.trace_PLie
#print axioms PosetJKS.jencaSarkoci_homology
#print axioms PosetJKS.hall_mu_eq_reducedEuler
#print axioms PosetJKS.thmS_a
#print axioms PosetJKS.thmS_b
#print axioms PosetJKS.thmPsi
#print axioms PosetJKS.corPsi_bijective
#print axioms PosetJKS.corPsi_equivariant
#print axioms PosetJKS.corPsi

-- Supporting results of the first milestone (lists; `PosetJKS/Words.lean`, `Milestone.lean`)
#print axioms PosetJKS.L.map_E_ShL
#print axioms PosetJKS.L.eq_zero_of_inBL
#print axioms PosetJKS.L.eq_zero_of_eqL
#print axioms PosetJKS.L.eqL_classSum
#print axioms PosetJKS.card_inB
#print axioms PosetJKS.wd_mem_SB_sup_R
#print axioms PosetJKS.pr_wEζ
#print axioms PosetJKS.actHP
#print axioms PosetJKS.actMP
#print axioms PosetJKS.muFixed

-- Second milestone, partial (`PosetJKS/LieTrace.lean`, `OPLattice.lean`, `Interval.lean`)
#print axioms PosetJKS.trace_actPLie
#print axioms PosetJKS.finrank_PLie
#print axioms PosetJKS.weisner
#print axioms PosetJKS.isOrderPreserving_inf
#print axioms PosetJKS.isOrderPreserving_orbitSetoid
#print axioms PosetJKS.isOrderPreserving_joinOrbit
#print axioms PosetJKS.rel_of_le_of_joinOrbit_eq_top
#print axioms PosetJKS.sum_mu_join_eq_top
#print axioms PosetJKS.mu_eq_of_interval
#print axioms PosetJKS.mu_interval
#print axioms PosetJKS.recursionW

-- prop:Lside (`PosetJKS/LieSide.lean`) and its general inputs (`RamanujanSum.lean`, `ECTransport.lean`)
#print axioms PosetJKS.prop_Lside
#print axioms PosetJKS.fixedB_struct
#print axioms PosetJKS.exists_fixedB
#print axioms PosetJKS.card_fiber
#print axioms PosetJKS.inF_blocksOf
#print axioms PosetJKS.blocksOf_of_inF
#print axioms PosetJKS.sum_primitiveRoots_eq_moebius
#print axioms PosetJKS.sum_pow_coprime_eq_moebius
#print axioms PosetJKS.L.inBL_map
#print axioms PosetJKS.card_BL
#print axioms PosetJKS.eC_congr
#print axioms PosetJKS.eC_image

-- lem:small (Theorem A, Proof W; `PosetJKS/MuOP.lean`), lem:interval(ii), prop:Mside (`Mside.lean`)
#print axioms PosetJKS.mu_OP_eq
#print axioms PosetJKS.weisner_dual
#print axioms PosetJKS.mu_op_rec
#print axioms PosetJKS.mu_pab_top
#print axioms PosetJKS.eC_rec
#print axioms PosetJKS.Mt_one
#print axioms PosetJKS.interval_sign
#print axioms PosetJKS.recursionW_signed
#print axioms PosetJKS.sum_mu_below_eq_zero
#print axioms PosetJKS.mu_eq_moebius_mul_sum
#print axioms PosetJKS.prop_Mside

-- Controls and counterexamples in `PosetJKS/Test.lean` (must not depend on `sorryAx`)
#print axioms PosetJKS.Test.fixedClassSum_g3_prim
#print axioms PosetJKS.Test.muFixed_chain2
#print axioms PosetJKS.Test.Mt_chain2
#print axioms PosetJKS.Test.not_op_chain3_02_1
#print axioms PosetJKS.relabel_wEζ_of_rot
#print axioms PosetJKS.bd_comp_bd
#print axioms PosetJKS.bd_zero_single
#print axioms PosetJKS.Test.corPsi_bijective_false
#print axioms PosetJKS.Test.trace_PLie_false
#print axioms Representation.nonempty_equiv_of_character_eq
#print axioms Representation.nonempty_equiv_iff_character_eq
#print axioms Representation.exists_linearEquiv_of_trace_eq
#print axioms PosetJKS.exists_iso_HP_PLie_of_trace
#print axioms PosetJKS.CharacterIsoTest.trivSgn_equiv_permRep
#print axioms PosetJKS.CharacterIsoTest.not_triv2_equiv_permRep
#print axioms PosetJKS.CharacterIsoTest.not_triv_equiv_sgn
