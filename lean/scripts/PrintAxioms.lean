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

-- Controls and counterexamples in `PosetJKS/Test.lean` (must not depend on `sorryAx`)
#print axioms PosetJKS.Test.fixedClassSum_g3_prim
#print axioms PosetJKS.Test.muFixed_chain2
#print axioms PosetJKS.Test.not_op_chain3_02_1
#print axioms PosetJKS.relabel_wEζ_of_rot
#print axioms PosetJKS.bd_comp_bd
#print axioms PosetJKS.bd_zero_single
#print axioms PosetJKS.Test.corPsi_bijective_false
#print axioms PosetJKS.Test.trace_PLie_false
