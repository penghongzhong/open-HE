import FCompactFullZSFromSource

set_option pp.all false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.piBinderTypes true
set_option pp.piBinderNames true
set_option pp.funBinderTypes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option format.width 120

#print axioms HartreeF.CompactFullZS.scalarSConstant
#print axioms HartreeF.CompactFullZS.scalarSConstant_nonneg
#print axioms HartreeF.CompactFullZS.fullZS_le_of_graph_endpoint
#print axioms HartreeF.CompactFullZS.complex_endpoint_le_three_of_coordinate
#print axioms HartreeF.CompactFullZS.forward_fullZS_of_graph_source
#print axioms HartreeF.CompactFullZS.forward_correction_fullZS_of_source
#print axioms HartreeF.CompactFullZS.backward_correction_fullZS_of_source
#print axioms HartreeF.CompactFullZS.correction_add_sub
#print axioms HartreeF.CompactFullZS.correction_sub_sub
#print axioms HartreeF.CompactFullZS.unit_smul_enorm

#check @HartreeF.CompactFullZS.scalarSConstant
#check @HartreeF.CompactFullZS.scalarSConstant_nonneg
#check @HartreeF.CompactFullZS.fullZS_le_of_graph_endpoint
#check @HartreeF.CompactFullZS.complex_endpoint_le_three_of_coordinate
#check @HartreeF.CompactFullZS.forward_fullZS_of_graph_source
#check @HartreeF.CompactFullZS.forward_correction_fullZS_of_source
#check @HartreeF.CompactFullZS.backward_correction_fullZS_of_source
#check @HartreeF.CompactFullZS.correction_add_sub
#check @HartreeF.CompactFullZS.correction_sub_sub
#check @HartreeF.CompactFullZS.unit_smul_enorm
