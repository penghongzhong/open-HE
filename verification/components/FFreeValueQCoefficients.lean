import FFreeValueQCoefficients

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120


#print axioms HartreeF.FreeValueFullCandidate.Q
#print axioms HartreeF.FreeValueFullCandidate.zero_direction_profile
#print axioms HartreeF.FreeValueFullCandidate.power_VSQ_le
#print axioms HartreeF.FreeValueFullCandidate.q_coefficients_joint
#print axioms HartreeF.FreeValueFullCandidate.q_coefficients_bound
#print axioms HartreeF.FreeValueFullCandidate.q_coefficients_finite
#print axioms HartreeF.FreeValueFullCandidate.Q_sum_le

#check @HartreeF.FreeValueFullCandidate.Q
#check @HartreeF.FreeValueFullCandidate.zero_direction_profile
#check @HartreeF.FreeValueFullCandidate.power_VSQ_le
#check @HartreeF.FreeValueFullCandidate.q_coefficients_joint
#check @HartreeF.FreeValueFullCandidate.q_coefficients_bound
#check @HartreeF.FreeValueFullCandidate.q_coefficients_finite
#check @HartreeF.FreeValueFullCandidate.Q_sum_le
