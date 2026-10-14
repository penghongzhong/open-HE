import FFreeValueFullCandidate

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print HartreeF.FreeValueFullCandidate.MixedDomain
#print HartreeF.FreeValueFullCandidate.FullCandidateControl

#print axioms HartreeF.FreeValueFullCandidate.MixedDomain
#print axioms HartreeF.FreeValueFullCandidate.mixedDomain_of_finite
#print axioms HartreeF.FreeValueFullCandidate.signed_riesz_product_bound
#print axioms HartreeF.FreeValueFullCandidate.candidate_eq_cross
#print axioms HartreeF.FreeValueFullCandidate.FullCandidateControl
#print axioms HartreeF.FreeValueFullCandidate.full_candidate_bound
#print axioms HartreeF.FreeValueFullCandidate.full_candidate_sum_bound

#check @HartreeF.FreeValueFullCandidate.MixedDomain
#check @HartreeF.FreeValueFullCandidate.mixedDomain_of_finite
#check @HartreeF.FreeValueFullCandidate.signed_riesz_product_bound
#check @HartreeF.FreeValueFullCandidate.candidate_eq_cross
#check @HartreeF.FreeValueFullCandidate.FullCandidateControl
#check @HartreeF.FreeValueFullCandidate.full_candidate_bound
#check @HartreeF.FreeValueFullCandidate.full_candidate_sum_bound
