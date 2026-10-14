import FActualResidualDomains

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print HartreeF.FullResidual.ActualResidualDomains
#print HartreeF.FullResidual.literalResidual
#print HartreeF.FullResidual.residualActual
#print HartreeF.FullResidual.residualCandidate

#print axioms HartreeF.FullResidual.sourceCandidate_eq_full
#print axioms HartreeF.FullResidual.sourceCandidate_congr
#print axioms HartreeF.FullResidual.sourceCandidate_congr_curve
#print axioms HartreeF.FullResidual.literalResidual
#print axioms HartreeF.FullResidual.residualCandidate
#print axioms HartreeF.FullResidual.residualActual
#print axioms HartreeF.FullResidual.source_candidate_canonical_weak
#print axioms HartreeF.FullResidual.vectorForcingNorm_sub_le
#print axioms HartreeF.FullResidual.ActualResidualDomains
#print axioms HartreeF.FullResidual.actual_residual_domains
#print axioms HartreeF.FullResidual.ActualResidualDomains.actual_weak
#print axioms HartreeF.FullResidual.ActualResidualDomains.actual_slice
#print axioms HartreeF.FullResidual.ActualResidualDomains.actual_tests
#print axioms HartreeF.FullResidual.residualCandidate_congr

#check @HartreeF.FullResidual.sourceCandidate_eq_full
#check @HartreeF.FullResidual.sourceCandidate_congr
#check @HartreeF.FullResidual.sourceCandidate_congr_curve
#check @HartreeF.FullResidual.literalResidual
#check @HartreeF.FullResidual.residualCandidate
#check @HartreeF.FullResidual.residualActual
#check @HartreeF.FullResidual.source_candidate_canonical_weak
#check @HartreeF.FullResidual.vectorForcingNorm_sub_le
#check @HartreeF.FullResidual.ActualResidualDomains
#check @HartreeF.FullResidual.actual_residual_domains
#check @HartreeF.FullResidual.ActualResidualDomains.actual_weak
#check @HartreeF.FullResidual.ActualResidualDomains.actual_slice
#check @HartreeF.FullResidual.ActualResidualDomains.actual_tests
#check @HartreeF.FullResidual.residualCandidate_congr
