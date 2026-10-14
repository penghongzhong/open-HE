import FFreeValueGradientDefect

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print HartreeF.GeneralProfileCross.ScalarProfile
#print HartreeF.SobolevStretch.InDotH1
#print HartreeF.FreeValueGradient.TruePairSlices
#print HartreeF.FreeValueGradient.ActualDefectDomains
#print HartreeF.FreeValueGradient.ActualDefectControl

#print axioms HartreeF.FreeValueGradient.directionCoordinate
#print axioms HartreeF.FreeValueGradient.directionCoordinate_add
#print axioms HartreeF.FreeValueGradient.projected_memLp_of_coordinates
#print axioms HartreeF.FreeValueGradient.inDotH1_add
#print axioms HartreeF.FreeValueGradient.TruePairSlices
#print axioms HartreeF.FreeValueGradient.true_pair_slices
#print axioms HartreeF.FreeValueGradient.literalForcing
#print axioms HartreeF.FreeValueGradient.actualGradient
#print axioms HartreeF.FreeValueGradient.candidateGradient
#print axioms HartreeF.FreeValueGradient.candidateGradient_coordinate
#print axioms HartreeF.FreeValueGradient.candidateGradient_eq_candidates
#print axioms HartreeF.FreeValueGradient.candidateGradient_joint
#print axioms HartreeF.FreeValueGradient.actualGradient_candidate_ae
#print axioms HartreeF.FreeValueGradient.ActualDefectDomains
#print axioms HartreeF.FreeValueGradient.actual_free_value_gradient_domains
#print axioms HartreeF.FreeValueGradient.ActualDefectControl
#print axioms HartreeF.FreeValueGradient.actual_free_value_gradient_bound

#check @HartreeF.FreeValueGradient.directionCoordinate
#check @HartreeF.FreeValueGradient.directionCoordinate_add
#check @HartreeF.FreeValueGradient.projected_memLp_of_coordinates
#check @HartreeF.FreeValueGradient.inDotH1_add
#check @HartreeF.FreeValueGradient.TruePairSlices
#check @HartreeF.FreeValueGradient.true_pair_slices
#check @HartreeF.FreeValueGradient.literalForcing
#check @HartreeF.FreeValueGradient.actualGradient
#check @HartreeF.FreeValueGradient.candidateGradient
#check @HartreeF.FreeValueGradient.candidateGradient_coordinate
#check @HartreeF.FreeValueGradient.candidateGradient_eq_candidates
#check @HartreeF.FreeValueGradient.candidateGradient_joint
#check @HartreeF.FreeValueGradient.actualGradient_candidate_ae
#check @HartreeF.FreeValueGradient.ActualDefectDomains
#check @HartreeF.FreeValueGradient.actual_free_value_gradient_domains
#check @HartreeF.FreeValueGradient.ActualDefectControl
#check @HartreeF.FreeValueGradient.actual_free_value_gradient_bound
