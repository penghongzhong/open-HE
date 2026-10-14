import FR2CompactSmallData

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print HartreeF.R2SmallData.AnchoredCompactBounds

#print axioms HartreeF.R2SmallData.AnchoredCompactBounds
#print axioms HartreeF.R2SmallData.rpow_mul_fifth
#print axioms HartreeF.R2SmallData.exists_source_power_bound
#print axioms HartreeF.R2SmallData.backwardHartreeDuhamelMap_zero_path
#print axioms HartreeF.R2SmallData.exists_uniform_backward_small_data_path
#print axioms HartreeF.R2SmallData.represented_state_norm_le
#print axioms HartreeF.R2SmallData.AnchoredCompactBounds.pointwise
#print axioms HartreeF.R2SmallData.represented_correction_state
#print axioms HartreeF.R2SmallData.AnchoredCompactBounds.correction_pointwise
#print axioms HartreeF.R2SmallData.exists_uniform_two_sided_small_data
#print axioms HartreeF.R2SmallData.actualMaximalTrajectory_global_of_recenter
#print axioms HartreeF.R2SmallData.matching_state_norm_le
#print axioms HartreeF.R2SmallData.exists_uniform_matching_compact_bounds
#print axioms HartreeF.R2SmallData.matching_state_pureGradient_le
#print axioms HartreeF.R2SmallData.matching_error_pureGradient_tendsto
#print axioms HartreeF.R2SmallData.actual_matching_zero_profile

#check @HartreeF.R2SmallData.AnchoredCompactBounds
#check @HartreeF.R2SmallData.rpow_mul_fifth
#check @HartreeF.R2SmallData.exists_source_power_bound
#check @HartreeF.R2SmallData.backwardHartreeDuhamelMap_zero_path
#check @HartreeF.R2SmallData.exists_uniform_backward_small_data_path
#check @HartreeF.R2SmallData.represented_state_norm_le
#check @HartreeF.R2SmallData.AnchoredCompactBounds.pointwise
#check @HartreeF.R2SmallData.represented_correction_state
#check @HartreeF.R2SmallData.AnchoredCompactBounds.correction_pointwise
#check @HartreeF.R2SmallData.exists_uniform_two_sided_small_data
#check @HartreeF.R2SmallData.actualMaximalTrajectory_global_of_recenter
#check @HartreeF.R2SmallData.matching_state_norm_le
#check @HartreeF.R2SmallData.exists_uniform_matching_compact_bounds
#check @HartreeF.R2SmallData.matching_state_pureGradient_le
#check @HartreeF.R2SmallData.matching_error_pureGradient_tendsto
#check @HartreeF.R2SmallData.actual_matching_zero_profile
