import FFullXGradientDifference

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print axioms HartreeF.FullResidual.differenceJointFields
#print axioms HartreeF.FullResidual.joint_projected_W_le_curveW
#print axioms HartreeF.FullResidual.tailCoefficient
#print axioms HartreeF.FullResidual.tailCoefficient_nonneg
#print axioms HartreeF.FullResidual.sourceCandidate_difference_norm_eq_actual
#print axioms HartreeF.FullResidual.exists_full_x_gradient_difference_bound

#check @HartreeF.FullResidual.differenceJointFields
#check @HartreeF.FullResidual.joint_projected_W_le_curveW
#check @HartreeF.FullResidual.tailCoefficient
#check @HartreeF.FullResidual.tailCoefficient_nonneg
#check @HartreeF.FullResidual.sourceCandidate_difference_norm_eq_actual
#check @HartreeF.FullResidual.exists_full_x_gradient_difference_bound
