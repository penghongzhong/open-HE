import FR2ActualTailForcing

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print HartreeF.R2Global.CurveFinite
#print HartreeF.FreeValueGradient.ActualDefectDomains

#print axioms HartreeF.R2TailForcing.sourceGradient
#print axioms HartreeF.R2TailForcing.sourceCandidate
#print axioms HartreeF.R2TailForcing.joint_scalar_profiles
#print axioms HartreeF.R2TailForcing.source_domains
#print axioms HartreeF.R2TailForcing.literal_source_eq
#print axioms HartreeF.R2TailForcing.source_scalar_canonical_ae
#print axioms HartreeF.R2TailForcing.exists_source_gradient_power_bound
#print axioms HartreeF.R2TailForcing.source_gradient_sum_le
#print axioms HartreeF.R2TailForcing.source_gradient_sum_finite

#check @HartreeF.R2TailForcing.sourceGradient
#check @HartreeF.R2TailForcing.sourceCandidate
#check @HartreeF.R2TailForcing.joint_scalar_profiles
#check @HartreeF.R2TailForcing.source_domains
#check @HartreeF.R2TailForcing.literal_source_eq
#check @HartreeF.R2TailForcing.source_scalar_canonical_ae
#check @HartreeF.R2TailForcing.exists_source_gradient_power_bound
#check @HartreeF.R2TailForcing.source_gradient_sum_le
#check @HartreeF.R2TailForcing.source_gradient_sum_finite
