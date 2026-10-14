import FFiniteProfileRieszMixed

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print axioms HartreeF.FiniteProfileRieszMixed.mixed_riesz_bound
#print axioms HartreeF.FiniteProfileRieszMixed.mixed_smul_le
#print axioms HartreeF.FiniteProfileRieszMixed.riesz_product_estimate
#print axioms HartreeF.FiniteProfileRieszMixed.riesz_product_tendsto

#check @HartreeF.FiniteProfileRieszMixed.mixed_riesz_bound
#check @HartreeF.FiniteProfileRieszMixed.mixed_smul_le
#check @HartreeF.FiniteProfileRieszMixed.riesz_product_estimate
#check @HartreeF.FiniteProfileRieszMixed.riesz_product_tendsto
