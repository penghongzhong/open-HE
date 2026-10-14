import FActualProfileEnergyLedger

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs false
set_option pp.proofs.withType true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 120

#print axioms HartreeF.ActualProfileEnergy.kappa_pos
#check @HartreeF.ActualProfileEnergy.kappa_pos
#print axioms HartreeF.ActualProfileEnergy.active_succ_eligible
#check @HartreeF.ActualProfileEnergy.active_succ_eligible
#print axioms HartreeF.ActualProfileEnergy.kinetic_prefix_and_remainder
#check @HartreeF.ActualProfileEnergy.kinetic_prefix_and_remainder
#print axioms HartreeF.ActualProfileEnergy.free_profile_energy_has_limit
#check @HartreeF.ActualProfileEnergy.free_profile_energy_has_limit
#print axioms HartreeF.ActualProfileEnergy.single_matching_limits
#check @HartreeF.ActualProfileEnergy.single_matching_limits
#print axioms HartreeF.ActualProfileEnergy.build_profile_energy_ledger
#check @HartreeF.ActualProfileEnergy.build_profile_energy_ledger
