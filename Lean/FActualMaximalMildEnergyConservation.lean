import FLocalMildTrajectoryEnergyConservation
import FActualMaximalMildTrajectory

/-!
This is the isolated implementation of the previously frozen preparation.
The old preparation and UNKNOWN record are preserved. Current acceptance is
reported by this directory's actual strict/dependency receipts.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest StateEnergy
open Retarded ActualStrichartz ForcingDomain EndpointOutput Regularization.Actual
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  actualMaximalTrajectory

/-- The concrete maximal lifespan solution inherits the proved local-domain
constant energy theorem because it is the actual LocalMildTrajectory already
constructed from the canonical local solutions. -/
theorem actualMaximalTrajectory_totalEnergy_constant (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
    ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = totalEnergy alpha u0 := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
  change ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = totalEnergy alpha u0
  intro t ht
  exact LocalMildTrajectory.totalEnergy_constant_on_domain hDensity hSob h0 hfree hret
    hefree heret hH S Bw Bs B6 M ht

theorem actualMaximalTrajectory_originalEnergy_constant (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
    ∀ t ∈ M.domain,
      DirectionalCoercivity.energy alpha (energyValue (M.state t))
        (energyProjectedGradient Complex.reCLM (M.state t))
        (energyProjectedGradient Complex.imCLM (M.state t)) =
      DirectionalCoercivity.energy alpha (energyValue u0)
        (energyProjectedGradient Complex.reCLM u0)
        (energyProjectedGradient Complex.imCLM u0) := by
  dsimp only
  intro t ht
  simpa only [totalEnergy_eq_original] using
    (actualMaximalTrajectory_totalEnergy_constant hDensity hSob h0 hfree hret hefree heret hH
      S Bw Bs B6 s0 u0 t ht)

#print axioms actualMaximalTrajectory_totalEnergy_constant
#print axioms actualMaximalTrajectory_originalEnergy_constant
end HartreeF.MaximalTrajectory
