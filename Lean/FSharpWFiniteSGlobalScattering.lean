import FActualDynamicSharpWTrapping
import FMaximalFiniteSGlobalScattering

/-! The W thresholds now supply the a priori gradient cap required by the
accepted maximal finite-S criterion. Finite S remains an explicit additional
criterion; this theorem does not assert that W thresholds produce finite S. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.DynamicSharpW
open EnergySpace CriticalPathSpace StateEnergy StateSharpThreshold MaximalTrajectory
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
open Regularization.Actual SharpOrdinary HeatRiesz MaximalFiniteSGlobal
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  actualMaximalTrajectory freeEnergyState

/-- Globality and both actual scattering states from the original W thresholds
plus the one remaining genuine finite-S criterion on the native maximal domain. -/
theorem actualMaximalTrajectory_global_scattering_of_W_and_finiteS
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha))
    (hfiniteS : FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
    U.domain = Set.univ ∧ ∃ uMinus uPlus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  have hcap := actualMaximalTrajectory_pureGradient_cap hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 s0 u0 henergy hgradient
  exact actual_maximal_global_and_two_sided_scattering_of_finite_s hDensity hSob h0 hfree hret
    hefree heret hOrd u0 (fun t ht => (hcap t ht).1) hfiniteS

#print axioms actualMaximalTrajectory_global_scattering_of_W_and_finiteS
end HartreeF.DynamicSharpW
