import FActualFiniteSScattering
import FActualMaximalMildTrajectory

/-! A direct consumer on the constructed maximal trajectory, retaining the
actual half-line lifespan and both finite-S and homogeneous-gradient caps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualScattering
open EnergySpace MaximalTrajectory SobolevStretch StationarySelfTest Retarded
open ActualStrichartz EndpointOutput ForcingDomain
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] energySubmodule freeEnergyState

theorem actual_maximal_dotH1_scattering_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState)
    (hI : Set.Ici a ⊆
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).domain)
    (hgradient : ∀ t ∈ Set.Ici a, pureGradientNorm
      ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t) ≤ G)
    (hS : FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0)) :
    ∃ uPlus : EnergyState,
      Tendsto (fun t : ℝ =>
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t -
          freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t -
          freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0
  have hG : 0 ≤ G := (pureGradientNorm_nonneg (U.state a)).trans
    (hgradient a (Set.mem_Ici.mpr (le_refl a)))
  exact exists_dotH1_scattering_state_of_finite_s hDensity hSob h0 hfree hret hH
    U hI hG hgradient hS

set_option pp.universes true
#check @actual_maximal_dotH1_scattering_of_finite_s
#print axioms actual_maximal_dotH1_scattering_of_finite_s
end HartreeF.ActualScattering
