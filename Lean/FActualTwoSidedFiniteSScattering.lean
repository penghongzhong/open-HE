import FActualLeftFiniteSScattering
import FActualMaximalFiniteSScattering

/-! Both scattering states for the same actual trajectory. Global lifespan,
genuine finite S in both directions, and the homogeneous norm cap remain
explicit criteria, not consequences of the ground-state initial thresholds. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open Filter
open scoped Topology
namespace HartreeF.ActualTwoSidedScattering
open EnergySpace MaximalTrajectory SobolevStretch StationarySelfTest Retarded
open ActualStrichartz EndpointOutput ForcingDomain
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] energySubmodule freeEnergyState

theorem actual_maximal_incoming_scattering_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState)
    (hI : Set.Iic a ⊆
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).domain)
    (hgradient : ∀ t ∈ Set.Iic a, pureGradientNorm
      ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t) ≤ G)
    (hS : ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0)) :
    ∃ uMinus : EnergyState,
      Tendsto (fun t : ℝ =>
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t -
          freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t -
          freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) := by
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0
  have hG : 0 ≤ G := (pureGradientNorm_nonneg (U.state a)).trans
    (hgradient a (Set.mem_Iic.mpr (le_refl a)))
  exact ActualLeftScattering.exists_dotH1_scattering_state_of_finite_s
    hDensity hSob h0 hfree hret hH U hI hG hgradient hS

/-- Actual forward and backward states for one global trajectory. -/
theorem exists_actual_two_sided_scattering_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hglobal : U.domain = Set.univ)
    (hgradient : ∀ t : ℝ, pureGradientNorm (U.state t) ≤ G)
    (hplus : ActualScattering.FiniteSAfter U)
    (hminus : ActualLeftScattering.FiniteSBefore U) :
    ∃ uMinus uPlus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  have hG : 0 ≤ G := (pureGradientNorm_nonneg (U.state a)).trans (hgradient a)
  have hIplus : Set.Ici a ⊆ U.domain := by rw [hglobal]; exact Set.subset_univ _
  have hIminus : Set.Iic a ⊆ U.domain := by rw [hglobal]; exact Set.subset_univ _
  obtain ⟨uPlus, hep, hgp⟩ := ActualScattering.exists_dotH1_scattering_state_of_finite_s
    hDensity hSob h0 hfree hret hH U hIplus hG (fun t _ => hgradient t) hplus
  obtain ⟨uMinus, hem, hgm⟩ := ActualLeftScattering.exists_dotH1_scattering_state_of_finite_s
    hDensity hSob h0 hfree hret hH U hIminus hG (fun t _ => hgradient t) hminus
  exact ⟨uMinus, uPlus, hem, hgm, hep, hgp⟩

set_option pp.universes true
#check @actual_maximal_incoming_scattering_of_finite_s
#print axioms actual_maximal_incoming_scattering_of_finite_s
#check @exists_actual_two_sided_scattering_of_finite_s
#print axioms exists_actual_two_sided_scattering_of_finite_s
end HartreeF.ActualTwoSidedScattering
