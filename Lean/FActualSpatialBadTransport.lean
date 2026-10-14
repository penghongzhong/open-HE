import FNormalizedBilateralGraphBounds
import FActualFiniteSideGraphStability
import FActualBilateralPathTools
import FActualCriticalThreshold
import FActualDynamicSharpWTrapping
import FFreeHartreeEnergyTails

/-! Spatial normalization preserves each bad time direction whenever the
normalized actual trajectory has its native gradient cap. No half-line
domain or spacetime bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualSpatialBadTransport
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open CriticalPathSpace CriticalSourceBounds BilateralPathTools BilateralSideStability
open SharpOrdinary Regularization.Actual HeatRiesz LinearWeakEquation
open ActualCriticalThreshold DynamicSharpW
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  actualMaximalTrajectory LocalMildTrajectory.path

open BilateralGraphBounds CriticalAffine

theorem forward_bad_of_spatial_normalization
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (f : EnergyState) {r : ℝ} (hr : 0 < r) (y : Space) (hB : 0 ≤ B)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0
        ((criticalAffineState r hr y).symm f)).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0
          ((criticalAffineState r hr y).symm f)).state t) ≤ B)
    (hbad : ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f)) :
    ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0
        ((criticalAffineState r hr y).symm f)) := by
  intro hfinite
  let z := (criticalAffineState r hr y).symm f
  have hz : Tendsto (fun _ : ℕ => ‖z - z‖) atTop (𝓝 0) := by
    simp only [sub_self, norm_zero]
    exact tendsto_const_nhds
  obtain ⟨R, hR, N, hcap⟩ := exists_eventual_forward_graph_cap_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique z hB hgradient hfinite
      (fun _ => z) hz
  obtain ⟨hdom, hgraph⟩ := hcap N le_rfl
  have hpull := future_cap_spatial_pullback hDensity hSob h0 hfree hret hefree heret hH
    f hr y 0 R hdom hgraph
  apply hbad
  let M : ℝ≥0 := ⟨graphSConstant K * R, mul_nonneg (graphSConstant_nonneg hSob) hR⟩
  refine ⟨M, ?_⟩
  intro b hb hI
  have hS := (pathValueSize_le_graph hDensity hSob
    ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).path hb hI)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hpull b hb hI)
      (graphSConstant_nonneg hSob)))
  exact hS.trans_eq (show ENNReal.ofReal (M : ℝ) = (M : ℝ≥0∞) from
    ENNReal.ofReal_coe_nnreal)

theorem backward_bad_of_spatial_normalization
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (f : EnergyState) {r : ℝ} (hr : 0 < r) (y : Space) (hB : 0 ≤ B)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0
        ((criticalAffineState r hr y).symm f)).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0
          ((criticalAffineState r hr y).symm f)).state t) ≤ B)
    (hbad : ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f)) :
    ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0
        ((criticalAffineState r hr y).symm f)) := by
  intro hfinite
  let z := (criticalAffineState r hr y).symm f
  have hz : Tendsto (fun _ : ℕ => ‖z - z‖) atTop (𝓝 0) := by
    simp only [sub_self, norm_zero]
    exact tendsto_const_nhds
  obtain ⟨R, hR, N, hcap⟩ := exists_eventual_backward_graph_cap_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique z hB hgradient hfinite
      (fun _ => z) hz
  obtain ⟨hdom, hgraph⟩ := hcap N le_rfl
  have hpull := past_cap_spatial_pullback hDensity hSob h0 hfree hret hefree heret hH
    f hr y 0 R hdom hgraph
  apply hbad
  let M : ℝ≥0 := ⟨graphSConstant K * R, mul_nonneg (graphSConstant_nonneg hSob) hR⟩
  refine ⟨M, ?_⟩
  intro b hb hI
  have hS := (pathValueSize_le_graph hDensity hSob
    ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).path hb hI)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hpull b hb hI)
      (graphSConstant_nonneg hSob)))
  exact hS.trans_eq (show ENNReal.ofReal (M : ℝ) = (M : ℝ≥0∞) from
    ENNReal.ofReal_coe_nnreal)

end HartreeF.ActualSpatialBadTransport
