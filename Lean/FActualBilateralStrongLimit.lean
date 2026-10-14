import FActualFiniteSideGraphStability
import FActualBilateralPathTools
import FActualCriticalThreshold
import FActualDynamicSharpWTrapping
import FFreeHartreeEnergyTails

/-! Strong limits preserve bilateral infinite S below the original ground
state thresholds. The native gradient cap is derived in the public threshold
statement. Globality and compactness of the limiting orbit are not asserted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualBilateralStrongLimit
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open CriticalPathSpace CriticalSourceBounds BilateralPathTools BilateralSideStability
open SharpOrdinary Regularization.Actual HeatRiesz LinearWeakEquation
open ActualCriticalThreshold DynamicSharpW
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  actualMaximalTrajectory LocalMildTrajectory.path

theorem forward_bad_of_strong_limit
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (psi : EnergyState) (hB : 0 ≤ B)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).state t) ≤ B)
    (z : ℕ → EnergyState) (hz : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0))
    (hbad : ∀ n, ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n))) :
    ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi) := by
  intro hfinite
  obtain ⟨R, hR, N, hcap⟩ := exists_eventual_forward_graph_cap_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique psi hB hgradient hfinite z hz
  obtain ⟨_hdom, hgraph⟩ := hcap N le_rfl
  apply hbad N
  let M : ℝ≥0 := ⟨graphSConstant K * R, mul_nonneg (graphSConstant_nonneg hSob) hR⟩
  refine ⟨M, ?_⟩
  intro b hb hI
  have hS := (pathValueSize_le_graph hDensity hSob
    ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z N)).path hb hI)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hgraph b hb hI)
      (graphSConstant_nonneg hSob)))
  exact hS.trans_eq (show ENNReal.ofReal (M : ℝ) = (M : ℝ≥0∞) from
    ENNReal.ofReal_coe_nnreal)

theorem backward_bad_of_strong_limit
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (psi : EnergyState) (hB : 0 ≤ B)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).state t) ≤ B)
    (z : ℕ → EnergyState) (hz : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0))
    (hbad : ∀ n, ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n))) :
    ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi) := by
  intro hfinite
  obtain ⟨R, hR, N, hcap⟩ := exists_eventual_backward_graph_cap_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique psi hB hgradient hfinite z hz
  obtain ⟨_hdom, hgraph⟩ := hcap N le_rfl
  apply hbad N
  let M : ℝ≥0 := ⟨graphSConstant K * R, mul_nonneg (graphSConstant_nonneg hSob) hR⟩
  refine ⟨M, ?_⟩
  intro b hb hI
  have hS := (pathValueSize_le_graph hDensity hSob
    ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z N)).path hb hI)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hgraph b hb hI)
      (graphSConstant_nonneg hSob)))
  exact hS.trans_eq (show ENNReal.ofReal (M : ℝ) = (M : ℝ≥0∞) from
    ENNReal.ofReal_coe_nnreal)

/-- The exact strong limit retains the energy level, a quantitative kinetic
gap, both infinite-S directions, and native conservation/trapping. No cap of
the limiting trajectory is a premise. -/
theorem threshold_bilateral_limit
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha Ec A : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hEc : 0 < Ec) (hEcW : Ec < totalEnergy alpha (normalizedBubbleState alpha))
    (hAW : A < gradientSquared (normalizedBubbleState alpha))
    (z : ℕ → EnergyState) (psi : EnergyState) (hz : Tendsto z atTop (𝓝 psi))
    (hE : ∀ n, totalEnergy alpha (z n) = Ec)
    (hA : ∀ n, gradientSquared (z n) ≤ A)
    (hfuture : ∀ n, ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n)))
    (hpast : ∀ n, ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) :
    psi ≠ 0 ∧ totalEnergy alpha psi = Ec ∧ gradientSquared psi ≤ A ∧
      StableDatum alpha psi ∧
      let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
      (¬ ActualScattering.FiniteSAfter V) ∧
      (¬ ActualLeftScattering.FiniteSBefore V) ∧
      ∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
        gradientSquared (V.state t) ≤ (2 * (3 + alpha) / (2 + alpha)) * Ec ∧
        (2 * (3 + alpha) / (2 + alpha)) * Ec <
          gradientSquared (normalizedBubbleState alpha) := by
  have hEpsi : totalEnergy alpha psi = Ec :=
    (isClosed_eq (totalEnergy_contDiff hOrd).continuous continuous_const).mem_of_tendsto
      hz (Eventually.of_forall hE)
  have hApsi : gradientSquared psi ≤ A :=
    (isClosed_le gradientSquared_continuous continuous_const).mem_of_tendsto
      hz (Eventually.of_forall hA)
  have hstable : StableDatum alpha psi :=
    ⟨hEpsi.trans_lt hEcW,
      (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr (hApsi.trans_lt hAW)⟩
  have hne : psi ≠ 0 := by
    intro hzero
    have hEzero : totalEnergy alpha (0 : EnergyState) = 0 := by
      simp [totalEnergy, gradientSquared, FreeTimeDecay.interactionLp_zero hH.order_pos]
    rw [hzero, hEzero] at hEpsi
    exact hEc.ne hEpsi
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have htrap := actualMaximalTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 0 psi hstable.1 hstable.2
  have hgradient : ∀ t ∈ V.domain,
      pureGradientNorm (V.state t) ≤ pureGradientNorm (normalizedBubbleState alpha) := by
    intro t ht
    have hc := htrap t ht
    exact ((pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr
      (hc.1.trans_lt hc.2)).le
  have hzNorm : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => psi) atTop (𝓝 psi) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hz.sub hc).norm
  refine ⟨hne, hEpsi, hApsi, hstable, ?_, ?_, ?_⟩
  · exact forward_bad_of_strong_limit hDensity hSob h0 hfree hret hefree heret
      hOrd hgen hUnique psi (pureGradientNorm_nonneg _) hgradient z hzNorm hfuture
  · exact backward_bad_of_strong_limit hDensity hSob h0 hfree hret hefree heret
      hOrd hgen hUnique psi (pureGradientNorm_nonneg _) hgradient z hzNorm hpast
  · intro t ht
    have hc := LocalMildTrajectory.totalEnergy_constant_on_domain hDensity hSob h0 hfree hret
      hefree heret hOrd S Bw Bs B6 V ht
    have hk := htrap t ht
    rw [hEpsi] at hk
    exact ⟨hc.trans hEpsi, hk⟩

end HartreeF.ActualBilateralStrongLimit

