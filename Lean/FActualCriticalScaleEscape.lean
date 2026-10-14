import FActualCriticalLimitGlobal
import FActualScaleEscapeContradiction

/-! Return-time escape in the original critical-energy environment.
Globality and nonvanishing of the strong limit are derived. Bilateral badness
of the normalized data remains explicit; the full subparabolic estimate is not asserted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualCriticalScaleEscape
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge NativeCompactGlobal ActualBilateralStrongLimit
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

open ActualCriticalLimitGlobal ActualScaleEscape
attribute [local irreducible] actualMaximalTrajectory

/-- Critical energy and bilateral badness supply the global nonzero limit
needed for the actual return-time contradiction. -/
theorem critical_normalized_return_time_not_tendsto
    (hDensity : OrdinaryH1Density) (hRel : OrdinaryRellichBall)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hExtract : OrdinaryLinearProfileExtraction hDensity hSob)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (cutoff : Highpass.Cutoff)
    {A : ℝ} (f : EnergyState) (hf : f ≠ 0)
    (c r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (y : ℕ → Space)
    (hc : ∀ n, c n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f).domain)
    (hscale : Tendsto r atTop atTop) (psi : EnergyState) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    let z := fun n => (criticalAffineState (r n) (hr n) (y n)).symm (M.state (c n))
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    A < gradientSquared (normalizedBubbleState alpha) →
    (∀ n, totalEnergy alpha (z n) = Ec) →
    (∀ n, gradientSquared (z n) ≤ A) →
    (∀ n, ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) →
    (∀ n, ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) →
    Tendsto z atTop (𝓝 psi) →
      ∀ t : ℝ, ¬ Tendsto (fun n => -c n / (r n)^2) atTop (𝓝 t) := by
  intro Ec M z hEc hEcW hAW hE hA hfuture hpast hz
  have hlimit := critical_strong_limit_global_compact hDensity hRel hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff z psi hz
    hEc hEcW hAW hE hA hfuture hpast
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have hglobal : V.domain = univ := hlimit.2.2.2.2.1
  have hEzero : totalEnergy alpha (0 : EnergyState) = 0 := by
    simp [totalEnergy, gradientSquared, FreeTimeDecay.interactionLp_zero hH.order_pos]
  have hnonzero (t : ℝ) : V.state t ≠ 0 := by
    intro hzero
    have ht : t ∈ V.domain := by rw [hglobal]; exact mem_univ t
    have he := (hlimit.2.2.2.2.2.2.2.1 t ht).1
    rw [hzero, hEzero] at he
    exact hEc.ne he
  exact normalized_return_time_not_tendsto hDensity hSob h0 hfree hret hefree heret hOrd
    hgen hUnique f hf c r hr y hc hscale psi hz hglobal hnonzero

end HartreeF.ActualCriticalScaleEscape
