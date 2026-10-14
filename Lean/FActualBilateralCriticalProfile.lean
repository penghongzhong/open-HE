import FActualSpatialPalaisSmale
import FActualBalancedGraphWindows

/-! The actual critical-energy datum is bad in both time directions.
Balanced windows come from one original bad canonical trajectory; every
recentered datum and the final spatial limit retain their genuine domains.
This does not assert global lifespan or compactness of an entire orbit.
UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualBilateralCriticalProfile
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy
  ActualCriticalThreshold ActualCriticalProfile FiniteSActualX BilateralWindows
  BilateralGraphBounds ActualSpatialPalaisSmale DynamicSharpW LocalRellich LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- The canonical mark of the final bilateral critical datum is exactly zero.
All energy and kinetic assertions concern its native maximal lifespan. -/
theorem exists_actual_bilateral_critical_datum
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
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    0 < Ec ∧ Ec < totalEnergy alpha (normalizedBubbleState alpha) ∧
      ∃ psi : EnergyState, totalEnergy alpha psi = Ec ∧ StableDatum alpha psi ∧
        let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
        (¬ ActualScattering.FiniteSAfter V) ∧
        (¬ ActualLeftScattering.FiniteSBefore V) ∧
        ∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
          gradientSquared (V.state t) ≤ kappa alpha*Ec ∧
          kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha) := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨hEc, hEcW, _u0, _hubad0, _hEu0, _sigma, _P, T, f, j0, _tau,
    _hsigma, _hP, _ht, _hmatch, _hjactive, _hjenergy, _hother, _htau,
    _hpure, _hnorm, hnotfinite, hNative⟩ :=
    exists_actual_critical_profile_concentration hDensity hRel hSob h0 hfree hret
      hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff hbad
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd
    (T j0) (f j0)
  obtain ⟨w⟩ := actual_zero_centered_windows hDensity hSob h0 hfree hret hefree heret
    hOrd (f j0) hnotfinite
  let u (n : ℕ) := M.state (w n).center
  have henergy (n : ℕ) : totalEnergy alpha (u n) = Ec :=
    (hNative (w n).center (w n).center_mem).1
  have hstable (n : ℕ) : StableDatum alpha (u n) := by
    have h := hNative (w n).center (w n).center_mem
    exact ⟨h.1.trans_lt hEcW,
      (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr (h.2.1.trans_lt h.2.2)⟩
  have hubad (n : ℕ) : BadDatum hDensity hSob h0 hfree hret hefree heret hOrd (u n) := by
    refine ⟨hstable n, ?_⟩
    intro hfinite
    have hzero := actualMaximalTrajectory_stable_global_curveFinite_of_finiteS
      hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6
      0 (u n) (hstable n).1 (hstable n).2 hfinite
    have hmarked := actualMaximalTrajectory_marked_global_curveFinite
      hDensity hSob h0 hfree hret hefree heret hOrd (w n).center (u n) hzero
    have horiginal := actualMaximalTrajectory_global_curveFinite_of_recenter
      hDensity hSob h0 hfree hret hefree heret hOrd (f j0) (w n).center_mem hmarked
    exact hnotfinite (finiteS_of_global_curveFinite M horiginal.1 horiginal.2)
  have hEu : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 Ec) := by
    have heq : (fun n => totalEnergy alpha (u n)) = fun _ : ℕ => Ec := funext henergy
    rw [heq]
    exact tendsto_const_nhds
  have hw : BilateralGraphWindows hDensity hSob h0 hfree hret hefree heret hOrd u := by
    intro n
    exact ⟨(w n).left, (w n).right, (w n).left_neg.le, (w n).right_pos.le,
      (w n).left_within, (w n).right_within, (w n).left_graph.le, (w n).right_graph.le⟩
  obtain ⟨_k, _lambda, _hlambda, _y, psi, _hk, _hz, hEpsi, _hApsi,
    hstablePsi, hfutureBad, hpastBad⟩ :=
    given_bilateral_bad_sequence_spatial_concentration hDensity hRel hSob h0 hfree hret
      hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff u hubad hEu hw
  refine ⟨hEc, hEcW, psi, hEpsi, hstablePsi, hfutureBad, hpastBad, ?_⟩
  intro t htV
  have hcons := LocalMildTrajectory.totalEnergy_constant_on_domain hDensity hSob h0 hfree hret
    hefree heret hOrd S Bw Bs B6
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi) htV
  have htrap := actualMaximalTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 0 psi hstablePsi.1 hstablePsi.2 t htV
  rw [hEpsi] at htrap
  exact ⟨hcons.trans hEpsi, htrap⟩

end HartreeF.ActualBilateralCriticalProfile
