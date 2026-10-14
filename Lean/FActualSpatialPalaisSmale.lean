import FNormalizedBilateralGraphBounds
import FActualFreeTailGraphCaps
import FActualFiniteSideGraphStability

/-! Spatial concentration for the given bilateral bad sequence. Infinite free
profile times are excluded by actual half-line graph bounds. The finite time
is absorbed in the new datum; its canonical mark is zero. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualSpatialPalaisSmale
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy
  CommonProfileTimes ActualCriticalThreshold GivenBadConcentration SpatialProfileLimit
  BilateralGraphBounds BilateralTail BilateralSideStability DynamicSharpW
  LocalRellich LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- Only spatial normalization remains. Both one-sided badness statements
refer to the actual canonical trajectory with mark zero and this same psi. -/
theorem given_bilateral_bad_sequence_spatial_concentration
    (hDensity : OrdinaryH1Density) (hRel : OrdinaryRellichBall)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hExtract : OrdinaryLinearProfileExtraction hDensity hSob)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (cutoff : Highpass.Cutoff)
    (u : ℕ → EnergyState)
    (hubad : ∀ n, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd (u n))
    (hEu : Tendsto (fun n => totalEnergy alpha (u n)) atTop
      (𝓝 (criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd)))
    (hw : BilateralGraphWindows hDensity hSob h0 hfree hret hefree heret hOrd u) :
    ∃ (k : ℕ → ℕ) (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n)
      (y : ℕ → Space) (psi : EnergyState),
      StrictMono k ∧
      Tendsto (fun n => (criticalAffineState (lambda n) (hlambda n) (y n)).symm
        (u (k n))) atTop (𝓝 psi) ∧
      totalEnergy alpha psi = criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
      gradientSquared psi ≤ kappa alpha *
        criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
      StableDatum alpha psi ∧
      let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
      (¬ ActualScattering.FiniteSAfter V) ∧ (¬ ActualLeftScattering.FiniteSBefore V) := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨k, lambda, hlambda, y, s, phi, hk, ht, herr⟩ :=
    given_bad_sequence_full_frame hDensity hRel hSob h0 hfree hret hefree heret hOrd
      hH hS S Bw Bs B6 hExtract hgen hUnique cutoff u hubad hEu
  let z (n : ℕ) := (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u (k n))
  have hfreeError : Tendsto (fun n => ‖z n-freeEnergyState hDensity hSob (s n) phi‖)
      atTop (𝓝 0) := by
    simpa only [z, spatial_inverse_error_norm] using herr
  have hfinite : ∃ sstar : ℝ, Tendsto s atTop (𝓝 sstar) := by
    rcases ht with hfin | hfuture | hpast
    · exact hfin
    · obtain ⟨R, _hR, N, hcap⟩ := exists_eventual_future_graph_cap
        hDensity hSob h0 hfree hret hefree heret hOrd phi z s hfreeError hfuture
      exact False.elim (no_eventual_future_cap hDensity hSob h0 hfree hret hefree heret hOrd
        u hw k hk R N (fun n hn => future_cap_spatial_pullback
          hDensity hSob h0 hfree hret hefree heret hOrd (u (k n)) (hlambda n)
          (y n) (s n) R (hcap n hn).1 (hcap n hn).2))
    · obtain ⟨R, _hR, N, hcap⟩ := exists_eventual_past_graph_cap
        hDensity hSob h0 hfree hret hefree heret hOrd phi z s hfreeError hpast
      exact False.elim (no_eventual_past_cap hDensity hSob h0 hfree hret hefree heret hOrd
        u hw k hk R N (fun n hn => past_cap_spatial_pullback
          hDensity hSob h0 hfree hret hefree heret hOrd (u (k n)) (hlambda n)
          (y n) (s n) R (hcap n hn).1 (hcap n hn).2))
  obtain ⟨sstar, hsstar⟩ := hfinite
  let psi := freeEnergyState hDensity hSob sstar phi
  have hz : Tendsto z atTop (𝓝 psi) := spatial_limit_of_finite_time hDensity hSob
    (u ∘ k) lambda hlambda y s phi herr hsstar
  have hEn : Tendsto (fun n => totalEnergy alpha (u (k n))) atTop (𝓝 Ec) :=
    hEu.comp hk.tendsto_atTop
  obtain ⟨hEpsi, hApsi⟩ := spatial_limit_energy_kinetic hOrd (u ∘ k) lambda hlambda y psi
    hEn (fun n => stable_kinetic_le_energy hOrd hH hS (hubad (k n)).1) hz
  obtain ⟨_hEc, hEcW⟩ := criticalLevel_pos_lt hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 ⟨u 0, hubad 0⟩
  have hgap : kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha) :=
    (mul_lt_mul_of_pos_left hEcW (kappa_pos hH.order_pos)).trans_eq
      (trapping_factor_ground_energy hDensity hOrd hH hS)
  have hstable : StableDatum alpha psi := ⟨hEpsi.trans_lt hEcW,
    (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr (hApsi.trans_lt hgap)⟩
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  let B := Real.sqrt ((2*(3+alpha)/(2+alpha))*totalEnergy alpha psi)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hgradient : ∀ t ∈ V.domain, pureGradientNorm (V.state t) ≤ B := by
    intro t htV
    exact (actualMaximalTrajectory_pureGradient_cap hDensity hSob h0 hfree hret
      hefree heret hOrd hH hS S Bw Bs B6 0 psi hstable.1 hstable.2 t htV).1
  have hznorm : Tendsto (fun n => ‖z n-psi‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have hfutureBad : ¬ ActualScattering.FiniteSAfter V := by
    intro hfiniteS
    obtain ⟨R, _hR, N, hcap⟩ := exists_eventual_forward_graph_cap_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique psi hB hgradient
        hfiniteS z hznorm
    exact no_eventual_future_cap hDensity hSob h0 hfree hret hefree heret hOrd
      u hw k hk R N (fun n hn => future_cap_spatial_pullback
        hDensity hSob h0 hfree hret hefree heret hOrd (u (k n)) (hlambda n)
        (y n) 0 R (hcap n hn).1 (hcap n hn).2)
  have hpastBad : ¬ ActualLeftScattering.FiniteSBefore V := by
    intro hfiniteS
    obtain ⟨R, _hR, N, hcap⟩ := exists_eventual_backward_graph_cap_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique psi hB hgradient
        hfiniteS z hznorm
    exact no_eventual_past_cap hDensity hSob h0 hfree hret hefree heret hOrd
      u hw k hk R N (fun n hn => past_cap_spatial_pullback
        hDensity hSob h0 hfree hret hefree heret hOrd (u (k n)) (hlambda n)
        (y n) 0 R (hcap n hn).1 (hcap n hn).2)
  exact ⟨k, lambda, hlambda, y, psi, hk, hz, hEpsi, hApsi, hstable, hfutureBad, hpastBad⟩

end HartreeF.ActualSpatialPalaisSmale
