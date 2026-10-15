import F121SubparabolicScale
import F121SelectedScaleWindows
import F121RelativeNormalization
import F121NormalizedGlobalTrajectory

/-! R8.4 Theorem 5.8: a single actual critical strong limit with bounded
physical scales on one fixed half-line. Compactness and globality are derived. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121BoundedHalfline
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualCriticalLimitGlobal ActualCompactTimeConvergence Paper121Subparabolic
  Paper121ScaleSelection Paper121Finiteness Paper121NormalizedGlobal
  Paper121RelativeNormalization Paper121AffineClosed Paper121PointwiseNormalization
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] actualMaximalTrajectory

theorem bounded_halfline_critical_limit
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
    (f : EnergyState) (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space)
    (C : Set EnergyState) (hC : IsCompact C) (hCzero : (0 : EnergyState) ∉ C) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha) →
    M.domain = univ →
    (∀ t : ℝ, totalEnergy alpha (M.state t) = Ec ∧
      gradientSquared (M.state t) ≤ kappa alpha * Ec) →
    TimeHolder.mixedNorm (volume.restrict (Ici 0)) volume 10 10
      (fun t => energyValue (M.state t)) = ∞ →
    TimeHolder.mixedNorm (volume.restrict (Iic 0)) volume 10 10
      (fun t => energyValue (M.state t)) = ∞ →
    (∀ t, (criticalAffineState (r t) (hr t) (y t)).symm (M.state t) ∈ C) →
    ∃ (psi : EnergyState) (sigma : ℝ),
      (sigma = 1 ∨ sigma = -1) ∧ psi ≠ 0 ∧ totalEnergy alpha psi = Ec ∧
      let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
      V.domain = univ ∧ (¬ ActualScattering.FiniteSAfter V) ∧
      (¬ ActualLeftScattering.FiniteSBefore V) ∧
      (∀ t, totalEnergy alpha (V.state t) = Ec ∧
        gradientSquared (V.state t) ≤ kappa alpha * Ec) ∧
      ∃ (rv : ℝ → ℝ) (hv : ∀ t, 0 < rv t) (xv : ℝ → Space) (Q : Set EnergyState),
        IsCompact Q ∧
        (∀ t, (criticalAffineState (rv t) (hv t) (xv t)).symm (V.state t) ∈ Q) ∧
        ∀ t, 0 ≤ sigma*t → rv t ≤ 2 := by
  intro Ec M hEc hEcW hgap hglobal hNative hfuture hpast hnorm
  let z : ℝ → EnergyState := fun t =>
    (criticalAffineState (r t) (hr t) (y t)).symm (M.state t)
  have hcpt : IsCompact (closure (range z)) :=
    hC.of_isClosed_subset isClosed_closure
      (closure_minimal (range_subset_iff.mpr hnorm) hC.isClosed)
  obtain ⟨_htail, _hratio, hfinite, hsmall⟩ :=
    subparabolic_scale_original_environment hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff f r hr y
      hEc hEcW hgap hglobal hNative hfuture hpast hcpt
  obtain ⟨tau, sigma, k, L, psi, _htau, hsigma, _hk, hL, _hpsi, hz, hwindow⟩ :=
    select_compact_scale_windows z hcpt r hr (fun T hT => (hfinite T hT).1) hsmall
  let c : ℕ → ℝ := fun n => tau (k n)
  let zn : ℕ → EnergyState := fun n => z (c n)
  let Un := fun n => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (zn n)
  have htM (t : ℝ) : t ∈ M.domain := by rw [hglobal]; trivial
  have hf : ¬ ActualScattering.FiniteSAfter M := by
    intro h
    have hinf : TimeHolder.mixedNorm (volume.restrict (M.domain ∩ Ici 0)) volume 10 10
        (fun t => energyValue (M.state t)) = ∞ := by
      simpa only [hglobal, univ_inter] using hfuture
    exact ((finite_after_iff_literal hDensity hSob M).mp h) hinf
  have hp : ¬ ActualLeftScattering.FiniteSBefore M := by
    intro h
    have hinf : TimeHolder.mixedNorm (volume.restrict (M.domain ∩ Iic 0)) volume 10 10
        (fun t => energyValue (M.state t)) = ∞ := by
      simpa only [hglobal, univ_inter] using hpast
    exact ((finite_before_iff_literal hDensity hSob M).mp h) hinf
  have hgradient : ∀ t ∈ M.domain,
      pureGradientNorm (M.state t) ≤ pureGradientNorm (normalizedBubbleState alpha) := by
    intro t _
    exact ((pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr
      ((hNative t).2.trans_lt hgap)).le
  have hbad (n : ℕ) := ActualRecenterBadTransport.normalized_bilateral_bad
    hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique f (c n) (htM _)
      hgradient (pureGradientNorm_nonneg _) (hr (c n)) (y (c n)) hf hp
  have hE (n : ℕ) : totalEnergy alpha (zn n) = Ec := by
    change totalEnergy alpha ((criticalAffineState (r (c n)) (hr _) (y (c n))).symm
      (M.state (c n))) = Ec
    rw [criticalAffineState_symm_eq_affineState, affineState_totalEnergy hOrd]
    exact (hNative _).1
  have hA (n : ℕ) : gradientSquared (zn n) ≤ kappa alpha * Ec := by
    change gradientSquared ((criticalAffineState (r (c n)) (hr _) (y (c n))).symm
      (M.state (c n))) ≤ kappa alpha * Ec
    rw [criticalAffineState_symm_eq_affineState, affineState_gradientSquared]
    exact (hNative _).2
  obtain ⟨hne, hEpsi, _hApsi, _hstable, hVglobal, hVfuture, hVpast, hVnative,
    r0, hr0, y0, Q0, hQ0, _hQne, _hQzero, _hQprop, _hg, hQnorm⟩ :=
    critical_strong_limit_global_compact hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff zn psi hz
      hEc hEcW hgap hE hA (fun n => (hbad n).1) (fun n => (hbad n).2)
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have htV (t : ℝ) : t ∈ V.domain := by rw [hVglobal]; trivial
  have hzNorm : Tendsto (fun n => ‖zn n - psi‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have hconv (t : ℝ) : Tendsto (fun n => (Un n).state t) atTop (𝓝 (V.state t)) :=
    (actual_moving_time_tendsto hDensity hSob h0 hfree hret hefree heret hOrd
      hgen hUnique psi zn hzNorm (min_le_right t 0) (le_max_right t 0)
      (fun _ => t) tendsto_const_nhds ⟨min_le_left _ _, le_max_left _ _⟩
      (Eventually.of_forall fun _ => ⟨min_le_left _ _, le_max_left _ _⟩)
      (fun s _ => htV s)).2
  have hwin (n : ℕ) (t : ℝ) (ht : 0 ≤ sigma*t) (htL : sigma*t ≤ L n) :
      (Un n).state t ∈ boundedAffineCarrier C 2 := by
    have hscale := hwindow n t ht htL
    have hcov := normalized_global_trajectory hDensity hSob h0 hfree hret hefree heret
      hOrd f (c n) (hr (c n)) (y (c n)) hglobal
    rw [hcov.2 t]
    exact rescaled_state_mem_bounded_carrier (hr (c n)) (hr _) (y (c n))
      (y (c n + (r (c n))^2*t)) (M.state (c n + (r (c n))^2*t))
      (hnorm _) hscale.2.2.le
  have hhalf := halfline_mem_of_expanding_windows hSob hC hCzero 2 sigma L hL
    (fun n => (Un n).state) V.state hconv hwin
  obtain ⟨rv, hv, xv, hcompact, hnormalized, hbound⟩ :=
    splice_pointwise_normalizers V.state sigma 2 C Q0 hC hQ0 hhalf r0 hr0 y0
      (fun t => hQnorm t (htV t))
  exact ⟨psi, sigma, hsigma, hne, hEpsi, hVglobal, hVfuture, hVpast,
    (fun t => ⟨(hVnative t (htV t)).1, (hVnative t (htV t)).2.1⟩),
    rv, hv, xv, C ∪ Q0, hcompact, hnormalized, hbound⟩

end HartreeF.Paper121BoundedHalfline
