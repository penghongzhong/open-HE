import F121BoundedHalflineLimit
import F121GlobalCritical
import F121LiteralSolutionClass
import F121SignedOrientation

/-! The bounded-half-line critical orbit from failure of the original
threshold conclusion. The final fixed dilation acts on the same actual
maximal trajectory and preserves literal bilateral infinite L10 size. -/
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
  Paper121GlobalCritical PaperMainEnvironment Paper121NormalizedGlobal
  Paper121RelativeNormalization Paper121Halfline Paper121ActualDomain Paper121LiteralClass
  Paper121SignedOrientation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] actualMaximalTrajectory

theorem bounded_halfline_of_threshold_failure
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
    (hfailure : ¬ PaperThresholdConclusion hDensity hSob h0 hfree hret hefree heret hOrd) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    0 < Ec ∧ Ec < totalEnergy alpha (normalizedBubbleState alpha) ∧
    ∃ (f : EnergyState) (sigma : ℝ),
      (sigma = 1 ∨ sigma = -1) ∧ f ≠ 0 ∧ totalEnergy alpha f = Ec ∧
      let W := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
      W.domain = univ ∧
      (∀ t, totalEnergy alpha (W.state t) = Ec ∧
        gradientSquared (W.state t) ≤ kappa alpha * Ec ∧
        kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha)) ∧
      (∀ t : ℝ,
        TimeHolder.mixedNorm (volume.restrict (Ici t)) volume 10 10
          (fun s => energyValue (W.state s)) = ∞ ∧
        TimeHolder.mixedNorm (volume.restrict (Iic t)) volume 10 10
          (fun s => energyValue (W.state s)) = ∞) ∧
      (∀ a b : ℝ, a ≤ b → LiteralMildOn alpha (standardRieszConstant alpha) a b W.state) ∧
      SignedHartreeTensorPDE hOrd sigma (fun s => W.state (sigma*s)) ∧
      ∃ (rw : ℝ → ℝ) (hw : ∀ t, 0 < rw t) (xw : ℝ → Space),
        IsCompact (closure {q : EnergyState | ∃ t : ℝ,
          q = (criticalAffineState (rw t) (hw t) (xw t)).symm (W.state t)}) ∧
        (∀ t, 0 ≤ sigma*t → rw t ≤ 1) ∧
        (∀ s : ℝ, 0 ≤ s → rw (sigma*s) ≤ 1 ∧
          totalEnergy alpha (W.state (sigma*s)) = Ec) := by
  intro Ec
  obtain ⟨hEc, hEcW, f0, _hf0, _hEf0, _hstable0, hMglobal, hMS, hMN,
    r, hr, y, C, hC, _hCne, hCzero, _hCprop, hCnorm, _hclosure⟩ :=
    global_critical_element_of_threshold_failure hDensity hRel hSob h0 hfree hret
      hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff hfailure
  have hgap : kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha) :=
    (hMN 0).2.2.2
  obtain ⟨psi, sigma, hsigma, hpsi, _hEpsi, hVglobal, hVfuture, hVpast, hVN,
    rv, hv, xv, Q, hQ, hQnorm, hbound⟩ :=
    bounded_halfline_critical_limit hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff f0 r hr y C hC hCzero
      hEc hEcW hgap hMglobal (fun t => ⟨(hMN t).1, (hMN t).2.2.1⟩)
      (hMS 0).1 (hMS 0).2 hCnorm
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have htwo : (0 : ℝ) < 2 := by norm_num
  let f : EnergyState := (criticalAffineState 2 htwo 0).symm psi
  let W := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
  have hinit : V.state 0 = psi := V.initial
  have hpow : (2 : ℝ)^2 = 4 := by norm_num
  have hW : W.domain = univ ∧ ∀ t,
      W.state t = (criticalAffineState 2 htwo 0).symm (V.state (4*t)) := by
    have h := normalized_global_trajectory hDensity hSob h0 hfree hret hefree heret
      hOrd psi 0 htwo 0 hVglobal
    change (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd
      0 ((criticalAffineState 2 htwo 0).symm (V.state 0))).domain = univ ∧
      ∀ t, (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd
        0 ((criticalAffineState 2 htwo 0).symm (V.state 0))).state t =
        (criticalAffineState 2 htwo 0).symm (V.state (0+2^2*t)) at h
    simpa only [hinit, zero_add, hpow] using h
  have hf : f ≠ 0 := by
    intro hz
    have he := congrArg (fun q => criticalAffineState 2 htwo 0 q) hz
    have hinv : criticalAffineState 2 htwo 0 f = psi :=
      (criticalAffineState 2 htwo 0).apply_symm_apply psi
    rw [hinv, map_zero] at he
    exact hpsi he
  have hWN (t : ℝ) : totalEnergy alpha (W.state t) = Ec ∧
      gradientSquared (W.state t) ≤ kappa alpha * Ec := by
    rw [hW.2 t, criticalAffineState_symm_eq_affineState,
      affineState_totalEnergy hOrd, affineState_gradientSquared]
    exact hVN (4*t)
  have htV (t : ℝ) : t ∈ V.domain := by rw [hVglobal]; trivial
  have htW (t : ℝ) : t ∈ W.domain := by rw [hW.1]; trivial
  have hgradient : ∀ t ∈ V.domain,
      pureGradientNorm (V.state t) ≤ pureGradientNorm (normalizedBubbleState alpha) := by
    intro t _
    exact ((pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr
      ((hVN t).2.trans_lt hgap)).le
  have hbad : (¬ ActualScattering.FiniteSAfter W) ∧
      (¬ ActualLeftScattering.FiniteSBefore W) := by
    have h := ActualRecenterBadTransport.normalized_bilateral_bad
      hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique psi 0 (htV 0)
      hgradient (pureGradientNorm_nonneg _) htwo 0 hVfuture hVpast
    change (¬ ActualScattering.FiniteSAfter (actualMaximalTrajectory
      hDensity hSob h0 hfree hret hefree heret hOrd 0
      ((criticalAffineState 2 htwo 0).symm (V.state 0)))) ∧
      (¬ ActualLeftScattering.FiniteSBefore (actualMaximalTrajectory
        hDensity hSob h0 hfree hret hefree heret hOrd 0
        ((criticalAffineState 2 htwo 0).symm (V.state 0)))) at h
    simpa only [hinit] using h
  let rw : ℝ → ℝ := fun t => rv (4*t)/2
  have hw (t : ℝ) : 0 < rw t := div_pos (hv _) htwo
  let xw : ℝ → Space := fun t => (2 : ℝ)⁻¹ • xv (4*t)
  have hcompact : IsCompact (closure {q : EnergyState | ∃ t : ℝ,
      q = (criticalAffineState (rw t) (hw t) (xw t)).symm (W.state t)}) := by
    apply hQ.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hQ.isClosed
    rintro q ⟨t, rfl⟩
    rw [hW.2 t]
    have he := normalize_rescaled_state htwo (hv (4*t)) 0 (xv (4*t)) (V.state (4*t))
    simpa only [sub_zero] using he.symm ▸ hQnorm (4*t)
  have hunit (t : ℝ) (ht : 0 ≤ sigma*t) : rw t ≤ 1 := by
    have hsign : 0 ≤ sigma*(4*t) := by nlinarith
    have hb := hbound (4*t) hsign
    dsimp only [rw]
    linarith
  refine ⟨hEc, hEcW, f, sigma, hsigma, hf, ?_, hW.1,
    (fun t => ⟨(hWN t).1, (hWN t).2, hgap⟩), ?_, ?_,
    actual_global_signed_tensor hDensity hSob hOrd h0 hfree hret hgen W hW.1 sigma hsigma,
    rw, hw, xw,
    hcompact, hunit, ?_⟩
  · simpa only [W.initial] using (hWN 0).1
  · intro t
    have h := actual_mixed_halfline_norms_eq_top hDensity hSob W
      ⟨nativeSAfter_eq_top_of_bad hDensity hSob W (htW t) hbad.1,
        nativeSBefore_eq_top_of_bad hDensity hSob W (htW t) hbad.2⟩
    simpa only [hW.1, univ_inter] using h
  · intro a b hab
    exact (ofNative W).mild hab (fun t _ => htW t)
  · intro s hs
    have hsign : 0 ≤ sigma*(sigma*s) := by
      rcases hsigma with he | he <;> rw [he] <;> nlinarith
    exact ⟨hunit _ hsign, (hWN _).1⟩

end HartreeF.Paper121BoundedHalfline
