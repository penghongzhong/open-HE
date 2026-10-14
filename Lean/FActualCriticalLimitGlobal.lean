import FActualNativeGlobalCompactOrbit
import FActualBilateralStrongLimit
import FActualCompactTimeConvergence

/-! Compactness and globality of the specified strong critical limit.
The datum in the conclusion is the supplied limit, not a newly extracted datum.
The remaining subparabolic-scale and bounded-halfline arguments are separate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualCriticalLimitGlobal
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge NativeCompactGlobal ActualBilateralStrongLimit
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- Native compact normalization for the specified bilateral critical datum. -/
theorem given_critical_native_compact_orbit
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
    (psi : EnergyState) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    (¬ ActualScattering.FiniteSAfter V) →
    (¬ ActualLeftScattering.FiniteSBefore V) →
    (∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
      gradientSquared (V.state t) ≤ kappa alpha * Ec ∧
      kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha)) →
        ∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space) (Q : Set EnergyState),
          IsCompact Q ∧ Q.Nonempty ∧ (0 : EnergyState) ∉ Q ∧
          (∀ q ∈ Q, totalEnergy alpha q = Ec ∧
            gradientSquared q ≤ kappa alpha*Ec ∧
            gradientSquared q < gradientSquared (normalizedBubbleState alpha) ∧
            totalEnergy alpha q < totalEnergy alpha (normalizedBubbleState alpha)) ∧
          (∀ t ∈ V.domain, L6OrbitGauge.Gauge (V.state t) (r t) (y t)) ∧
          ∀ t ∈ V.domain,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q := by
  intro Ec V hEc hEcW hfuture hpast hNative
  classical
  have hEzero : totalEnergy alpha (0 : EnergyState) = 0 := by
    simp [totalEnergy, gradientSquared, FreeTimeDecay.interactionLp_zero hH.order_pos]
  have hnonzero (t : V.domain) : V.state t ≠ 0 := by
    intro hz
    have he := (hNative t t.property).1
    rw [hz, hEzero] at he
    exact hEc.ne he
  have hseq : SpatialSequentialConcentration (fun t : V.domain => V.state t) := by
    intro t
    obtain ⟨k, lambda, hlambda, z, v, hk, hv, hEv⟩ :=
      native_sequence_spatial_concentration hDensity hRel hSob h0 hfree hret hefree heret
        hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff psi hEcW hfuture hpast hNative
          (fun n => (t n : ℝ)) (fun n => (t n).property)
    refine ⟨k, lambda, hlambda, z, v, hk, hv, ?_⟩
    intro hz
    rw [hz, hEzero] at hEv
    exact hEc.ne hEv
  obtain ⟨r0, hr0, y0, hg0, hcompact⟩ := exists_compact_normalization_with_gauge hSob
    (fun t : V.domain => V.state t) hnonzero hseq
  let p (t : V.domain) :=
    (criticalAffineState (r0 t) (hr0 t) (y0 t)).symm (V.state t)
  let Q : Set EnergyState := closure (range p)
  have hQc : IsCompact Q := hcompact
  have hQenergy : ∀ q ∈ Q, totalEnergy alpha q = Ec := by
    apply closure_minimal _ (isClosed_eq (totalEnergy_contDiff hOrd).continuous continuous_const)
    rintro q ⟨t, rfl⟩
    change totalEnergy alpha (p t) = Ec
    rw [show p t = affineState (hr0 t) (y0 t) (V.state t) from
      criticalAffineState_symm_eq_affineState _ _ _ _, affineState_totalEnergy hOrd]
    exact (hNative t t.property).1
  have hQkinetic : ∀ q ∈ Q, gradientSquared q ≤ kappa alpha*Ec := by
    apply closure_minimal _ (isClosed_le DynamicSharpW.gradientSquared_continuous continuous_const)
    rintro q ⟨t, rfl⟩
    change gradientSquared (p t) ≤ kappa alpha*Ec
    rw [show p t = affineState (hr0 t) (y0 t) (V.state t) from
      criticalAffineState_symm_eq_affineState _ _ _ _, affineState_gradientSquared]
    exact (hNative t t.property).2.1
  have hgap : kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha) :=
    (hNative 0 V.center_mem).2.2
  have hQzero : (0 : EnergyState) ∉ Q := by
    intro hz
    have he := hQenergy 0 hz
    rw [hEzero] at he
    exact hEc.ne he
  have hQne : Q.Nonempty :=
    ⟨p ⟨0, V.center_mem⟩, subset_closure (mem_range_self _)⟩
  let r (t : ℝ) := if ht : t ∈ V.domain then r0 ⟨t, ht⟩ else 1
  let y (t : ℝ) := if ht : t ∈ V.domain then y0 ⟨t, ht⟩ else 0
  have hr (t : ℝ) : 0 < r t := by
    by_cases ht : t ∈ V.domain
    · simpa only [r, dite_eq_left ht] using hr0 ⟨t, ht⟩
    · simp only [r, dite_eq_right ht, zero_lt_one]
  refine ⟨r, hr, y, Q, hQc, hQne, hQzero, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨hQenergy q hq, hQkinetic q hq, (hQkinetic q hq).trans_lt hgap,
      (hQenergy q hq).trans_lt hEcW⟩
  · intro t ht
    change L6OrbitGauge.Gauge (V.state t) (r t) (y t)
    have hr_eq : r t = r0 ⟨t, ht⟩ := dite_eq_left ht
    have hy_eq : y t = y0 ⟨t, ht⟩ := dite_eq_left ht
    rw [hr_eq, hy_eq]
    exact hg0 ⟨t, ht⟩
  · intro t ht
    have hp : p ⟨t, ht⟩ ∈ Q := subset_closure (mem_range_self _)
    let normalAt : ℝ → Space → Prop := fun a z =>
      ∀ ha : 0 < a, (criticalAffineState a ha z).symm (V.state t) ∈ Q
    have hraw : normalAt (r0 ⟨t, ht⟩) (y0 ⟨t, ht⟩) := fun _ => hp
    have hr_eq : r t = r0 ⟨t, ht⟩ := dite_eq_left ht
    have hy_eq : y t = y0 ⟨t, ht⟩ := dite_eq_left ht
    have hnormalized : normalAt (r t) (y t) :=
      Eq.mpr (congrArg₂ normalAt hr_eq hy_eq) hraw
    exact hnormalized (hr t)

/-- Strong critical limits retain their own global compact orbit. The energy
level and the strict kinetic gap are inputs on the approximating data; native
trapping, bilateral badness, compactness and globality are outputs. -/
theorem critical_strong_limit_global_compact
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
    {A : ℝ} (z : ℕ → EnergyState) (psi : EnergyState)
    (hz : Tendsto z atTop (𝓝 psi)) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    A < gradientSquared (normalizedBubbleState alpha) →
    (∀ n, totalEnergy alpha (z n) = Ec) →
    (∀ n, gradientSquared (z n) ≤ A) →
    (∀ n, ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) →
    (∀ n, ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) →
    psi ≠ 0 ∧ totalEnergy alpha psi = Ec ∧ gradientSquared psi ≤ A ∧
      StableDatum alpha psi ∧
      let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
      V.domain = univ ∧
      (¬ ActualScattering.FiniteSAfter V) ∧
      (¬ ActualLeftScattering.FiniteSBefore V) ∧
      (∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
      gradientSquared (V.state t) ≤ kappa alpha * Ec ∧
      kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha)) ∧
        ∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space) (Q : Set EnergyState),
          IsCompact Q ∧ Q.Nonempty ∧ (0 : EnergyState) ∉ Q ∧
          (∀ q ∈ Q, totalEnergy alpha q = Ec ∧
            gradientSquared q ≤ kappa alpha*Ec ∧
            gradientSquared q < gradientSquared (normalizedBubbleState alpha) ∧
            totalEnergy alpha q < totalEnergy alpha (normalizedBubbleState alpha)) ∧
          (∀ t ∈ V.domain, L6OrbitGauge.Gauge (V.state t) (r t) (y t)) ∧
          ∀ t ∈ V.domain,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q := by
  intro Ec hEc hEcW hAW hE hA hfuture hpast
  obtain ⟨hne, hEpsi, hApsi, hstable, hf, hp, hn⟩ :=
    threshold_bilateral_limit hDensity hSob h0 hfree hret hefree heret hOrd hH hS
      S Bw Bs B6 hgen hUnique hEc hEcW hAW z psi hz hE hA hfuture hpast
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have hNative : ∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
      gradientSquared (V.state t) ≤ kappa alpha * Ec ∧
      kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha) := by
    simpa only [kappa] using hn
  obtain ⟨r, hr, y, Q, hQc, hQne, hQzero, hQproperties, hg, hnormalized⟩ :=
    given_critical_native_compact_orbit hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff psi hEc hEcW hf hp hNative
  have hglobal : V.domain = univ :=
    actual_compact_normalized_global hDensity hSob h0 hfree hret hefree heret hOrd
      hgen psi hne hQc r y (fun t _ => hr t) (fun t ht => hnormalized t ht)
  exact ⟨hne, hEpsi, hApsi, hstable, hglobal, hf, hp, hNative,
    r, hr, y, Q, hQc, hQne, hQzero, hQproperties, hg, hnormalized⟩

end HartreeF.ActualCriticalLimitGlobal

