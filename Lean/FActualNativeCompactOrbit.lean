import FActualNativeOrbitWindows
import FActualCompactOrbitGauge
import FSharpWStateTopology

/-! The same actual bilateral critical trajectory has a compact spatially
normalized orbit on its native lifespan. The normalizers are only pointwise
choices; globality, a scale floor and scattering are not asserted here.
Author source; UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualNativeCompactOrbit
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge ActualBilateralCriticalProfile
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- All compactness inputs are produced from the same actual bilateral datum.
The closed carrier retains a fixed quantitative kinetic gap, not merely a
closure of the strict sublevel. The original `hbad` remains a contradiction
hypothesis; this theorem is not a nonscattering counterexample. -/
theorem exists_actual_native_compact_orbit
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
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    0 < Ec ∧ Ec < totalEnergy alpha (normalizedBubbleState alpha) ∧
      ∃ psi : EnergyState, totalEnergy alpha psi = Ec ∧ StableDatum alpha psi ∧
        let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
        (¬ ActualScattering.FiniteSAfter V) ∧
        (¬ ActualLeftScattering.FiniteSBefore V) ∧
        (∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
          gradientSquared (V.state t) ≤ kappa alpha*Ec ∧
          kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha)) ∧
        ∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space) (Q : Set EnergyState),
          IsCompact Q ∧ Q.Nonempty ∧ (0 : EnergyState) ∉ Q ∧
          (∀ q ∈ Q, totalEnergy alpha q = Ec ∧
            gradientSquared q ≤ kappa alpha*Ec ∧
            gradientSquared q < gradientSquared (normalizedBubbleState alpha) ∧
            totalEnergy alpha q < totalEnergy alpha (normalizedBubbleState alpha)) ∧
          ∀ t ∈ V.domain,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨hEc, hEcW, psi, hEpsi, hstable, hfuture, hpast, hNative⟩ :=
    exists_actual_bilateral_critical_datum hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff hbad
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
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
  obtain ⟨r0, hr0, y0, hcompact⟩ := exists_compact_normalization hSob
    (fun t : V.domain => V.state t) hnonzero hseq
  let p (t : V.domain) :=
    (criticalAffineState (r0 t) (hr0 t) (y0 t)).symm (V.state t)
  let Q : Set EnergyState := closure (range p)
  have hQc : IsCompact Q := hcompact
  have hQenergy : ∀ q ∈ Q, totalEnergy alpha q = Ec := by
    apply closure_minimal _ (isClosed_eq (totalEnergy_contDiff hOrd).continuous continuous_const)
    rintro q ⟨t, rfl⟩
    rw [show p t = affineState (hr0 t) (y0 t) (V.state t) from
      criticalAffineState_symm_eq_affineState _ _ _ _, affineState_totalEnergy hOrd]
    exact (hNative t t.property).1
  have hQkinetic : ∀ q ∈ Q, gradientSquared q ≤ kappa alpha*Ec := by
    apply closure_minimal _ (isClosed_le DynamicSharpW.gradientSquared_continuous continuous_const)
    rintro q ⟨t, rfl⟩
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
    · simpa only [r, dif_pos ht] using hr0 ⟨t, ht⟩
    · simp only [r, dif_neg ht, zero_lt_one]
  refine ⟨hEc, hEcW, psi, hEpsi, hstable, hfuture, hpast, hNative,
    r, hr, y, Q, hQc, hQne, hQzero, ?_, ?_⟩
  · intro q hq
    exact ⟨hQenergy q hq, hQkinetic q hq, (hQkinetic q hq).trans_lt hgap,
      (hQenergy q hq).trans_lt hEcW⟩
  · intro t ht
    have hp : p ⟨t, ht⟩ ∈ Q := subset_closure (mem_range_self _)
    simpa only [r, y, p, dif_pos ht] using hp

end HartreeF.ActualNativeCompactOrbit
