import FGaugeCompactParameterBounds
import FActualNativeCompactOrbit
import FNativeCompactFiniteEndpointGlobal
import FActualNativeOrbitWindows
import FActualCompactOrbitGauge
import FSharpWStateTopology

/-! Join native critical-orbit extraction to the proved finite-endpoint
exclusion. This adds globality without assuming a halfline or a scale bound.
Candidate proof: acceptance requires actual pinned Lean compilation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualNativeGlobalCompactOrbit
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge ActualBilateralCriticalProfile
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

open ActualNativeCompactOrbit NativeCompactGlobal

theorem exists_actual_global_compact_orbit
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
        V.domain = Set.univ ∧
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
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q  := by
  classical
  obtain ⟨hEc, hEcW, psi, hEpsi, hstable, hfuture, hpast, hNative,
    r, hr, y, Q, hQc, hQne, hQzero, hQproperties, hNormalized⟩ :=
    exists_actual_native_compact_orbit hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff hbad
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have hpsi : psi ≠ 0 := by
    intro hz
    have hn : (criticalAffineState (r 0) (hr 0) (y 0)).symm (V.state 0) ∈ Q :=
      hNormalized 0 V.center_mem
    rw [V.initial, hz, map_zero] at hn
    exact hQzero hn
  have hglobal : V.domain = Set.univ :=
    actual_compact_normalized_global hDensity hSob h0 hfree hret hefree heret hOrd
      hgen psi hpsi hQc r y (fun t _ => hr t) (fun t ht => hNormalized t ht)
  exact ⟨hEc, hEcW, psi, hEpsi, hstable, hglobal, hfuture, hpast, hNative,
    r, hr, y, Q, hQc, hQne, hQzero, hQproperties, hNormalized⟩

theorem exists_actual_global_compact_orbit_with_local_bounds
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
        V.domain = Set.univ ∧
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
          (∀ t ∈ V.domain, L6OrbitGauge.Gauge (V.state t) (r t) (y t)) ∧
          (∀ J : Set ℝ, IsCompact J → ∃ m : ℕ, ∀ t ∈ J,
            1 / ((m : ℝ) + 1) ≤ r t ∧ r t ≤ 2 * ((m : ℝ) + 1) ∧
              ‖y t‖ ≤ 3 * ((m : ℝ) + 1)) ∧
          ∀ t ∈ V.domain,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q  := by
  classical
  obtain ⟨hEc, hEcW, psi, hEpsi, hstable, hfuture, hpast, hNative,
    r, hr, y, Q, hQc, hQne, hQzero, hQproperties, hGauge, hNormalized⟩ :=
    exists_actual_native_compact_orbit_with_gauge hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff hbad
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have hpsi : psi ≠ 0 := by
    intro hz
    have hn : (criticalAffineState (r 0) (hr 0) (y 0)).symm (V.state 0) ∈ Q :=
      hNormalized 0 V.center_mem
    rw [V.initial, hz, map_zero] at hn
    exact hQzero hn
  have hglobal : V.domain = Set.univ :=
    actual_compact_normalized_global hDensity hSob h0 hfree hret hefree heret hOrd
      hgen psi hpsi hQc r y (fun t _ => hr t) (fun t ht => hNormalized t ht)
  have htime (t : ℝ) : t ∈ V.domain := by rw [hglobal]; trivial
  have hnonzero (t : ℝ) : V.state t ≠ 0 := by
    intro hz
    have hq := hNormalized t (htime t)
    rw [hz, map_zero] at hq
    exact hQzero hq
  have hbounds (J : Set ℝ) (hJ : IsCompact J) : ∃ m : ℕ, ∀ t ∈ J,
      1 / ((m : ℝ) + 1) ≤ r t ∧ r t ≤ 2 * ((m : ℝ) + 1) ∧
        ‖y t‖ ≤ 3 * ((m : ℝ) + 1) :=
    L6OrbitGauge.gauge_parameters_bounded_on_compact_time hJ V.state
      (V.continuous.mono (fun t _ => htime t)) (fun t _ => hnonzero t)
      r y (fun t _ => hGauge t (htime t))
  exact ⟨hEc, hEcW, psi, hEpsi, hstable, hglobal, hfuture, hpast, hNative,
    r, hr, y, Q, hQc, hQne, hQzero, hQproperties, hGauge, hbounds, hNormalized⟩

end HartreeF.ActualNativeGlobalCompactOrbit

