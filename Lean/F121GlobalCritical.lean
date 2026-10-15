import F121CriticalEnvironment
import F121CompactClosureGlobal

/-! Failure of the original two-threshold conclusion gives a critical orbit
with genuine native half-line L10 norms infinite at every native time. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121GlobalCritical
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge ActualBilateralCriticalProfile
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

open Paper121CriticalEnvironment Paper121CompactGlobal PaperMainEnvironment

theorem global_critical_element_of_threshold_failure
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
      ∃ psi : EnergyState, psi ≠ 0 ∧ totalEnergy alpha psi = Ec ∧ StableDatum alpha psi ∧
        let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
        V.domain = univ ∧
        (∀ t : ℝ,
          TimeHolder.mixedNorm (volume.restrict (Ici t)) volume 10 10
              (fun z => energyValue (V.state z)) = ∞ ∧
          TimeHolder.mixedNorm (volume.restrict (Iic t)) volume 10 10
              (fun z => energyValue (V.state z)) = ∞) ∧
        (∀ t : ℝ, totalEnergy alpha (V.state t) = Ec ∧
          2 * Ec ≤ gradientSquared (V.state t) ∧
          gradientSquared (V.state t) ≤ kappa alpha*Ec ∧
          kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha)) ∧
        ∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space) (Q : Set EnergyState),
          IsCompact Q ∧ Q.Nonempty ∧ (0 : EnergyState) ∉ Q ∧
          (∀ q ∈ Q, totalEnergy alpha q = Ec ∧
            2 * Ec ≤ gradientSquared q ∧
            gradientSquared q ≤ kappa alpha*Ec ∧
            gradientSquared q < gradientSquared (normalizedBubbleState alpha) ∧
            totalEnergy alpha q < totalEnergy alpha (normalizedBubbleState alpha)) ∧
          (∀ t : ℝ,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q) ∧
          IsCompact (closure {q : EnergyState | ∃ t ∈ V.domain,
            q = (criticalAffineState (r t) (hr t) (y t)).symm (V.state t)}) := by
  obtain ⟨hEc, hEcW, psi, hpsi, hEpsi, hs, hSall, hn,
    r, hr, y, Q, hc, hne, hz, hq, hnorm, hclosure⟩ :=
    critical_element_on_actual_maximal_lifespan
      hDensity hRel hSob h0 hfree hret hefree heret hOrd hH hS
      S Bw Bs B6 hExtract hgen hUnique cutoff hfailure
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have hglobal : V.domain = univ :=
    (no_finite_endpoint_of_compact_closure hDensity hSob h0 hfree hret hefree heret
      hOrd hgen psi hpsi r y (fun t _ => hr t) hclosure).2.2
  have ht (t : ℝ) : t ∈ V.domain := by rw [hglobal]; trivial
  refine ⟨hEc, hEcW, psi, hpsi, hEpsi, hs, hglobal, ?_,
    (fun t => hn t (ht t)), r, hr, y, Q, hc, hne, hz, hq,
    (fun t => hnorm t (ht t)), hclosure⟩
  intro t
  have h := hSall t (ht t)
  simpa only [hglobal, univ_inter] using h

#print axioms global_critical_element_of_threshold_failure
end HartreeF.Paper121GlobalCritical
