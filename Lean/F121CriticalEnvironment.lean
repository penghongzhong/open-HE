import F121CriticalAllTimes
import F121ActualValueDomain
import FPaperMainEnvironment

/-! Failure of the original two-threshold conclusion gives a critical orbit
with genuine native half-line L10 norms infinite at every native time. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121CriticalEnvironment
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge ActualBilateralCriticalProfile
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

open Paper121Halfline Paper121CriticalBounds Paper121ActualNorm Paper121ActualDomain PaperMainEnvironment

theorem critical_element_on_actual_maximal_lifespan
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
        (∀ t ∈ V.domain,
          TimeHolder.mixedNorm (volume.restrict (V.domain ∩ Ici t)) volume 10 10
              (fun z => energyValue (V.state z)) = ∞ ∧
          TimeHolder.mixedNorm (volume.restrict (V.domain ∩ Iic t)) volume 10 10
              (fun z => energyValue (V.state z)) = ∞) ∧
        (∀ t ∈ V.domain, totalEnergy alpha (V.state t) = Ec ∧
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
          (∀ t ∈ V.domain,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q) ∧
          IsCompact (closure {q : EnergyState | ∃ t ∈ V.domain,
            q = (criticalAffineState (r t) (hr t) (y t)).symm (V.state t)}) := by
  have hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f := by
    by_contra hNoBad
    exact hfailure (paper_threshold_conclusion_of_no_bad
      hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6 hNoBad)
  obtain ⟨hEc, hEcW, psi, hEpsi, hs, hSall, hn,
    r, hr, y, Q, hc, hne, hz, hq, hnorm⟩ :=
    Paper121CriticalAllTimes.exists_native_compact_orbit_all_times
      hDensity hRel hSob h0 hfree hret hefree heret hOrd hH hS
      S Bw Bs B6 hExtract hgen hUnique cutoff hbad
  have hpsi : psi ≠ 0 := by
    intro hzpsi
    have hk := (hn 0 (actualMaximalTrajectory
      hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).center_mem).2.1
    rw [(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).initial,
      hzpsi] at hk
    have hgzero : gradientSquared (0 : EnergyState) = 0 := by
      simp [gradientSquared]
    rw [hgzero] at hk
    linarith
  refine ⟨hEc, hEcW, psi, hpsi, hEpsi, hs, ?_, hn,
    r, hr, y, Q, hc, hne, hz, hq, hnorm, ?_⟩
  · intro t ht
    exact actual_mixed_halfline_norms_eq_top hDensity hSob _ (hSall t ht)
  · apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hc.isClosed
    rintro q ⟨t, ht, rfl⟩
    exact hnorm t ht

#print axioms critical_element_on_actual_maximal_lifespan
end HartreeF.Paper121CriticalEnvironment
