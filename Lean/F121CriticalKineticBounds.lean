import FActualNativeCompactOrbit

/-! R8.4 Proposition 5.2: both kinetic bounds on the same native critical
trajectory and compact carrier. This module does not yet assert the literal
whole-half-line S norm identities at every native time. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121CriticalBounds
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge ActualBilateralCriticalProfile
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

theorem twice_energy_le_kinetic {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha)) (u : EnergyState) :
    2 * totalEnergy alpha u ≤ gradientSquared u := by
  have hc := hOrd.normalization_pos.le
  have hD : 0 ≤ EnergyVariation.interactionLp alpha (energyValue u) := by
    change 0 ≤ ∫ x, potential alpha (standardRieszConstant alpha) (energyValue u) x *
      powerDensity alpha (energyValue u) x
    apply integral_nonneg
    intro x
    have hp : 0 ≤ potential alpha (standardRieszConstant alpha) (energyValue u) x := by
      apply integral_nonneg
      intro y
      unfold rieszKernel powerDensity
      positivity
    exact mul_nonneg hp (Real.rpow_nonneg (norm_nonneg _) _)
  have hden : 0 ≤ 2 * (3 + alpha) := by linarith [hOrd.order_pos]
  have hquot := div_nonneg hD hden
  unfold totalEnergy
  linarith

theorem exists_native_compact_orbit_with_two_sided_kinetic_bounds
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
          ∀ t ∈ V.domain,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q := by
  obtain ⟨hEc, hEcW, psi, hEpsi, hs, hf, hp, hn,
    r, hr, y, Q, hc, hne, hz, hq, hnorm⟩ :=
    ActualNativeCompactOrbit.exists_actual_native_compact_orbit
      hDensity hRel hSob h0 hfree hret hefree heret hOrd hH hS
      S Bw Bs B6 hExtract hgen hUnique cutoff hbad
  refine ⟨hEc, hEcW, psi, hEpsi, hs, hf, hp, ?_,
    r, hr, y, Q, hc, hne, hz, ?_, hnorm⟩
  · intro t ht
    obtain ⟨he, hk, hgap⟩ := hn t ht
    have hlo := twice_energy_le_kinetic hOrd
      ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).state t)
    rw [he] at hlo
    exact ⟨he, hlo, hk, hgap⟩
  · intro q hqmem
    obtain ⟨he, hk, hgap, henergy⟩ := hq q hqmem
    have hlo := twice_energy_le_kinetic hOrd q
    rw [he] at hlo
    exact ⟨he, hlo, hk, hgap, henergy⟩

#print axioms twice_energy_le_kinetic
#print axioms exists_native_compact_orbit_with_two_sided_kinetic_bounds
end HartreeF.Paper121CriticalBounds
