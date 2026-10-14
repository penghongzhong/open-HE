import FActualCriticalProfileConcentration

/-! Threshold concentration for the GIVEN bad sequence. No replacing the input
sequence by the existential minimizing sequence of the preceding producer.
The fixed-J scalar ledger and one final J0 subsequence are reused. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HartreeF.GivenBadConcentration
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2Global R2SquareTail CriticalAffine
  ProfileEnergy CountableNonlinearProfiles CommonProfileTimes ActualProfileEnergy
  ActualCriticalThreshold ActualCriticalProfile FiniteSActualX ConditionalNonlinearReconstruction
  LocalRellich LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- The same input sequence, its extraction and final subsequence are composed
synchronously before exposing the scale, center and normalized free time. -/
theorem given_bad_sequence_full_frame
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
    (u : ℕ → EnergyState)
    (hubad : ∀ n, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd (u n))
    (hEu : Tendsto (fun n => totalEnergy alpha (u n)) atTop
      (𝓝 (criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd))) :
    ∃ (k : ℕ → ℕ) (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n)
      (y : ℕ → Space) (s : ℕ → ℝ) (phi : EnergyState),
      StrictMono k ∧ TimeRegime s ∧
      Tendsto (fun n => ‖u (k n) - criticalAffineState (lambda n) (hlambda n) (y n)
        (freeEnergyState hDensity hSob (s n) phi)‖) atTop (𝓝 0) := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨delta, hdelta, hrec⟩ := exists_conditional_nonlinear_reconstruction
    hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique cutoff
  obtain ⟨_hEc, hEcW⟩ := criticalLevel_pos_lt hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 ⟨u 0, hubad 0⟩
  let B := pureGradientNorm (normalizedBubbleState alpha)
  have hcap (n : ℕ) : pureGradientNorm (u n) ≤ B := (hubad n).1.2.le
  obtain ⟨sigma, hsigma, P, hP, ht⟩ := ordinary_extraction_common_time_normalization
    hDensity hSob hExtract u B hcap
  obtain ⟨T, f, hmatch⟩ := exists_countable_actual_nonlinear_profiles
    hDensity hSob h0 hfree hret hefree heret hOrd P ht
  have hE : Tendsto (fun n => totalEnergy alpha ((u ∘ sigma) n)) atTop (𝓝 Ec) :=
    hEu.comp hsigma.tendsto_atTop
  have hkin (n : ℕ) : gradientSquared ((u ∘ sigma) n) ≤
      kappa alpha * totalEnergy alpha ((u ∘ sigma) n) :=
    stable_kinetic_le_energy hOrd hH hS (hubad (sigma n)).1
  have hgapEc : kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha) := by
    have h := mul_lt_mul_of_pos_left hEcW (kappa_pos hH.order_pos)
    exact h.trans_eq (trapping_factor_ground_energy hDensity hOrd hH hS)
  have hL := build_profile_energy_ledger hDensity hRel hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 P (u ∘ sigma) T f hP ht hmatch
      (fun n => hcap (sigma n)) hE hkin hgapEc hEcW
  have hcontradiction
      (hlarge : ∀ j, delta < actualProfileSize P j →
        let Mj := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd
          (T j) (f j)
        Mj.domain = univ ∧ CurveFinite Mj.state) : False := by
    obtain ⟨_hall, _M, _hM, _haug, happ⟩ :=
      hrec P (u ∘ sigma) B (fun n => hcap (sigma n)) hP T f hmatch hlarge
    obtain ⟨_J, N, _helig, hn⟩ := happ 1 (by norm_num)
    have hgood := hn N le_rfl
    exact (hubad (sigma N)).2
      (finiteS_of_global_curveFinite
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (u (sigma N)))
        hgood.1 hgood.2.1)
  have hcritical : ∃ j, delta < actualProfileSize P j ∧ totalEnergy alpha (f j) = Ec := by
    by_contra! hnone
    apply hcontradiction
    intro j hj
    exact ledger_profile_global_of_lower_energy hDensity hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hL j (lt_of_le_of_ne (hL.energy_le j) (hnone j hj))
  obtain ⟨j0, hjlarge, hjenergy⟩ := hcritical
  have hjactive : (j0 : WithTop ℕ) < P.count := by
    by_contra hinactive
    have hz := P.inactive_zero j0 hinactive
    have hsize : actualProfileSize P j0 = 0 := by
      unfold actualProfileSize
      rw [hz]
      exact (pureGradientNorm_eq_zero_iff hSob 0).mpr rfl
    rw [hsize] at hjlarge
    exact (not_lt_of_ge hdelta.le) hjlarge
  have hother := other_profiles_zero hDensity hSob h0 hfree hret hefree heret hOrd
    hL hjactive hjenergy
  obtain ⟨tau, htau, _hpure, hnorm⟩ := single_profile_concentration
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS P (u ∘ sigma) T f hL hE
      j0 hjactive hjenergy hother
  refine ⟨sigma ∘ tau, fun n => P.scale j0 (tau n), fun n => P.scale_pos j0 (tau n),
    fun n => P.center j0 (tau n), (P.time j0) ∘ tau, P.profile j0,
    hsigma.comp htau, timeRegime_comp (ht j0) htau, ?_⟩
  simpa only [Function.comp_apply, profileAtom, linearProfileFrame_apply] using hnorm

end HartreeF.GivenBadConcentration
