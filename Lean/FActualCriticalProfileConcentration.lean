import FActualCriticalThreshold
import FSingleProfileEnergyConcentration
import FConditionalNonlinearReconstruction
import FCommonLinearProfileTimeNormalization

/-! The original bad sequence forces one actual critical-energy nonlinear
profile.  Large-profile finite X is produced from strict lower energy, not
retained as an input.  The final extraction acts on data and every frame
parameter together.  No spatial Palais--Smale, exclusion of infinite profile
time, global critical orbit, or scattering theorem is claimed. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HartreeF.ActualCriticalProfile
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2Global R2SmallData R2SquareTail
  ProfileEnergy CountableNonlinearProfiles CommonProfileTimes ActualProfileEnergy
  ActualCriticalThreshold FiniteSActualX ConditionalNonlinearReconstruction
  LocalRellich LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- A genuine stable matching state transfers the strict lower-energy result
to the originally selected canonical profile, with whole-curve equality. -/
theorem ledger_profile_global_of_lower_energy (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha E0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    {P : LinearProfileFamily} {u : ℕ → EnergyState} {T : ℕ → ℝ} {f : ℕ → EnergyState}
    (hL : ProfileEnergyLedger hDensity hSob h0 hfree hret hefree heret hOrd P u T f E0)
    (j : ℕ)
    (he : totalEnergy alpha (f j) < criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd (T j) (f j)
    M.domain = Set.univ ∧ CurveFinite M.state := by
  obtain ⟨t, ht, henergy, hEW, hPW⟩ := hL.stable_state j
  have hrec := marked_global_curveFinite_below_criticalLevel hDensity hSob h0 hfree
    hret hefree heret hOrd hH hS S Bw Bs B6 t ⟨hEW, hPW⟩ (henergy.trans_lt he)
  exact actualMaximalTrajectory_global_curveFinite_of_recenter
    hDensity hSob h0 hfree hret hefree heret hOrd (f j) ht hrec

/-- Only a genuinely positive full-energy label is kept.  Active zero labels
are allowed and no count is changed to one. -/
theorem other_profiles_zero (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha E0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    {P : LinearProfileFamily} {u : ℕ → EnergyState} {T : ℕ → ℝ} {f : ℕ → EnergyState}
    (hL : ProfileEnergyLedger hDensity hSob h0 hfree hret hefree heret hOrd P u T f E0)
    {j0 : ℕ} (hj0 : (j0 : WithTop ℕ) < P.count)
    (hcrit : totalEnergy alpha (f j0) = E0) :
    ∀ j, j ≠ j0 → P.profile j = 0 := by
  classical
  intro j hj
  by_cases hactive : (j : WithTop ℕ) < P.count
  · let J := max (j+1) (j0+1)
    have hJ : (J : WithTop ℕ) ≤ P.count := by
      rcases le_total (j+1) (j0+1) with h | h
      · simpa only [J, max_eq_right h] using active_succ_eligible P j0 hj0
      · simpa only [J, max_eq_left h] using active_succ_eligible P j hactive
    have hjmem : j ∈ Finset.range J := Finset.mem_range.mpr
      ((Nat.lt_succ_self j).trans_le (le_max_left _ _))
    have hj0mem : j0 ∈ Finset.range J := Finset.mem_range.mpr
      ((Nat.lt_succ_self j0).trans_le (le_max_right _ _))
    have hsingle := Finset.single_le_sum (fun k _ => hL.energy_nonneg k)
      (Finset.mem_erase.mpr ⟨hj, hjmem⟩ : j ∈ (Finset.range J).erase j0)
    have hsum := Finset.sum_erase_add (Finset.range J)
      (fun k => totalEnergy alpha (f k)) hj0mem
    have halloc := hL.allocation J hJ
    have hezero : totalEnergy alpha (f j) = 0 := by
      have hn := hL.energy_nonneg j
      rw [hcrit] at hsum
      linarith
    have hkin := hL.kinetic_le_energy j
    rw [hezero, mul_zero] at hkin
    have hz : gradientSquared (P.profile j) = 0 :=
      le_antisymm hkin (gradientSquared_nonneg _)
    apply (pureGradientNorm_eq_zero_iff hSob (P.profile j)).mp
    simp only [pureGradientNorm, hz, Real.sqrt_zero]
  · exact P.inactive_zero j hactive

/-- The first actual threshold producer.  Its output is one bad canonical
profile and strong concentration modulo the FULL linear frame.  Its lifespan
need not be all of R, and its normalized profile time may still diverge. -/
theorem exists_actual_critical_profile_concentration
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
      ∃ u : ℕ → EnergyState,
        (∀ n, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd (u n)) ∧
        Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 Ec) ∧
        ∃ (sigma : ℕ → ℕ) (P : LinearProfileFamily) (T : ℕ → ℝ) (f : ℕ → EnergyState)
          (j0 : ℕ) (tau : ℕ → ℕ),
          StrictMono sigma ∧
          LinearProfileProperties hDensity hSob (u ∘ sigma) P ∧
          (∀ j, TimeRegime (P.time j)) ∧
          ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hOrd P T f ∧
          (j0 : WithTop ℕ) < P.count ∧ totalEnergy alpha (f j0) = Ec ∧
          (∀ j, j ≠ j0 → P.profile j = 0) ∧ StrictMono tau ∧
          Tendsto (fun n => pureGradientNorm
            (u (sigma (tau n))-profileAtom hDensity hSob P j0 (tau n))) atTop (𝓝 0) ∧
          Tendsto (fun n => ‖u (sigma (tau n))-profileAtom hDensity hSob P j0 (tau n)‖)
            atTop (𝓝 0) ∧
          let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd
            (T j0) (f j0)
          ¬ FiniteSOnDomain M ∧
            ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = Ec ∧
              gradientSquared (M.state t) ≤ kappa alpha*Ec ∧
              kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha) := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨delta, hdelta, hrec⟩ := exists_conditional_nonlinear_reconstruction
    hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique cutoff
  obtain ⟨hEc, hEcW⟩ := criticalLevel_pos_lt hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 hbad
  obtain ⟨Estar, u, hEstar, _hEstarW, hubad, hEu, hkin, hcap, hgap⟩ :=
    exists_bad_minimizing_sequence hDensity hSob h0 hfree hret hefree heret hOrd
      hH hS S Bw Bs B6 hbad
  let B := Real.sqrt ((2*(3+alpha)/(2+alpha))*Estar)
  obtain ⟨sigma, hsigma, P, hP, ht⟩ := ordinary_extraction_common_time_normalization
    hDensity hSob hExtract u B hcap
  obtain ⟨T, f, hmatch⟩ := exists_countable_actual_nonlinear_profiles
    hDensity hSob h0 hfree hret hefree heret hOrd P ht
  have hE : Tendsto (fun n => totalEnergy alpha ((u ∘ sigma) n)) atTop (𝓝 Ec) :=
    hEu.comp hsigma.tendsto_atTop
  have hkin' (n : ℕ) : gradientSquared ((u ∘ sigma) n) ≤
      kappa alpha*totalEnergy alpha ((u ∘ sigma) n) := hkin (sigma n)
  have hgapEc : kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha) :=
    (mul_le_mul_of_nonneg_left hEstar.le (kappa_pos hH.order_pos).le).trans_lt hgap
  have hL := build_profile_energy_ledger hDensity hRel hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 P (u ∘ sigma) T f hP ht hmatch
      (fun n => hcap (sigma n)) hE hkin' hgapEc hEcW
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
  obtain ⟨tau, htau, hpure, hnorm⟩ := single_profile_concentration
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS P (u ∘ sigma) T f hL hE j0 hjactive hjenergy hother
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd
    (T j0) (f j0)
  have hnotfinite : ¬ FiniteSOnDomain M := by
    intro hfinite
    have hMcap : ∀ t ∈ M.domain,
        pureGradientNorm (M.state t) ≤ Real.sqrt (kappa alpha*totalEnergy alpha (f j0)) := by
      intro t htM
      exact pureGradientNorm_le_of_gradientSquared_le _ (hL.native_trapping j0 t htM).1
    have hMglobal := actualMaximalTrajectory_global_curveFinite_of_finiteS
      hDensity hSob h0 hfree hret hefree heret hOrd (T j0) (f j0) hMcap hfinite
    apply hcontradiction
    intro j hj
    by_cases hjeq : j = j0
    · subst j
      exact hMglobal
    · have hz := hother j hjeq
      have hsize : actualProfileSize P j = 0 := by
        unfold actualProfileSize
        rw [hz]
        exact (pureGradientNorm_eq_zero_iff hSob 0).mpr rfl
      rw [hsize] at hj
      exact False.elim ((not_lt_of_ge hdelta.le) hj)
  refine ⟨hEc, hEcW, u, hubad, hEu, sigma, P, T, f, j0, tau,
    hsigma, hP, ht, hmatch, hjactive, hjenergy, hother, htau, hpure, hnorm,
    hnotfinite, ?_⟩
  intro t htM
  have hcons := LocalMildTrajectory.totalEnergy_constant_on_domain hDensity hSob h0 hfree hret
    hefree heret hOrd S Bw Bs B6 M htM
  have htrap := hL.native_trapping j0 t htM
  rw [hjenergy] at htrap
  exact ⟨hcons.trans hjenergy, htrap⟩

end HartreeF.ActualCriticalProfile
