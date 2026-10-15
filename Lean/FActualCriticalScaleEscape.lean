import FActualCriticalLimitGlobal
import FActualScaleEscapeContradiction
import FActualRecenterBadTransport

/-! Return-time escape in the original critical-energy environment.
Globality and nonvanishing of the strong limit are derived. The native theorem
also derives normalized-data badness; the full subparabolic estimate is not asserted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualCriticalScaleEscape
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge NativeCompactGlobal ActualBilateralStrongLimit
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

open ActualCriticalLimitGlobal ActualScaleEscape
attribute [local irreducible] actualMaximalTrajectory

/-- Critical energy and bilateral badness supply the global nonzero limit
needed for the actual return-time contradiction. -/
theorem critical_normalized_return_time_not_tendsto
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
    {A : ℝ} (f : EnergyState) (hf : f ≠ 0)
    (c r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (y : ℕ → Space)
    (hc : ∀ n, c n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f).domain)
    (hscale : Tendsto r atTop atTop) (psi : EnergyState) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    let z := fun n => (criticalAffineState (r n) (hr n) (y n)).symm (M.state (c n))
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    A < gradientSquared (normalizedBubbleState alpha) →
    (∀ n, totalEnergy alpha (z n) = Ec) →
    (∀ n, gradientSquared (z n) ≤ A) →
    (∀ n, ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) →
    (∀ n, ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n))) →
    Tendsto z atTop (𝓝 psi) →
      ∀ t : ℝ, ¬ Tendsto (fun n => -c n / (r n)^2) atTop (𝓝 t) := by
  intro Ec M z hEc hEcW hAW hE hA hfuture hpast hz
  have hlimit := critical_strong_limit_global_compact hDensity hRel hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff z psi hz
    hEc hEcW hAW hE hA hfuture hpast
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have hglobal : V.domain = univ := hlimit.2.2.2.2.1
  have hEzero : totalEnergy alpha (0 : EnergyState) = 0 := by
    simp [totalEnergy, gradientSquared, FreeTimeDecay.interactionLp_zero hH.order_pos]
  have hnonzero (t : ℝ) : V.state t ≠ 0 := by
    intro hzero
    have ht : t ∈ V.domain := by rw [hglobal]; exact mem_univ t
    have he := (hlimit.2.2.2.2.2.2.2.1 t ht).1
    rw [hzero, hEzero] at he
    exact hEc.ne he
  exact normalized_return_time_not_tendsto hDensity hSob h0 hfree hret hefree heret hOrd
    hgen hUnique f hf c r hr y hc hscale psi hz hglobal hnonzero

/-- The original native energy ledger and bilateral badness generate all
normalized-sequence hypotheses. A strong limit is still supplied explicitly. -/
theorem native_critical_return_time_not_tendsto
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
    {A : ℝ} (f : EnergyState)
    (c r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (y : ℕ → Space)
    (hc : ∀ n, c n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f).domain)
    (hscale : Tendsto r atTop atTop) (psi : EnergyState) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    let z := fun n => (criticalAffineState (r n) (hr n) (y n)).symm (M.state (c n))
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    A < gradientSquared (normalizedBubbleState alpha) →
    (∀ t ∈ M.domain, totalEnergy alpha (M.state t) = Ec ∧ gradientSquared (M.state t) ≤ A) →
    (¬ ActualScattering.FiniteSAfter M) → (¬ ActualLeftScattering.FiniteSBefore M) →
    Tendsto z atTop (𝓝 psi) →
      ∀ t : ℝ, ¬ Tendsto (fun n => -c n / (r n)^2) atTop (𝓝 t) := by
  intro Ec M z hEc hEcW hAW hNative hfuture hpast hz
  have hEzero : totalEnergy alpha (0 : EnergyState) = 0 := by
    simp [totalEnergy, gradientSquared, FreeTimeDecay.interactionLp_zero hH.order_pos]
  have hf : f ≠ 0 := by
    intro hzero
    have he := (hNative 0 M.center_mem).1
    rw [M.initial, hzero, hEzero] at he
    exact hEc.ne he
  have hgradient : ∀ t ∈ M.domain,
      pureGradientNorm (M.state t) ≤ pureGradientNorm (normalizedBubbleState alpha) := by
    intro t ht
    exact ((pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr
      ((hNative t ht).2.trans_lt hAW)).le
  have hbad (n : ℕ) := ActualRecenterBadTransport.normalized_bilateral_bad
    hDensity hSob h0 hfree hret hefree heret hOrd hgen hUnique f (c n) (hc n)
      hgradient (pureGradientNorm_nonneg _) (hr n) (y n) hfuture hpast
  have hE (n : ℕ) : totalEnergy alpha (z n) = Ec := by
    have he := criticalAffineState_totalEnergy hOrd (r n) (hr n) (y n) (z n)
    have hinv : criticalAffineState (r n) (hr n) (y n) (z n) = M.state (c n) :=
      (criticalAffineState (r n) (hr n) (y n)).apply_symm_apply _
    rw [hinv] at he
    exact he.symm.trans (hNative (c n) (hc n)).1
  have hA (n : ℕ) : gradientSquared (z n) ≤ A := by
    have he := criticalAffineState_gradientSquared (r n) (hr n) (y n) (z n)
    have hinv : criticalAffineState (r n) (hr n) (y n) (z n) = M.state (c n) :=
      (criticalAffineState (r n) (hr n) (y n)).apply_symm_apply _
    rw [hinv] at he
    exact he.symm.le.trans (hNative (c n) (hc n)).2
  exact critical_normalized_return_time_not_tendsto hDensity hRel hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff f hf c r hr y hc hscale psi
      hEc hEcW hAW hE hA (fun n => (hbad n).1) (fun n => (hbad n).2) hz

/-- Hartree v23, Lemma 2.19 (one-sided-normalization), the left-length step.
Here r_n = 1/N_n, so c_n/r_n² = t_n N_n². Compactness supplies the
strong subsequence; no strong-limit or global-limit hypothesis is added.
This is only the length-divergence step, not the full normalization lemma. -/
theorem native_return_length_tendsto_atTop
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
    {A : ℝ} (f : EnergyState)
    (c r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (y : ℕ → Space)
    (hc : ∀ n, c n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f).domain)
    (hscale : Tendsto r atTop atTop) (hcpos : ∀ n, 0 ≤ c n) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    let z := fun n => (criticalAffineState (r n) (hr n) (y n)).symm (M.state (c n))
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    A < gradientSquared (normalizedBubbleState alpha) →
    (∀ t ∈ M.domain, totalEnergy alpha (M.state t) = Ec ∧ gradientSquared (M.state t) ≤ A) →
    (¬ ActualScattering.FiniteSAfter M) → (¬ ActualLeftScattering.FiniteSBefore M) →
    IsCompact (closure (range z)) →
      Tendsto (fun n => c n / (r n)^2) atTop atTop := by
  intro Ec M z hEc hEcW hAW hNative hfuture hpast hcompact
  classical
  let L : ℕ → ℝ := fun n => c n / (r n)^2
  have hLpos (n : ℕ) : 0 ≤ L n := div_nonneg (hcpos n) (sq_nonneg _)
  apply tendsto_atTop.2
  intro b
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, L n < b := by
    simpa only [not_le] using (not_eventually.mp hnot)
  have hpcompact : IsCompact (closure (range z) ×ˢ Icc (0 : ℝ) b) :=
    hcompact.prod isCompact_Icc
  have hmem : ∃ᶠ n in atTop, (z n, L n) ∈ closure (range z) ×ˢ Icc (0 : ℝ) b :=
    hfreq.mono fun n hn => ⟨subset_closure (mem_range_self n), hLpos n, hn.le⟩
  obtain ⟨p, _hp, k, hk, hlimit⟩ := hpcompact.tendsto_subseq' hmem
  have hz : Tendsto (fun n => z (k n)) atTop (𝓝 p.1) := hlimit.fst_nhds
  have htime : Tendsto (fun n => -c (k n) / (r (k n))^2) atTop (𝓝 (-p.2)) := by
    simpa only [Function.comp_def, L, neg_div] using hlimit.snd_nhds.neg
  exact native_critical_return_time_not_tendsto hDensity hRel hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff f
    (fun n => c (k n)) (fun n => r (k n)) (fun n => hr (k n))
    (fun n => y (k n)) (fun n => hc (k n)) (hscale.comp hk.tendsto_atTop) p.1
    hEc hEcW hAW hNative hfuture hpast hz (-p.2) htime

end HartreeF.ActualCriticalScaleEscape
