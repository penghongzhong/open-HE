import FActualCriticalLimitGlobal
import F121HalflineFiniteness
import F121CompactConvergence
import F121LiteralSolutionClass

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121StrongLimit
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold LocalRellich LinearWeakEquation
  ActualCriticalLimitGlobal Paper121Finiteness Paper121Halfline Paper121ActualDomain
  Paper121CompactConvergence ActualCompactTimeConvergence
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

theorem strong_critical_limit_original_environment
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
    (z : ℕ → EnergyState) (psi : EnergyState)
    (hz : Tendsto z atTop (𝓝 psi)) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let Un := fun n => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (z n)
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha) →
    (∀ n, totalEnergy alpha (z n) = Ec) →
    (∀ n, gradientSquared (z n) ≤ kappa alpha * Ec) →
    (∀ n,
      TimeHolder.mixedNorm (volume.restrict ((Un n).domain ∩ Ici 0)) volume 10 10
        (fun t => energyValue ((Un n).state t)) = ∞ ∧
      TimeHolder.mixedNorm (volume.restrict ((Un n).domain ∩ Iic 0)) volume 10 10
        (fun t => energyValue ((Un n).state t)) = ∞) →
    psi ≠ 0 ∧ totalEnergy alpha psi = Ec ∧ gradientSquared psi ≤ kappa alpha * Ec ∧
      let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
      V.domain = univ ∧
      (∀ t : ℝ,
        TimeHolder.mixedNorm (volume.restrict (Ici t)) volume 10 10
          (fun s => energyValue (V.state s)) = ∞ ∧
        TimeHolder.mixedNorm (volume.restrict (Iic t)) volume 10 10
          (fun s => energyValue (V.state s)) = ∞) ∧
      (∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space),
        IsCompact (closure {q : EnergyState | ∃ t : ℝ,
          q = (criticalAffineState (r t) (hr t) (y t)).symm (V.state t)})) ∧
      (∀ a b : ℝ,
        (∀ᶠ n in atTop, Icc a b ⊆ (Un n).domain) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Icc a b,
          ‖(Un n).state t - V.state t‖ < ε) ∧
      (∀ (a b t : ℝ) (tau : ℕ → ℝ), t ∈ Icc a b →
        Tendsto tau atTop (𝓝 t) → (∀ᶠ n in atTop, tau n ∈ Icc a b) →
        Tendsto (fun n => (Un n).state (tau n)) atTop (𝓝 (V.state t))) := by
  intro Ec Un hEc hEcW hgap hE hG hSinf
  have hf (n : ℕ) : ¬ ActualScattering.FiniteSAfter (Un n) := by
    intro h
    exact ((finite_after_iff_literal hDensity hSob (Un n)).mp h) (hSinf n).1
  have hp (n : ℕ) : ¬ ActualLeftScattering.FiniteSBefore (Un n) := by
    intro h
    exact ((finite_before_iff_literal hDensity hSob (Un n)).mp h) (hSinf n).2
  obtain ⟨hne, hEpsi, hGpsi, _hstable, hglobal, hfuture, hpast, _hn,
    r, hr, y, Q, hQc, _hQne, _hQzero, _hQproperties, _hg, hnormalized⟩ :=
    critical_strong_limit_global_compact hDensity hRel hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff z psi hz
      hEc hEcW hgap hE hG hf hp
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  have htV (t : ℝ) : t ∈ V.domain := by rw [hglobal]; trivial
  have hzNorm : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have hwindow (a b : ℝ) : Icc (min a 0) (max b 0) ⊆ V.domain :=
    fun t _ => htV t
  refine ⟨hne, hEpsi, hGpsi, hglobal, ?_, ?_, ?_, ?_⟩
  · intro t
    have h := actual_mixed_halfline_norms_eq_top hDensity hSob V
      ⟨nativeSAfter_eq_top_of_bad hDensity hSob V (htV t) hfuture,
        nativeSBefore_eq_top_of_bad hDensity hSob V (htV t) hpast⟩
    change V.domain = univ at hglobal
    simpa only [hglobal, univ_inter] using h
  · refine ⟨r, hr, y, hQc.of_isClosed_subset isClosed_closure ?_⟩
    apply closure_minimal _ hQc.isClosed
    rintro q ⟨t, rfl⟩
    exact hnormalized t (htV t)
  · intro a b
    have hsub : Icc a b ⊆ Icc (min a 0) (max b 0) :=
      fun _ ht => ⟨(min_le_left _ _).trans ht.1, ht.2.trans (le_max_left _ _)⟩
    obtain ⟨hdom, hconv⟩ := uniform_compact_convergence hDensity hSob h0 hfree hret
      hefree heret hOrd hgen hUnique psi z hzNorm
      (min_le_right a 0) (le_max_right b 0) (hwindow a b)
    refine ⟨hdom.mono (fun _ hn => hsub.trans hn), ?_⟩
    intro ε hε
    exact (hconv ε hε).mono (fun _ hn t ht => hn t (hsub ht))
  · intro a b t tau ht htau htauI
    exact (actual_moving_time_tendsto hDensity hSob h0 hfree hret hefree heret
      hOrd hgen hUnique psi z hzNorm (min_le_right a 0) (le_max_right b 0)
      tau htau ⟨(min_le_left a 0).trans ht.1, ht.2.trans (le_max_left b 0)⟩
      (htauI.mono fun _ hn =>
        ⟨(min_le_left a 0).trans hn.1, hn.2.trans (le_max_left b 0)⟩)
      (hwindow a b)).2

end HartreeF.Paper121StrongLimit
