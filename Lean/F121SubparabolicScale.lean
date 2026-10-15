import F121RunningScaleSupremum
import F121ArbitraryLocalProperness
import F121HalflineFiniteness

/-! R8.4, Proposition 5.7: every compact pointwise normalization of the
given global bilaterally bad critical trajectory is subparabolic. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121Subparabolic
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge NativeCompactGlobal ActualBilateralStrongLimit
  ActualCriticalScaleEscape Paper121SubparabolicScalar Paper121LocalProperness Paper121Finiteness
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] actualMaximalTrajectory

theorem subparabolic_scale_original_environment
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
    (f : EnergyState) (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    0 < Ec → Ec < totalEnergy alpha (normalizedBubbleState alpha) →
    kappa alpha * Ec < gradientSquared (normalizedBubbleState alpha) →
    M.domain = univ →
    (∀ t : ℝ, totalEnergy alpha (M.state t) = Ec ∧
      gradientSquared (M.state t) ≤ kappa alpha * Ec) →
    TimeHolder.mixedNorm (volume.restrict (Ici 0)) volume 10 10
      (fun t => energyValue (M.state t)) = ∞ →
    TimeHolder.mixedNorm (volume.restrict (Iic 0)) volume 10 10
      (fun t => energyValue (M.state t)) = ∞ →
    IsCompact (closure (range (fun t =>
      (criticalAffineState (r t) (hr t) (y t)).symm (M.state t)))) →
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ t : ℝ, R ≤ |t| → (r t) ^ 2 ≤ ε * |t|) ∧
    Tendsto (fun t => (r t) ^ 2 / |t|)
      (comap (fun t : ℝ => |t|) atTop) (𝓝 0) ∧
    (∀ T : ℝ, 0 ≤ T → BddAbove (r '' Icc 0 T) ∧ 0 < runningScaleSupremum r T) ∧
    Tendsto (fun T => runningScaleSupremum r T / Real.sqrt T) atTop (𝓝 0) := by
  intro Ec M hEc hEcW hgap hglobal hNative hfuture hpast hcompact
  let z : ℝ → EnergyState := fun t =>
    (criticalAffineState (r t) (hr t) (y t)).symm (M.state t)
  have htM (t : ℝ) : t ∈ M.domain := by rw [hglobal]; trivial
  have hf : ¬ ActualScattering.FiniteSAfter M := by
    intro h
    have hne := (finite_after_iff_literal hDensity hSob M).mp h
    have hinf : TimeHolder.mixedNorm (volume.restrict (M.domain ∩ Ici 0)) volume 10 10
        (fun t => energyValue (M.state t)) = ∞ := by
      simpa only [hglobal, univ_inter] using hfuture
    exact hne hinf
  have hp : ¬ ActualLeftScattering.FiniteSBefore M := by
    intro h
    have hne := (finite_before_iff_literal hDensity hSob M).mp h
    have hinf : TimeHolder.mixedNorm (volume.restrict (M.domain ∩ Iic 0)) volume 10 10
        (fun t => energyValue (M.state t)) = ∞ := by
      simpa only [hglobal, univ_inter] using hpast
    exact hne hinf
  have htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ t : ℝ, R ≤ |t| → (r t) ^ 2 ≤ ε * |t| := by
    apply tail_of_no_compact_return z r hr hcompact
    intro c hscale psi hz τ hτ
    exact native_critical_return_time_not_tendsto hDensity hRel hSob h0 hfree hret
      hefree heret hOrd hH hS S Bw Bs B6 hExtract hgen hUnique cutoff f
      c (fun n => r (c n)) (fun n => hr (c n)) (fun n => y (c n))
      (fun n => htM (c n)) hscale psi hEc hEcW hgap
      (fun t _ => hNative t) hf hp hz τ hτ
  have hlocal (T : ℝ) (_hT : 0 ≤ T) :
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, r t ≤ C := by
    obtain ⟨a, C, X, _ha, hC, _hX, hbox⟩ :=
      arbitrary_normalizers_bounded_on_compact_time hOrd hEc isCompact_Icc
        M.state (M.continuous.mono (fun t _ => htM t))
        (fun t _ => (hNative t).1) r hr y hcompact
        (fun t _ => subset_closure (mem_range_self t))
    exact ⟨C, hC, fun t ht => (hbox t ht).2.1⟩
  obtain ⟨hfinite, hsup⟩ := running_supremum_subparabolic r hr hlocal htail
  exact ⟨htail, ratio_tendsto_of_tail r htail, hfinite, hsup⟩

end HartreeF.Paper121Subparabolic
