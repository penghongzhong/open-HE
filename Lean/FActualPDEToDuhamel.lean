import FActualRetardedWeakPDE

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport

theorem weakOperator_smul (c : ℂ) (U : ℝ → TD) (η : TimeTest) (φ : Test) (t : ℝ) :
    weakOperator (fun s => c • U s) η φ t = c * weakOperator U η φ t := by
  simp only [weakOperator, smul_apply, smul_eq_mul]
  ring

theorem WeakEquation.smul {a b : ℝ} {U F : ℝ → TD}
    (h : WeakEquation a b U F) (c : ℂ) :
    WeakEquation a b (fun t => c • U t) (fun t => c • F t) := by
  intro η hη φ
  obtain ⟨hUi, hFi, he⟩ := h η hη φ
  have hleft : weakOperator (fun t => c • U t) η φ =
      fun t => c * weakOperator U η φ t := funext (weakOperator_smul c U η φ)
  have hright : (fun t => η t * (c • F t) φ) = fun t => c * (η t * F t φ) := by
    funext t
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [hleft, hright]
  exact ⟨hUi.const_mul c, hFi.const_mul c, by rw [integral_const_mul, integral_const_mul, he]⟩

/-- Native weak PDE for the free term follows from the precise ordinary generator
by scalar FTC. The initial tempered distribution need not lie in L2 or Hminus1. -/
theorem actualFreeDistribution_weakEquation (hgen : OrdinaryFreeDistributionScalarGenerator)
    {a b : ℝ} (hab : a ≤ b) (T : TD) :
    WeakEquation a b (fun t => FreeFlow.free (t-a) T) (fun _ => 0) := by
  intro η hη φ
  have hop : weakOperator (fun t => FreeFlow.free (t-a) T) η φ = kernelWeakTest T η φ a := by
    funext t
    simp only [weakOperator, kernelWeakTest, free_apply]
  rw [hop]
  refine ⟨(kernelWeakTest_continuous hgen T η φ a).integrableOn_Icc, ?_, ?_⟩
  · simp only [zero_apply, mul_zero]
    exact integrable_zero ℝ ℂ _
  · simp only [zero_apply, mul_zero, integral_zero]
    rw [integral_Icc_eq_integral_Ioc,
      kernelWeakTest_integral hgen T η φ hab (timeTest_right_zero η hη),
      timeTest_left_zero η hη, mul_zero, zero_mul]

variable (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b)
  (E : CompatibleL1IntervalSource a b) (u₀ : EnergyState)

include hDensity hSob h0 hret hab

/-- The actual candidate's weak PDE is now produced: iR forcing is canceled
by the explicit -i normalization. There is no candidate PDE assumption. -/
theorem actualRetardedCandidate_weakEquation
    (hgen : OrdinaryFreeDistributionScalarGenerator) :
    WeakEquation a b
      (fun t => energyDistribution (actualRetardedCandidate hDensity hSob h0 hret hab E u₀ t))
      (fun t => Lp.toTemperedDistribution (E.value t)) := by
  have hf := actualFreeDistribution_weakEquation hgen hab (energyDistribution u₀)
  have hr := (actualPureRetardedDistribution_weakEquation hDensity hSob h0 hret hab E hgen).smul Complex.I
  have h := hf.sub hr
  simpa only [actualRetardedCandidate, map_sub, map_smul, freeEnergyState_distribution,
    actualPureRetardedDistribution, smul_smul, Complex.I_mul_I, neg_one_smul,
    zero_sub, neg_neg] using h

/-- Actual PDE-to-literal-Duhamel bridge on a compact interval. The only new
ordinary analytic premises concern homogeneous linear L2 uniqueness and the exact
free Fourier distribution generator. The retarded PDE is a native output. -/
theorem distributional_energy_literal_formula
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2HomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : WeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (hinit : u a = u₀) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution u₀) φ - Complex.I *
        ∫ s in Set.Ioc a (t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) :=
  literal_formula_of_candidate_weakEquation hDensity hSob h0 hret hab E u₀ hUnique
    u hucont hu (actualRetardedCandidate_weakEquation hDensity hSob h0 hret hab E u₀ hgen)
    hinit t φ

end HartreeF.LinearWeakEquation
