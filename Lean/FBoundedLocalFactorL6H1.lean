import HartreeLocalFactorWeakEndpoint

/-! STATIC-ONLY, UNCOMPILED CANDIDATE.
Bounded actual values upgrade the existing local-factor weak chain rule to
exactly L6 for the value and L2 for its same canonical weak gradient.
No original function L2 assumption, HLS premise, or product-gradient premise.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.ActualUpperProduct
open SobolevStretch StationarySelfTest WeakHartreeChain

/-- Bounded u in L6 gives the literal projected local factor in L6. -/
theorem projectedLocalFactor_memLp_six_bounded {q M : ℝ} (hq : 1 < q)
    (hM : 0 ≤ M) (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    {u : Space → ℂ} (hu : MemLp u 6 volume)
    (hb : ∀ᵐ x ∂volume, ‖u x‖ ≤ M) :
    MemLp (fun x => projectedLocalFactor q A (u x)) 6 volume := by
  have hMq : 0 ≤ M ^ q := Real.rpow_nonneg hM q
  apply ((hu.norm).const_mul (M ^ q)).of_le
    ((projectedLocalFactor_contDiff_one hq A).continuous.comp_aestronglyMeasurable
      hu.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  calc
    ‖projectedLocalFactor q A (u x)‖ ≤ 1 * ‖u x‖ ^ (q + 1) :=
      projectedLocalFactor_norm_bound hq A hA (u x)
    _ = ‖u x‖ ^ q * ‖u x‖ := by
      rw [one_mul, Real.rpow_add_one' (norm_nonneg _) (by linarith : q + 1 ≠ 0)]
    _ ≤ M ^ q * ‖u x‖ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) hx (by linarith)) (norm_nonneg _)
    _ = ‖M ^ q * ‖u x‖‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hMq (norm_nonneg _))]

/-- The same projected derivative has an L2 domain, via its bounded differential. -/
theorem projectedLocalFactorGradient_memLp_two_bounded {q M : ℝ} (hq : 1 < q)
    (hM : 0 ≤ M) (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space}
    (hu : AEStronglyMeasurable u volume)
    (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    (hb : ∀ᵐ x ∂volume, ‖u x‖ ≤ M) :
    MemLp (projectedLocalFactorGradient q A u U V) 2 volume := by
  have hMq : 0 ≤ M ^ q := Real.rpow_nonneg hM q
  have hq1 : 0 ≤ q + 1 := by linarith
  have hm : MemLp (complexChainGradient (projectedLocalFactor q A) u U V) 2 volume := by
    apply ((hU.norm.add hV.norm).const_mul ((q + 1) * M ^ q)).of_le
      (complexChainGradient_aestronglyMeasurable
        (projectedLocalFactor_contDiff_one hq A) hu
        hU.aestronglyMeasurable hV.aestronglyMeasurable)
    filter_upwards [hb] with x hx
    calc
      ‖complexChainGradient (projectedLocalFactor q A) u U V x‖ ≤
          (q + 1) * powerGradientMajorant q u U V x :=
        complexChainGradient_bound (projectedLocalFactor_fderiv_bound hq A hA) u U V x
      _ = (q + 1) * ‖u x‖ ^ q * (‖U x‖ + ‖V x‖) := by
        unfold powerGradientMajorant
        ring
      _ ≤ (q + 1) * M ^ q * (‖U x‖ + ‖V x‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hx (by linarith)) hq1)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖(q + 1) * M ^ q * (‖U x‖ + ‖V x‖)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (mul_nonneg hq1 hMq) (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
  convert hm using 1
  funext x
  simp only [projectedLocalFactorGradient, complexChainGradient,
    projectedLocalFactor_fderiv hq, ContinuousLinearMap.comp_apply]

/-- Actual local-factor weak gradient plus the asymmetric-Leibniz input domains.
The L10/L30/13 inputs are consumed only by the already proved weak chain rule;
they will be produced for the same lowEnergyState in the concrete consumer. -/
theorem bounded_projectedLocalFactor_weak_domains (hDensity : OrdinaryH1Density)
    {q M : ℝ} (hq : 1 < q) (hq4 : q < 4) (hM : 0 ≤ M)
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hb : ∀ᵐ x ∂volume, ‖u x‖ ≤ M) :
    HasWeakGradient (fun x => projectedLocalFactor q A (u x))
      (projectedLocalFactorGradient q A u U V) ∧
    MemLp (fun x => projectedLocalFactor q A (u x)) 6 volume ∧
    MemLp (projectedLocalFactorGradient q A u U V) 2 volume :=
  ⟨projectedLocalFactor_hasWeakGradient hDensity hq hq4 A hA hu hu10 hU hV,
    projectedLocalFactor_memLp_six_bounded hq hM A hA hu.function_L6 hb,
    projectedLocalFactorGradient_memLp_two_bounded hq hM A hA
      hu.function_L6.aestronglyMeasurable hu.real_gradient_L2 hu.imag_gradient_L2 hb⟩

#print axioms projectedLocalFactor_memLp_six_bounded
#print axioms projectedLocalFactorGradient_memLp_two_bounded
#print axioms bounded_projectedLocalFactor_weak_domains
end HartreeF.ActualUpperProduct
