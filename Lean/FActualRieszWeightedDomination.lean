import FSameStateWeightedRieszProduct
import FRieszGradientConvolutionDomain
import FMixedRemainderLpCore

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.WeightedRieszProduct
open EnergySpace SobolevStretch StationarySelfTest ForcingDomain RieszWeakDerivative
  RieszKernelDerivative RieszConvolutionDerivative GradientMajorants MixedRemainderLp
  BoundedHartreeGradient

/-- Pointwise norm domination for the same literal real potential. -/
theorem actual_potential_norm_le {α c : ℝ} (hc : 0 < c) (h : V → ℝ) (x : V) :
    ‖rieszConvolution α c h x‖ ≤ c * ∫ y, ‖x-y‖ ^ (α-3) * ‖h y‖ := by
  calc
    _ ≤ ∫ y, ‖rieszKernel α c (x-y) * h y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, c * (‖x-y‖ ^ (α-3) * ‖h y‖) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_mul]
      simp only [rieszKernel, Real.norm_eq_abs, abs_mul, abs_of_pos hc,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      ring
    _ = _ := integral_const_mul _ _

/-- The exact c*(3-alpha) coefficient belongs to the original vector gradient kernel. -/
theorem actual_potentialGradient_norm_le {α c : ℝ}
    (hα3 : α < 3) (hc : 0 < c) (h : V → ℝ) (x : V) :
    ‖gradientConvolution α c h x‖ ≤
      (c * (3-α)) * ∫ y, ‖x-y‖ ^ (α-4) * ‖h y‖ := by
  calc
    _ ≤ ∫ y, ‖h y • rieszKernelGradient α c (x-y)‖ := norm_integral_le_integral_norm _
    _ = ∫ y, (c * (3-α)) * (‖x-y‖ ^ (α-4) * ‖h y‖) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_smul, rieszKernelGradient_norm hα3 hc]
      ring
    _ = _ := integral_const_mul _ _

/-- Actual gradient convolution times the original state's value power is L1. -/
theorem actual_potentialGradient_weighted_L1 (hDensity : OrdinaryH1Density)
    {K α c A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hc : 0 < c) (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) :
    MemLp (fun x => ‖gradientConvolution α c h x‖ * ‖energyValue u x‖ ^ (α+2)) 1 volume ∧
      actualNorm 1 (fun x => ‖gradientConvolution α c h x‖ * ‖energyValue u x‖ ^ (α+2)) ≤
        (c*(3-α)) * ((A^(4-α) * derivativeConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖) := by
  have hmajor := spatialBound_const_mul
    (derivativeProduct_domain_bound hDensity hSob hα2 hα3 hA0 u hA hh).2.2
    (mul_nonneg hc.le (by linarith : 0 ≤ 3-α))
  have hmeas : AEStronglyMeasurable
      (fun x => ‖gradientConvolution α c h x‖ * ‖energyValue u x‖ ^ (α+2)) volume := by
    have hg : AEStronglyMeasurable (gradientConvolution α c h) volume :=
      hh.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        (rieszKernelGradient_measurable α c).aestronglyMeasurable
    exact hg.norm.mul (value_power_aestronglyMeasurable u (α+2))
  have hd := domain_bound_of_spatialBound hmajor hmeas (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (norm_nonneg _) _)), derivativeProductMajorant_eq]
    calc
      _ ≤ ((c*(3-α)) * ∫ y, ‖x-y‖^(α-4)*‖h y‖) * ‖energyValue u x‖^(α+2) :=
        mul_le_mul_of_nonneg_right (actual_potentialGradient_norm_le hα3 hc h x)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by ring)
  simpa only [one_div_one, ENNReal.ofReal_one] using hd

/-- Actual potential times the original coordinate-gradient factor is L1. -/
theorem actual_potential_weighted_coordinate_L1 (hDensity : OrdinaryH1Density)
    {K α c A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hc : 0 < c) (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) (j : Fin 3) :
    MemLp (fun x => ‖rieszConvolution α c h x‖ * ‖energyValue u x‖ ^ (α+1) *
      ‖energyGradient j u x‖) 1 volume ∧
      actualNorm 1 (fun x => ‖rieszConvolution α c h x‖ * ‖energyValue u x‖ ^ (α+1) *
        ‖energyGradient j u x‖) ≤
      c * ((A^(4-α) * localGradientConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖) := by
  have hmajor := spatialBound_const_mul
    (localGradientProduct_domain_bound hDensity hSob hα2 hα3 hA0 u hA hh j).2.2 hc.le
  have hmeas : AEStronglyMeasurable
      (fun x => ‖rieszConvolution α c h x‖ * ‖energyValue u x‖ ^ (α+1) *
        ‖energyGradient j u x‖) volume := by
    have hp : AEStronglyMeasurable (rieszKernel α c) volume :=
      (rieszKernel_measurable α c).aestronglyMeasurable
    have ha : AEStronglyMeasurable (fun x => ∫ y, h y * rieszKernel α c (x-y)) volume :=
      hh.aestronglyMeasurable.convolution (ContinuousLinearMap.mul ℝ ℝ) hp
    have he : (fun x => ∫ y, h y * rieszKernel α c (x-y)) = rieszConvolution α c h := by
      funext x
      unfold rieszConvolution
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    rw [he] at ha
    exact (ha.norm.mul (value_power_aestronglyMeasurable u (α+1))).mul
      (Lp.aestronglyMeasurable (energyGradient j u)).norm
  have hd := domain_bound_of_spatialBound hmajor hmeas (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)), localGradientProductMajorant_eq]
    calc
      _ ≤ (c * ∫ y, ‖x-y‖^(α-3)*‖h y‖) * ‖energyValue u x‖^(α+1) *
          ‖energyGradient j u x‖ := by
        gcongr
        exact actual_potential_norm_le hc h x
      _ = _ := by ring)
  simpa only [one_div_one, ENNReal.ofReal_one] using hd

end HartreeF.WeightedRieszProduct
