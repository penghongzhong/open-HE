import ComplexRadialRetraction

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace HartreeF.WeakHartreeChain

def retractedMap (F : ℂ → ℝ) (ε : ℝ) : ℂ → ℝ := F ∘ radialRetraction ε

theorem retractedMap_contDiff_one {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    {ε : ℝ} (hε : 0 ≤ ε) : ContDiff ℝ 1 (retractedMap F ε) :=
  hF.comp (radialRetraction_contDiff_one hε)

theorem retractedMap_fderiv {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    fderiv ℝ (retractedMap F ε) z =
      (fderiv ℝ F (radialRetraction ε z)).comp (radialRetractionDerivative ε z) :=
  (((hF.differentiable (by simp)) _).hasFDerivAt.comp z
    (radialRetraction_hasFDerivAt hε z)).fderiv

theorem retractedMap_zero {F : ℂ → ℝ} (hz : F 0 = 0) (ε : ℝ) :
    retractedMap F ε 0 = 0 := by
  simpa only [retractedMap,Function.comp_def,radialRetraction,smul_zero] using hz

theorem retractedMap_norm_bound {F : ℂ → ℝ} {m D ε : ℝ}
    (hm : 0 ≤ m) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hbound : ∀ z, ‖F z‖ ≤ D*‖z‖^m) (z : ℂ) :
    ‖retractedMap F ε z‖ ≤ D*‖z‖^m :=
  (hbound _).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) (norm_radialRetraction_le hε z) hm) hD)

theorem retractedMap_fderiv_bound {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    {q C ε : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C*‖z‖^q) (z : ℂ) :
    ‖fderiv ℝ (retractedMap F ε) z‖ ≤ (3*C)*‖z‖^q := by
  rw [retractedMap_fderiv hF hε]
  calc
    _ ≤ ‖fderiv ℝ F (radialRetraction ε z)‖*‖radialRetractionDerivative ε z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C*‖radialRetraction ε z‖^q)*3 :=
      mul_le_mul (hbound _) (radialRetractionDerivative_bound hε z) (norm_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
    _ ≤ (C*‖z‖^q)*3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (norm_radialRetraction_le hε z) hq) hC) (by norm_num)
    _ = _ := by ring

theorem retractedMap_fderiv_bounded {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    {q C ε : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C*‖z‖^q) (z : ℂ) :
    ‖fderiv ℝ (retractedMap F ε) z‖ ≤ (3*C)*(1+ε⁻¹)^q := by
  rw [retractedMap_fderiv hF hε.le]
  calc
    _ ≤ ‖fderiv ℝ F (radialRetraction ε z)‖*‖radialRetractionDerivative ε z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C*‖radialRetraction ε z‖^q)*3 :=
      mul_le_mul (hbound _) (radialRetractionDerivative_bound hε.le z) (norm_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
    _ ≤ (C*(1+ε⁻¹)^q)*3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (radialRetraction_bounded hε z) hq) hC) (by norm_num)
    _ = _ := by ring

theorem retractedMap_tendsto {F : ℂ → ℝ} (hF : Continuous F) (z : ℂ) :
    Tendsto (fun n => retractedMap F (saturationParameter n) z) atTop (𝓝 (F z)) :=
  (hF.tendsto z).comp (radialRetraction_tendsto z)

theorem retractedMap_fderiv_tendsto {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F) (z : ℂ) :
    Tendsto (fun n => fderiv ℝ (retractedMap F (saturationParameter n)) z) atTop
      (𝓝 (fderiv ℝ F z)) := by
  have hf := ((hF.continuous_fderiv (by simp)).tendsto z).comp (radialRetraction_tendsto z)
  have ht := ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).continuous₂.tendsto
    (fderiv ℝ F z,ContinuousLinearMap.id ℝ ℂ)).comp
      (hf.prodMk_nhds (radialRetractionDerivative_tendsto z))
  simp only [Function.comp_def,ContinuousLinearMap.compL_apply] at ht
  convert! ht using 1
  funext n
  exact retractedMap_fderiv hF (saturationParameter_pos n).le z

#print axioms retractedMap_contDiff_one
#print axioms retractedMap_fderiv
#print axioms retractedMap_zero
#print axioms retractedMap_norm_bound
#print axioms retractedMap_fderiv_bound
#print axioms retractedMap_fderiv_bounded
#print axioms retractedMap_tendsto
#print axioms retractedMap_fderiv_tendsto
end HartreeF.WeakHartreeChain
