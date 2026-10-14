import SaturatedDensityWeakGradient

/-! A genuine C1 bounded radial retraction, with a uniform derivative bound.
This is an amplitude approximation mechanism for unbounded C1 compositions. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology RealInnerProductSpace
namespace HartreeF.WeakHartreeChain

def radialWeight (ε : ℝ) (z : ℂ) : ℝ := (1+ε*density 2 z)⁻¹
def radialRetraction (ε : ℝ) (z : ℂ) : ℂ := radialWeight ε z • z
def radialRetractionDerivative (ε : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  radialWeight ε z • ContinuousLinearMap.id ℝ ℂ +
    (-(ε*saturationCoeff 2 ε z) • densityDerivative 2 z).smulRight z

theorem radialWeight_nonneg {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) : 0 ≤ radialWeight ε z :=
  inv_nonneg.mpr (saturation_denominator_pos hε 2 z).le

theorem radialWeight_le_one {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) : radialWeight ε z ≤ 1 := by
  apply (inv_le_one₀ (saturation_denominator_pos hε 2 z)).mpr
  have := mul_nonneg hε (density_nonneg 2 z)
  linarith

theorem radialWeight_hasFDerivAt {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    HasFDerivAt (radialWeight ε) (-(ε*saturationCoeff 2 ε z) • densityDerivative 2 z) z := by
  have hd := ((density_hasFDerivAt (by norm_num : (1 : ℝ)<2) z).const_mul ε).const_add 1
  have hh := (hasDerivAt_inv (saturation_denominator_pos hε 2 z).ne').comp_hasFDerivAt z hd
  convert! hh using 1
  ext w
  simp only [saturationCoeff,smul_apply,smul_eq_mul]
  ring

theorem radialRetraction_hasFDerivAt {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    HasFDerivAt (radialRetraction ε) (radialRetractionDerivative ε z) z :=
  (radialWeight_hasFDerivAt hε z).smul (hasFDerivAt_id z)

theorem radialRetraction_contDiff_one {ε : ℝ} (hε : 0 ≤ ε) :
    ContDiff ℝ 1 (radialRetraction ε) := by
  have hw : ContDiff ℝ 1 (radialWeight ε) :=
    (contDiff_const.add (contDiff_const.mul (density_contDiff_one (by norm_num : (1 : ℝ)<2)))).inv
      (fun z => (saturation_denominator_pos hε 2 z).ne')
  exact hw.smul contDiff_id

theorem norm_radialRetraction_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖radialRetraction ε z‖ ≤ ‖z‖ := by
  rw [radialRetraction,norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialWeight_nonneg hε z)]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialWeight_le_one hε z)

theorem radialRetraction_bounded {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ‖radialRetraction ε z‖ ≤ 1+ε⁻¹ := by
  have hd := saturation_denominator_pos hε.le 2 z
  have hεb := mul_nonneg hε.le (density_nonneg 2 z)
  have hbig : density 2 z ≤ ε⁻¹*(1+ε*density 2 z) :=
    (le_inv_mul_iff₀ hε).mpr (by linarith)
  have hr : ‖z‖ ≤ 1+density 2 z := by
    simp only [density,Real.rpow_two]
    nlinarith [sq_nonneg (‖z‖-1)]
  rw [radialRetraction,norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialWeight_nonneg hε.le z)]
  change (1+ε*density 2 z)⁻¹*‖z‖ ≤ _
  apply (inv_mul_le_iff₀ hd).mpr
  nlinarith

theorem radialRetractionDerivative_bound {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖radialRetractionDerivative ε z‖ ≤ 3 := by
  have hd := saturation_denominator_pos hε 2 z
  have hc := saturationCoeff_nonneg (ε := ε) 2 z
  have hεb := mul_nonneg hε (density_nonneg 2 z)
  have hterm : ε*saturationCoeff 2 ε z*density 2 z ≤ 1 := by
    unfold saturationCoeff
    rw [mul_comm ε _,mul_assoc]
    exact (inv_mul_le_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith)
  calc
    _ ≤ ‖radialWeight ε z • ContinuousLinearMap.id ℝ ℂ‖ +
        ‖(-(ε*saturationCoeff 2 ε z) • densityDerivative 2 z).smulRight z‖ := norm_add_le _ _
    _ = radialWeight ε z+2*(ε*saturationCoeff 2 ε z*density 2 z) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialWeight_nonneg hε z),
        ContinuousLinearMap.norm_id,mul_one,ContinuousLinearMap.norm_smulRight_apply,
        norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (mul_nonneg hε hc),
        densityDerivative_norm (by norm_num : (1 : ℝ)<2)]
      norm_num [density,Real.rpow_two]
      ring
    _ ≤ 3 := by linarith [radialWeight_le_one hε z]

theorem radialWeight_tendsto (z : ℂ) :
    Tendsto (fun n => radialWeight (saturationParameter n) z) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add (saturationParameter_tendsto.mul_const (density 2 z))
  convert ht.inv₀ (by norm_num : (1 : ℝ)+0*density 2 z ≠ 0) using 1 <;> simp [radialWeight]

theorem radialRetraction_tendsto (z : ℂ) :
    Tendsto (fun n => radialRetraction (saturationParameter n) z) atTop (𝓝 z) := by
  convert! (radialWeight_tendsto z).smul (tendsto_const_nhds (x := z)) using 1
  simp

theorem radialRetractionDerivative_tendsto (z : ℂ) :
    Tendsto (fun n => radialRetractionDerivative (saturationParameter n) z) atTop
      (𝓝 (ContinuousLinearMap.id ℝ ℂ)) := by
  have ht := ((saturationParameter_tendsto.mul (saturationCoeff_tendsto 2 z)).neg).smul
    (tendsto_const_nhds (x := densityDerivative 2 z))
  simp only [zero_mul,neg_zero,zero_smul] at ht
  have hs := ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).flip z).continuous.tendsto 0 |>.comp ht
  have ha := ((radialWeight_tendsto z).smul (tendsto_const_nhds (x := ContinuousLinearMap.id ℝ ℂ))).add
    hs
  convert! ha using 1
  simp

#print axioms radialWeight_nonneg
#print axioms radialWeight_le_one
#print axioms radialWeight_hasFDerivAt
#print axioms radialRetraction_hasFDerivAt
#print axioms radialRetraction_contDiff_one
#print axioms norm_radialRetraction_le
#print axioms radialRetraction_bounded
#print axioms radialRetractionDerivative_bound
#print axioms radialWeight_tendsto
#print axioms radialRetraction_tendsto
#print axioms radialRetractionDerivative_tendsto
end HartreeF.WeakHartreeChain
