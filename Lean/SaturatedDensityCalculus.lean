import HartreePowerCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace
namespace HartreeF.WeakHartreeChain

def saturatedDensity (p ε : ℝ) (z : ℂ) : ℝ := density p z / (1+ε*density p z)
def saturationCoeff (p ε : ℝ) (z : ℂ) : ℝ := ((1+ε*density p z)^2)⁻¹

theorem density_nonneg (p : ℝ) (z : ℂ) : 0 ≤ density p z :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem saturation_denominator_pos {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ) (z : ℂ) :
    0 < 1+ε*density p z := by
  have := mul_nonneg hε (density_nonneg p z)
  linarith

theorem saturatedDensity_hasFDerivAt {p ε : ℝ} (hp : 1 < p) (hε : 0 ≤ ε) (z : ℂ) :
    HasFDerivAt (saturatedDensity p ε) (saturationCoeff p ε z • densityDerivative p z) z := by
  have hb := density_hasFDerivAt hp z
  have hs := (hasDerivAt_id (density p z)).div
    (((hasDerivAt_id (density p z)).const_mul ε).const_add 1)
    (saturation_denominator_pos hε p z).ne'
  have hd := hs.comp_hasFDerivAt z hb
  have he : (1*(1+ε*density p z)-density p z*(ε*1))/(1+ε*density p z)^2 =
      saturationCoeff p ε z := by
    unfold saturationCoeff
    ring
  simp only [id_eq,he] at hd
  convert! hd using 1

theorem saturatedDensity_contDiff_one {p ε : ℝ} (hp : 1 < p) (hε : 0 ≤ ε) :
    ContDiff ℝ 1 (saturatedDensity p ε) :=
  (density_contDiff_one hp).div (contDiff_const.add (contDiff_const.mul (density_contDiff_one hp)))
    (fun z => (saturation_denominator_pos hε p z).ne')

theorem saturationCoeff_nonneg {ε : ℝ} (p : ℝ) (z : ℂ) :
    0 ≤ saturationCoeff p ε z := by
  unfold saturationCoeff
  positivity

theorem saturationCoeff_le_one {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ) (z : ℂ) :
    saturationCoeff p ε z ≤ 1 := by
  have hb := mul_nonneg hε (density_nonneg p z)
  apply (inv_le_one₀ (sq_pos_of_pos (saturation_denominator_pos hε p z))).mpr
  nlinarith

theorem saturatedDensity_nonneg {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ) (z : ℂ) :
    0 ≤ saturatedDensity p ε z :=
  div_nonneg (density_nonneg p z) (saturation_denominator_pos hε p z).le

theorem saturatedDensity_le_density {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ) (z : ℂ) :
    saturatedDensity p ε z ≤ density p z := by
  apply div_le_self (density_nonneg p z)
  have := mul_nonneg hε (density_nonneg p z)
  linarith

theorem rpow_sub_one_le_one_add {p r : ℝ} (hp : 1 < p) (hr : 0 ≤ r) :
    r^(p-1) ≤ 1+r^p := by
  by_cases h : r ≤ 1
  · have h1 : r^(p-1) ≤ 1 := by
      simpa using Real.rpow_le_rpow hr h (by linarith : 0 ≤ p-1)
    exact h1.trans (le_add_of_nonneg_right (Real.rpow_nonneg hr p))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith : p-1 ≤ p)).trans
      (le_add_of_nonneg_left (by norm_num))

theorem saturatedDensity_derivative_bound {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) (z : ℂ) :
    ‖saturationCoeff p ε z • densityDerivative p z‖ ≤ p*(1+ε⁻¹) := by
  have hden := saturation_denominator_pos hε.le p z
  have hb := density_nonneg p z
  have hεb := mul_nonneg hε.le hb
  have hsq : 1 ≤ (1+ε*density p z)^2 := by nlinarith
  have hbig : ε*density p z ≤ (1+ε*density p z)^2 := by nlinarith
  have hdiv : density p z ≤ ε⁻¹*((1+ε*density p z)^2) :=
    (le_inv_mul_iff₀ hε).mpr hbig
  have hbnd : ‖z‖^(p-1) ≤ (1+ε⁻¹)*(1+ε*density p z)^2 := by
    have h := rpow_sub_one_le_one_add hp (norm_nonneg z)
    change ‖z‖^(p-1) ≤ 1+density p z at h
    nlinarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (saturationCoeff_nonneg p z),
    densityDerivative_norm hp]
  unfold saturationCoeff
  have hh := mul_le_mul_of_nonneg_left hbnd (show 0 ≤ p by linarith)
  have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (sq_nonneg (1+ε*density p z)))
  convert ht using 1
  field_simp

#print axioms saturatedDensity_hasFDerivAt
#print axioms saturatedDensity_contDiff_one
#print axioms saturationCoeff_nonneg
#print axioms saturationCoeff_le_one
#print axioms saturatedDensity_nonneg
#print axioms saturatedDensity_le_density
#print axioms rpow_sub_one_le_one_add
#print axioms saturatedDensity_derivative_bound
end HartreeF.WeakHartreeChain
