import WeightedProjectionDifference

noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace
namespace HartreeF.WeakHartreeChain

theorem localFactorDerivative_eq_weightedProjection {q : ℝ} (hq : 1 < q) (z : ℂ) :
    localFactorDerivative q z = ‖z‖^q • ContinuousLinearMap.id ℝ ℂ+q • weightedProjection q z := by
  by_cases hz : z = 0
  · subst z
    ext w
    simp [localFactorDerivative_zero (by linarith : 0 < q),weightedProjection,unitProjection,
      rankOne,Real.zero_rpow (show q ≠ 0 by linarith)]
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpow : ‖z‖^(q-2) = ‖z‖^q*(‖z‖⁻¹*‖z‖⁻¹) := by
    rw [Real.rpow_sub hzp,Real.rpow_two,div_eq_mul_inv,pow_two,mul_inv_rev]
  ext w
  simp only [localFactorDerivative,weightedProjection,unitProjection,rankOne,NormedSpace.normalize,
    densityDerivative,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,real_inner_smul_left,smul_smul,
    smul_eq_mul,hpow]
  module

theorem localFactorDerivative_difference_bound {q : ℝ} (hq : 1 < q) (z w : ℂ) :
    ‖localFactorDerivative q z-localFactorDerivative q w‖ ≤
      (q*(q+5))*(‖z‖+‖w‖)^(q-1)*‖z-w‖ := by
  have hq0 : 0 < q := by linarith
  have he : localFactorDerivative q z-localFactorDerivative q w =
      (‖z‖^q-‖w‖^q) • ContinuousLinearMap.id ℝ ℂ+
        q • (weightedProjection q z-weightedProjection q w) := by
    rw [localFactorDerivative_eq_weightedProjection hq,localFactorDerivative_eq_weightedProjection hq]
    module
  have hfirst : ‖(‖z‖^q-‖w‖^q) • ContinuousLinearMap.id ℝ ℂ‖ ≤
      q*(‖z‖+‖w‖)^(q-1)*‖z-w‖ := by
    rw [norm_smul,ContinuousLinearMap.norm_id,mul_one]
    exact density_difference_bound hq z w
  have hsecond : ‖q • (weightedProjection q z-weightedProjection q w)‖ ≤
      q*((q+4)*(‖z‖+‖w‖)^(q-1)*‖z-w‖) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq0]
    exact mul_le_mul_of_nonneg_left (weightedProjection_difference_bound hq z w) hq0.le
  rw [he]
  have ht := norm_add_le ((‖z‖^q-‖w‖^q) • ContinuousLinearMap.id ℝ ℂ)
    (q • (weightedProjection q z-weightedProjection q w))
  nlinarith

#print axioms localFactorDerivative_eq_weightedProjection
#print axioms localFactorDerivative_difference_bound
end HartreeF.WeakHartreeChain
