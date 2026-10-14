import HartreePowerCalculus
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace
namespace HartreeF.WeakHartreeChain
open NormedSpace

def rankOne (z : ℂ) : ℂ →L[ℝ] ℂ := (innerSL ℝ z).smulRight z
def unitProjection (z : ℂ) : ℂ →L[ℝ] ℂ := rankOne (NormedSpace.normalize z)

theorem rankOne_norm (z : ℂ) : ‖rankOne z‖ = ‖z‖^2 := by
  rw [rankOne,ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,pow_two]

theorem normalized_norm_le_one (z : ℂ) : ‖NormedSpace.normalize z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (norm_normalize hz).le

theorem unitProjection_norm_le_one (z : ℂ) : ‖unitProjection z‖ ≤ 1 := by
  rw [unitProjection,rankOne_norm]
  nlinarith [normalized_norm_le_one z,norm_nonneg (NormedSpace.normalize z)]

theorem rankOne_difference_bound (z w : ℂ) :
    ‖rankOne z-rankOne w‖ ≤ (‖z‖+‖w‖)*‖z-w‖ := by
  have he : rankOne z-rankOne w =
      (innerSL ℝ (z-w)).smulRight z+(innerSL ℝ w).smulRight (z-w) := by
    ext t
    simp only [rankOne,sub_apply,add_apply,ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply,inner_sub_left]
    module
  rw [he]
  calc
    _ ≤ ‖(innerSL ℝ (z-w)).smulRight z‖+‖(innerSL ℝ w).smulRight (z-w)‖ := norm_add_le _ _
    _ = _ := by rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_smulRight_apply,
      innerSL_apply_norm,innerSL_apply_norm]; ring

theorem unitProjection_difference_bound (z w : ℂ) :
    ‖unitProjection z-unitProjection w‖ ≤ 2*‖NormedSpace.normalize z-NormedSpace.normalize w‖ := by
  exact (rankOne_difference_bound _ _).trans
    (mul_le_mul_of_nonneg_right (by linarith [normalized_norm_le_one z,normalized_norm_le_one w]) (norm_nonneg _))

theorem weighted_normalize_difference_le (z w : ℂ) (hzw : ‖z‖ ≤ ‖w‖) :
    ‖z‖*‖NormedSpace.normalize z-NormedSpace.normalize w‖ ≤ 2*‖z-w‖ := by
  by_cases hw : w = 0
  · have hz : z = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [hw,norm_zero] using hzw) (norm_nonneg z))
    simp [hz,hw]
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he : ‖z‖ • (NormedSpace.normalize z-NormedSpace.normalize w) =
      (z-w)+(1-‖z‖/‖w‖) • w := by
    rw [smul_sub,norm_smul_normalize]
    simp only [NormedSpace.normalize,smul_smul,div_eq_mul_inv]
    module
  have hterm : ‖(1-‖z‖/‖w‖) • w‖ = ‖w‖-‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ((div_le_one hwp).mpr hzw))]
    field_simp
  calc
    _ = ‖‖z‖ • (NormedSpace.normalize z-NormedSpace.normalize w)‖ := by rw [norm_smul,norm_norm]
    _ = ‖(z-w)+(1-‖z‖/‖w‖) • w‖ := by rw [he]
    _ ≤ ‖z-w‖+‖(1-‖z‖/‖w‖) • w‖ := norm_add_le _ _
    _ = ‖z-w‖+(‖w‖-‖z‖) := by rw [hterm]
    _ ≤ _ := by have ht := norm_sub_norm_le w z; rw [norm_sub_rev] at ht; linarith

#print axioms rankOne_norm
#print axioms normalized_norm_le_one
#print axioms unitProjection_norm_le_one
#print axioms rankOne_difference_bound
#print axioms unitProjection_difference_bound
#print axioms weighted_normalize_difference_le
end HartreeF.WeakHartreeChain
