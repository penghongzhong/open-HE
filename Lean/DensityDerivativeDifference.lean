import HartreePowerCalculus

noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace
namespace HartreeF.WeakHartreeChain

theorem densityDerivative_eq_inner_localFactor (p : ℝ) (z : ℂ) :
    densityDerivative p z = p • innerSL ℝ (localFactor (p-2) z) := by
  ext w
  simp only [densityDerivative, localFactor, smul_apply, innerSL_apply_apply,
    real_inner_smul_left, smul_eq_mul]
  ring

theorem densityDerivative_difference_bound {p : ℝ} (hp : 3 < p) (z w : ℂ) :
    ‖densityDerivative p z-densityDerivative p w‖ ≤
      p*(p-1)*(‖z‖+‖w‖)^(p-2)*‖z-w‖ := by
  have he : densityDerivative p z-densityDerivative p w =
      p • innerSL ℝ (localFactor (p-2) z-localFactor (p-2) w) := by
    ext t
    simp only [densityDerivative_eq_inner_localFactor,sub_apply,smul_apply,
      innerSL_apply_apply,inner_sub_left,smul_eq_mul]
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < p),innerSL_apply_norm]
  convert mul_le_mul_of_nonneg_left
    (localFactor_difference_bound (by linarith : 1 < p-2) z w) (by linarith : 0 ≤ p) using 1
  ring

#print axioms densityDerivative_eq_inner_localFactor
#print axioms densityDerivative_difference_bound
end HartreeF.WeakHartreeChain
