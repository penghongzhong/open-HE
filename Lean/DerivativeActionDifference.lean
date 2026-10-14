import LocalFactorDerivativeDifference
import DensityDerivativeDifference
import ProjectedLocalFactorCalculus

/-! Pointwise directional derivative algebra for the actual real derivatives.
These estimates do not assume or assert that a convolution has a weak derivative. -/
noncomputable section
set_option autoImplicit false
namespace HartreeF.DerivativeMajorization
open WeakHartreeChain

theorem clm_apply_difference_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L M : E →L[ℝ] F) (h k : E) :
    ‖L h-M k‖ ≤ ‖L‖*‖h-k‖+‖L-M‖*‖k‖ := by
  have he : L h-M k = L (h-k)+(L-M) k := by simp [map_sub]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (L.le_opNorm _) ((L-M).le_opNorm _))

theorem densityDerivative_action_difference {p : ℝ} (hp : 3<p) (z w h k : ℂ) :
    ‖densityDerivative p z h-densityDerivative p w k‖ ≤
      p*(‖z‖+‖w‖)^(p-1)*‖h-k‖+
      p*(p-1)*(‖z‖+‖w‖)^(p-2)*‖z-w‖*‖k‖ := by
  have hn : ‖densityDerivative p z‖ ≤ p*(‖z‖+‖w‖)^(p-1) := by
    rw [densityDerivative_norm (by linarith)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      (le_add_of_nonneg_right (norm_nonneg w)) (by linarith)) (by linarith)
  exact (clm_apply_difference_bound _ _ h k).trans (add_le_add
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (densityDerivative_difference_bound hp z w) (norm_nonneg _)))

theorem localFactorDerivative_action_difference {q : ℝ} (hq : 1<q) (z w h k : ℂ) :
    ‖localFactorDerivative q z h-localFactorDerivative q w k‖ ≤
      (q+1)*(‖z‖+‖w‖)^q*‖h-k‖+
      (q*(q+5))*(‖z‖+‖w‖)^(q-1)*‖z-w‖*‖k‖ := by
  have hn : ‖localFactorDerivative q z‖ ≤ (q+1)*(‖z‖+‖w‖)^q :=
    (localFactorDerivative_bound hq z).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg w)) (by linarith))
      (by linarith))
  exact (clm_apply_difference_bound _ _ h k).trans (add_le_add
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (localFactorDerivative_difference_bound hq z w) (norm_nonneg _)))

theorem densityDerivative_action_bound_right {p : ℝ} (hp : 1<p) (z w k : ℂ) :
    ‖densityDerivative p w k‖ ≤ p*(‖z‖+‖w‖)^(p-1)*‖k‖ := by
  apply ((densityDerivative p w).le_opNorm k).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [densityDerivative_norm hp]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
    (le_add_of_nonneg_left (norm_nonneg z)) (by linarith)) (by linarith)

theorem localFactorDerivative_action_bound_right {q : ℝ} (hq : 1<q) (z w k : ℂ) :
    ‖localFactorDerivative q w k‖ ≤ (q+1)*(‖z‖+‖w‖)^q*‖k‖ := by
  apply ((localFactorDerivative q w).le_opNorm k).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (localFactorDerivative_bound hq w).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg z)) (by linarith))
    (by linarith))

theorem localFactor_bound_sum {q : ℝ} (hq : 1<q) (z w : ℂ) :
    ‖localFactor q z‖ ≤ (‖z‖+‖w‖)^(q+1) := by
  rw [localFactor_norm (by linarith)]
  exact Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg w)) (by linarith)

#print axioms clm_apply_difference_bound
#print axioms densityDerivative_action_difference
#print axioms localFactorDerivative_action_difference
#print axioms densityDerivative_action_bound_right
#print axioms localFactorDerivative_action_bound_right
#print axioms localFactor_bound_sum
end HartreeF.DerivativeMajorization
