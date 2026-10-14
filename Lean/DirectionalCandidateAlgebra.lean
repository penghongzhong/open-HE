import DerivativeActionDifference
noncomputable section
set_option autoImplicit false
namespace HartreeF.DerivativeMajorization
open WeakHartreeChain

theorem smul_difference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (x y : E) :
    ‖a • x-b • y‖ ≤ ‖a‖*‖x-y‖+‖a-b‖*‖y‖ := by
  have he : a • x-b • y=a • (x-y)+(a-b) • y := by module
  rw [he]
  simpa only [norm_smul] using norm_add_le (a • (x-y)) ((a-b) • y)

theorem smul_difference_bound_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (x y : E) :
    ‖a • x-b • y‖ ≤ ‖a-b‖*‖x‖+‖b‖*‖x-y‖ := by
  have he : a • x-b • y=(a-b) • x+b • (x-y) := by module
  rw [he]
  simpa only [norm_smul] using norm_add_le ((a-b) • x) (b • (x-y))

theorem directional_candidate_algebra {α : ℝ} (ha : 0<α) (z w h k : ℂ)
    (A B D E P P2 P4 P5 P6 : ℝ)
    (hA : ‖A‖ ≤ P) (hAB : ‖A-B‖ ≤ (3+α)*P2)
    (hE : ‖E‖ ≤ (3+α)*P6)
    (hDE : ‖D-E‖ ≤ (3+α)*P4+((3+α)*(2+α))*P5) :
    ‖(D • localFactor (1+α) z+A • localFactorDerivative (1+α) z h)-
      (E • localFactor (1+α) w+B • localFactorDerivative (1+α) w k)‖ ≤
      ((3+α)*P4+((3+α)*(2+α))*P5)*(‖z‖+‖w‖)^(2+α)+
      ((3+α)*P6)*((2+α)*(‖z‖+‖w‖)^(1+α)*‖z-w‖)+
      P*((2+α)*(‖z‖+‖w‖)^(1+α)*‖h-k‖+
        ((1+α)*(6+α))*(‖z‖+‖w‖)^α*‖z-w‖*‖k‖)+
      ((3+α)*P2)*((2+α)*(‖z‖+‖w‖)^(1+α)*‖k‖) := by
  have hq : 1<1+α := by linarith
  have haz : ‖localFactor (1+α) z‖ ≤ (‖z‖+‖w‖)^(2+α) := by
    simpa only [show 1+α+1=2+α by ring] using localFactor_bound_sum hq z w
  have had : ‖localFactor (1+α) z-localFactor (1+α) w‖ ≤
      (2+α)*(‖z‖+‖w‖)^(1+α)*‖z-w‖ := by
    simpa only [show 1+α+1=2+α by ring] using localFactor_difference_bound hq z w
  have hdk : ‖localFactorDerivative (1+α) w k‖ ≤ (2+α)*(‖z‖+‖w‖)^(1+α)*‖k‖ := by
    simpa only [show 1+α+1=2+α by ring] using localFactorDerivative_action_bound_right hq z w k
  have hdd : ‖localFactorDerivative (1+α) z h-localFactorDerivative (1+α) w k‖ ≤
      (2+α)*(‖z‖+‖w‖)^(1+α)*‖h-k‖+
      ((1+α)*(6+α))*(‖z‖+‖w‖)^α*‖z-w‖*‖k‖ := by
    simpa only [show 1+α+1=2+α by ring,show 1+α+5=6+α by ring,
      show 1+α-1=α by ring] using localFactorDerivative_action_difference hq z w h k
  have ht1 := smul_difference_bound_right D E (localFactor (1+α) z) (localFactor (1+α) w)
  have ht2 := smul_difference_bound A B (localFactorDerivative (1+α) z h) (localFactorDerivative (1+α) w k)
  have hb1 := ht1.trans (add_le_add
    (mul_le_mul hDE haz (norm_nonneg _) ((norm_nonneg _).trans hDE))
    (mul_le_mul hE had (norm_nonneg _) ((norm_nonneg _).trans hE)))
  have hb2 := ht2.trans (add_le_add
    (mul_le_mul hA hdd (norm_nonneg _) ((norm_nonneg _).trans hA))
    (mul_le_mul hAB hdk (norm_nonneg _) ((norm_nonneg _).trans hAB)))
  have he : (D • localFactor (1+α) z+A • localFactorDerivative (1+α) z h)-
      (E • localFactor (1+α) w+B • localFactorDerivative (1+α) w k)=
      (D • localFactor (1+α) z-E • localFactor (1+α) w)+
      (A • localFactorDerivative (1+α) z h-B • localFactorDerivative (1+α) w k) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hb1 hb2).trans_eq (by ring))

#print axioms smul_difference_bound
#print axioms smul_difference_bound_right
#print axioms directional_candidate_algebra
end HartreeF.DerivativeMajorization
