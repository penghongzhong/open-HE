import ActualBubbleSobolev
import PhysicalHeatTonelli

/-!
Actual nonnegative Laplace/Gamma representation of Japanese-bracket profiles.
Pointwise time integrability and the full space-times-time L1 domain are proved.
There are no assumed profile identities or unproved exchanges of integrals.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
namespace HartreeF.BubbleProfile
open HeatRiesz

def bracketProfile (s : ℝ) (x : Space) : ℝ := (1+‖x‖^2)^(-s)

def gammaProfile (s : ℝ) (x : Space) (t : ℝ) : ℝ :=
  t^(s-1)*Real.exp (-((1+‖x‖^2)*t))/Real.Gamma s

theorem gammaProfile_time_integrable {s : ℝ} (hs : 0 < s) (x : Space) :
    Integrable (gammaProfile s x) positiveTimeMeasure :=
  (gammaRate_integrable hs (by positivity : 0 < 1+‖x‖^2)).div_const _

theorem gammaProfile_time_integral {s : ℝ} (hs : 0 < s) (x : Space) :
    (∫ t, gammaProfile s x t ∂positiveTimeMeasure) = bracketProfile s x := by
  unfold gammaProfile positiveTimeMeasure
  simp only [div_eq_mul_inv, integral_mul_const]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity : 0 < 1+‖x‖^2)]
  rw [mul_assoc, mul_inv_cancel₀ (Real.Gamma_pos_of_pos hs).ne', mul_one, one_div,
    ← Real.rpow_neg_eq_inv_rpow]
  rfl

theorem gammaProfile_nonneg {s : ℝ} (hs : 0 < s) (x : Space) {t : ℝ} (ht : 0 < t) :
    0 ≤ gammaProfile s x t :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    (Real.Gamma_pos_of_pos hs).le

theorem gammaProfile_factor (s : ℝ) (x : Space) (t : ℝ) :
    gammaProfile s x t = (t^(s-1)*Real.exp (-t)/Real.Gamma s) *
      Real.exp (-t*‖x‖^2) := by
  unfold gammaProfile
  rw [show -((1+‖x‖^2)*t) = -t + (-t*‖x‖^2) by ring, Real.exp_add]
  ring

theorem bracketProfile_integrable {s : ℝ} (hs : 3/2 < s) :
    Integrable (bracketProfile s) volume := by
  have h : Integrable (fun x : Space => (1+‖x‖^2)^(-(2*s)/2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num [Space]; linarith)
  convert h using 1
  funext x
  unfold bracketProfile
  congr 1
  ring

theorem gammaProfile_joint_measurable (s : ℝ) :
    AEStronglyMeasurable (fun p : Space × ℝ => gammaProfile s p.1 p.2)
      (volume.prod positiveTimeMeasure) := by
  apply Measurable.aestronglyMeasurable
  unfold gammaProfile
  fun_prop

/-- Positive profile domain plus the native pointwise Gamma identity supplies
joint absolute integrability before the order of integration is exchanged. -/
theorem gammaProfile_joint_integrable {s : ℝ} (hs : 3/2 < s) :
    Integrable (fun p : Space × ℝ => gammaProfile s p.1 p.2)
      (volume.prod positiveTimeMeasure) := by
  have hs0 : 0 < s := by linarith
  apply (integrable_prod_iff (gammaProfile_joint_measurable s)).mpr
  refine ⟨Eventually.of_forall (gammaProfile_time_integrable hs0), ?_⟩
  apply (bracketProfile_integrable hs).congr
  filter_upwards [] with x
  rw [← gammaProfile_time_integral hs0 x]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (Real.norm_of_nonneg (gammaProfile_nonneg hs0 x ht)).symm

#print axioms gammaProfile_time_integrable
#print axioms gammaProfile_time_integral
#print axioms gammaProfile_nonneg
#print axioms gammaProfile_factor
#print axioms bracketProfile_integrable
#print axioms gammaProfile_joint_measurable
#print axioms gammaProfile_joint_integrable
end HartreeF.BubbleProfile
