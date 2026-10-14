import ExactBubbleIntegrals

/-!
Actual direct Gaussian-rate representation of the standard Riesz kernel.
The rate integral is asserted only at nonzero separation. For a fixed centre,
the excluded singleton is proved null before any spatial integral is used.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
namespace HartreeF.BubbleProfile
open HeatRiesz

def rieszWeightDenom (α : ℝ) : ℝ :=
  (2:ℝ)^α * Real.pi^(3/2:ℝ) * Real.Gamma (α/2)

def rieszLaplace (α : ℝ) (z : Space) (r : ℝ) : ℝ :=
  r^((3-α)/2-1)*Real.exp (-(‖z‖^2*r))/rieszWeightDenom α

theorem rieszWeightDenom_pos {α : ℝ} (hα : 0<α) : 0<rieszWeightDenom α := by
  have hg := Real.Gamma_pos_of_pos (show 0<α/2 by linarith)
  unfold rieszWeightDenom
  positivity

theorem rieszLaplace_integrable_nonzero {α : ℝ} (hα3 : α<3) {z : Space} (hz : z≠0) :
    Integrable (rieszLaplace α z) positiveTimeMeasure :=
  (gammaRate_integrable (show 0<(3-α)/2 by linarith)
    (sq_pos_of_pos (norm_pos_iff.mpr hz))).div_const _

theorem rieszLaplace_integral_nonzero {α : ℝ} (hα3 : α<3) {z : Space} (hz : z≠0) :
    (∫ r, rieszLaplace α z r ∂positiveTimeMeasure) =
      rieszKernel α (standardRieszConstant α) z := by
  unfold rieszLaplace positiveTimeMeasure
  simp only [div_eq_mul_inv, integral_mul_const]
  rw [← div_eq_mul_inv (3-α) (2:ℝ)]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0<(3-α)/2 by linarith)
    (sq_pos_of_pos (norm_pos_iff.mpr hz)), one_div,
    ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast_mul (norm_nonneg z)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-((3-α)/2)) = α-3 by ring]
  unfold rieszKernel standardRieszConstant rieszWeightDenom
  ring

theorem rieszLaplace_nonneg {α : ℝ} (hα : 0<α) (z : Space) {r : ℝ} (hr : 0<r) :
    0≤rieszLaplace α z r :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le)
    (rieszWeightDenom_pos hα).le

theorem rieszLaplace_factor (α : ℝ) (z : Space) (r : ℝ) :
    rieszLaplace α z r = (r^((3-α)/2-1)/rieszWeightDenom α)*Real.exp (-r*‖z‖^2) := by
  unfold rieszLaplace
  rw [show -(‖z‖^2*r) = -r*‖z‖^2 by ring]
  ring

theorem fixed_difference_ne_zero_ae (x : Space) : ∀ᵐ y : Space ∂volume, x-y≠0 := by
  rw [ae_iff]
  simp only [not_not, sub_eq_zero]
  have he : {y : Space | x=y} = {x} := by
    ext y
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact eq_comm
  rw [he, measure_singleton]

theorem rieszLaplace_fixed_time_integrable_ae {α : ℝ} (hα3 : α<3) (x : Space) :
    ∀ᵐ y : Space ∂volume, Integrable (rieszLaplace α (x-y)) positiveTimeMeasure := by
  filter_upwards [fixed_difference_ne_zero_ae x] with y hy
  exact rieszLaplace_integrable_nonzero hα3 hy

theorem rieszLaplace_fixed_integral_ae {α : ℝ} (hα3 : α<3) (x : Space) :
    (fun y => ∫ r, rieszLaplace α (x-y) r ∂positiveTimeMeasure) =ᵐ[volume]
      (fun y => rieszKernel α (standardRieszConstant α) (x-y)) := by
  filter_upwards [fixed_difference_ne_zero_ae x] with y hy
  exact rieszLaplace_integral_nonzero hα3 hy

#print axioms rieszWeightDenom_pos
#print axioms rieszLaplace_integrable_nonzero
#print axioms rieszLaplace_integral_nonzero
#print axioms rieszLaplace_nonneg
#print axioms rieszLaplace_factor
#print axioms fixed_difference_ne_zero_ae
#print axioms rieszLaplace_fixed_time_integrable_ae
#print axioms rieszLaplace_fixed_integral_ae
end HartreeF.BubbleProfile
