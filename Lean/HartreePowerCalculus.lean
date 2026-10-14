import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

/-! Real Frechet calculus for the genuine noninteger Hartree powers, including zero.
Only C1 regularity is asserted. -/
noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace
namespace HartreeF.WeakHartreeChain

def density (p : ℝ) (z : ℂ) : ℝ := ‖z‖ ^ p

def localFactor (q : ℝ) (z : ℂ) : ℂ := ‖z‖ ^ q • z

def densityDerivative (p : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (p * ‖z‖ ^ (p-2)) • innerSL ℝ z

def localFactorDerivative (q : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ‖z‖ ^ q • ContinuousLinearMap.id ℝ ℂ + (densityDerivative q z).smulRight z

theorem density_hasFDerivAt {p : ℝ} (hp : 1 < p) (z : ℂ) :
    HasFDerivAt (density p) (densityDerivative p z) z :=
  hasFDerivAt_norm_rpow z hp

theorem localFactor_hasFDerivAt {q : ℝ} (hq : 1 < q) (z : ℂ) :
    HasFDerivAt (localFactor q) (localFactorDerivative q z) z :=
  (density_hasFDerivAt hq z).smul (hasFDerivAt_id z)

theorem density_contDiff_one {p : ℝ} (hp : 1 < p) : ContDiff ℝ 1 (density p) :=
  contDiff_norm_rpow hp

theorem localFactor_contDiff_one {q : ℝ} (hq : 1 < q) : ContDiff ℝ 1 (localFactor q) :=
  (contDiff_norm_rpow hq).smul contDiff_id

theorem densityDerivative_apply (p : ℝ) (z w : ℂ) :
    densityDerivative p z w = p * ‖z‖ ^ (p-2) * (z.re*w.re+z.im*w.im) := by
  simp only [densityDerivative, smul_apply, innerSL_apply_apply,
    smul_eq_mul, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem localFactorDerivative_apply (q : ℝ) (z w : ℂ) :
    localFactorDerivative q z w = ‖z‖ ^ q • w +
      (q * ‖z‖ ^ (q-2) * (z.re*w.re+z.im*w.im)) • z := by
  simp only [localFactorDerivative, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, densityDerivative_apply]

theorem densityDerivative_zero (p : ℝ) : densityDerivative p 0 = 0 := by
  simp [densityDerivative]

theorem localFactorDerivative_zero {q : ℝ} (hq : 0 < q) :
    localFactorDerivative q 0 = 0 := by
  ext w
  simp [localFactorDerivative_apply, Real.zero_rpow hq.ne']

theorem densityDerivative_continuous {p : ℝ} (hp : 1 < p) :
    Continuous (densityDerivative p) := by
  convert (density_contDiff_one hp).continuous_fderiv (by simp) using 1
  funext z
  exact (density_hasFDerivAt hp z).fderiv.symm

theorem localFactorDerivative_continuous {q : ℝ} (hq : 1 < q) :
    Continuous (localFactorDerivative q) := by
  convert (localFactor_contDiff_one hq).continuous_fderiv (by simp) using 1
  funext z
  exact (localFactor_hasFDerivAt hq z).fderiv.symm

theorem densityDerivative_norm {p : ℝ} (hp : 1 < p) (z : ℂ) :
    ‖densityDerivative p z‖ = p * ‖z‖ ^ (p-1) := by
  rw [← (density_hasFDerivAt hp z).fderiv]
  exact norm_fderiv_norm_id_rpow z hp

theorem localFactorDerivative_bound {q : ℝ} (hq : 1 < q) (z : ℂ) :
    ‖localFactorDerivative q z‖ ≤ (q+1)*‖z‖^q := by
  calc
    _ ≤ ‖‖z‖^q • ContinuousLinearMap.id ℝ ℂ‖ + ‖(densityDerivative q z).smulRight z‖ :=
      norm_add_le _ _
    _ = ‖z‖^q + q*‖z‖^(q-1)*‖z‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ContinuousLinearMap.norm_smulRight_apply, densityDerivative_norm hq]
    _ = (q+1)*‖z‖^q := by
      rw [mul_assoc, ← Real.rpow_add_one' (norm_nonneg z) (by linarith : q-1+1 ≠ 0)]
      rw [sub_add_cancel]
      ring

theorem density_difference_bound {p : ℝ} (hp : 1 < p) (z w : ℂ) :
    ‖density p z-density p w‖ ≤ p*(‖z‖+‖w‖)^(p-1)*‖z-w‖ := by
  apply (convex_closedBall (0 : ℂ) (‖z‖+‖w‖)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (density_hasFDerivAt hp x).differentiableAt)
  · intro x hx
    rw [(density_hasFDerivAt hp x).fderiv, densityDerivative_norm hp]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa using hx) (by linarith)) (by linarith)
  · simp [Metric.mem_closedBall, norm_nonneg]
  · simp [Metric.mem_closedBall, norm_nonneg]

theorem localFactor_difference_bound {q : ℝ} (hq : 1 < q) (z w : ℂ) :
    ‖localFactor q z-localFactor q w‖ ≤ (q+1)*(‖z‖+‖w‖)^q*‖z-w‖ := by
  apply (convex_closedBall (0 : ℂ) (‖z‖+‖w‖)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (localFactor_hasFDerivAt hq x).differentiableAt)
  · intro x hx
    rw [(localFactor_hasFDerivAt hq x).fderiv]
    exact (localFactorDerivative_bound hq x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa using hx) (by linarith)) (by linarith))
  · simp [Metric.mem_closedBall, norm_nonneg]
  · simp [Metric.mem_closedBall, norm_nonneg]

#print axioms density_hasFDerivAt
#print axioms localFactor_hasFDerivAt
#print axioms density_contDiff_one
#print axioms localFactor_contDiff_one
#print axioms densityDerivative_apply
#print axioms localFactorDerivative_apply
#print axioms densityDerivative_zero
#print axioms localFactorDerivative_zero
#print axioms densityDerivative_continuous
#print axioms localFactorDerivative_continuous
#print axioms densityDerivative_norm
#print axioms localFactorDerivative_bound
#print axioms density_difference_bound
#print axioms localFactor_difference_bound
end HartreeF.WeakHartreeChain
