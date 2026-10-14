import L1PaperFourier
import Mathlib.MeasureTheory.Group.Integral

/-! Actual three-dimensional Gaussian mass and convolution, using square completion
and translation invariance of Lebesgue measure. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace

namespace HartreeF.BubbleProfile

/-- The real Gaussian mass integrand is genuinely integrable. -/
theorem gaussian_mass_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : Space => Real.exp (-t * ‖y‖ ^ 2)) volume := by
  exact GaussianFourierBridge.gaussianRate_real_integrable ht

/-- Gaussian mass for the actual Lebesgue measure on `Space`. -/
theorem gaussian_mass_integral {t : ℝ} (ht : 0 < t) :
    (∫ y : Space, Real.exp (-t * ‖y‖ ^ 2)) = (Real.pi / t) ^ (3 / 2 : ℝ) := by
  have h := BWork.Gaussian.gaussianRate_fourier ht (0 : Space)
  simp only [BWork.Gaussian.paperFourier, inner_zero_left, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul, norm_zero, zero_pow (by decide : 2 ≠ 0),
    neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one, mul_one,
    integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- The unintegrated product of two real Gaussian kernels. -/
def gaussianProduct (r s : ℝ) (x y : Space) : ℝ :=
  Real.exp (-r * ‖x - y‖ ^ 2) * Real.exp (-s * ‖y‖ ^ 2)

/-- Exact square completion in the genuine three-dimensional Euclidean space. -/
theorem gaussian_square_completion {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (x y : Space) :
    r * ‖x - y‖ ^ 2 + s * ‖y‖ ^ 2 =
      (r + s) * ‖y - (r / (r + s)) • x‖ ^ 2 +
        (r * s / (r + s)) * ‖x‖ ^ 2 := by
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm y x]
  field_simp
  ring

/-- Square completion rewritten as an equality of the positive Gaussian integrands. -/
theorem gaussianProduct_eq_completed {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (x y : Space) :
    gaussianProduct r s x y =
      Real.exp (-(r + s) * ‖y - (r / (r + s)) • x‖ ^ 2) *
        Real.exp (-(r * s / (r + s)) * ‖x‖ ^ 2) := by
  unfold gaussianProduct
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have h := gaussian_square_completion hr hs x y
  linarith

/-- Each convolution fiber is an actual integrable function of `y`. -/
theorem gaussianProduct_integrable {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (x : Space) : Integrable (gaussianProduct r s x) volume := by
  have h := (gaussian_mass_integrable (add_pos hr hs)).comp_sub_right
    ((r / (r + s)) • x)
  exact (h.mul_const (Real.exp (-(r * s / (r + s)) * ‖x‖ ^ 2))).congr
    (Filter.Eventually.of_forall (fun y => (gaussianProduct_eq_completed hr hs x y).symm))

/-- Exact convolution of two Gaussian kernels, with no Fourier inversion premise. -/
theorem gaussianProduct_integral {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (x : Space) :
    (∫ y : Space, gaussianProduct r s x y) =
      (Real.pi / (r + s)) ^ (3 / 2 : ℝ) *
        Real.exp (-(r * s / (r + s)) * ‖x‖ ^ 2) := by
  simp_rw [gaussianProduct_eq_completed hr hs]
  rw [integral_mul_const,
    integral_sub_right_eq_self (fun y : Space => Real.exp (-(r + s) * ‖y‖ ^ 2)),
    gaussian_mass_integral (add_pos hr hs)]

#print axioms gaussian_mass_integrable
#print axioms gaussian_mass_integral
#print axioms gaussian_square_completion
#print axioms gaussianProduct_eq_completed
#print axioms gaussianProduct_integrable
#print axioms gaussianProduct_integral

end HartreeF.BubbleProfile
