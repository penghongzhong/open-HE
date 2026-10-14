import Lemma_4_1_FrameCoordinates
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Gaussian Fourier formulas with the paper's explicit phase exp(-i x·xi).
Mathlib's normalized Fourier transform has a 2*pi factor in its phase; this file
instead applies its proved Gaussian integral directly, so that convention is
never silently substituted. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace Topology
namespace BWork.Gaussian
open Angular

/-- Paper Fourier convention, with no 2*pi in the exponent. -/
def paperFourier (f : E → ℝ) (ξ : E) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * (⟪ξ,x⟫ : ℝ)) * (f x : ℂ)

def gaussian (x : E) : ℝ := Real.exp (-‖x‖^2 / 2)

def gaussianRate (b : ℝ) (x : E) : ℝ := Real.exp (-b * ‖x‖^2)

def scaledGaussian (R : ℝ) (x : E) : ℝ := R⁻¹ * gaussian (R⁻¹ • x)

theorem gaussianRate_integrand (b : ℝ) (ξ x : E) :
    Complex.exp (-Complex.I * (⟪ξ,x⟫ : ℝ)) * (gaussianRate b x : ℂ) =
      Complex.exp (-(b : ℂ) * (‖x‖ : ℂ)^2 + (-Complex.I) * (⟪ξ,x⟫ : ℝ)) := by
  unfold gaussianRate
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gaussianRate_fourier_integrable {b : ℝ} (hb : 0 < b) (ξ : E) :
    Integrable (fun x => Complex.exp (-Complex.I * (⟪ξ,x⟫ : ℝ)) * (gaussianRate b x : ℂ)) := by
  simp_rw [gaussianRate_integrand]
  exact GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) (-Complex.I) ξ

theorem gaussianRate_fourier {b : ℝ} (hb : 0 < b) (ξ : E) :
    paperFourier (gaussianRate b) ξ =
      Complex.ofReal ((Real.pi / b) ^ (3 / 2 : ℝ)) *
        (Real.exp (-‖ξ‖^2 / (4*b)) : ℂ) := by
  unfold paperFourier
  simp_rw [gaussianRate_integrand]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) (-Complex.I) ξ]
  have hdim : Module.finrank ℝ E = 3 := by simp [E]
  rw [hdim]
  norm_num only [Nat.cast_ofNat]
  have hpow : (Real.pi / (b : ℂ)) ^ ((3 : ℂ) / 2) =
      Complex.ofReal ((Real.pi / b) ^ (3 / 2 : ℝ)) := by
    have h := Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hb.le) (3/2 : ℝ)
    push_cast at h
    exact h.symm
  rw [hpow, Complex.ofReal_exp]
  congr 2
  push_cast
  simp only [neg_sq, Complex.I_sq]
  ring

theorem gaussian_eq_rate : gaussian = gaussianRate (1/2) := by
  funext x
  unfold gaussian gaussianRate
  congr 1
  ring

/-- The paper's exact Gamma(xi) = (2*pi)^(3/2) exp(-|xi|²/2). -/
theorem gaussian_fourier (ξ : E) :
    paperFourier gaussian ξ =
      Complex.ofReal ((2*Real.pi) ^ (3/2 : ℝ)) * (gaussian ξ : ℂ) := by
  rw [gaussian_eq_rate, gaussianRate_fourier (by norm_num : (0 : ℝ)<1/2)]
  have hpi : Real.pi / (1/2 : ℝ) = 2*Real.pi := by ring
  rw [hpi]
  unfold gaussianRate
  congr 2
  congr 1
  norm_num
  ring

theorem paperFourier_const_mul (a : ℝ) (f : E → ℝ) (ξ : E) :
    paperFourier (fun x => a*f x) ξ = (a : ℂ) * paperFourier f ξ := by
  unfold paperFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  ring

theorem scaledGaussian_eq_rate {R : ℝ} (hR : 0 < R) :
    scaledGaussian R = fun x => R⁻¹ * gaussianRate (1/(2*R^2)) x := by
  funext x
  unfold scaledGaussian gaussian gaussianRate
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  congr 2
  ring

/-- Exact scaled Fourier formula before simplifying its positive real power. -/
theorem scaledGaussian_fourier_exact {R : ℝ} (hR : 0 < R) (ξ : E) :
    paperFourier (scaledGaussian R) ξ =
      (R⁻¹ : ℂ) * (Complex.ofReal ((Real.pi / (1/(2*R^2))) ^ (3/2 : ℝ)) *
        (Real.exp (-‖ξ‖^2 / (4*(1/(2*R^2)))) : ℂ)) := by
  rw [scaledGaussian_eq_rate hR, paperFourier_const_mul,
    gaussianRate_fourier (by positivity : (0 : ℝ) < 1/(2*R^2))]
  norm_cast

#print axioms gaussianRate_integrand
#print axioms gaussianRate_fourier_integrable
#print axioms gaussianRate_fourier
#print axioms gaussian_eq_rate
#print axioms gaussian_fourier
#print axioms paperFourier_const_mul
#print axioms scaledGaussian_eq_rate
#print axioms scaledGaussian_fourier_exact
end BWork.Gaussian
