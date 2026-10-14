import WeakDirectionalStretch
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
An actual distributional product rule on the C11 Euclidean space.
The multiplier is C-infinity in the ENat sense. The Sobolev function only
has the local integrability already present in `HasWeakGradient`.
The new gradient is the literal Mathlib gradient of the multiplier.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch

theorem smooth_gradient_continuous {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : Continuous (gradient χ) := by
  exact (InnerProductSpace.toDual ℝ Space).symm.continuous.comp
    (hχ.continuous_fderiv (by simp))

/-- Multiplication of a genuine weakly differentiable function by a smooth
scalar, derived by using `χ * φ` as the old compactly supported test. -/
theorem HasWeakGradient.mul_smooth {u : Space → ℝ} {V : Space → Space}
    (h : HasWeakGradient u V) {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    HasWeakGradient (fun x => χ x * u x)
      (fun x => χ x • V x + u x • gradient χ x) := by
  have hcu : LocallyIntegrable (fun x => χ x * u x) volume :=
    h.function_local.continuous_mul hχ.continuous
  have hcv : LocallyIntegrable (fun x => χ x • V x) volume :=
    h.gradient_local.continuous_smul hχ.continuous
  have hug : LocallyIntegrable (fun x => u x • gradient χ x) volume :=
    h.function_local.smul_continuous (smooth_gradient_continuous hχ)
  refine ⟨hcu, hcv.add hug, ?_⟩
  intro v φ hφ hcφ
  have htest : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * φ x) := hχ.mul hφ
  have htestc : HasCompactSupport (fun x => χ x * φ x) := hcφ.mul_left
  have hold := h.integration_by_parts v (fun x => χ x * φ x) htest htestc
  have hiA : Integrable (fun x => χ x * u x * fderiv ℝ φ x v) volume :=
    (weak_test_integrable hcu hcv hφ hcφ v).1
  have hiB : Integrable (fun x => u x * fderiv ℝ χ x v * φ x) volume := by
    simpa only [real_inner_smul_left, inner_gradient_left] using
      (weak_test_integrable h.function_local hug hφ hcφ v).2
  have hiC : Integrable (fun x => χ x * ⟪V x, v⟫ * φ x) volume := by
    simpa only [real_inner_smul_left] using
      (weak_test_integrable h.function_local hcv hφ hcφ v).2
  have hd (x : Space) : fderiv ℝ (fun y => χ y * φ y) x v =
      χ x * fderiv ℝ φ x v + φ x * fderiv ℝ χ x v := by
    rw [fderiv_fun_mul (hχ.differentiable (by simp) x)
      (hφ.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hleft : (fun x => u x * fderiv ℝ (fun y => χ y * φ y) x v) =
      (fun x => χ x * u x * fderiv ℝ φ x v + u x * fderiv ℝ χ x v * φ x) := by
    funext x
    rw [hd]
    ring
  have hright : (fun x => ⟪V x, v⟫ * (χ x * φ x)) =
      (fun x => χ x * ⟪V x, v⟫ * φ x) := by
    funext x
    ring
  rw [hleft, integral_add hiA hiB, hright] at hold
  have hout : (fun x => ⟪χ x • V x + u x • gradient χ x, v⟫ * φ x) =
      (fun x => χ x * ⟪V x, v⟫ * φ x + u x * fderiv ℝ χ x v * φ x) := by
    funext x
    simp only [inner_add_left, real_inner_smul_left, inner_gradient_left]
    ring
  rw [hout, integral_add hiC hiB]
  linarith

#print axioms smooth_gradient_continuous
#print axioms HasWeakGradient.mul_smooth
end HartreeF.SobolevStretch
