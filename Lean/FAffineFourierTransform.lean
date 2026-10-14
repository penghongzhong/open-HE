import FCriticalAffineGeometry
import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace HartreeF.FreeAffine
open CriticalAffine

/-- Literal affine Fourier transform with the pinned cycles/unit convention.
The exact 3D Jacobian and positive scale are retained. -/
theorem fourier_affine {a : ℝ} (ha : 0<a) (b : Space) (f : Space → ℂ) (ξ : Space) :
    𝓕 (fun x => f (affine a b x)) ξ =
      (a^3)⁻¹ • (Real.fourierChar (inner ℝ b (a⁻¹ • ξ)) • 𝓕 f (a⁻¹ • ξ)) := by
  let g (z : Space) : ℂ := Real.fourierChar (-inner ℝ (a⁻¹ • (z-b)) ξ) • f z
  have hl : (fun x => g (affine a b x))=
      (fun x => Real.fourierChar (-inner ℝ x ξ) • f (affine a b x)) := by
    funext x
    simp only [g, affine, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have hj := affine_integral ha b g
  rw [hl] at hj
  rw [Real.fourier_eq, hj, Real.fourier_eq]
  apply congrArg (fun z : ℂ => (a^3)⁻¹ • z)
  have he (z : Space) : -inner ℝ (a⁻¹ • (z-b)) ξ=
      inner ℝ b (a⁻¹ • ξ)+(-inner ℝ z (a⁻¹ • ξ)) := by
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left]
    ring
  simp only [g, he, AddChar.map_add_eq_mul, mul_smul, Circle.smul_def, smul_eq_mul]
  exact integral_const_mul (Real.fourierChar (inner ℝ b (a⁻¹ • ξ)) : ℂ)
    (fun z => (Real.fourierChar (-inner ℝ z (a⁻¹ • ξ)) : ℂ)*f z)

/-- The homogeneous value amplitude is an actual real scalar multiplier. -/
theorem fourier_valuePullback {a : ℝ} (ha : 0<a) (b : Space) (f : Space → ℂ) (ξ : Space) :
    𝓕 (valuePullback a b f) ξ =
      (Real.sqrt a*(a^3)⁻¹) •
        (Real.fourierChar (inner ℝ b (a⁻¹ • ξ)) • 𝓕 f (a⁻¹ • ξ)) := by
  have h : 𝓕 (valuePullback a b f) ξ = Real.sqrt a • 𝓕 (fun x => f (affine a b x)) ξ := by
    simp only [Real.fourier_eq, valuePullback, smul_comm (Real.fourierChar _) (Real.sqrt a), integral_smul]
  rw [h, fourier_affine ha b f ξ, smul_smul]

#print axioms fourier_affine
#print axioms fourier_valuePullback
end HartreeF.FreeAffine
