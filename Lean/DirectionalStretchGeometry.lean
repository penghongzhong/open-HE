import PhysicalStretchKernel
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian

/-!
Actual rank-one directional dilation on Euclidean R3. The continuous linear
isomorphism, inverse, self-adjoint pairing, determinant and Jacobian are all
produced natively. No determinant, change-of-variables or weak-gradient rule
is assumed. This module does not claim a Sobolev pullback theorem.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace HartreeF.DirectionalStretch
open PhysicalStretch

def stretch (ω : Space) (l : ℝ) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space + (innerSL ℝ ω).smulRight ((l-1) • ω)

@[simp] theorem stretch_apply (ω : Space) (l : ℝ) (z : Space) :
    stretch ω l z = z + ((l-1)*⟪ω,z⟫) • ω := by
  simp [stretch, smul_smul, mul_comm]

@[simp] theorem stretch_one (ω : Space) (z : Space) : stretch ω 1 z = z := by
  simp

theorem stretch_inner {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) (z : Space) :
    ⟪ω, stretch ω l z⟫ = l*⟪ω,z⟫ := by
  rw [stretch_apply, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hω]
  ring

/-- The same rank-one map is self-adjoint under the actual Euclidean pairing. -/
theorem stretch_self_adjoint (ω : Space) (l : ℝ) (ξ z : Space) :
    ⟪ξ, stretch ω l z⟫ = ⟪stretch ω l ξ, z⟫ := by
  simp only [stretch_apply, inner_add_right, inner_add_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_comm ξ ω]
  ring

theorem stretch_comp {ω : Space} (hω : ‖ω‖ = 1) (l μ : ℝ) (z : Space) :
    stretch ω μ (stretch ω l z) = stretch ω (μ*l) z := by
  rw [stretch_apply ω μ, stretch_inner hω, stretch_apply, stretch_apply]
  module

theorem stretch_inverse {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : l ≠ 0) (z : Space) :
    stretch ω l⁻¹ (stretch ω l z) = z := by
  rw [stretch_comp hω, inv_mul_cancel₀ hl, stretch_one]

def stretchEquiv (ω : Space) (hω : ‖ω‖ = 1) (l : ℝ) (hl : l ≠ 0) : Space ≃L[ℝ] Space :=
  { stretch ω l with
    invFun := stretch ω l⁻¹
    left_inv := stretch_inverse hω hl
    right_inv := fun z => by
      change stretch ω l (stretch ω l⁻¹ z) = z
      rw [stretch_comp hω, mul_inv_cancel₀ hl, stretch_one]
    continuous_invFun := (stretch ω l⁻¹).continuous }

@[simp] theorem stretchEquiv_apply (ω : Space) (hω : ‖ω‖ = 1) (l : ℝ) (hl : l ≠ 0) (z : Space) :
    stretchEquiv ω hω l hl z = stretch ω l z := rfl

@[simp] theorem stretchEquiv_symm_apply (ω : Space) (hω : ‖ω‖ = 1) (l : ℝ) (hl : l ≠ 0) (z : Space) :
    (stretchEquiv ω hω l hl).symm z = stretch ω l⁻¹ z := rfl

theorem stretch_norm_sq {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) (z : Space) :
    ‖stretch ω l z‖^2 = l^2 * longitudinalSq ω z + transverseSq ω z := by
  rw [stretch_apply, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm z ω]
  unfold transverseSq longitudinalSq
  rw [real_inner_comm z ω]
  ring

/-- Native rank-one determinant lemma, proved through an actual basis matrix. -/
theorem det_id_add_smulRight (f : Space →ₗ[ℝ] ℝ) (v : Space) :
    LinearMap.det (LinearMap.id + f.smulRight v) = 1 + f v := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have h := congrArg f (b.sum_repr v)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simpa only [dotProduct, Function.comp_apply, mul_comm] using congrArg (fun x : ℝ => 1+x) h

theorem stretch_det {ω : Space} (hω : ‖ω‖ = 1) (l : ℝ) :
    (stretch ω l).det = l := by
  change LinearMap.det (LinearMap.id +
    (innerSL ℝ ω).toLinearMap.smulRight ((l-1) • ω)) = l
  rw [det_id_add_smulRight]
  change 1 + ⟪ω, (l-1) • ω⟫ = l
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hω]
  ring

/-- Actual Jacobian identity for scalar or vector Bochner integrals. -/
theorem stretch_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l) (f : Space → F) :
    l • (∫ x, f (stretch ω l x)) = ∫ x, f x := by
  have hi : InjOn (stretch ω l) univ := (stretchEquiv ω hω l hl.ne').injective.injOn
  have hs : stretch ω l '' univ = univ :=
    image_univ_of_surjective (stretchEquiv ω hω l hl.ne').surjective
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Space)
    MeasurableSet.univ (fun x _ => (stretch ω l).hasFDerivAt.hasFDerivWithinAt) hi f
  rw [hs, setIntegral_univ, setIntegral_univ] at h
  simpa only [stretch_det hω, abs_of_pos hl, integral_smul] using h.symm

/-- The same actual Jacobian supplies the L1 pullback domain, not merely a total-integral equation. -/
theorem stretch_integrable_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l) (f : Space → F) :
    Integrable (fun x => f (stretch ω l x)) volume ↔ Integrable f volume := by
  have hi : InjOn (stretch ω l) univ := (stretchEquiv ω hω l hl.ne').injective.injOn
  have hs : stretch ω l '' univ = univ :=
    image_univ_of_surjective (stretchEquiv ω hω l hl.ne').surjective
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure Space)
    MeasurableSet.univ (fun x _ => (stretch ω l).hasFDerivAt.hasFDerivWithinAt) hi f
  rw [hs, integrableOn_univ, integrableOn_univ] at h
  simp only [stretch_det hω, abs_of_pos hl] at h
  have hsml : Integrable (fun x => l • f (stretch ω l x)) volume ↔
      Integrable (fun x => f (stretch ω l x)) volume := integrable_smul_iff hl.ne' _
  exact hsml.symm.trans h.symm

#print axioms stretch_apply
#print axioms stretch_one
#print axioms stretch_inner
#print axioms stretch_self_adjoint
#print axioms stretch_comp
#print axioms stretch_inverse
#print axioms stretchEquiv_apply
#print axioms stretchEquiv_symm_apply
#print axioms stretch_norm_sq
#print axioms det_id_add_smulRight
#print axioms stretch_det
#print axioms stretch_integral
#print axioms stretch_integrable_iff
end HartreeF.DirectionalStretch
