import FSpatialMollifierLp
import ClassicalWeakGradient
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory
open scoped ENNReal NNReal Topology Convolution RealInnerProductSpace
namespace HartreeF.ProfileSpatialSmoothing
open SobolevStretch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal convolution with the normalized bump is infinitely smooth for locally integrable data. -/
theorem spatialMollify_contDiff (φ : ContDiffBump (0 : Space)) {f : Space → E}
    (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialMollify φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

/-- The reflected translate is an actual compact smooth weak test. -/
theorem reflected_test_class {κ : Space → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (x-y)) ∧
    HasCompactSupport (fun y => κ (x-y)) := by
  let σ : Space ≃ₜ Space :=
    { toFun := fun y => x-y
      invFun := fun y => x-y
      left_inv := fun y => sub_sub_cancel x y
      right_inv := fun y => sub_sub_cancel x y
      continuous_toFun := continuous_const.sub continuous_id
      continuous_invFun := continuous_const.sub continuous_id }
  exact ⟨hκ.comp (contDiff_const.sub contDiff_id), hc.comp_homeomorph σ⟩

theorem reflected_test_fderiv {κ : Space → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (x y v : Space) :
    fderiv ℝ (fun z => κ (x-z)) y v = - fderiv ℝ κ (x-y) v := by
  have hd := ((hκ.differentiable (by simp)) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change fderiv ℝ (κ ∘ (fun z : Space => x-z)) y v = _
  rw [hd.fderiv]
  simp

/-- The derivative of the literal mollification, without differentiating the rough source. -/
theorem spatialMollify_fderiv (φ : ContDiffBump (0 : Space)) {u : Space → ℝ}
    (hu : LocallyIntegrable u volume) (x v : Space) :
    fderiv ℝ (spatialMollify φ u) x v =
      ∫ y, u y * fderiv ℝ (φ.normed volume) (x-y) v := by
  rw [spatialMollify, ← convolution_flip]
  have hc1 : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  rw [(φ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hu hc1 x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ).flip hu
    (φ.hasCompactSupport_normed.fderiv ℝ) (hc1.continuous_fderiv (by simp))]
  simp only [convolution, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_comm]

/-- Actual weak-gradient coupling, obtained by testing the rough function against the
reflected kernel and applying the classical-to-weak producer to the resulting smooth field. -/
theorem hasWeakGradient_spatialMollify (φ : ContDiffBump (0 : Space))
    {u : Space → ℝ} {U : Space → Space} (h : HasWeakGradient u U) :
    HasWeakGradient (spatialMollify φ u) (spatialMollify φ U) := by
  apply hasWeakGradient_of_differentiable
    ((spatialMollify_contDiff φ h.function_local).differentiable (by simp))
    (spatialMollify_contDiff φ h.gradient_local).continuous
  intro x v
  have ht := reflected_test_class (φ.contDiff_normed (μ := volume)) φ.hasCompactSupport_normed x
  have hw := h.integration_by_parts v (fun y => φ.normed volume (x-y)) ht.1 ht.2
  simp only [reflected_test_fderiv (φ.contDiff_normed (μ := volume)), mul_neg,
    integral_neg, neg_inj] at hw
  rw [spatialMollify_fderiv φ h.function_local, hw]
  have hi : Integrable (fun y => φ.normed volume (x-y) • U y) volume :=
    h.gradient_local.integrable_smul_left_of_hasCompactSupport ht.1.continuous ht.2
  rw [spatialMollify, convolution_lsmul_swap, real_inner_comm,
    ← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [inner_smul_right, real_inner_comm]
  ring

#print axioms spatialMollify_contDiff
#print axioms spatialMollify_fderiv
#print axioms hasWeakGradient_spatialMollify
end HartreeF.ProfileSpatialSmoothing
