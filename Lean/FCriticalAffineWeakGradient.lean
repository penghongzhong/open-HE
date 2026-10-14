import FCriticalAffineGeometry
import FEnergyStateInverse

/-! Weak-gradient covariance under the actual isotropic affine map.
The domain is L6 with two real L2 weak gradients, with no value L2 premise. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.CriticalAffine
open SobolevStretch

theorem inverse_affine_test_class {a : ℝ} (ha : 0 < a) (b : Space)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (a⁻¹ • (y-b))) ∧
    HasCompactSupport (fun y => φ (a⁻¹ • (y-b))) := by
  refine ⟨hφ.comp ((contDiff_id.sub contDiff_const).const_smul a⁻¹), ?_⟩
  exact hc.comp_homeomorph (affineHomeomorph ha.ne' b).symm

theorem inverse_affine_test_derivative {a : ℝ} (ha : 0 < a) (b : Space)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y v : Space) :
    fderiv ℝ (fun z => φ (a⁻¹ • (z-b))) y (a • v) =
      fderiv ℝ φ (a⁻¹ • (y-b)) v := by
  have hi : HasFDerivAt (fun z : Space => a⁻¹ • (z-b))
      (a⁻¹ • ContinuousLinearMap.id ℝ Space) y :=
    ((hasFDerivAt_id y).sub_const b).const_smul a⁻¹
  have hd := ((hφ.differentiable (by simp)) (a⁻¹ • (y-b))).hasFDerivAt.comp y hi
  change (fderiv ℝ (φ ∘ (fun z : Space => a⁻¹ • (z-b))) y) (a • v) = _
  rw [hd.fderiv]
  simp [ha.ne']

theorem hasWeakGradient_affine_pullback {u : Space → ℝ} {V : Space → Space}
    (h : HasWeakGradient u V) (hu : MemLp u 6 volume) (hV : MemLp V 2 volume)
    {a : ℝ} (ha : 0 < a) (b : Space) :
    HasWeakGradient (valuePullback a b u) (gradientPullback a b V) := by
  refine ⟨(valuePullback_memLp ha b (by norm_num) (by norm_num) hu).locallyIntegrable (by norm_num),
    (gradientPullback_memLp ha b (by norm_num) (by norm_num) hV).locallyIntegrable (by norm_num), ?_⟩
  intro v φ hφ hc
  let ψ : Space → ℝ := fun y => φ (a⁻¹ • (y-b))
  have ht := inverse_affine_test_class ha b hφ hc
  have hw := h.integration_by_parts (a • v) ψ ht.1 ht.2
  have hj1 := affine_integral ha b (fun y => u y * fderiv ℝ ψ y (a • v))
  have hj2 := affine_integral ha b (fun y => ⟪V y,a • v⟫ * ψ y)
  have hd (x : Space) : fderiv ℝ ψ (affine a b x) (a • v) = fderiv ℝ φ x v := by
    rw [inverse_affine_test_derivative ha b hφ]
    simp [affine, smul_smul, ha.ne']
  have hp (x : Space) : ψ (affine a b x) = φ x := by
    simp [ψ, affine, smul_smul, ha.ne']
  simp only [hd, smul_eq_mul] at hj1
  simp only [hp, smul_eq_mul] at hj2
  have he : (∫ x, u (affine a b x) * fderiv ℝ φ x v) =
      -(∫ x, ⟪V (affine a b x),a • v⟫ * φ x) := by
    rw [hj1, hw, mul_neg, ← hj2]
  have hg (x : Space) : ⟪gradientPullback a b V x,v⟫ =
      Real.sqrt a * ⟪V (affine a b x),a • v⟫ := by
    simp only [gradientPullback, real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [valuePullback, smul_eq_mul, hg, mul_assoc, integral_const_mul, he, mul_neg]

theorem inDotH1_affine_pullback {u : Space → ℂ} {U V : Space → Space}
    (h : InDotH1 u U V) {a : ℝ} (ha : 0 < a) (b : Space) :
    InDotH1 (valuePullback a b u) (gradientPullback a b U) (gradientPullback a b V) := by
  refine ⟨valuePullback_memLp ha b (by norm_num) (by norm_num) h.function_L6,
    gradientPullback_memLp ha b (by norm_num) (by norm_num) h.real_gradient_L2,
    gradientPullback_memLp ha b (by norm_num) (by norm_num) h.imag_gradient_L2, ?_, ?_⟩
  · convert hasWeakGradient_affine_pullback h.real_weak
      (h.function_L6.continuousLinearMap_comp Complex.reCLM) h.real_gradient_L2 ha b using 1
    funext x
    simp [valuePullback, Complex.real_smul]
  · convert hasWeakGradient_affine_pullback h.imag_weak
      (h.function_L6.continuousLinearMap_comp Complex.imCLM) h.imag_gradient_L2 ha b using 1
    funext x
    simp [valuePullback, Complex.real_smul]

#print axioms inverse_affine_test_class
#print axioms inverse_affine_test_derivative
#print axioms hasWeakGradient_affine_pullback
#print axioms inDotH1_affine_pullback
end HartreeF.CriticalAffine
