import SobolevStretchLp

/-!
Distributional directional stretching on the actual F Euclidean R3.
Weak gradients are defined by all compactly supported smooth real tests,
with local integrability on both sides. Complex dotH1 means L6 together
with L2 weak gradients of the real and imaginary parts. No pointwise
classical differentiability of the Sobolev function is used.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch

structure HasWeakGradient (u : Space → ℝ) (V : Space → Space) : Prop where
  function_local : LocallyIntegrable u volume
  gradient_local : LocallyIntegrable V volume
  integration_by_parts : ∀ (v : Space) (φ : Space → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, ⟪V x,v⟫ * φ x)

structure InDotH1 (u : Space → ℂ) (GRe GIm : Space → Space) : Prop where
  function_L6 : MemLp u 6 volume
  real_gradient_L2 : MemLp GRe 2 volume
  imag_gradient_L2 : MemLp GIm 2 volume
  real_weak : HasWeakGradient (fun x => (u x).re) GRe
  imag_weak : HasWeakGradient (fun x => (u x).im) GIm

theorem HasWeakGradient.test_integrable {u : Space → ℝ} {V : Space → Space}
    (h : HasWeakGradient u V) {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (v : Space) :
    Integrable (fun x => u x * fderiv ℝ φ x v) volume ∧
    Integrable (fun x => ⟪V x,v⟫ * φ x) volume :=
  weak_test_integrable h.function_local h.gradient_local hφ hc v

/-- The inverse linear pullback stays in the actual smooth compact test class. -/
theorem inverse_test_class {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (DirectionalStretch.stretch ω l⁻¹ y)) ∧
    HasCompactSupport (fun y => φ (DirectionalStretch.stretch ω l⁻¹ y)) := by
  exact ⟨hφ.comp (DirectionalStretch.stretch ω l⁻¹).contDiff,
    hc.comp_homeomorph (stretchEquiv ω hω l hl.ne').symm.toHomeomorph⟩

theorem inverse_test_derivative {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y v : Space) :
    fderiv ℝ (fun z => φ (DirectionalStretch.stretch ω l⁻¹ z)) y (DirectionalStretch.stretch ω l v) =
      fderiv ℝ φ (DirectionalStretch.stretch ω l⁻¹ y) v := by
  have h := ((hφ.differentiable (by simp)) (DirectionalStretch.stretch ω l⁻¹ y)).hasFDerivAt.comp y
    (DirectionalStretch.stretch ω l⁻¹).hasFDerivAt
  change (fderiv ℝ (φ ∘ DirectionalStretch.stretch ω l⁻¹) y) _ = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, stretch_inverse hω hl.ne']

/-- Genuine weak chain rule, obtained by testing u against phi o T_l^{-1}
and applying the produced Jacobian twice. -/
theorem HasWeakGradient.stretch {u : Space → ℝ} {V : Space → Space}
    (h : HasWeakGradient u V) (hu : MemLp u 6 volume) (hV : MemLp V 2 volume)
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l) :
    HasWeakGradient (stretchedFunction ω l u) (stretchedGradient ω l V) := by
  refine ⟨(stretchedFunction_memLp hω hl (by norm_num) (by norm_num) hu).locallyIntegrable
      (by norm_num),
    (stretchedGradient_memLp hω hl hV).locallyIntegrable (by norm_num), ?_⟩
  intro v φ hφ hc
  let ψ : Space → ℝ := fun y => φ (DirectionalStretch.stretch ω l⁻¹ y)
  have ht := inverse_test_class hω hl hφ hc
  have hw := h.integration_by_parts (DirectionalStretch.stretch ω l v) ψ ht.1 ht.2
  have hj1 := stretch_integral hω hl (fun y => u y * fderiv ℝ ψ y (DirectionalStretch.stretch ω l v))
  have hj2 := stretch_integral hω hl (fun y => ⟪V y, DirectionalStretch.stretch ω l v⟫ * ψ y)
  have hd (x : Space) : fderiv ℝ ψ (DirectionalStretch.stretch ω l x) (DirectionalStretch.stretch ω l v) = fderiv ℝ φ x v := by
    rw [inverse_test_derivative hω hl hφ, stretch_inverse hω hl.ne']
  simp only [hd, smul_eq_mul] at hj1
  simp only [ψ, stretch_inverse hω hl.ne', smul_eq_mul] at hj2
  have hi : (∫ x, u (DirectionalStretch.stretch ω l x) * fderiv ℝ φ x v) =
      -(∫ x, ⟪V (DirectionalStretch.stretch ω l x), DirectionalStretch.stretch ω l v⟫ * φ x) := by
    rw [← hj1, ← hj2] at hw
    exact (mul_left_cancel₀ hl.ne') (by nlinarith [hw])
  have hg (x : Space) : ⟪stretchedGradient ω l V x,v⟫ =
      Real.sqrt l * ⟪V (DirectionalStretch.stretch ω l x),DirectionalStretch.stretch ω l v⟫ := by
    rw [stretchedGradient, real_inner_smul_left, ← stretch_self_adjoint]
  simp only [stretchedFunction, smul_eq_mul, hg, mul_assoc, integral_const_mul, hi, mul_neg]

/-- Complex homogeneous Sobolev stretching with its actual two real weak
partial gradients; all L6/L2 output domains are produced. -/
theorem InDotH1.stretch {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : InDotH1 u GRe GIm) {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l) :
    InDotH1 (stretchedFunction ω l u)
      (stretchedGradient ω l GRe) (stretchedGradient ω l GIm) := by
  refine ⟨stretchedFunction_memLp hω hl (by norm_num) (by norm_num) h.function_L6,
    stretchedGradient_memLp hω hl h.real_gradient_L2,
    stretchedGradient_memLp hω hl h.imag_gradient_L2, ?_, ?_⟩
  · convert h.real_weak.stretch (h.function_L6.continuousLinearMap_comp Complex.reCLM)
      h.real_gradient_L2 hω hl using 1
    funext x
    simp [stretchedFunction, Complex.real_smul]
  · convert h.imag_weak.stretch (h.function_L6.continuousLinearMap_comp Complex.imCLM)
      h.imag_gradient_L2 hω hl using 1
    funext x
    simp [stretchedFunction, Complex.real_smul]

#print axioms HasWeakGradient.test_integrable
#print axioms inverse_test_class
#print axioms inverse_test_derivative
#print axioms HasWeakGradient.stretch
#print axioms InDotH1.stretch
end HartreeF.SobolevStretch
