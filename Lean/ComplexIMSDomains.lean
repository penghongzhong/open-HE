import ComplexIMSGeometry

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch WeakCutoffLp

theorem function_smul_angle_gradient_L2 {θ : Space → ℝ} {R : ℝ}
    (hθ : AngleCutoff θ R) {f : Space → ℝ} (hf : MemLp f 6 volume) :
    MemLp (fun x => f x • gradient θ x) 2 volume := by
  have : ENNReal.HolderTriple 6 3 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num⟩
  exact hf.smul (hθ.gradient_memLp 3)

/-- Each of the four real product-rule terms is genuinely L2. -/
theorem real_gradient_terms_L2 {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {f : Space → ℝ} {G : Space → Space} (hf : MemLp f 6 volume)
    (hG : MemLp G 2 volume) :
    MemLp (fun x => Real.cos (θ x) • G x) 2 volume ∧
    MemLp (fun x => (Real.sin (θ x) * f x) • gradient θ x) 2 volume ∧
    MemLp (fun x => Real.sin (θ x) • G x) 2 volume ∧
    MemLp (fun x => (Real.cos (θ x) * f x) • gradient θ x) 2 volume := by
  have hc := cos_memLp_top hθ.smooth.continuous
  have hs := sin_memLp_top hθ.smooth.continuous
  have he := function_smul_angle_gradient_L2 hθ hf
  refine ⟨hc.smul hG, ?_, hs.smul hG, ?_⟩
  · have hh : MemLp (fun x => Real.sin (θ x) • (f x • gradient θ x)) 2 volume := hs.smul he
    simpa only [smul_smul] using hh
  · have hh : MemLp (fun x => Real.cos (θ x) • (f x • gradient θ x)) 2 volume := hc.smul he
    simpa only [smul_smul] using hh

theorem real_gradients_L2 {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {f : Space → ℝ} {G : Space → Space} (hf : MemLp f 6 volume)
    (hG : MemLp G 2 volume) :
    MemLp (coreGradient θ f G) 2 volume ∧ MemLp (tailGradient θ f G) 2 volume := by
  obtain ⟨hc, hec, hs, hes⟩ := real_gradient_terms_L2 hθ hf hG
  exact ⟨hc.sub hec, hs.add hes⟩

/-- Distributional product rule with the literal trigonometric chain rule. -/
theorem weak_gradient_core {θ f : Space → ℝ} {G : Space → Space}
    (hθ : ContDiff ℝ (⊤ : ENat) θ) (hf : HasWeakGradient f G) :
    HasWeakGradient (fun x => Real.cos (θ x) * f x) (coreGradient θ f G) := by
  have h := hf.mul_smooth hθ.cos
  convert h using 1
  funext x
  rw [angle_gradient_cos hθ]
  simp [coreGradient, smul_smul, smul_neg, mul_comm, sub_eq_add_neg]

theorem weak_gradient_tail {θ f : Space → ℝ} {G : Space → Space}
    (hθ : ContDiff ℝ (⊤ : ENat) θ) (hf : HasWeakGradient f G) :
    HasWeakGradient (fun x => Real.sin (θ x) * f x) (tailGradient θ f G) := by
  have h := hf.mul_smooth hθ.sin
  convert h using 1
  funext x
  rw [angle_gradient_sin hθ]
  simp only [tailGradient, smul_smul]
  rw [mul_comm]

/-- Complex core dotH1, with its actual real and imaginary weak gradients. -/
theorem core_dotH1 {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    InDotH1 (core θ u) (coreGradient θ (fun x => (u x).re) GRe)
      (coreGradient θ (fun x => (u x).im) GIm) := by
  refine ⟨(cos_memLp_top hθ.smooth.continuous).smul hu.function_L6,
    (real_gradients_L2 hθ (hu.function_L6.continuousLinearMap_comp Complex.reCLM)
      hu.real_gradient_L2).1,
    (real_gradients_L2 hθ (hu.function_L6.continuousLinearMap_comp Complex.imCLM)
      hu.imag_gradient_L2).1, ?_, ?_⟩
  · simpa only [core, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using weak_gradient_core hθ.smooth hu.real_weak
  · simpa only [core, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using weak_gradient_core hθ.smooth hu.imag_weak

/-- Complex tail dotH1. No global L2 hypothesis on u is introduced. -/
theorem tail_dotH1 {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    InDotH1 (tail θ u) (tailGradient θ (fun x => (u x).re) GRe)
      (tailGradient θ (fun x => (u x).im) GIm) := by
  refine ⟨(sin_memLp_top hθ.smooth.continuous).smul hu.function_L6,
    (real_gradients_L2 hθ (hu.function_L6.continuousLinearMap_comp Complex.reCLM)
      hu.real_gradient_L2).2,
    (real_gradients_L2 hθ (hu.function_L6.continuousLinearMap_comp Complex.imCLM)
      hu.imag_gradient_L2).2, ?_, ?_⟩
  · simpa only [tail, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using weak_gradient_tail hθ.smooth hu.real_weak
  · simpa only [tail, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using weak_gradient_tail hθ.smooth hu.imag_weak

theorem core_L2 {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    MemLp (core θ u) 2 volume :=
  hu.cutoff_memLp_two hθ.smooth.cos hθ.cos_compact

/-- The IMS error has its L1 domain from the genuine (6,3,2) Holder step. -/
theorem error_integrable {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    Integrable (fun x => ‖u x‖^2 * ‖gradient θ x‖^2) volume := by
  have he := function_smul_angle_gradient_L2 hθ hu.function_L6.norm
  have hi := he.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  simpa only [norm_smul, Real.norm_eq_abs, abs_norm, mul_pow] using hi

end HartreeF.ComplexIMS
