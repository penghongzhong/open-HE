import UniformIMSEstimates

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch CutoffApproximation

/-- Strong finite-Lp convergence of the actual cosine-core. -/
theorem core_error_eLpNorm_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {p : ℝ≥0∞} (hf : MemLp f p volume) (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun x => Real.cos (cutoffAngle n x) • f x - f x) p volume)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (exteriorTail_eLpNorm_tendsto_zero hf hp0 hpt)
  · intro n
    exact bot_le
  · exact core_error_eLpNorm_le_tail hf.aestronglyMeasurable

/-- Strong finite-Lp disappearance of the actual sine-tail. -/
theorem tail_eLpNorm_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {p : ℝ≥0∞} (hf : MemLp f p volume) (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun x => Real.sin (cutoffAngle n x) • f x) p volume)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (exteriorTail_eLpNorm_tendsto_zero hf hp0 hpt)
  · intro n
    exact bot_le
  · exact tail_eLpNorm_le_tail hf.aestronglyMeasurable

/-- The true angle-gradient correction vanishes with only the L6 hypothesis. -/
theorem angle_correction_eLpNorm_tendsto_zero {f : Space → ℝ} (hf : MemLp f 6 volume) :
    Tendsto (fun n => eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume)
      atTop (𝓝 0) := by
  simp_rw [angle_correction_eLpNorm]
  have ht := ENNReal.Tendsto.const_mul (cutoff_gradient_correction_tendsto_zero hf)
    (Or.inr (by simp : ‖-(Real.pi / 2)‖ₑ ≠ ∞))
  simpa only [mul_zero] using ht

/-- The complete cosine-core weak gradient converges strongly in L2. -/
theorem core_gradient_error_eLpNorm_tendsto_zero {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => coreGradient (cutoffAngle n) f G x - G x) 2 volume)
      atTop (𝓝 0) := by
  have ht := (exteriorTail_eLpNorm_tendsto_zero hG (by norm_num) (by norm_num)).add
    (angle_correction_eLpNorm_tendsto_zero hf)
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact bot_le
  · exact core_gradient_error_eLpNorm_le hf hG

/-- The complete sine-tail weak gradient tends strongly to zero in L2. -/
theorem tail_gradient_eLpNorm_tendsto_zero {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) :
    Tendsto (fun n => eLpNorm (tailGradient (cutoffAngle n) f G) 2 volume)
      atTop (𝓝 0) := by
  have ht := (exteriorTail_eLpNorm_tendsto_zero hG (by norm_num) (by norm_num)).add
    (angle_correction_eLpNorm_tendsto_zero hf)
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact bot_le
  · exact tail_gradient_eLpNorm_le hf hG

/-- Actual IMS split with genuine domains and all six homogeneous strong limits. -/
theorem cutoffAngle_strong_approximation {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) :
    (∀ n, InDotH1 (core (cutoffAngle n) u)
      (coreGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (coreGradient (cutoffAngle n) (fun x => (u x).im) GIm) ∧
      InDotH1 (tail (cutoffAngle n) u)
      (tailGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (tailGradient (cutoffAngle n) (fun x => (u x).im) GIm) ∧
      MemLp (core (cutoffAngle n) u) 2 volume) ∧
    Tendsto (fun n => eLpNorm (fun x => core (cutoffAngle n) u x - u x) 6 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (tail (cutoffAngle n) u) 6 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => coreGradient (cutoffAngle n) (fun y => (u y).re) GRe x - GRe x) 2 volume)
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => coreGradient (cutoffAngle n) (fun y => (u y).im) GIm x - GIm x) 2 volume)
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (tailGradient (cutoffAngle n) (fun y => (u y).re) GRe) 2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (tailGradient (cutoffAngle n) (fun y => (u y).im) GIm) 2 volume) atTop (𝓝 0) := by
  have hr := hu.function_L6.continuousLinearMap_comp Complex.reCLM
  have hi := hu.function_L6.continuousLinearMap_comp Complex.imCLM
  refine ⟨?_, core_error_eLpNorm_tendsto_zero hu.function_L6 (by norm_num) (by norm_num),
    tail_eLpNorm_tendsto_zero hu.function_L6 (by norm_num) (by norm_num),
    core_gradient_error_eLpNorm_tendsto_zero hr hu.real_gradient_L2,
    core_gradient_error_eLpNorm_tendsto_zero hi hu.imag_gradient_L2,
    tail_gradient_eLpNorm_tendsto_zero hr hu.real_gradient_L2,
    tail_gradient_eLpNorm_tendsto_zero hi hu.imag_gradient_L2⟩
  intro n
  exact ⟨core_dotH1 (cutoffAngle_valid n) hu, tail_dotH1 (cutoffAngle_valid n) hu,
    core_L2 (cutoffAngle_valid n) hu⟩

#print axioms core_error_eLpNorm_tendsto_zero
#print axioms tail_eLpNorm_tendsto_zero
#print axioms angle_correction_eLpNorm_tendsto_zero
#print axioms core_gradient_error_eLpNorm_tendsto_zero
#print axioms tail_gradient_eLpNorm_tendsto_zero
#print axioms cutoffAngle_strong_approximation
end HartreeF.ComplexIMS
