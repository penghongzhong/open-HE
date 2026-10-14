import UniformIMSConvergence

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch CutoffApproximation

/-- The actual squared-norm integral is the square of its finite L2 seminorm. -/
theorem integral_norm_sq_eq_eLpNorm_sq {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖^2) = (eLpNorm f 2 volume).toReal^2 := by
  have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
    hf.aestronglyMeasurable
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at hpow
  rw [← ENNReal.toReal_pow, hpow]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => sq_nonneg ‖f x‖))
    (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The literal IMS error integral tends to zero without global L2 of the field. -/
theorem ims_error_integral_tendsto_zero {u : Space → ℂ} (hu : MemLp u 6 volume) :
    Tendsto (fun n => ∫ x, ‖u x‖^2 * ‖gradient (cutoffAngle n) x‖^2)
      atTop (𝓝 0) := by
  have hlim := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
    (angle_correction_eLpNorm_tendsto_zero hu.norm)
  have hs := hlim.pow 2
  simp only [ENNReal.toReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  convert hs using 1
  ext n
  have he := function_smul_angle_gradient_L2 (cutoffAngle_valid n) hu.norm
  have hsq := integral_norm_sq_eq_eLpNorm_sq he
  simpa only [norm_smul, Real.norm_eq_abs, abs_norm, mul_pow, Function.comp_apply] using hsq

/-- Squared L2 norms of complete sine-tail weak gradients vanish. -/
theorem tail_gradient_energy_tendsto_zero {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) :
    Tendsto (fun n => ∫ x, ‖tailGradient (cutoffAngle n) f G x‖^2) atTop (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
    (tail_gradient_eLpNorm_tendsto_zero hf hG)
  have hs := ht.pow 2
  simp only [ENNReal.toReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  convert hs using 1
  ext n
  exact integral_norm_sq_eq_eLpNorm_sq (real_gradients_L2 (cutoffAngle_valid n) hf hG).2

/-- The actual complex sine-tail kinetic energy disappears. -/
theorem tail_kinetic_tendsto_zero {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) :
    Tendsto (fun n => kinetic
      (tailGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (tailGradient (cutoffAngle n) (fun x => (u x).im) GIm)) atTop (𝓝 0) := by
  have hr := hu.function_L6.continuousLinearMap_comp Complex.reCLM
  have hi := hu.function_L6.continuousLinearMap_comp Complex.imCLM
  have hs := (tail_gradient_energy_tendsto_zero hr hu.real_gradient_L2).add
    (tail_gradient_energy_tendsto_zero hi hu.imag_gradient_L2)
  simp only [zero_add] at hs
  convert hs using 1
  ext n
  unfold kinetic
  simp only [complexGradient_norm_sq]
  exact integral_add
    ((real_gradients_L2 (cutoffAngle_valid n) hr hu.real_gradient_L2).2.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    ((real_gradients_L2 (cutoffAngle_valid n) hi hu.imag_gradient_L2).2.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))

/-- Exact IMS together with vanishing tail and error gives core kinetic convergence. -/
theorem core_kinetic_tendsto {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) :
    Tendsto (fun n => kinetic
      (coreGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (coreGradient (cutoffAngle n) (fun x => (u x).im) GIm))
      atTop (𝓝 (kinetic GRe GIm)) := by
  have ht := ((tendsto_const_nhds (x := kinetic GRe GIm)).add (ims_error_integral_tendsto_zero hu.function_L6)).sub
    (tail_kinetic_tendsto_zero hu)
  simp only [add_zero, sub_zero] at ht
  convert ht using 1
  ext n
  linarith [(cutoffAngle_ims hu n).2.2.2]

#print axioms integral_norm_sq_eq_eLpNorm_sq
#print axioms ims_error_integral_tendsto_zero
#print axioms tail_gradient_energy_tendsto_zero
#print axioms tail_kinetic_tendsto_zero
#print axioms core_kinetic_tendsto
end HartreeF.ComplexIMS
