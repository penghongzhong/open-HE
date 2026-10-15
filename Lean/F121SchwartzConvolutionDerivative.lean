import F121SchwartzLocalMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Paper121SmoothConvolution
open EnergySpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- The literal integral, also for derivative kernels taking values in real linear maps. -/
def kernelIntegral (k : 𝓢(V, E)) (f : V → ℂ) (x : V) : E :=
  ∫ y : V, f y • k (x-y)

omit [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
theorem kernel_integrand_measurable (k : 𝓢(V, E)) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) (x : V) :
    AEStronglyMeasurable (fun y : V => f y • k (x-y)) volume :=
  hf.smul (k.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable

omit [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
theorem kernel_integrand_integrable (k : 𝓢(V, E)) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) {d : ℕ}
    (hw : Integrable (fun y : V => ‖f y‖*(1+‖y‖)^(-(d : ℝ))) volume) (x : V) :
    Integrable (fun y : V => f y • k (x-y)) volume := by
  obtain ⟨C, _, hC⟩ := schwartz_local_majorant k d x
  refine (hw.const_mul C).mono' (kernel_integrand_measurable k hf x) ?_
  filter_upwards with y
  rw [norm_smul]
  calc
    _ ≤ ‖f y‖*(C*(1+‖y‖)^(-(d : ℝ))) :=
      mul_le_mul_of_nonneg_left (hC x (Metric.mem_ball_self zero_lt_one) y) (norm_nonneg _)
    _ = _ := by ring

/-- Differentiation of the actual convolution integral under a proved local integrable bound. -/
theorem kernelIntegral_hasFDerivAt (k : 𝓢(V, E)) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) {d : ℕ}
    (hw : Integrable (fun y : V => ‖f y‖*(1+‖y‖)^(-(d : ℝ))) volume) (x₀ : V) :
    HasFDerivAt (kernelIntegral k f)
      (kernelIntegral (SchwartzMap.fderivCLM ℂ V E k) f x₀) x₀ := by
  let Dk := SchwartzMap.fderivCLM ℂ V E k
  obtain ⟨C, _, hC⟩ := schwartz_local_majorant Dk d x₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x₀ 1) (bound := fun y : V => C*(‖f y‖*(1+‖y‖)^(-(d : ℝ))))
    (F' := fun x y : V => f y • Dk (x-y))
    (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall (kernel_integrand_measurable k hf)
  · exact kernel_integrand_integrable k hf hw x₀
  · exact kernel_integrand_measurable Dk hf x₀
  · filter_upwards with y
    intro x hx
    rw [norm_smul]
    calc
      _ ≤ ‖f y‖*(C*(1+‖y‖)^(-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left (hC x hx y) (norm_nonneg _)
      _ = _ := by ring
  · exact hw.const_mul C
  · filter_upwards with y
    intro x _
    have h := (k.hasFDerivAt (x-y)).comp x ((hasFDerivAt_id x).sub_const y)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, Pi.smul_def,
      Dk, SchwartzMap.fderivCLM_apply] using h.const_smul (f y)

end HartreeF.Paper121SmoothConvolution
