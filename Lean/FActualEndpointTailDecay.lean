import FActualYoungEndpointSource
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.MassAsymptotics
open MassRecovery

variable {E : Type*} [NormedAddCommGroup E]

/-- The tail norm is the norm of the actual indicator L2 class, not a totalized infinite norm. -/
theorem tailNorm_eq_sqrt_integral (F : Lp E 2 (volume : Measure ℝ)) (t : ℝ) :
    tailNorm t F = Real.sqrt (∫ s in Ici t, ‖F s‖^2) := by
  rw [tailNorm_eq_restricted,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) ((Lp.memLp F).restrict (Ici t))]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)

theorem tailNorm_nonneg (F : Lp E 2 (volume : Measure ℝ)) (t : ℝ) : 0 ≤ tailNorm t F :=
  norm_nonneg _

theorem tailNorm_le_norm (F : Lp E 2 (volume : Measure ℝ)) (t : ℝ) : tailNorm t F ≤ ‖F‖ := by
  change ‖tailSource t F‖ ≤ ‖F‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [tailSource_coe t F] with s hs
  rw [hs]
  exact norm_indicator_le_norm_self (F : ℝ → E) s

theorem actual_square_integrable (F : Lp E 2 (volume : Measure ℝ)) :
    Integrable (fun s : ℝ => ‖F s‖^2) volume :=
  (Lp.memLp F).integrable_norm_pow (by norm_num)

/-- Actual finite-L2 halfline tails vanish along all real times, not just a subsequence. -/
theorem tailNorm_tendsto_zero (F : Lp E 2 (volume : Measure ℝ)) :
    Tendsto (fun t : ℝ => tailNorm t F) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => ∫ s in Ici t, ‖F s‖^2) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_zero, ← tailNorm_eq_sqrt_integral] using hr

/-- In particular the actual original L2_t L1_x source has vanishing future tail. -/
theorem endpointOne_tail_tendsto_zero (F : EndpointOne) :
    Tendsto (fun t : ℝ => tailNorm t F) atTop (𝓝 0) := tailNorm_tendsto_zero F

end HartreeF.MassAsymptotics
