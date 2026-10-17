import FRieszKernelDerivative
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
F-only static proof candidate. NOT COMPILED; no native verification claim.
The split is literally at |z| < 1 and its complement, for the frozen actual
Riesz kernel and actual vector derivative. No changed cutoff or coordinates.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace HartreeF.RieszL1LocalDomains
open ForcingDomain RieszWeakDerivative RieszKernelDerivative SobolevStretch

variable {E : Type*} [NormedAddCommGroup E]

def nearPart (k : Space → E) : Space → E := (Metric.ball 0 1).indicator k

def farPart (k : Space → E) : Space → E := (Metric.ball 0 1)ᶜ.indicator k

theorem nearPart_add_farPart (k : Space → E) (x : Space) :
    nearPart k x + farPart k x = k x := by
  classical
  by_cases hx : x ∈ Metric.ball (0 : Space) 1 <;> simp [nearPart, farPart, hx]

theorem nearPart_aestronglyMeasurable {k : Space → E}
    (hk : AEStronglyMeasurable k volume) :
    AEStronglyMeasurable (nearPart k) volume :=
  hk.indicator measurableSet_ball

theorem farPart_aestronglyMeasurable {k : Space → E}
    (hk : AEStronglyMeasurable k volume) :
    AEStronglyMeasurable (farPart k) volume :=
  hk.indicator measurableSet_ball.compl

variable [MeasurableSpace E]

theorem nearPart_measurable {k : Space → E} (hk : Measurable k) :
    Measurable (nearPart k) := hk.indicator measurableSet_ball

theorem farPart_measurable {k : Space → E} (hk : Measurable k) :
    Measurable (farPart k) := hk.indicator measurableSet_ball.compl

theorem near_rieszKernel_integrable {α c : ℝ} (hα : 0 < α) :
    Integrable (nearPart (rieszKernel α c)) volume := by
  rw [nearPart, integrable_indicator_iff measurableSet_ball]
  exact ((rieszKernel_locallyIntegrable hα c).integrableOn_isCompact
    (isCompact_closedBall (0 : Space) 1)).mono_set Metric.ball_subset_closedBall

theorem near_rieszKernelGradient_integrable {α c : ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) :
    Integrable (nearPart (rieszKernelGradient α c)) volume := by
  rw [nearPart, integrable_indicator_iff measurableSet_ball]
  exact ((rieszKernelGradient_locallyIntegrable hα1 hα3 hc).integrableOn_isCompact
    (isCompact_closedBall (0 : Space) 1)).mono_set Metric.ball_subset_closedBall

theorem rieszKernel_norm {α c : ℝ} (hc : 0 < c) (z : Space) :
    ‖rieszKernel α c z‖ = c * ‖z‖ ^ (α - 3) := by
  simp only [rieszKernel, Real.norm_eq_abs, abs_mul, abs_of_pos hc,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]

theorem far_rieszKernel_norm_le {α c : ℝ}
    (hα3 : α < 3) (hc : 0 < c) (z : Space) :
    ‖farPart (rieszKernel α c) z‖ ≤ c := by
  classical
  by_cases hz : z ∈ Metric.ball (0 : Space) 1
  · simp [farPart, hz, hc.le]
  · have hn : 1 ≤ ‖z‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
    rw [farPart, Set.indicator_of_mem (Set.mem_compl hz), rieszKernel_norm hc]
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)) hc.le).trans_eq (mul_one c)

theorem far_rieszKernelGradient_norm_le {α c : ℝ}
    (hα3 : α < 3) (hc : 0 < c) (z : Space) :
    ‖farPart (rieszKernelGradient α c) z‖ ≤ c * (3 - α) := by
  classical
  have hC : 0 ≤ c * (3 - α) := mul_nonneg hc.le (by linarith)
  by_cases hz : z ∈ Metric.ball (0 : Space) 1
  · simp [farPart, hz, hC]
  · have hn : 1 ≤ ‖z‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
    rw [farPart, Set.indicator_of_mem (Set.mem_compl hz), rieszKernelGradient_norm hα3 hc]
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)) hC).trans_eq (mul_one _)

end HartreeF.RieszL1LocalDomains
