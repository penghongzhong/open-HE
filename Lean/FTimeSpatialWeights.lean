import FTimeCriticalHolder
import FTimeValueDifferenceHolder
import FTimeMixedHolder
import FTimeSliceMeasurability
import HartreeGradientMajorantSum

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory GradientMajorants
open scoped ENNReal NNReal

/-- The literal real slice norm used by the accepted C26 weights is time measurable.
As in C26, interpreting `toReal` as a finite norm requires separate slice MemLp data. -/
theorem spatial_norm_time_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] {q : ℝ} (hq : 0 < q)
    (V : T → Space → ℝ)
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun t => spatialNorm q (V t)) mu := by
  exact spatial_lp_time_toReal_measurable mu volume (ENNReal.ofReal q)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top V hV

theorem norm_spatialNorm (q : ℝ) (f : Space → ℝ) :
    ‖spatialNorm q f‖ = spatialNorm q f :=
  Real.norm_of_nonneg (spatialNorm_nonneg q f)

/-- Time integration of the literal C26 single weight; no interval-length loss. -/
theorem single_weight_time_bound {alpha : ℝ} (ha : 0 < alpha)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (V Z : T → Space → ℝ)
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hZ : AEStronglyMeasurable (fun z : T × Space => Z z.1 z.2) (mu.prod volume)) :
    eLpNorm (fun t => singleWeight alpha (V t) (Z t)) 2 mu ≤
      eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ^ (2 * alpha) *
      eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ^ (4 : ℝ) *
      eLpNorm (fun t => spatialNorm (30/13) (Z t)) 10 mu := by
  have hh := temporal_critical_holder ha mu
    (fun t => spatialNorm 6 (V t)) (fun t => spatialNorm 10 (V t))
    (fun t => spatialNorm (30/13) (Z t))
    (spatial_norm_time_measurable mu (by norm_num) V hV)
    (spatial_norm_time_measurable mu (by norm_num) V hV)
    (spatial_norm_time_measurable mu (by norm_num) Z hZ)
  simpa only [singleWeight, norm_spatialNorm] using hh

/-- Time integration of the literal C26 spacetime difference weight. -/
theorem spacetime_difference_weight_time_bound {alpha : ℝ} (ha : 0 < alpha)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (V W Y : T → Space → ℝ)
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hW : AEStronglyMeasurable (fun z : T × Space => W z.1 z.2) (mu.prod volume))
    (hY : AEStronglyMeasurable (fun z : T × Space => Y z.1 z.2) (mu.prod volume)) :
    eLpNorm (fun t => spacetimeDifferenceWeight alpha (V t) (W t) (Y t)) 2 mu ≤
      eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ^ (2 * alpha) *
      eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ^ (3 : ℝ) *
      eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu *
      eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu := by
  have hh := temporal_value_difference_holder ha mu
    (fun t => spatialNorm 6 (V t)) (fun t => spatialNorm 10 (V t))
    (fun t => spatialNorm (30/13) (Y t)) (fun t => spatialNorm 10 (W t))
    (spatial_norm_time_measurable mu (by norm_num) V hV)
    (spatial_norm_time_measurable mu (by norm_num) V hV)
    (spatial_norm_time_measurable mu (by norm_num) Y hY)
    (spatial_norm_time_measurable mu (by norm_num) W hW)
  simpa only [spacetimeDifferenceWeight, norm_spatialNorm, mul_assoc] using hh

/-- Time integration of the exact C26 mixed allocation theta = (3-alpha)/3. -/
theorem mixed_difference_weight_time_bound {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (V W Y : T → Space → ℝ)
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hW : AEStronglyMeasurable (fun z : T × Space => W z.1 z.2) (mu.prod volume))
    (hY : AEStronglyMeasurable (fun z : T × Space => Y z.1 z.2) (mu.prod volume)) :
    eLpNorm (fun t => mixedDifferenceWeight alpha (V t) (W t) (Y t)) 2 mu ≤
      eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ^ (5 * alpha / 3) *
      eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ^ (4 - theta alpha) *
      eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu *
      eLpNorm (fun t => spatialNorm 6 (W t)) ∞ mu ^ (alpha / 3) *
      eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu ^ theta alpha := by
  have ht0 : 0 < theta alpha := by dsimp [theta]; linarith
  have ht4 : theta alpha < 4 := by dsimp [theta]; linarith
  have hh := temporal_uniform_difference_holder ha ht0 ht4 mu
    (fun t => spatialNorm 6 (V t)) (fun t => spatialNorm 10 (V t))
    (fun t => spatialNorm 6 (W t)) (fun t => spatialNorm 10 (W t))
    (fun t => spatialNorm (30/13) (Y t))
    (spatial_norm_time_measurable mu (by norm_num) V hV)
    (spatial_norm_time_measurable mu (by norm_num) V hV)
    (spatial_norm_time_measurable mu (by norm_num) W hW)
    (spatial_norm_time_measurable mu (by norm_num) W hW)
    (spatial_norm_time_measurable mu (by norm_num) Y hY)
  simpa only [mixedDifferenceWeight, norm_spatialNorm, mul_assoc, mul_left_comm, mul_comm] using hh

end HartreeF.TimeHolder
