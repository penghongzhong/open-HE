import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.FreeTimeDecay

/-- A finite time-L12 budget rules out persistent spikes of a uniformly continuous
nonnegative real function. The proof uses actual positive-length intervals. -/
theorem uniformContinuous_integrable_pow_tendsto_zero_atTop {f : ℝ → ℝ}
    (hu : UniformContinuous f) (hpos : ∀ t, 0≤f t)
    (hi : Integrable (fun t => f t^12) volume) : Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun t => ha.trans_le (hpos t))
  · intro eps heps
    obtain ⟨delta,hdelta,huc⟩ := Metric.uniformContinuous_iff.mp hu (eps/2) (half_pos heps)
    have hc : 0<(eps/2)^12*(delta/2) := by positivity
    have ht : Tendsto (fun t : ℝ => ∫ s in Ioi t, f s^12) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    filter_upwards [ht.eventually (gt_mem_nhds hc)] with t ht
    by_contra hlt
    have hlarge : eps≤f t := le_of_not_gt hlt
    have hnear (s : ℝ) (hs : s∈Ioc t (t+delta/2)) : eps/2 ≤ f s := by
      have hdist : dist s t<delta := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs.1)]
        linarith [hs.2]
      have hh := huc hdist
      rw [Real.dist_eq] at hh
      have hh' := (abs_lt.mp hh).1
      linarith
    have hlower : (eps/2)^12*(delta/2) ≤ ∫ s in Ioc t (t+delta/2), f s^12 := by
      have hh := setIntegral_ge_of_const_le_real (μ:=volume) measurableSet_Ioc
        (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        (fun s hs => pow_le_pow_left₀ (half_pos heps).le (hnear s hs) 12) hi.integrableOn
      simpa only [Real.volume_real_Ioc_of_le (by linarith : t≤t+delta/2), add_sub_cancel_left] using hh
    have hupper : (∫ s in Ioc t (t+delta/2), f s^12) ≤ ∫ s in Ioi t, f s^12 :=
      setIntegral_mono_set hi.integrableOn
        (Eventually.of_forall (fun s => pow_nonneg (hpos s) 12))
        (Eventually.of_forall (fun s hs => hs.1))
    exact (not_lt_of_ge (hlower.trans hupper)) ht

/-- The identical positive-interval argument on the negative tail. -/
theorem uniformContinuous_integrable_pow_tendsto_zero_atBot {f : ℝ → ℝ}
    (hu : UniformContinuous f) (hpos : ∀ t, 0≤f t)
    (hi : Integrable (fun t => f t^12) volume) : Tendsto f atBot (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun t => ha.trans_le (hpos t))
  · intro eps heps
    obtain ⟨delta,hdelta,huc⟩ := Metric.uniformContinuous_iff.mp hu (eps/2) (half_pos heps)
    have hc : 0<(eps/2)^12*(delta/2) := by positivity
    have ht : Tendsto (fun t : ℝ => ∫ s in Iio t, f s^12) atBot (𝓝 0) :=
      tendsto_integral_Iio_zero tendsto_id
    filter_upwards [ht.eventually (gt_mem_nhds hc)] with t ht
    by_contra hlt
    have hlarge : eps≤f t := le_of_not_gt hlt
    have hnear (s : ℝ) (hs : s∈Ico (t-delta/2) t) : eps/2 ≤ f s := by
      have hdist : dist s t<delta := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs.2)]
        linarith [hs.1]
      have hh := huc hdist
      rw [Real.dist_eq] at hh
      have hh' := (abs_lt.mp hh).1
      linarith
    have hlower : (eps/2)^12*(delta/2) ≤ ∫ s in Ico (t-delta/2) t, f s^12 := by
      have hh := setIntegral_ge_of_const_le_real (μ:=volume) measurableSet_Ico
        (by simp only [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
        (fun s hs => pow_le_pow_left₀ (half_pos heps).le (hnear s hs) 12) hi.integrableOn
      simpa only [Real.volume_real_Ico_of_le (by linarith : t-delta/2≤t), sub_sub_cancel] using hh
    have hupper : (∫ s in Ico (t-delta/2) t, f s^12) ≤ ∫ s in Iio t, f s^12 :=
      setIntegral_mono_set hi.integrableOn
        (Eventually.of_forall (fun s => pow_nonneg (hpos s) 12))
        (Eventually.of_forall (fun s hs => hs.2))
    exact (not_lt_of_ge (hlower.trans hupper)) ht

#print axioms uniformContinuous_integrable_pow_tendsto_zero_atTop
#print axioms uniformContinuous_integrable_pow_tendsto_zero_atBot
end HartreeF.FreeTimeDecay
