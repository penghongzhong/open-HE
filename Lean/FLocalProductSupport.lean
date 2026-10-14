import FCompactCrossCylinder
import FCompactCrossFrameGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.LocalProfileProducts
open TimeHolder CompactCross CriticalAffine AffineMixed

/-- A jointly continuous field supported in a finite cylinder has its literal extended
mixed norm bounded by the amplitude times the exact spatial and temporal volumes. -/
theorem cylinder_mixed_bound {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    {S : Set Space} {I : Set ℝ} (hS : MeasurableSet S) (hI : MeasurableSet I)
    (hSf : volume S ≠ ∞) (_hIf : volume I ≠ ∞)
    {F : ℝ → Space → ℝ}
    (hF : Continuous (fun z : ℝ × Space => F z.1 z.2))
    (hbound : ∀ t x, ‖F t x‖ ≤ M)
    (hspace : ∀ t x, x ∉ S → F t x = 0)
    (htime : ∀ t, t ∉ I → ∀ x, F t x = 0) :
    mixedNorm volume volume 5 (ENNReal.ofReal q) F ≤
      ENNReal.ofReal M * volume S ^ (1/q) * volume I ^ (1/5 : ℝ) := by
  have hslice (t : ℝ) := finite_support_lp_bound volume hq hM hS hSf
    (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (hbound t) (hspace t)
  have hnmeas := spatial_lp_time_measurable volume volume (ENNReal.ofReal q)
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top F hF.aestronglyMeasurable
  have hzero (t : ℝ) (ht : t ∉ I) : F t = 0 := funext (htime t ht)
  have hnorm : mixedNorm volume volume 5 (ENNReal.ofReal q) F ≤
      eLpNorm (I.indicator (fun _ : ℝ => ENNReal.ofReal M * volume S ^ (1/q))) 5 volume := by
    apply eLpNorm_mono_enorm_ae hnmeas
    filter_upwards [] with t
    simp only [enorm_eq_self]
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      exact (hslice t).2
    · rw [indicator_of_notMem ht, hzero t ht]
      simp
  rw [eLpNorm_indicator_const hI.nullMeasurableSet (by norm_num) (by norm_num)] at hnorm
  norm_num only [enorm_eq_self, ENNReal.toReal_ofNat] at hnorm
  exact hnorm

/-- The support budget is finite before any conversion to a real constant. -/
theorem cylinder_budget_ne_top {q : ℝ} (hq : 0 < q)
    {S : Set Space} {I : Set ℝ} (hSf : volume S ≠ ∞) (hIf : volume I ≠ ∞) (M : ℝ) :
    ENNReal.ofReal M * volume S ^ (1/q) * volume I ^ (1/5 : ℝ) ≠ ∞ := by
  have hq' : 0 ≤ 1/q := by positivity
  finiteness

#print axioms cylinder_mixed_bound
#print axioms cylinder_budget_ne_top
end HartreeF.LocalProfileProducts
