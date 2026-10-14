import Mathlib

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

/-- Joint a.e. strong measurability gives measurable finite-exponent slice eLpNorms.
This is a conditional product-measure theorem, not a PDE measurability construction. -/
theorem spatial_lp_time_measurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (mu : Measure T) (nu : Measure X) [SigmaFinite mu] [SigmaFinite nu]
    (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (f : T → X → E)
    (hf : AEStronglyMeasurable (fun z : T × X => f z.1 z.2) (mu.prod nu)) :
    AEStronglyMeasurable (fun t => eLpNorm (f t) q nu) mu := by
  have hh := ((hf.enorm.pow_const q.toReal).lintegral_prod_right').pow_const (1 / q.toReal)
  apply hh.aestronglyMeasurable.congr
  filter_upwards [hf.prodMk_left] with t ht
  symm
  exact eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop ht

theorem spatial_lp_time_toReal_measurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (mu : Measure T) (nu : Measure X) [SigmaFinite mu] [SigmaFinite nu]
    (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (f : T → X → E)
    (hf : AEStronglyMeasurable (fun z : T × X => f z.1 z.2) (mu.prod nu)) :
    AEStronglyMeasurable (fun t => (eLpNorm (f t) q nu).toReal) mu :=
  (spatial_lp_time_measurable mu nu q hq0 hqtop f hf).aemeasurable.ennreal_toReal.aestronglyMeasurable

end HartreeF.TimeHolder

