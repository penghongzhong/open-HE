import FTimeSliceMeasurability

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

/-- The extended mixed norm retains infinity; no toReal truncation is built in. -/
def mixedNorm {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] (mu : Measure T) (nu : Measure X)
    (p q : ℝ≥0∞) (f : T → X → E) : ℝ≥0∞ :=
  eLpNorm (fun t => eLpNorm (f t) q nu) p mu

/-- Passing to real norms is legitimate only after a.e. finiteness is supplied. -/
theorem finite_extended_norm_bridge {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (p : ℝ≥0∞) (a : T → ℝ≥0∞)
    (ha : AEStronglyMeasurable a mu) (hfin : ∀ᵐ t ∂mu, a t ≠ ∞) :
    eLpNorm a p mu = eLpNorm (fun t => (a t).toReal) p mu := by
  apply eLpNorm_congr_enorm_ae ha ha.aemeasurable.ennreal_toReal.aestronglyMeasurable
  filter_upwards [hfin] with t ht
  simpa only [enorm_eq_self] using (Real.enorm_toReal ht).symm

end HartreeF.TimeHolder
