import F121LpRealTimeTails
import FActualDifferenceNormExhaustion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HartreeF.IntervalNormExhaustion
open TimeHolder RealTimeTails

/-- A constructed actual nested-Lp representative yields literal right-half-line
mixed-norm decay. The finite exponent is a time exponent, never a mass input. -/
theorem actualNestedLpBound_Ici_tail {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (ν : Measure X) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hp : p ≠ ∞)
    {T C : ℝ} {g : ℝ → X → E} (h : ActualNestedLpBound ν p r (Ici T) g C) :
    Tendsto (fun a : ℝ => mixedNorm (volume.restrict (Ici a)) ν p r g) atTop (𝓝 0) := by
  obtain ⟨F,_,hactual,_⟩ := h
  apply (lp_restrict_Ici_tendsto_zero hp F).congr'
  filter_upwards [eventually_ge_atTop T] with a ha
  have hlocal := ae_mono (Measure.restrict_mono_set volume (Ici_subset_Ici.mpr ha)) hactual
  symm
  calc
    _ = eLpNorm (fun t => ‖F t‖ₑ) p (volume.restrict (Ici a)) := by
      apply eLpNorm_congr_ae
      filter_upwards [hlocal] with t ht
      exact (eLpNorm_congr_ae ht.symm).trans (Lp.enorm_def _).symm
    _ = eLpNorm F p (volume.restrict (Ici a)) :=
      eLpNorm_enorm _ ((Lp.aestronglyMeasurable F).mono_measure Measure.restrict_le_self)

/-- The corresponding literal negative-time tail for the same actual field. -/
theorem actualNestedLpBound_Iic_tail {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (ν : Measure X) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hp : p ≠ ∞)
    {T C : ℝ} {g : ℝ → X → E} (h : ActualNestedLpBound ν p r (Iic T) g C) :
    Tendsto (fun a : ℝ => mixedNorm (volume.restrict (Iic a)) ν p r g) atBot (𝓝 0) := by
  obtain ⟨F,_,hactual,_⟩ := h
  apply (lp_restrict_Iic_tendsto_zero hp F).congr'
  filter_upwards [eventually_le_atBot T] with a ha
  have hlocal := ae_mono (Measure.restrict_mono_set volume (Iic_subset_Iic.mpr ha)) hactual
  symm
  calc
    _ = eLpNorm (fun t => ‖F t‖ₑ) p (volume.restrict (Iic a)) := by
      apply eLpNorm_congr_ae
      filter_upwards [hlocal] with t ht
      exact (eLpNorm_congr_ae ht.symm).trans (Lp.enorm_def _).symm
    _ = eLpNorm F p (volume.restrict (Iic a)) :=
      eLpNorm_enorm _ ((Lp.aestronglyMeasurable F).mono_measure Measure.restrict_le_self)

end HartreeF.IntervalNormExhaustion
