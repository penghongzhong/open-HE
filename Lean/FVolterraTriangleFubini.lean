import FL1RetardedScalarIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set

namespace HartreeF.VolterraTriangle

/-- The physical retarded triangle is always `source time < observation time`. -/
def kernel (H : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  {p : ℝ × ℝ | p.1 < p.2}.indicator H

theorem measurableSet_triangle : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
  measurableSet_lt measurable_fst measurable_snd

theorem kernel_past (H : ℝ × ℝ → ℂ) (t : ℝ) :
    (fun s => kernel H (s, t)) = (Iio t).indicator (fun s => H (s, t)) := by
  classical
  funext s
  simp only [kernel, indicator_apply, mem_ofPred_eq, mem_Iio]

theorem kernel_future (H : ℝ × ℝ → ℂ) (s : ℝ) :
    (fun t => kernel H (s, t)) = (Ioi s).indicator (fun t => H (s, t)) := by
  classical
  funext t
  simp only [kernel, indicator_apply, mem_ofPred_eq, mem_Ioi]

theorem kernel_integrable {μ ν : Measure ℝ} {H : ℝ × ℝ → ℂ}
    (hH : Integrable H (μ.prod ν)) : Integrable (kernel H) (μ.prod ν) :=
  hH.indicator measurableSet_triangle

theorem kernel_past_integral (μ : Measure ℝ) (H : ℝ × ℝ → ℂ) (t : ℝ) :
    (∫ s, kernel H (s, t) ∂μ) = ∫ s in Iio t, H (s, t) ∂μ := by
  rw [kernel_past, integral_indicator measurableSet_Iio]

theorem kernel_future_integral (ν : Measure ℝ) (H : ℝ × ℝ → ℂ) (s : ℝ) :
    (∫ t, kernel H (s, t) ∂ν) = ∫ t in Ioi s, H (s, t) ∂ν := by
  rw [kernel_future, integral_indicator measurableSet_Ioi]

/-- Integrating an integrable product kernel over the retarded past produces an
integrable function of observation time. -/
theorem past_integral_integrable {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {H : ℝ × ℝ → ℂ} (hH : Integrable H (μ.prod ν)) :
    Integrable (fun t => ∫ s in Iio t, H (s, t) ∂μ) ν := by
  simpa only [kernel_past_integral] using (kernel_integrable hH).integral_prod_right

/-- Integrating the same triangle in the other direction produces an integrable
function of source time. -/
theorem future_integral_integrable {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {H : ℝ × ℝ → ℂ} (hH : Integrable H (μ.prod ν)) :
    Integrable (fun s => ∫ t in Ioi s, H (s, t) ∂ν) μ := by
  simpa only [kernel_future_integral] using (kernel_integrable hH).integral_prod_left

/-- Native Fubini on the strict retarded triangle, keeping the same physical
region on both sides. -/
theorem integral_past_eq_integral_future {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {H : ℝ × ℝ → ℂ} (hH : Integrable H (μ.prod ν)) :
    (∫ t, ∫ s in Iio t, H (s, t) ∂μ ∂ν) =
      ∫ s, ∫ t in Ioi s, H (s, t) ∂ν ∂μ := by
  simpa only [kernel_past_integral, kernel_future_integral] using
    (integral_integral_swap (f := fun s t => kernel H (s, t))
      (kernel_integrable hH)).symm

/-- Restricting the interval measure to the past is exactly the literal retarded region. -/
theorem restrict_interval_past (a b t : ℝ) :
    (volume.restrict (Icc a b)).restrict (Iio t) =
      volume.restrict (Icc a b ∩ Iio t) := by
  rw [Measure.restrict_restrict measurableSet_Iio, inter_comm]

/-- Restricting the interval measure to the future is exactly the transposed region. -/
theorem restrict_interval_future (a b s : ℝ) :
    (volume.restrict (Icc a b)).restrict (Ioi s) =
      volume.restrict (Icc a b ∩ Ioi s) := by
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_comm]

theorem integral_interval_past (a b t : ℝ) (f : ℝ → ℂ) :
    (∫ s in Iio t, f s ∂volume.restrict (Icc a b)) =
      ∫ s in Icc a b ∩ Iio t, f s := by
  rw [restrict_interval_past]

theorem integral_interval_future (a b s : ℝ) (f : ℝ → ℂ) :
    (∫ t in Ioi s, f t ∂volume.restrict (Icc a b)) =
      ∫ t in Icc a b ∩ Ioi s, f t := by
  rw [restrict_interval_future]

/-- The literal finite-interval retarded integrals are integrable and can be
swapped using only integrability of the original two-variable kernel. -/
theorem interval_triangle_fubini {a b : ℝ} {H : ℝ × ℝ → ℂ}
    (hH : Integrable H ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc a b)))) :
    IntegrableOn (fun t => ∫ s in Icc a b ∩ Iio t, H (s, t)) (Icc a b) ∧
    IntegrableOn (fun s => ∫ t in Icc a b ∩ Ioi s, H (s, t)) (Icc a b) ∧
    (∫ t in Icc a b, ∫ s in Icc a b ∩ Iio t, H (s, t)) =
      ∫ s in Icc a b, ∫ t in Icc a b ∩ Ioi s, H (s, t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [IntegrableOn, integral_interval_past] using past_integral_integrable hH
  · simpa only [IntegrableOn, integral_interval_future] using future_integral_integrable hH
  · simpa only [integral_interval_past, integral_interval_future] using
      integral_past_eq_integral_future hH

end HartreeF.VolterraTriangle

#check @HartreeF.VolterraTriangle.kernel
#check @HartreeF.VolterraTriangle.measurableSet_triangle
#check @HartreeF.VolterraTriangle.kernel_past
#check @HartreeF.VolterraTriangle.kernel_future
#check @HartreeF.VolterraTriangle.kernel_integrable
#check @HartreeF.VolterraTriangle.kernel_past_integral
#check @HartreeF.VolterraTriangle.kernel_future_integral
#check @HartreeF.VolterraTriangle.past_integral_integrable
#check @HartreeF.VolterraTriangle.future_integral_integrable
#check @HartreeF.VolterraTriangle.integral_past_eq_integral_future
#check @HartreeF.VolterraTriangle.restrict_interval_past
#check @HartreeF.VolterraTriangle.restrict_interval_future
#check @HartreeF.VolterraTriangle.integral_interval_past
#check @HartreeF.VolterraTriangle.integral_interval_future
#check @HartreeF.VolterraTriangle.interval_triangle_fubini
#print axioms HartreeF.VolterraTriangle.kernel
#print axioms HartreeF.VolterraTriangle.measurableSet_triangle
#print axioms HartreeF.VolterraTriangle.kernel_past
#print axioms HartreeF.VolterraTriangle.kernel_future
#print axioms HartreeF.VolterraTriangle.kernel_integrable
#print axioms HartreeF.VolterraTriangle.kernel_past_integral
#print axioms HartreeF.VolterraTriangle.kernel_future_integral
#print axioms HartreeF.VolterraTriangle.past_integral_integrable
#print axioms HartreeF.VolterraTriangle.future_integral_integrable
#print axioms HartreeF.VolterraTriangle.integral_past_eq_integral_future
#print axioms HartreeF.VolterraTriangle.restrict_interval_past
#print axioms HartreeF.VolterraTriangle.restrict_interval_future
#print axioms HartreeF.VolterraTriangle.integral_interval_past
#print axioms HartreeF.VolterraTriangle.integral_interval_future
#print axioms HartreeF.VolterraTriangle.interval_triangle_fubini
