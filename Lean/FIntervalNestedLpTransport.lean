import FIntervalTimeTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.IntervalTimeTransport

/-- Nested spatial representative transport, with the Lp class equality
converted to pointwise equality before any nonlinear field is substituted. -/
theorem toLocalLp_nested_coeFn {a b : ℝ} (hab : a ≤ b)
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (p q : ℝ≥0∞) [Fact (1 ≤ q)] (ν : Measure X)
    (f : Lp (Lp E q ν) p (CriticalPathSpace.intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, (toLocalLp hab p f t : X → E) =ᵐ[ν]
      (f (Set.projIcc a b hab t) : X → E) := by
  filter_upwards [toLocalLp_coeFn hab p f] with t ht
  exact Eventually.of_forall (fun x => congrArg (fun v : Lp E q ν => v x) ht)

end HartreeF.IntervalTimeTransport
