import FActualPathGluing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathGluing
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction

variable {a c b : ℝ}

/-- Every path is exactly recovered from its two actual restrictions. -/
theorem gluePath_restrictions (hac : a ≤ c) (hcb : c ≤ b)
    (w : CriticalPath (intervalMeasure a b)) :
    gluePath hac hcb (restrictPath le_rfl hac hcb w)
      (restrictPath hac hcb le_rfl w) (by rfl) = w := by
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  by_cases ht : (t : ℝ) ≤ c
  · have he := gluedEnergyPath_left hac hcb (restrictPath le_rfl hac hcb w)
      (restrictPath hac hcb le_rfl w) (by rfl) ⟨t, t.property.1, ht⟩
    exact he
  · have he := gluedEnergyPath_right hac hcb (restrictPath le_rfl hac hcb w)
      (restrictPath hac hcb le_rfl w) (by rfl) ⟨t, (lt_of_not_ge ht).le, t.property.2⟩
    exact he

end HartreeF.CriticalPathGluing
