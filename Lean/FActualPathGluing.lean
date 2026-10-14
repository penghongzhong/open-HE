import FCompatiblePathGluing
import FCriticalPathRestriction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathGluing
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction

variable {a c b : ℝ}

/-- Restricting the actual glued graph to its left piece returns the original path. -/
theorem restrict_gluePath_left (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩) :
    restrictPath le_rfl hac hcb (gluePath hac hcb u v hm) = u := by
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  change gluedEnergyPath hac hcb u v hm (t : ℝ) = energyPath _ u t
  exact gluedEnergyPath_left hac hcb u v hm t

/-- The shared endpoint is preserved, including in the right restriction. -/
theorem restrict_gluePath_right (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩) :
    restrictPath hac hcb le_rfl (gluePath hac hcb u v hm) = v := by
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  change gluedEnergyPath hac hcb u v hm (t : ℝ) = energyPath _ v t
  exact gluedEnergyPath_right hac hcb u v hm t

/-- The actual middle state is the common endpoint used in the construction. -/
theorem gluePath_middle (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩) :
    energyPath _ (gluePath hac hcb u v hm) ⟨c, hac, hcb⟩ =
      energyPath _ u ⟨c, hac, le_rfl⟩ :=
  gluedEnergyPath_left hac hcb u v hm ⟨c, hac, le_rfl⟩

end HartreeF.CriticalPathGluing
