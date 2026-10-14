import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option warningAsError true
open scoped NNReal
namespace HartreeF.CriticalPathBall

/-- Convert an actual norm difference estimate to contraction on a preserved
subset, before instantiating the larger concrete path-space structure. -/
theorem half_contracting_restrict {E : Type*} [NormedAddCommGroup E]
    (S : Set E) (Φ : E → E) (hself : Set.MapsTo Φ S S)
    (hcontract : ∀ u ∈ S, ∀ v ∈ S, ‖Φ u - Φ v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖) :
    ContractingWith (1 / 2 : ℝ≥0) (hself.restrict Φ S S) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  change dist (Φ u.val) (Φ v.val) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist u.val v.val
  rw [dist_eq_norm, dist_eq_norm]
  change ‖Φ u.val - Φ v.val‖ ≤ (1 / 2 : ℝ) * ‖u.val - v.val‖
  exact hcontract u.val u.property v.val v.property

end HartreeF.CriticalPathBall
