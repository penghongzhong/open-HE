import FActualWPartition
import FL10PartitionAssembly

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HartreeF.ActualPathPartitions
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open TimePartition CriticalJointSources
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields criticalGradient

/-- The same whole path is controlled by actual bounds on its restrictions.
This is the assembly step; later PDE consumers must produce the piece bounds. -/
theorem actual_path_norm_le_of_piece_bounds {a b B C : ℝ} (hab : a ≤ b)
    (P : Partition a b) (q : CriticalPath (intervalMeasure a b)) (hC : 0 ≤ C)
    (hE : ‖energyPath (intervalMeasure a b) q‖ ≤ B)
    (hp : ∀ i : Fin P.count, ‖piecePath P q i‖ ≤ C) :
    ‖q‖ ≤ max B ((P.count : ℝ) * C) := by
  rw [criticalPath_norm]
  apply max_le
  · exact hE.trans (le_max_left _ _)
  · apply (pi_norm_le_iff_of_nonneg
      ((mul_nonneg (by positivity) hC).trans (le_max_right _ _))).mpr
    intro j
    let f := toLocalLp hab 10 (criticalGradient (intervalMeasure a b) j q)
    have hn : lpNorm f 10 (localMeasure a b) =
        ‖criticalGradient (intervalMeasure a b) j q‖ :=
      (Lp.norm_def f).symm.trans (toLocalLp_norm hab 10 (criticalGradient _ j q))
    have hpieces : ∀ i : Fin P.count,
        lpNorm f 10 (localMeasure (P.time i.castSucc) (P.time i.succ)) ≤ C := by
      intro i
      have he := restricted_criticalGradient_norm_eq
        (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2 q j
      have hb := (criticalGradient_norm_le _ (piecePath P q i) j).trans (hp i)
      exact he.symm.le.trans hb
    have h := lpNorm_le_count_mul_piece_bound hab P (Lp.memLp f) hC hpieces
    exact (hn.symm.le.trans h).trans (le_max_right _ _)

#print axioms actual_path_norm_le_of_piece_bounds
end HartreeF.ActualPathPartitions
