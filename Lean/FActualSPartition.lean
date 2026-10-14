import FPathRestrictionLpNorms
import FL10TimePartition

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.ActualPathPartitions
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open ActualSTail SobolevStretch StationarySelfTest CriticalSourceBounds TimePartition CriticalJointSources
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields criticalGradient

theorem piece_order {a b : ℝ} (P : Partition a b) (i : Fin P.count) :
    P.time i.castSucc ≤ P.time i.succ :=
  P.ordered (by exact_mod_cast Nat.le_succ i.val)

/-- The exact same original path, restricted to the actual partition piece. -/
def piecePath {a b : ℝ} (P : Partition a b) (q : CriticalPath (intervalMeasure a b))
    (i : Fin P.count) : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)) :=
  restrictPath (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2 q

theorem exists_actual_small_S_partition (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {a b eta : ℝ} (hab : a ≤ b)
    (q : CriticalPath (intervalMeasure a b)) (heta : 0 < eta) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ (pathValueSize (intervalMeasure a b) q).toReal ^ (10 : ℕ) /
        eta ^ (10 : ℕ) + 1 ∧
      ∀ i : Fin P.count,
        pathValueSize (intervalMeasure (P.time i.castSucc) (P.time i.succ)) (piecePath P q i) ≤
          ENNReal.ofReal eta := by
  let f := toLocalLp hab 10 (pathValueLp hDensity hSob q)
  have hn : lpNorm f 10 (localMeasure a b) = (pathValueSize (intervalMeasure a b) q).toReal := by
    exact (Lp.norm_def f).symm.trans
      ((toLocalLp_norm hab 10 (pathValueLp hDensity hSob q)).trans
        (pathValueLp_norm hDensity hSob q))
  obtain ⟨P, hc, hp⟩ := exists_partition_small_L10 hab (Lp.memLp f) heta
  refine ⟨P, ?_, ?_⟩
  · simpa only [hn] using hc
  · intro i
    change pathValueSize _ (restrictPath _ _ _ q) ≤ _
    rw [restricted_pathValueSize_eq hDensity hSob]
    exact hp i

#print axioms piece_order
#print axioms exists_actual_small_S_partition
end HartreeF.ActualPathPartitions
