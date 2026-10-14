import FActualSPartition
import FFiniteFamilyTimePartition

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

/-- One actual partition makes all three original complex gradient coordinates
small simultaneously, with the original W size controlling its count. -/
theorem exists_actual_small_W_partition {a b eta : ℝ} (hab : a ≤ b)
    (q : CriticalPath (intervalMeasure a b)) (heta : 0 < eta) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ (∑ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j q‖) ^ (10 : ℕ) /
        eta ^ (10 : ℕ) + 1 ∧
      ∀ i : Fin P.count,
        ‖fun j => criticalGradient (intervalMeasure (P.time i.castSucc) (P.time i.succ)) j
          (piecePath P q i)‖ ≤ eta := by
  let f (j : Fin 3) : Lp SpatialCritical 10 (localMeasure a b) :=
    toLocalLp hab 10 (criticalGradient (intervalMeasure a b) j q)
  have hn (j : Fin 3) : lpNorm (f j) 10 (localMeasure a b) =
      ‖criticalGradient (intervalMeasure a b) j q‖ :=
    (Lp.norm_def (f j)).symm.trans (toLocalLp_norm hab 10 (criticalGradient _ j q))
  let result := exists_partition_small_L10_family (E := SpatialCritical) (J := Fin 3)
    hab (fun j t => f j t) (fun j => Lp.memLp (f j)) heta
  let P : Partition a b := Classical.choose result
  have hc : (P.count : ℝ) ≤ (∑ j : Fin 3, lpNorm (f j) 10 (localMeasure a b)) ^ (10 : ℕ) /
      eta ^ (10 : ℕ) + 1 := (Classical.choose_spec result).1
  have hp : ∀ (i : Fin P.count) (j : Fin 3),
      eLpNorm (f j) 10 (localMeasure (P.time i.castSucc) (P.time i.succ)) ≤
        ENNReal.ofReal eta := (Classical.choose_spec result).2
  refine ⟨P, ?_, ?_⟩
  · have hs : (∑ j : Fin 3, lpNorm (f j) 10 (localMeasure a b)) =
        ∑ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j q‖ :=
      Finset.sum_congr rfl (fun j _ => hn j)
    exact hc.trans_eq (congrArg (fun z : ℝ => z ^ (10 : ℕ) / eta ^ (10 : ℕ) + 1) hs)
  · intro i
    apply (pi_norm_le_iff_of_nonneg heta.le).mpr
    intro j
    change ‖criticalGradient _ j (restrictPath _ _ _ q)‖ ≤ eta
    rw [restricted_criticalGradient_norm_eq]
    change lpNorm (f j) 10 (localMeasure (P.time i.castSucc) (P.time i.succ)) ≤ eta
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hp i j)
    simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal heta.le] using h

#print axioms exists_actual_small_W_partition
end HartreeF.ActualPathPartitions
