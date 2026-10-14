import FPartitionGlobalGraphBound
import FActualFinitePerturbationRecursion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.BackwardFinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalPathGluing
open ActualDuhamelPath ActualPathPartitions TimePartition FinitePerturbation
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient restrictPath gluePath

/-- The same original trajectory evaluated at an actual partition node. -/
def referenceAt {a b : ℝ} (P : Partition a b) (q : CriticalPath (intervalMeasure a b))
    (k : Fin (P.count+1)) : EnergyState := energyPath _ q ⟨P.time k,P.mem_interval k⟩

/-- An actual suffix restricted to one original piece, with no time reflection. -/
def suffixPiecePath {a b : ℝ} (P : Partition a b) (k : Fin (P.count+1))
    (u : CriticalPath (intervalMeasure (P.time k) (P.time (Fin.last P.count))))
    (i : Fin P.count) (hi : k.val ≤ i.val) :
    CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)) :=
  restrictPath (P.ordered (show k ≤ i.castSucc from hi)) (piece_order P i)
    (P.ordered (Fin.le_last i.succ)) u

/-- The newly added piece of a joined suffix is the same actual local solution. -/
theorem suffixPiecePath_glue_new {a b : ℝ} (P : Partition a b) (i : Fin P.count)
    (v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)))
    (u : CriticalPath (intervalMeasure (P.time i.succ) (P.time (Fin.last P.count))))
    (hm : energyPath _ v ⟨P.time i.succ,piece_order P i,le_rfl⟩ =
      energyPath _ u ⟨P.time i.succ,le_rfl,P.ordered (Fin.le_last i.succ)⟩) :
    suffixPiecePath P i.castSucc
      (gluePath (piece_order P i) (P.ordered (Fin.le_last i.succ)) v u hm) i le_rfl = v :=
  restrict_gluePath_left (piece_order P i) (P.ordered (Fin.le_last i.succ)) v u hm

/-- Joining on the left leaves every already solved right piece unchanged. -/
theorem suffixPiecePath_glue_old {a b : ℝ} (P : Partition a b) (i : Fin P.count)
    (v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)))
    (u : CriticalPath (intervalMeasure (P.time i.succ) (P.time (Fin.last P.count))))
    (hm : energyPath _ v ⟨P.time i.succ,piece_order P i,le_rfl⟩ =
      energyPath _ u ⟨P.time i.succ,le_rfl,P.ordered (Fin.le_last i.succ)⟩)
    (j : Fin P.count) (hj : i.val+1 ≤ j.val) :
    suffixPiecePath P i.castSucc
      (gluePath (piece_order P i) (P.ordered (Fin.le_last i.succ)) v u hm) j (by change i.val ≤ j.val; omega) =
      suffixPiecePath P i.succ u j hj := by
  have he := restrict_gluePath_right (piece_order P i) (P.ordered (Fin.le_last i.succ)) v u hm
  have hr := congrArg (restrictPath (P.ordered (show i.succ ≤ j.castSucc from hj))
    (piece_order P j) (P.ordered (Fin.le_last j.succ))) he
  exact (restrictPath_trans (piece_order P i) (P.ordered (Fin.le_last i.succ)) le_rfl
    (P.ordered (show i.succ ≤ j.castSucc from hj)) (piece_order P j) (P.ordered (Fin.le_last j.succ))
    (gluePath (piece_order P i) (P.ordered (Fin.le_last i.succ)) v u hm)).symm.trans hr

/-- The true graph error on a piece bounds its true left endpoint error. -/
theorem piece_initial_error_le {a b : ℝ} (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) (i : Fin P.count)
    (v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ))) :
    ‖energyPath _ v ⟨P.time i.castSucc,le_rfl,piece_order P i⟩-referenceAt P q i.castSucc‖ ≤
      ‖v-piecePath P q i‖ := by
  have he := criticalPath_energy_sub_apply v (piecePath P q i)
    ⟨P.time i.castSucc,le_rfl,piece_order P i⟩
  have href : energyPath _ (piecePath P q i) ⟨P.time i.castSucc,le_rfl,piece_order P i⟩ =
      referenceAt P q i.castSucc := piecePath_energy P q i ⟨P.time i.castSucc,le_rfl,piece_order P i⟩
  have he' := he.trans (congrArg (fun z : EnergyState =>
    energyPath _ v ⟨P.time i.castSucc,le_rfl,piece_order P i⟩-z) href)
  exact (congrArg norm he').symm.le.trans
    (energyPath_value_norm_le _ (v-piecePath P q i) ⟨P.time i.castSucc,le_rfl,piece_order P i⟩)

end HartreeF.BackwardFinitePerturbation
