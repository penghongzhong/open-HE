import FActualSPartition
import FActualHartreeSolutionConcatenation
import FFullZPathGluing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalPathGluing
open ActualDuhamelPath ActualPathPartitions TimePartition
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient restrictPath gluePath

/-- The exact nth node of the original actual partition. -/
def node {a b : ℝ} (P : Partition a b) (n : ℕ) (hn : n ≤ P.count) : ℝ :=
  P.time ⟨n, Nat.lt_succ_of_le hn⟩

theorem node_mem {a b : ℝ} (P : Partition a b) (n : ℕ) (hn : n ≤ P.count) :
    node P n hn ∈ Set.Icc a b := P.mem_interval _

theorem node_order {a b : ℝ} (P : Partition a b) {m n : ℕ}
    (hm : m ≤ P.count) (hn : n ≤ P.count) (h : m ≤ n) : node P m hm ≤ node P n hn :=
  P.ordered (show (⟨m,Nat.lt_succ_of_le hm⟩ : Fin (P.count+1)) ≤ ⟨n,Nat.lt_succ_of_le hn⟩ from h)

@[simp] theorem node_zero {a b : ℝ} (P : Partition a b) : node P 0 (Nat.zero_le _) = a := P.left
@[simp] theorem node_last {a b : ℝ} (P : Partition a b) : node P P.count le_rfl = b := P.right

/-- A true prefix path restricted to an already solved original piece. -/
def prefixPiecePath {a b : ℝ} (P : Partition a b) (n : ℕ) (hn : n ≤ P.count)
    (u : CriticalPath (intervalMeasure (P.time 0) (node P n hn)))
    (i : Fin P.count) (hi : i.val < n) :
    CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)) :=
  restrictPath (P.ordered (Fin.zero_le _)) (piece_order P i)
    (P.ordered (show i.succ ≤ (⟨n,Nat.lt_succ_of_le hn⟩ : Fin (P.count+1)) from hi)) u

/-- An entire prefix consists of its first piece when n=1. -/
theorem prefixPiecePath_first {a b : ℝ} (P : Partition a b)
    (u : CriticalPath (intervalMeasure (P.time 0) (node P 1 P.positive))) :
    prefixPiecePath P 1 P.positive u ⟨0,P.positive⟩ (by change (0 : ℕ) < 1; omega) = u := by
  change restrictPath le_rfl (piece_order P ⟨0,P.positive⟩) le_rfl u = u
  exact restrictPath_self _ u

/-- Appending one new piece leaves every earlier actual piece unchanged. -/
theorem prefixPiecePath_glue_old {a b : ℝ} (P : Partition a b) {n : ℕ}
    (hn : n < P.count)
    (u : CriticalPath (intervalMeasure (P.time 0) (node P n hn.le)))
    (v : CriticalPath (intervalMeasure (node P n hn.le) (node P (n+1) hn)))
    (hm : energyPath _ u ⟨node P n hn.le, P.ordered (Fin.zero_le _), le_rfl⟩ =
      energyPath _ v ⟨node P n hn.le, le_rfl, node_order P hn.le hn (Nat.le_succ n)⟩)
    (i : Fin P.count) (hi : i.val < n) :
    prefixPiecePath P (n+1) hn
      (gluePath (P.ordered (Fin.zero_le _)) (node_order P hn.le hn (Nat.le_succ n)) u v hm)
      i (by omega) = prefixPiecePath P n hn.le u i hi := by
  have he := restrict_gluePath_left (P.ordered (Fin.zero_le _))
    (node_order P hn.le hn (Nat.le_succ n)) u v hm
  have hr := congrArg (restrictPath (P.ordered (Fin.zero_le i.castSucc)) (piece_order P i)
    (P.ordered (show i.succ ≤ (⟨n,Nat.lt_succ_of_le hn.le⟩ : Fin (P.count+1)) from hi))) he
  exact (restrictPath_trans le_rfl (P.ordered (Fin.zero_le _))
    (node_order P hn.le hn (Nat.le_succ n)) (P.ordered (Fin.zero_le i.castSucc))
    (piece_order P i) (P.ordered (show i.succ ≤ (⟨n,Nat.lt_succ_of_le hn.le⟩ : Fin (P.count+1)) from hi))
    (gluePath (P.ordered (Fin.zero_le _)) (node_order P hn.le hn (Nat.le_succ n)) u v hm)).symm.trans hr

/-- The appended original piece is exactly the new solution. -/
theorem prefixPiecePath_glue_new {a b : ℝ} (P : Partition a b) {n : ℕ}
    (hn : n < P.count)
    (u : CriticalPath (intervalMeasure (P.time 0) (node P n hn.le)))
    (v : CriticalPath (intervalMeasure (node P n hn.le) (node P (n+1) hn)))
    (hm : energyPath _ u ⟨node P n hn.le, P.ordered (Fin.zero_le _), le_rfl⟩ =
      energyPath _ v ⟨node P n hn.le, le_rfl, node_order P hn.le hn (Nat.le_succ n)⟩) :
    prefixPiecePath P (n+1) hn
      (gluePath (P.ordered (Fin.zero_le _)) (node_order P hn.le hn (Nat.le_succ n)) u v hm)
      ⟨n,hn⟩ (Nat.lt_succ_self n) = v :=
  restrict_gluePath_right (P.ordered (Fin.zero_le _)) (node_order P hn.le hn (Nat.le_succ n)) u v hm

end HartreeF.FinitePerturbation
