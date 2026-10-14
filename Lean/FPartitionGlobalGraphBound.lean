import FPartitionPrefixGeometry
import FActualPartitionGraphAssembly
import FActualFreePathDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalPathGluing
open ActualDuhamelPath ActualPathPartitions TimePartition
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient restrictPath

/-- Non-strict partitions cover every point, including repeated endpoints. -/
theorem exists_partition_piece_mem {a b t : ℝ} (P : Partition a b) (ht : t ∈ Set.Icc a b) :
    ∃ i : Fin P.count, t ∈ Set.Icc (P.time i.castSucc) (P.time i.succ) := by
  have hlo : P.time 0 ≤ t := P.left.le.trans ht.1
  have aux : ∀ n : ℕ, 1 ≤ n → ∀ hn : n ≤ P.count,
      t ≤ node P n hn → ∃ i : Fin P.count, i.val < n ∧
        t ∈ Set.Icc (P.time i.castSucc) (P.time i.succ) := by
    intro n h1
    induction n,h1 using Nat.le_induction with
    | base =>
      intro hn hlast
      refine ⟨⟨0,P.positive⟩,?_,hlo,hlast⟩
      change (0 : ℕ) < 1
      omega
    | succ n h1 ih =>
      intro hn hlast
      have hnlt : n < P.count := hn
      by_cases htold : t ≤ node P n hnlt.le
      · obtain ⟨i,hi,hit⟩ := ih hnlt.le htold
        exact ⟨i,by omega,hit⟩
      · exact ⟨⟨n,hnlt⟩,Nat.lt_succ_self n,le_of_lt (lt_of_not_ge htold),hlast⟩
  obtain ⟨i,_,hi⟩ := aux P.count P.positive le_rfl (by simpa only [node_last] using ht.2)
  exact ⟨i,hi⟩

theorem piecePath_energy {a b : ℝ} (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) (i : Fin P.count)
    (t : Set.Icc (P.time i.castSucc) (P.time i.succ)) :
    energyPath _ (piecePath P q i) t = energyPath _ q
      ⟨t,(P.mem_interval i.castSucc).1.trans t.property.1,t.property.2.trans (P.mem_interval i.succ).2⟩ :=
  restrictPath_energy (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2 q t

/-- Per-piece bounds control the actual whole continuous energy coordinate. -/
theorem global_energy_norm_le_piece_bound {a b G : ℝ} (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) (hG : 0 ≤ G)
    (hp : ∀ i : Fin P.count, ‖energyPath _ (piecePath P q i)‖ ≤ G) :
    ‖energyPath _ q‖ ≤ G := by
  apply (ContinuousMap.norm_le _ hG).mpr
  intro t
  obtain ⟨i,hi⟩ := exists_partition_piece_mem P t.property
  have he : energyPath _ (piecePath P q i) ⟨t,hi⟩ = energyPath _ q t :=
    piecePath_energy P q i ⟨t,hi⟩
  exact (congrArg norm he).symm.le.trans
    (((energyPath _ (piecePath P q i)).norm_coe_le_norm ⟨t,hi⟩).trans (hp i))

/-- The full canonical graph is assembled without an independent whole-energy premise. -/
theorem global_graph_norm_le_piece_bound {a b G : ℝ} (hab : a ≤ b) (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) (hG : 0 ≤ G)
    (hp : ∀ i : Fin P.count, ‖piecePath P q i‖ ≤ G) :
    ‖q‖ ≤ (P.count : ℝ)*G := by
  have hE : ‖energyPath _ q‖ ≤ G := global_energy_norm_le_piece_bound P q hG
    (fun i => (energyPath_norm_le _ _).trans (hp i))
  have hn : (1 : ℝ) ≤ P.count := by exact_mod_cast P.positive
  have hg : G ≤ (P.count : ℝ)*G := by nlinarith
  exact (actual_path_norm_le_of_piece_bounds hab P q hG hE hp).trans (max_le hg le_rfl)

/-- The original restriction operation preserves the same literal path difference. -/
theorem piecePath_sub {a b : ℝ} (P : Partition a b)
    (u q : CriticalPath (intervalMeasure a b)) (i : Fin P.count) :
    piecePath P (u-q) i = piecePath P u i-piecePath P q i := by
  apply energyPath_injective _
  apply ContinuousMap.ext
  intro t
  have hl := piecePath_energy P (u-q) i t
  have hu := piecePath_energy P u i t
  have hq := piecePath_energy P q i t
  exact hl.trans ((criticalPath_energy_sub_apply u q
    ⟨t,(P.mem_interval i.castSucc).1.trans t.property.1,t.property.2.trans (P.mem_interval i.succ).2⟩).trans
      ((congrArg₂ (fun x y : EnergyState => x-y) hu.symm hq.symm).trans
        (criticalPath_energy_sub_apply (piecePath P u i) (piecePath P q i) t).symm))

end HartreeF.FinitePerturbation
