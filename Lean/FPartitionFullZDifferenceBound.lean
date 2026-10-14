import FPartitionGlobalGraphBound
import FPartitionEndpointBound
import FActualFullZForcingPerturbation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace ActualPathPartitions TimePartition ActualPerturbation
open EndpointOutput SobolevStretch StationarySelfTest TimeHolder
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient

/-- Actual local difference bounds assemble into the whole canonical graph,
Euclidean endpoint, and scalar S difference on the same two paths. -/
theorem partition_fullZ_difference_bound (hDensity : OrdinaryH1Density) {K a b G H : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b) (P : Partition a b)
    (u q : CriticalPath (intervalMeasure a b)) (hz : FullZPath (u-q))
    (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hgraph : ∀ i : Fin P.count, ‖piecePath P u i-piecePath P q i‖ ≤ G)
    (hpieces : ∀ i : Fin P.count,
      fullZSDifferenceSize (piecePath P u i) (piecePath P q i) ≤ ENNReal.ofReal H) :
    ‖u-q‖ ≤ (P.count : ℝ)*G ∧
    fullZSDifferenceSize u q ≤ ENNReal.ofReal
      ((P.count : ℝ)*G+3*(P.count : ℝ)*H+((5/3 : ℝ)*K^(1/6 : ℝ)*6)*((P.count : ℝ)*G)) := by
  have hg : ‖u-q‖ ≤ (P.count : ℝ)*G := global_graph_norm_le_piece_bound hab P (u-q) hG
    (fun i => (congrArg norm (piecePath_sub P u q i)).trans_le (hgraph i))
  have he : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x-energyComplexGradient (energyPath _ q t) x) ≤
      ENNReal.ofReal (3*(P.count : ℝ)*H) := by
    rw [actual_complex_difference_mixedNorm_eq]
    apply global_endpoint_le_piece_bound hab P (u-q) hz hH
    intro i
    rw [piecePath_sub, ← actual_complex_difference_mixedNorm_eq]
    exact (le_add_right (le_add_left le_rfl)).trans (hpieces i)
  let S := (5/3 : ℝ)*K^(1/6 : ℝ)*6
  have hK := hSob.nonneg
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs : mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x-energyValue (energyPath _ q t) x) ≤
      ENNReal.ofReal (S*((P.count : ℝ)*G)) := by
    have h := (actual_scalar_difference_S_bound hDensity hSob u q).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg))
    exact h.trans_eq (ENNReal.ofReal_mul hS).symm
  refine ⟨hg,?_⟩
  unfold fullZSDifferenceSize
  exact (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hg) he) hs).trans_eq
    (ofReal_sum_three (mul_nonneg (Nat.cast_nonneg _) hG)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hH)
      (mul_nonneg hS (mul_nonneg (Nat.cast_nonneg _) hG)))

end HartreeF.FinitePerturbation
