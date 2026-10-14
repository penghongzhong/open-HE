import FActualApproximateGlobalWBound

/-! The long-time partition is now produced from the original approximate
PDE and energy/S bounds. No original numerical W bound is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HartreeF.ApproximateGlobalW
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open ActualDuhamelPath CriticalSourceBounds TimePartition ActualPathPartitions
open HartreeDistributionalBridge LinearWeakEquation ForcedSmallS
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath hartreeDuhamelMap CompatibleL1IntervalSource.restrict
  CompatibleL1IntervalSource.retardedCriticalPath

theorem exists_uniform_W_partition_of_actual_PDE_energy_S
    (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha kernel B M : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {eta a b : ℝ} (_heta : 0 < eta) (hab : a ≤ b)
      (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b),
      ForcedHartreeCompactTestIdentity alpha kernel hab q E →
      ‖energyPath (intervalMeasure a b) q‖ ≤ B →
      pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal M →
      ‖E.gradient‖ ≤ 1 →
      ‖q‖ ≤ L ∧ ∃ P : Partition a b,
        (P.count : ℝ) ≤ (3 * L) ^ (10 : ℕ) / eta ^ (10 : ℕ) + 1 ∧
        ∀ i : Fin P.count,
          ‖fun j => criticalGradient (intervalMeasure (P.time i.castSucc) (P.time i.succ)) j
            (piecePath P q i)‖ ≤ eta := by
  let choice := exists_uniform_graph_bound_of_actual_PDE_energy_S
    hDensity hSob h0 hfree hret hH hgen hUnique hB hM
  let L : ℝ := Classical.choose choice
  have hL : 0 ≤ L := (Classical.choose_spec choice).1
  refine ⟨L, hL, ?_⟩
  intro eta a b heta hab q E hPDE hE hS herr
  have hq : ‖q‖ ≤ L := (Classical.choose_spec choice).2 hab q E hPDE hE hS herr
  let part := exists_actual_small_W_partition hab q heta
  let P : Partition a b := Classical.choose part
  have hcount : (P.count : ℝ) ≤
      (∑ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j q‖) ^ (10 : ℕ) /
        eta ^ (10 : ℕ) + 1 := (Classical.choose_spec part).1
  have hpieces : ∀ i : Fin P.count,
      ‖fun j => criticalGradient (intervalMeasure (P.time i.castSucc) (P.time i.succ)) j
        (piecePath P q i)‖ ≤ eta := (Classical.choose_spec part).2
  have hsum : (∑ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j q‖) ≤ 3 * L := by
    calc
      _ ≤ ∑ _j : Fin 3, L := Finset.sum_le_sum fun j _ =>
        (criticalGradient_norm_le _ q j).trans hq
      _ = 3 * L := by simp
  refine ⟨hq, P, ?_, hpieces⟩
  exact hcount.trans (add_le_add (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => norm_nonneg _) hsum (10 : ℕ))
      (pow_nonneg heta.le _)) le_rfl)

#print axioms exists_uniform_W_partition_of_actual_PDE_energy_S
end HartreeF.ApproximateGlobalW
