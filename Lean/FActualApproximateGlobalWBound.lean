import FActualPartitionGraphAssembly
import FForcedSmallSUniformBound
import FActualHartreePDERestriction

/-! A uniform whole-interval E+W bound for the actual approximate Hartree
trajectory, produced from its original energy/S caps and original PDE error.
No numerical W cap or per-piece mild identity is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
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

theorem exists_uniform_graph_bound_of_actual_PDE_energy_S
    (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha kernel B M : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b),
      ForcedHartreeCompactTestIdentity alpha kernel hab q E →
      ‖energyPath (intervalMeasure a b) q‖ ≤ B →
      pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal M →
      ‖E.gradient‖ ≤ 1 → ‖q‖ ≤ L := by
  let small := exists_small_s_uniform_approximate_bound hDensity hSob h0 hfree hret hH hB
  let eta : ℝ := Classical.choose small
  have heta : 0 < eta := (Classical.choose_spec small).1
  let Cf := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  let Q := max (energyEndpointConstant K C0) Cr
  let C := 2 * (Cf * B + Q)
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hCf hB) hQ)
  let countBound := M ^ (10 : ℕ) / eta ^ (10 : ℕ) + 1
  let L := max B (countBound * C)
  refine ⟨L, hB.trans (le_max_left _ _), ?_⟩
  intro a b hab q E hPDE hE hS herr
  let part := exists_actual_small_S_partition hDensity hSob hab q heta
  let P : Partition a b := Classical.choose part
  have hcount : (P.count : ℝ) ≤
      (pathValueSize (intervalMeasure a b) q).toReal ^ (10 : ℕ) / eta ^ (10 : ℕ) + 1 :=
    (Classical.choose_spec part).1
  have hpiecesS : ∀ i : Fin P.count,
      pathValueSize (intervalMeasure (P.time i.castSucc) (P.time i.succ)) (piecePath P q i) ≤
        ENNReal.ofReal eta := (Classical.choose_spec part).2
  have hpieces : ∀ i : Fin P.count, ‖piecePath P q i‖ ≤ C := by
    intro i
    let c := P.time i.castSucc
    let d := P.time i.succ
    have hac : a ≤ c := (P.mem_interval i.castSucc).1
    have hcd : c ≤ d := piece_order P i
    have hdb : d ≤ b := (P.mem_interval i.succ).2
    have hforced := actual_restricted_forced_mild_of_distributional
      hDensity hSob hH hab q E h0 hfree hret hgen hUnique hPDE hac hcd hdb
    have hself : restrictPath hac hcd hdb q =
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd
          (energyPath _ (restrictPath hac hcd hdb q) ⟨c, le_rfl, hcd⟩)
          (restrictPath hac hcd hdb q) -
        Complex.I • (E.restrict hac hdb).retardedCriticalPath hDensity hSob h0 hret := by
      exact hforced.trans (congrArg (fun g : EnergyState =>
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd g
          (restrictPath hac hcd hdb q) -
        Complex.I • (E.restrict hac hdb).retardedCriticalPath hDensity hSob h0 hret)
        (restrictPath_initial hac hcd hdb q).symm)
    have he : ‖energyPath _ (restrictPath hac hcd hdb q)‖ ≤ B :=
      (restrictPath_energy_norm_le hac hcd hdb q).trans hE
    have herror : ‖(E.restrict hac hdb).gradient‖ ≤ 1 :=
      (E.restrict_gradient_norm_le hac hdb).trans herr
    exact (Classical.choose_spec small).2.2 hcd (restrictPath hac hcd hdb q)
      (E.restrict hac hdb) hself he (hpiecesS i) herror
  have hrealS : (pathValueSize (intervalMeasure a b) q).toReal ≤ M := by
    simpa only [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hS
  have hn : (P.count : ℝ) ≤ countBound :=
    hcount.trans (add_le_add (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ ENNReal.toReal_nonneg hrealS (10 : ℕ)) (pow_nonneg heta.le _)) le_rfl)
  exact (actual_path_norm_le_of_piece_bounds hab P q hC hE hpieces).trans
    (max_le_max le_rfl (mul_le_mul_of_nonneg_right hn hC))

#print axioms exists_uniform_graph_bound_of_actual_PDE_energy_S
end HartreeF.ApproximateGlobalW
