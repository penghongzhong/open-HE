import FActualBackwardFinitePerturbation
import FActualUniformPerturbationPartition
import FUniformIterationConstants

/-! Uniform terminal-data compact-interval perturbation from the original approximate PDE
and energy/S bounds. The partition, its quantitative count and all piece
solutions are generated internally. This source is a new consumer and must be
compiled against the final backward finite-iteration gate before acceptance. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.BackwardCompactLongTimePerturbation
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation FinitePerturbation
open BackwardFinitePerturbation CompactLongTimePerturbation
open ApproximateGlobalW ActualPathPartitions TimePartition CriticalSourceBounds
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  backwardHartreeDuhamelMap criticalPathIntervalSource CompatibleL1IntervalSource.advancedCriticalPath

theorem exists_actual_uniform_backward_compact_perturbation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ {a b epsilon : ℝ} (hab : a ≤ b) (f : EnergyState)
      (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b),
      ForcedHartreeCompactTestIdentity alpha kernel hab q E →
      ‖energyPath _ q‖ ≤ B → pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal M →
      0 ≤ epsilon → epsilon ≤ epsilon0 →
      ‖f-energyPath _ q ⟨b,hab,le_rfl⟩‖ ≤ epsilon → ‖E.gradient‖ ≤ epsilon →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsBackwardMildHartreePath hab alpha kernel f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
        energyPath _ u ⟨b,hab,le_rfl⟩=f ∧ ‖u-q‖ ≤ C*epsilon ∧
        fullZSDifferenceSize u q ≤ ENNReal.ofReal (C*epsilon) ∧
        ∀ v : CriticalPath (intervalMeasure a b), IsBackwardMildHartreePath hab alpha kernel f v → v=u := by
  let globalChoice := exists_uniform_W_partition_of_actual_PDE_energy_S
    hDensity hSob h0 hfree hret hH hgen hUnique hB hM
  let L : ℝ := Classical.choose globalChoice
  let finiteChoice := exists_actual_backward_finite_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB
  let r : ℝ := Classical.choose finiteChoice
  let cChoice := Classical.choose_spec finiteChoice
  let Cs : ℝ := Classical.choose cChoice
  have hs := Classical.choose_spec cChoice
  have hr : 0 < r := hs.1
  have hCs : 0 < Cs := hs.2.2.1
  let Cf := max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch
  let Q := max (energyEndpointConstant K C0) (Ch*C0+Cr)
  let D := iterationMultiplier Cf Q
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hD : 1 ≤ D := iterationMultiplier_one_le hCf hQ
  let R := (3*L)^(10 : ℕ)/r^(10 : ℕ)+1
  let N := Nat.ceil R
  let allowance := exists_uniform_iteration_allowance hr hD hCs N
  let epsilon0 : ℝ := Classical.choose allowance
  let aChoice := Classical.choose_spec allowance
  let C : ℝ := Classical.choose aChoice
  have ha := Classical.choose_spec aChoice
  refine ⟨epsilon0,C,ha.1,ha.2.1,ha.2.2.1,?_⟩
  intro a b epsilon hab f q E hPDE hE hS heps hepsSmall hf herr
  have herr1 : ‖E.gradient‖ ≤ 1 := herr.trans (hepsSmall.trans ha.2.1)
  let partitionResult := (Classical.choose_spec globalChoice).2 hr hab q E hPDE hE hS herr1
  let P : Partition a b := Classical.choose partitionResult.2
  have hcount : (P.count : ℝ) ≤ R := (Classical.choose_spec partitionResult.2).1
  have hWP : ∀ i : Fin P.count,
      ‖fun j => criticalGradient _ j (piecePath P q i)‖ ≤ r :=
    (Classical.choose_spec partitionResult.2).2
  have hPN : P.count ≤ N := by exact_mod_cast hcount.trans (Nat.le_ceil R)
  have stepBounds := ha.2.2.2 P.count hPN epsilon heps hepsSmall
  have hsmall : D^(P.count+1)*epsilon ≤ r/2 := stepBounds.1
  have hinit : ‖f-referenceAt P q (Fin.last P.count)‖ ≤ epsilon :=
    (congrArg (fun v : EnergyState => ‖f-v‖) (referenceAt_right hab P q)).le.trans hf
  let solved := hs.2.2.2 hab f q E P epsilon hPDE hE hWP heps hinit herr hsmall
  let u : CriticalPath (intervalMeasure a b) := Classical.choose solved
  have hu := Classical.choose_spec solved
  refine ⟨u,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,?_,?_,hu.2.2.2.2.2.2⟩
  · exact hu.2.2.2.2.1.trans stepBounds.2.1
  · exact hu.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal
      stepBounds.2.2)

#print axioms exists_actual_uniform_backward_compact_perturbation
end HartreeF.BackwardCompactLongTimePerturbation
