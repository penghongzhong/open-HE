import FActualFinitePerturbationRecursion
import FFinalPrefixSolution
import FPartitionFullZDifferenceBound

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace ActualPathPartitions TimePartition ActualPerturbation
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  hartreeDuhamelMap criticalPathIntervalSource CompatibleL1IntervalSource.retardedCriticalPath

/-- True finite-interval perturbation iteration. The actual partition and its
same-q W bounds are still explicit intermediate inputs. All piece solutions,
matching traces, whole-interval mild solution, uniqueness and Z/S bounds are outputs. -/
theorem exists_actual_finite_perturbation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator) (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hB : 0 ≤ B) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f : EnergyState) (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
      (P : Partition a b) (epsilon : ℝ),
      ForcedHartreeCompactTestIdentity alpha c hab q E →
      ‖energyPath _ q‖ ≤ B →
      (∀ i : Fin P.count, ‖fun j => criticalGradient _ j (piecePath P q i)‖ ≤ r) →
      0 ≤ epsilon → ‖f-referenceState P q 0 (Nat.zero_le _)‖ ≤ epsilon → ‖E.gradient‖ ≤ epsilon →
      (iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
        (max (energyEndpointConstant K C0) Cr))^(P.count+1)*epsilon ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
        energyPath _ u ⟨a,le_rfl,hab⟩=f ∧
        ‖u-q‖ ≤ (P.count : ℝ)*(iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
          (max (energyEndpointConstant K C0) Cr))^P.count*epsilon ∧
        fullZSDifferenceSize u q ≤ ENNReal.ofReal
          (C*(P.count : ℝ)*(iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
            (max (energyEndpointConstant K C0) Cr))^P.count*epsilon) ∧
        ∀ v : CriticalPath (intervalMeasure a b), IsMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_perturbation_prefixes hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB
  let r : ℝ := Classical.choose choice
  let cc := Classical.choose_spec choice
  let C0s : ℝ := Classical.choose cc
  have hs := Classical.choose_spec cc
  have hC0s : 0 < C0s := hs.2.2.1
  let S := (5/3 : ℝ)*K^(1/6 : ℝ)*6
  have hK := hSob.nonneg
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let C := 1+6*C0s+S
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r,C,hs.1,hs.2.1,hC,?_⟩
  intro a b hab f q E P epsilon hPDE hqE hqW heps hf hE hsmall
  let Cf := max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch
  let Q := max (energyEndpointConstant K C0) Cr
  let D := iterationMultiplier Cf Q
  let G := D^P.count*epsilon
  let H := 2*C0s*D^P.count*epsilon
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hD : 1 ≤ D := iterationMultiplier_one_le hCf hQ
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hHH : 0 ≤ H := by dsimp [H]; positivity
  let s : PrefixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H P.count le_rfl :=
    Classical.choice (hs.2.2.2 hab f q E P epsilon hPDE hqE hqW heps hf hE hsmall
    P.count P.positive le_rfl)
  let result := finalPrefix_solution hDensity hSob h0 hfree hret hH hab P f q s
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  have humild := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f u).mpr hu.1
  have hforced := actual_forced_mild_of_distributional hDensity hSob hH hab q E h0 hfree hret hgen hUnique hPDE
  have hdiff : FullZPath (u-q) := ⟨actual_forced_difference_endpointWitness hDensity hSob h0 hfree hret
    hefree heret hH hab f (energyPath _ q ⟨a,le_rfl,hab⟩) u q E hu.1 hforced⟩
  have hpieces (i : Fin P.count) : ‖piecePath P u i-piecePath P q i‖ ≤ G :=
    (hu.2.2 i).1.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hD (show i.val+1 ≤ P.count from i.isLt)) heps)
  have hb := partition_fullZ_difference_bound hDensity hSob hab P u q hdiff hG hHH hpieces
    (fun i => (hu.2.2 i).2.2)
  refine ⟨u,humild,hu.2.1,hdiff,
    actual_fixedPoint_initial hDensity hSob h0 hfree hret hH hab f u hu.1,?_,?_,?_⟩
  · exact hb.1.trans_eq (by dsimp [G]; ring)
  · exact hb.2.trans_eq (congrArg ENNReal.ofReal (by dsimp [G,H,C,S]; ring))
  · intro v hv
    exact actual_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH hab f v u
      ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f v).mp hv) hu.1

end HartreeF.FinitePerturbation
