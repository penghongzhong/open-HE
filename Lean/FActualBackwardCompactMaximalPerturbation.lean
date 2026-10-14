import FActualBackwardCompactLongTimePerturbation
import FClosedPerturbationMaximalIdentification

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.BackwardCompactLongTimePerturbation
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  backwardHartreeDuhamelMap criticalPathIntervalSource

/-- The complete literal compact perturbation conclusion, named to keep
transport along exact path equality from expanding the entire maximal object. -/
def CompactBackwardPerturbationResult {a b : ℝ} (hab : a ≤ b) (alpha kernel : ℝ)
    (f : EnergyState) (q : CriticalPath (intervalMeasure a b)) (C epsilon : ℝ)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  IsBackwardMildHartreePath hab alpha kernel f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
  energyPath _ u ⟨b,hab,le_rfl⟩=f ∧ ‖u-q‖ ≤ C*epsilon ∧
  fullZSDifferenceSize u q ≤ ENNReal.ofReal (C*epsilon) ∧
  ∀ v : CriticalPath (intervalMeasure a b), IsBackwardMildHartreePath hab alpha kernel f v → v=u

/-- The same uniform finite-interval constants control the already constructed
maximal solution; interval inclusion and exact path identification are outputs. -/
theorem exists_actual_maximal_backward_compact_perturbation (hDensity : OrdinaryH1Density)
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
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH b f
      ∃ hI : Icc a b ⊆ U.domain,
        CompactBackwardPerturbationResult hab alpha kernel f q C epsilon (U.path hab hI) := by
  let result := exists_actual_uniform_backward_compact_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilon0 : ℝ := Classical.choose result
  let constants := Classical.choose_spec result
  let C : ℝ := Classical.choose constants
  have hs := Classical.choose_spec constants
  refine ⟨epsilon0,C,hs.1,hs.2.1,hs.2.2.1,?_⟩
  intro a b epsilon hab f q E hPDE hE hS heps hepsSmall hf herr
  let solved := hs.2.2.2 hab f q E hPDE hE hS heps hepsSmall hf herr
  let u : CriticalPath (intervalMeasure a b) := Classical.choose solved
  have hu := Classical.choose_spec solved
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH b f
  let identified := actual_maximal_path_eq_of_closed_backward
    hDensity hSob h0 hfree hret hefree heret hH hab f u hu.1
  let hI : Icc a b ⊆ U.domain := Classical.choose identified
  have he : U.path hab hI = u := Classical.choose_spec identified
  refine ⟨hI,?_⟩
  have hu' : CompactBackwardPerturbationResult hab alpha kernel f q C epsilon u :=
    ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,hu.2.2.2.2.1,hu.2.2.2.2.2.1,hu.2.2.2.2.2.2⟩
  exact (congrArg (CompactBackwardPerturbationResult hab alpha kernel f q C epsilon) he).mpr hu' 

#print axioms exists_actual_maximal_backward_compact_perturbation
end HartreeF.BackwardCompactLongTimePerturbation
