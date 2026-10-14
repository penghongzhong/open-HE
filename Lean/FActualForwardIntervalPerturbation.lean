import FActualCompactMaximalPerturbation

/-! Assembly on an arbitrary interval from its genuine local critical paths.
The same original approximate state is represented on every compact segment.
Actual maximal lifespan inclusion and all uniform compact bounds are outputs.
No numerical W bound, per-piece solution or prior target-domain inclusion is
assumed. This module treats the part to the right of the original datum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalPerturbation
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open CompactLongTimePerturbation CriticalPathRestriction CriticalPathGluing
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  hartreeDuhamelMap criticalPathIntervalSource

theorem energyPointDifference_norm_le {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (t : Icc a b) :
    ‖energyPath _ u t - energyPath _ q t‖ ≤ ‖u-q‖ := by
  have he := criticalPath_energy_sub_apply u q t
  exact (congrArg norm he).symm.le.trans (energyPath_value_norm_le _ (u-q) t)

/-- The local path and PDE hypotheses are precisely the compact restrictions
of the given approximate trajectory and its original source. Uniform constants
are chosen before the interval, all restrictions, the datum and the error. The
output is one actual maximal trajectory on the entire right-hand portion. -/
theorem exists_actual_forward_interval_perturbation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ (I : Set ℝ) (hconn : OrdConnected I) {s epsilon : ℝ} (hsI : s ∈ I),
      ∀ (f : EnergyState) (q : ℝ → EnergyState)
      (Q : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b))
      (E : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CompatibleL1IntervalSource a b),
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) (t : Icc a b),
        energyPath _ (Q hab hI) t = q t) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I),
        ForcedHartreeCompactTestIdentity alpha kernel hab (Q hab hI) (E hab hI)) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I), ‖energyPath _ (Q hab hI)‖ ≤ B) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I),
        pathValueSize (intervalMeasure a b) (Q hab hI) ≤ ENNReal.ofReal M) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I), ‖(E hab hI).gradient‖ ≤ epsilon) →
      0 ≤ epsilon → epsilon ≤ epsilon0 → ‖f-q s‖ ≤ epsilon →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
      I ∩ Ici s ⊆ U.domain ∧
      (∀ {b : ℝ} (hb : b ∈ I) (hsb : s ≤ b),
        ∃ hU : Icc s b ⊆ U.domain,
          CompactPerturbationResult hsb alpha kernel f
            (Q hsb (hconn.out' hsI hb)) C epsilon (U.path hsb hU)) ∧
      ∀ t ∈ I ∩ Ici s, ‖U.state t-q t‖ ≤ C*epsilon := by
  let chosen := exists_actual_maximal_compact_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilon0 : ℝ := Classical.choose chosen
  let constants := Classical.choose_spec chosen
  let C : ℝ := Classical.choose constants
  have hs := Classical.choose_spec constants
  refine ⟨epsilon0,C,hs.1,hs.2.1,hs.2.2.1,?_⟩
  intro I hconn s epsilon hsI f q Q E hQ hPDE hE hS herr heps hsmall hf
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  have solved (b : ℝ) (hb : b ∈ I) (hsb : s ≤ b) :
      ∃ hU : Icc s b ⊆ U.domain,
        CompactPerturbationResult hsb alpha kernel f
          (Q hsb (hconn.out' hsI hb)) C epsilon (U.path hsb hU) := by
    let hI : Icc s b ⊆ I := hconn.out' hsI hb
    have hi : ‖f-energyPath _ (Q hsb hI) ⟨s,le_rfl,hsb⟩‖ ≤ epsilon := by
      rw [hQ]
      exact hf
    exact hs.2.2.2 hsb f (Q hsb hI) (E hsb hI)
      (hPDE hsb hI) (hE hsb hI) (hS hsb hI) heps hsmall hi (herr hsb hI)
  refine ⟨?_,fun hb hsb => solved _ hb hsb,?_⟩
  · intro t ht
    exact (Classical.choose (solved t ht.1 ht.2)) ⟨ht.2,le_rfl⟩
  · intro t ht
    let result := solved t ht.1 ht.2
    let hU : Icc s t ⊆ U.domain := Classical.choose result
    have hp : CompactPerturbationResult ht.2 alpha kernel f
        (Q ht.2 (hconn.out' hsI ht.1)) C epsilon (U.path ht.2 hU) :=
      Classical.choose_spec result
    have hb := (energyPointDifference_norm_le (U.path ht.2 hU)
      (Q ht.2 (hconn.out' hsI ht.1)) ⟨t,ht.2,le_rfl⟩).trans hp.2.2.2.2.1
    have hu : energyPath _ (U.path ht.2 hU) ⟨t,ht.2,le_rfl⟩ = U.state t :=
      U.path_agrees ht.2 hU ⟨t,ht.2,le_rfl⟩
    have hq : energyPath _ (Q ht.2 (hconn.out' hsI ht.1)) ⟨t,ht.2,le_rfl⟩ = q t :=
      hQ ht.2 (hconn.out' hsI ht.1) ⟨t,ht.2,le_rfl⟩
    exact (congrArg norm (congrArg₂ (fun x y : EnergyState => x-y) hu hq)).symm.le.trans hb

#print axioms energyPointDifference_norm_le
#print axioms exists_actual_forward_interval_perturbation
end HartreeF.IntervalPerturbation
