import FActualBackwardIntervalPerturbation

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
open CompactLongTimePerturbation BackwardCompactLongTimePerturbation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource

/-- Enlarging the bound preserves every property of the same actual forward path. -/
theorem compactPerturbationResult_mono_bound {a b alpha kernel C1 C2 epsilon : ℝ}
    (hab : a ≤ b) (f : EnergyState) (q u : CriticalPath (intervalMeasure a b))
    (heps : 0 ≤ epsilon) (hC : C1 ≤ C2)
    (hu : CompactPerturbationResult hab alpha kernel f q C1 epsilon u) :
    CompactPerturbationResult hab alpha kernel f q C2 epsilon u :=
  ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,
    hu.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hC heps),
    hu.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC heps)),
    hu.2.2.2.2.2.2⟩

/-- Enlarging the bound preserves every property of the same actual terminal path. -/
theorem compactBackwardPerturbationResult_mono_bound {a b alpha kernel C1 C2 epsilon : ℝ}
    (hab : a ≤ b) (f : EnergyState) (q u : CriticalPath (intervalMeasure a b))
    (heps : 0 ≤ epsilon) (hC : C1 ≤ C2)
    (hu : CompactBackwardPerturbationResult hab alpha kernel f q C1 epsilon u) :
    CompactBackwardPerturbationResult hab alpha kernel f q C2 epsilon u :=
  ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,
    hu.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hC heps),
    hu.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC heps)),
    hu.2.2.2.2.2.2⟩

/-- The actual forward and backward constructions share the original datum and
therefore the same maximal trajectory. Uniform constants precede all interval
data; the complete two anchored compact specifications and whole-interval
pointwise estimate are retained. Global mixed-Lp exhaustion is a separate step. -/
theorem exists_actual_two_sided_interval_perturbation (hDensity : OrdinaryH1Density)
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
      I ⊆ U.domain ∧
      (∀ {b : ℝ} (hb : b ∈ I) (hsb : s ≤ b),
        ∃ hU : Icc s b ⊆ U.domain,
          CompactPerturbationResult hsb alpha kernel f
            (Q hsb (hconn.out' hsI hb)) C epsilon (U.path hsb hU)) ∧
      (∀ {a : ℝ} (ha : a ∈ I) (has : a ≤ s),
        ∃ hU : Icc a s ⊆ U.domain,
          CompactBackwardPerturbationResult has alpha kernel f
            (Q has (hconn.out' ha hsI)) C epsilon (U.path has hU)) ∧
      ∀ t ∈ I, ‖U.state t-q t‖ ≤ C*epsilon := by
  let rightChoice := exists_actual_forward_interval_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilonR : ℝ := Classical.choose rightChoice
  let rightConstants := Classical.choose_spec rightChoice
  let CR : ℝ := Classical.choose rightConstants
  have hr := Classical.choose_spec rightConstants
  let leftChoice := exists_actual_backward_interval_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilonL : ℝ := Classical.choose leftChoice
  let leftConstants := Classical.choose_spec leftChoice
  let CL : ℝ := Classical.choose leftConstants
  have hl := Classical.choose_spec leftConstants
  refine ⟨min epsilonR epsilonL,max CR CL,lt_min hr.1 hl.1,
    (min_le_left _ _).trans hr.2.1,hr.2.2.1.trans_le (le_max_left _ _),?_⟩
  intro I hconn s epsilon hsI f q Q E hQ hPDE hE hS herr heps hsmall hf
  have right := hr.2.2.2 I hconn hsI f q Q E hQ hPDE hE hS herr heps
    (hsmall.trans (min_le_left _ _)) hf
  have left := hl.2.2.2 I hconn hsI f q Q E hQ hPDE hE hS herr heps
    (hsmall.trans (min_le_right _ _)) hf
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    by_cases hst : s ≤ t
    · exact right.1 ⟨ht,hst⟩
    · exact left.1 ⟨ht,(le_of_not_ge hst)⟩
  · intro b hb hsb
    let solved := right.2.1 hb hsb
    let hU : Icc s b ⊆ U.domain := Classical.choose solved
    exact ⟨hU,compactPerturbationResult_mono_bound hsb f _ _ heps
      (le_max_left CR CL) (Classical.choose_spec solved)⟩
  · intro a ha has
    let solved := left.2.1 ha has
    let hU : Icc a s ⊆ U.domain := Classical.choose solved
    exact ⟨hU,compactBackwardPerturbationResult_mono_bound has f _ _ heps
      (le_max_right CR CL) (Classical.choose_spec solved)⟩
  · intro t ht
    by_cases hst : s ≤ t
    · exact (right.2.2 t ⟨ht,hst⟩).trans (mul_le_mul_of_nonneg_right (le_max_left CR CL) heps)
    · exact (left.2.2 t ⟨ht,le_of_not_ge hst⟩).trans
        (mul_le_mul_of_nonneg_right (le_max_right CR CL) heps)

end HartreeF.IntervalPerturbation
