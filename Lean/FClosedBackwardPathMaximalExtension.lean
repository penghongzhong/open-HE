import FSmallSTailContinuation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalUniqueness SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource

/-- The actual advanced path is rebased at its own left state, extended by
true centered local existence, and marked again at its given terminal datum. -/
theorem closed_backward_mildPath_extends_to_localTrajectory (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel T c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hTc : T ≤ c) (uc : EnergyState) (u : CriticalPath (intervalMeasure T c))
    (hu : IsBackwardMildHartreePath hTc alpha kernel uc u) :
    ∃ V : LocalMildTrajectory alpha kernel c uc,
      Set.Icc T c ⊆ V.domain ∧
      ∀ t : Set.Icc T c, V.state t = energyPath _ u t := by
  have hf := (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hTc uc u).mp hu
  have hh := backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH
    hTc uc u hf
  have hm := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hTc (energyPath _ u ⟨T, le_rfl, hTc⟩) u).mpr hh
  have hc : energyPath _ u ⟨c, hTc, le_rfl⟩ = uc := by
    rw [← hf]
    exact backwardHartreeDuhamelMap_terminal hDensity hSob h0 hfree hret hH hTc uc u
  obtain ⟨V, hV, he⟩ := closed_mildPath_extends_to_localTrajectory
    hDensity hSob h0 hfree hret hefree heret hH hTc
      (energyPath _ u ⟨T, le_rfl, hTc⟩) u hm
  exact ⟨V.recenterWithDatum c uc (hV ⟨hTc, le_rfl⟩)
    ((he ⟨c, hTc, le_rfl⟩).trans hc), hV, he⟩

/-- A closed literal backward path supplies an endpoint of the original
terminal-data maximal domain. -/
theorem closed_backward_mildPath_left_mem_maximalDomain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel T c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hTc : T ≤ c) (uc : EnergyState) (u : CriticalPath (intervalMeasure T c))
    (hu : IsBackwardMildHartreePath hTc alpha kernel uc u) :
    T ∈ maximalDomain alpha kernel c uc := by
  obtain ⟨V, hV, _⟩ := closed_backward_mildPath_extends_to_localTrajectory
    hDensity hSob h0 hfree hret hefree heret hH hTc uc u hu
  exact subset_maximalDomain V (hV ⟨le_rfl, hTc⟩)

/-- Marking the maximal trajectory at the old datum preserves the entire
old domain and produces a strict actual extension across the left endpoint. -/
theorem closed_backward_mildPath_gives_strict_trajectory_extension
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hTc : T ≤ c) (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hc : c ∈ U.domain) (hTU : T ∉ U.domain)
    (u : CriticalPath (intervalMeasure T c))
    (hu : IsBackwardMildHartreePath hTc alpha kernel (U.state c) u) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  let R := U.recenter c hc
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH c (U.state c)
  have hRV : R.domain ⊆ V.domain := subset_maximalDomain R
  have hTV : T ∈ V.domain := closed_backward_mildPath_left_mem_maximalDomain
    hDensity hSob h0 hfree hret hefree heret hH hTc (U.state c) u hu
  have hstrict : R.domain ⊂ V.domain := Set.ssubset_iff_subset_ne.mpr ⟨hRV, by
    intro he
    exact hTU (he.symm ▸ hTV)⟩
  have hEq : Set.EqOn V.state R.state R.domain := by
    intro t ht
    exact LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH V R (hRV ht) ht
  exact FiniteSContinuation.strict_extension_from_recenter U hc V hstrict hTV hEq

#print axioms closed_backward_mildPath_extends_to_localTrajectory
#print axioms closed_backward_mildPath_left_mem_maximalDomain
#print axioms closed_backward_mildPath_gives_strict_trajectory_extension
end HartreeF.MaximalTrajectory
