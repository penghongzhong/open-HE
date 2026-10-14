import FClosedMildPathMaximalExtension
import FClosedBackwardPathMaximalExtension

/-! Genuine closed solutions identify with the one already constructed
maximal trajectory. These consumers are used after finite perturbation gluing. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  hartreeDuhamelMap backwardHartreeDuhamelMap

theorem actual_maximal_path_eq_of_local_extension (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b))
    (V : LocalMildTrajectory alpha kernel s0 u0) (hV : Icc a b ⊆ V.domain)
    (hstate : ∀ t : Icc a b, V.state t = energyPath _ u t) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
    ∃ hI : Icc a b ⊆ U.domain, U.path hab hI = u := by
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
  have hI : Icc a b ⊆ U.domain := fun t ht => subset_maximalDomain V (hV ht)
  refine ⟨hI, ?_⟩
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  have hmax : U.state t = V.state t :=
    maximalState_agrees hDensity hSob h0 hfree hret hH V (hV t.property)
  exact (U.path_agrees hab hI t).trans (hmax.trans (hstate t))

theorem actual_maximal_path_eq_of_closed_forward (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (f : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hu : IsMildHartreePath hab alpha kernel f u) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a f
    ∃ hI : Icc a b ⊆ U.domain, U.path hab hI = u := by
  obtain ⟨V, hV, hs⟩ := closed_mildPath_extends_to_localTrajectory
    hDensity hSob h0 hfree hret hefree heret hH hab f u hu
  exact actual_maximal_path_eq_of_local_extension hDensity hSob h0 hfree hret
    hefree heret hH f hab u V hV hs

theorem actual_maximal_path_eq_of_closed_backward (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (f : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hu : IsBackwardMildHartreePath hab alpha kernel f u) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH b f
    ∃ hI : Icc a b ⊆ U.domain, U.path hab hI = u := by
  obtain ⟨V, hV, hs⟩ := closed_backward_mildPath_extends_to_localTrajectory
    hDensity hSob h0 hfree hret hefree heret hH hab f u hu
  exact actual_maximal_path_eq_of_local_extension hDensity hSob h0 hfree hret
    hefree heret hH f hab u V hV hs

#print axioms actual_maximal_path_eq_of_local_extension
#print axioms actual_maximal_path_eq_of_closed_forward
#print axioms actual_maximal_path_eq_of_closed_backward
end HartreeF.MaximalTrajectory
