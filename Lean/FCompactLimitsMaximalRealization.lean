import FPositiveTerminalCauchyFamily
import FClosedMildPathMaximalExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalUniqueness MaximalTrajectory
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest Retarded
open ActualStrichartz ForcingDomain EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath IsMildHartreePath

/-- The common datum is selected from the genuine singleton compact limit. -/
def compactLimitDatum {T : ℝ}
    (V : ∀ S : ℝ, T≤S → CriticalPath (intervalMeasure T S)) : EnergyState :=
  energyPath _ (V T le_rfl) ⟨T,le_rfl,le_rfl⟩

/-- Restriction compatibility proves the SAME left trace for all compact limits. -/
theorem compatibleCompactLimits_initial {T : ℝ}
    (V : ∀ S : ℝ, T≤S → CriticalPath (intervalMeasure T S))
    (hV : ∀ S R (hTS : T≤S) (hSR : S≤R),
      restrictPath le_rfl hTS hSR (V R (hTS.trans hSR))=V S hTS)
    (S : ℝ) (hTS : T≤S) :
    energyPath _ (V S hTS) ⟨T,le_rfl,hTS⟩=compactLimitDatum V := by
  have hc := hV T S le_rfl hTS
  have hv := congrArg (fun u : CriticalPath (intervalMeasure T T) =>
    energyPath _ u ⟨T,le_rfl,le_rfl⟩) hc
  exact (restrictPath_energy le_rfl le_rfl hTS (V S hTS)
    (⟨T,le_rfl,le_rfl⟩ : Icc T T)).symm.trans hv

/-- The accepted closed-mild extension theorem places every compatible
compact limit in the SAME canonical maximal domain and identifies its state. -/
theorem compatibleCompactLimits_maximal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (V : ∀ S : ℝ, T≤S → CriticalPath (intervalMeasure T S))
    (hV : ∀ S R (hTS : T≤S) (hSR : S≤R),
      restrictPath le_rfl hTS hSR (V R (hTS.trans hSR))=V S hTS)
    (hmild : ∀ S (hTS : T≤S), IsMildHartreePath hTS alpha kernel
      (energyPath _ (V S hTS) ⟨T,le_rfl,hTS⟩) (V S hTS)) :
    Ici T ⊆ maximalDomain alpha kernel T (compactLimitDatum V) ∧
    ∀ S (hTS : T≤S) (t : Icc T S),
      maximalState alpha kernel T (compactLimitDatum V) t=energyPath _ (V S hTS) t := by
  have extended : ∀ S (hTS : T≤S),
      ∃ M : LocalMildTrajectory alpha kernel T (compactLimitDatum V),
        Icc T S ⊆ M.domain ∧ ∀ t : Icc T S, M.state t=energyPath _ (V S hTS) t := by
    intro S hTS
    have hi := compatibleCompactLimits_initial V hV S hTS
    have hm : IsMildHartreePath hTS alpha kernel (compactLimitDatum V) (V S hTS) :=
      hi ▸ hmild S hTS
    exact closed_mildPath_extends_to_localTrajectory
      hDensity hSob h0 hfree hret hefree heret hH hTS (compactLimitDatum V) (V S hTS) hm
  constructor
  · intro t ht
    let choice := extended t ht
    let M := Classical.choose choice
    exact subset_maximalDomain M ((Classical.choose_spec choice).1 ⟨ht,le_rfl⟩)
  · intro S hTS t
    let choice := extended S hTS
    let M := Classical.choose choice
    have htM : (t:ℝ)∈M.domain := (Classical.choose_spec choice).1 t.property
    exact (maximalState_agrees hDensity hSob h0 hfree hret hH M htM).trans
      ((Classical.choose_spec choice).2 t)

end HartreeF.WaveRealization
