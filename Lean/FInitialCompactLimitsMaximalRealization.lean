import FNegativeInitialCauchyFamily
import FClosedBackwardPathMaximalExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.IncomingWaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalUniqueness MaximalTrajectory
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest Retarded
open ActualStrichartz ForcingDomain EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath IsBackwardMildHartreePath

/-- The common right datum is the actual energy value of the singleton limit. -/
def incomingCompactLimitDatum {T : ℝ}
    (V : ∀ S : ℝ, S≤T → CriticalPath (intervalMeasure S T)) : EnergyState :=
  energyPath _ (V T le_rfl) ⟨T,le_rfl,le_rfl⟩

/-- Compatibility proves the SAME right energy trace for every compact limit. -/
theorem compatibleInitialCompactLimits_terminal {T : ℝ}
    (V : ∀ S : ℝ, S≤T → CriticalPath (intervalMeasure S T))
    (hV : ∀ S R (hST : S≤T) (hRS : R≤S),
      restrictPath hRS hST le_rfl (V R (hRS.trans hST))=V S hST)
    (S : ℝ) (hST : S≤T) :
    energyPath _ (V S hST) ⟨T,hST,le_rfl⟩=incomingCompactLimitDatum V := by
  have hc := hV T S le_rfl hST
  have hv := congrArg (fun u : CriticalPath (intervalMeasure T T) =>
    energyPath _ u ⟨T,le_rfl,le_rfl⟩) hc
  exact (restrictPath_energy hST le_rfl le_rfl (V S hST)
    (⟨T,le_rfl,le_rfl⟩ : Icc T T)).symm.trans hv

/-- Actual closed-backward extension places all compact limits in the SAME
canonical maximal domain marked at the common right trace. -/
theorem compatibleInitialCompactLimits_maximal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (V : ∀ S : ℝ, S≤T → CriticalPath (intervalMeasure S T))
    (hV : ∀ S R (hST : S≤T) (hRS : R≤S),
      restrictPath hRS hST le_rfl (V R (hRS.trans hST))=V S hST)
    (hmild : ∀ S (hST : S≤T), IsBackwardMildHartreePath hST alpha kernel
      (energyPath _ (V S hST) ⟨T,hST,le_rfl⟩) (V S hST)) :
    Iic T ⊆ maximalDomain alpha kernel T (incomingCompactLimitDatum V) ∧
    ∀ S (hST : S≤T) (t : Icc S T),
      maximalState alpha kernel T (incomingCompactLimitDatum V) t=energyPath _ (V S hST) t := by
  have extended : ∀ S (hST : S≤T),
      ∃ M : LocalMildTrajectory alpha kernel T (incomingCompactLimitDatum V),
        Icc S T ⊆ M.domain ∧ ∀ t : Icc S T, M.state t=energyPath _ (V S hST) t := by
    intro S hST
    have hi := compatibleInitialCompactLimits_terminal V hV S hST
    have hm : IsBackwardMildHartreePath hST alpha kernel (incomingCompactLimitDatum V) (V S hST) :=
      hi ▸ hmild S hST
    exact closed_backward_mildPath_extends_to_localTrajectory
      hDensity hSob h0 hfree hret hefree heret hH hST (incomingCompactLimitDatum V) (V S hST) hm
  constructor
  · intro t ht
    let choice := extended t ht
    let M := Classical.choose choice
    exact subset_maximalDomain M ((Classical.choose_spec choice).1 ⟨le_rfl,ht⟩)
  · intro S hST t
    let choice := extended S hST
    let M := Classical.choose choice
    have htM : (t:ℝ)∈M.domain := (Classical.choose_spec choice).1 t.property
    exact (maximalState_agrees hDensity hSob h0 hfree hret hH M htM).trans
      ((Classical.choose_spec choice).2 t)

end HartreeF.IncomingWaveRealization
