import FLocalMildTrajectory
import FCenteredHartreeWholeMild

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput CenteredLocalSolution
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- The open interior of an actual centered finite mild path is a genuine
local solution. Every compact witness is obtained by actual path restriction. -/
def localTrajectoryOfCenteredPath (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b s0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (ha : a < s0) (hb : s0 < b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hcenter : energyPath _ u ⟨s0, ha.le, hb.le⟩ = u0)
    (hmild : IsMildHartreePath (ha.le.trans hb.le) alpha kernel
      (energyPath _ u ⟨a, le_rfl, ha.le.trans hb.le⟩) u) :
    LocalMildTrajectory alpha kernel s0 u0 where
  domain := Set.Ioo a b
  state := extendEnergyPath (ha.le.trans hb.le) (energyPath _ u)
  domain_open := isOpen_Ioo
  domain_connected := Set.ordConnected_Ioo
  center_mem := ⟨ha, hb⟩
  continuous := (extendEnergyPath (ha.le.trans hb.le) (energyPath _ u)).continuous.continuousOn
  initial := (extendEnergyPath_val (ha.le.trans hb.le)
    (energyPath _ u) ⟨s0, ha.le, hb.le⟩).trans hcenter
  compact := by
    intro c d hcd hI
    have hc : c ∈ Set.Ioo a b := hI ⟨le_rfl, hcd⟩
    have hd : d ∈ Set.Ioo a b := hI ⟨hcd, le_rfl⟩
    let v := restrictPath hc.1.le hcd hd.2.le u
    have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      (ha.le.trans hb.le) (energyPath _ u ⟨a, le_rfl, ha.le.trans hb.le⟩) u).mp hmild
    have hv := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
      hc.1.le hcd hd.2.le (energyPath _ u ⟨a, le_rfl, ha.le.trans hb.le⟩) u hfix
    have hdata : extendEnergyPath (ha.le.trans hb.le) (energyPath _ u) c =
        energyPath _ u ⟨c, hc.1.le, hcd.trans hd.2.le⟩ :=
      extendEnergyPath_val (ha.le.trans hb.le) (energyPath _ u)
        ⟨c, hc.1.le, hcd.trans hd.2.le⟩
    refine ⟨v, ?_, ?_⟩
    · intro t
      exact (restrictPath_energy hc.1.le hcd hd.2.le u t).trans
        (extendEnergyPath_val (ha.le.trans hb.le) (energyPath _ u)
          (intervalInclusion hc.1.le hd.2.le t)).symm
    · apply (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
        hcd (extendEnergyPath (ha.le.trans hb.le) (energyPath _ u) c) v).mpr
      exact (congrArg (fun z : EnergyState =>
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd z v) hdata).trans hv

/-- The ordinary eight analytic premises produce a nonempty actual local
solution family around every energy datum. No abstract local-existence input
is exposed at this interface. -/
theorem exists_localMildTrajectory (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (s0 : ℝ) (u0 : EnergyState) :
    Nonempty (LocalMildTrajectory alpha kernel s0 u0) := by
  let e := exists_actual_centered_whole_mild_fullZ
    hDensity hSob h0 hfree hret hefree heret hH s0 u0
  let a : ℝ := Classical.choose e
  let ea := Classical.choose_spec e
  let b : ℝ := Classical.choose ea
  let eb := Classical.choose_spec ea
  let ha : a < s0 := Classical.choose eb
  let ec := Classical.choose_spec eb
  let hb : s0 < b := Classical.choose ec
  let ed := Classical.choose_spec ec
  let u : CriticalPath (intervalMeasure a b) := Classical.choose ed
  let hu := Classical.choose_spec ed
  exact ⟨localTrajectoryOfCenteredPath hDensity hSob h0 hfree hret hH
    ha hb u0 u hu.1 hu.2.2⟩

end HartreeF.MaximalTrajectory
