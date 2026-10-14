import FDirectionalHartreeRebasing
import FHartreeSubintervalFixedPoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory
namespace HartreeF.CriticalPathRestriction
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- The actual restriction is backward mild with its own right endpoint value.
This follows from the proved two directional rebasings and the actual forward
restriction, so no extra advanced-integral splitting premise is needed. -/
theorem restrictPath_backward_hartree_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b c d : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (ub : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hfix : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH
      (hac.trans (hcd.trans hdb)) ub u = u) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd
      (energyPath _ u ⟨d, hac.trans hcd, hdb⟩)
      (restrictPath hac hcd hdb u) = restrictPath hac hcd hdb u := by
  let hab : a ≤ b := hac.trans (hcd.trans hdb)
  let u0 : EnergyState := energyPath _ u ⟨a, le_rfl, hab⟩
  have hfwd := backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH
    hab ub u hfix
  have hres := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    hac hcd hdb u0 u hfwd
  have hback := forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH
    hcd (energyPath _ u ⟨c, hac, hcd.trans hdb⟩) (restrictPath hac hcd hdb u) hres
  have hend := restrictPath_energy hac hcd hdb u (⟨d, hcd, le_rfl⟩ : Set.Icc c d)
  exact (congrArg (fun x : EnergyState =>
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd x
      (restrictPath hac hcd hdb u)) hend).symm.trans hback

end HartreeF.CriticalPathRestriction
