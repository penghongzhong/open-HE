import FBackwardFreePathDifference
import FActualBackwardHartreeMap
import Mathlib.Tactic.Abel

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.BackwardUniformData
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule freeCriticalPath
  energyPath criticalGradient freeEnergyState backwardHartreeDuhamelMap
  intervalAdvancedCriticalPath criticalPathIntervalSource

theorem cancel_common_subtrahend {E : Type*} [AddCommGroup E] (f g r : E) :
    (f-r)-(g-r) = f-g := by abel

/-- The actual nonlinear future terms cancel when only the terminal datum changes. -/
theorem actual_backwardHartreeDuhamelMap_data_sub (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 v0 : EnergyState) (u : CriticalPath (intervalMeasure a b)) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 u =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) (u0-v0)) := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) u0)
  let g := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) v0)
  let r := Complex.I • intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold backwardHartreeDuhamelMap
  change (f-r)-(g-r) = _
  exact (cancel_common_subtrahend f g r).trans
    (actual_backwardFreeCriticalPath_sub hDensity hSob hfree a b u0 v0)

/-- The literal two-terminal-data map splits in the unchanged actual graph. -/
theorem actual_backwardHartreeDuhamelMap_two_data_split (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 v0 : EnergyState) (u v : CriticalPath (intervalMeasure a b)) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) (u0-v0)) +
      (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 u -
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v) := by
  let P := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
  exact (sub_add_sub_cancel (P u0 u) (P v0 u) (P v0 v)).symm.trans
    (congrArg (fun x : CriticalPath (intervalMeasure a b) => x + (P v0 u-P v0 v))
      (actual_backwardHartreeDuhamelMap_data_sub hDensity hSob h0 hfree hret hH hab u0 v0 u))

end HartreeF.BackwardUniformData
