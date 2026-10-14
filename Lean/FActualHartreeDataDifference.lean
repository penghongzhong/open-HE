import FActualFreePathDifference
import FActualHartreeDuhamelDifference

/-! Data dependence of the literal Hartree map on a given finite interval.
This does not assert the existence of a common nonlinear interval. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FreeDataDependence
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule freeCriticalPath
  energyPath criticalGradient freeEnergyState hartreeDuhamelMap
  intervalRetardedCriticalPath criticalPathIntervalSource

/-- Holding the nonlinear path fixed makes the actual nonlinear terms cancel. -/
theorem actual_hartreeDuhamelMap_data_sub (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 v0 : EnergyState) (u : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 u =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) (u0-v0)) := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let g := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) v0)
  let r := Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold hartreeDuhamelMap
  change (f+r) - (g+r) = _
  exact (add_sub_add_right_eq_sub f g r).trans
    (actual_shiftedFreeCriticalPath_sub hDensity hSob hfree a b u0 v0)

/-- Exact decomposition into the actual free-data difference and the existing
same-datum nonlinear difference, with equality in the entire graph path. -/
theorem actual_hartreeDuhamelMap_two_data_split (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 v0 : EnergyState) (u v : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) (u0-v0)) +
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 u -
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v) := by
  let P := hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
  exact (sub_add_sub_cancel (P u0 u) (P v0 u) (P v0 v)).symm.trans
    (congrArg (fun x : CriticalPath (intervalMeasure a b) => x + (P v0 u - P v0 v))
      (actual_hartreeDuhamelMap_data_sub hDensity hSob h0 hfree hret hH hab u0 v0 u))

/-- The two-data identity retains the literal retarded forcing-difference source. -/
theorem actual_hartreeDuhamelMap_two_data_sub (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 v0 : EnergyState) (u v : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) (u0-v0)) +
      Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret
        (criticalPathIntervalSource hDensity hSob hH hab u v) := by
  exact (actual_hartreeDuhamelMap_two_data_split hDensity hSob h0 hfree hret hH hab
    u0 v0 u v).trans (congrArg
      (fun x : CriticalPath (intervalMeasure a b) =>
        freeCriticalPath hDensity hSob hfree a b
          (freeEnergyState hDensity hSob (-a) (u0-v0)) + x)
      (hartreeDuhamelMap_sub hDensity hSob h0 hfree hret hH hab v0 u v))

/-- Quantitative two-data bound in the unchanged full E+W path norm.
Both constants are derived by the existing linear estimates, and the source
is the actual Hartree forcing difference. There is no output-bound premise. -/
theorem actual_hartreeDuhamelMap_two_data_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 v0 : EnergyState) (u v : CriticalPath (intervalMeasure a b)) :
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖u0-v0‖ +
      max (energyEndpointConstant K C0) Cr *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient‖ := by
  apply (congrArg (fun x : CriticalPath (intervalMeasure a b) => ‖x‖)
    (actual_hartreeDuhamelMap_two_data_split hDensity hSob h0 hfree hret hH hab
      u0 v0 u v)).le.trans
  exact (norm_add_le _ _).trans (add_le_add
    (actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b (u0-v0))
    (hartreeDuhamelMap_sub_norm hDensity hSob h0 hfree hret hH hab v0 u v))

/-- Coordinatewise control of the constructed input source transfers to the
full two-data map estimate. This premise concerns forcing, not the output. -/
theorem actual_hartreeDuhamelMap_two_data_norm_of_gradient_bound
    (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha c a b B : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 v0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b))
    (hB : ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤ B) :
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖u0-v0‖ +
      max (energyEndpointConstant K C0) Cr * B := by
  apply (congrArg (fun x : CriticalPath (intervalMeasure a b) => ‖x‖)
    (actual_hartreeDuhamelMap_two_data_split hDensity hSob h0 hfree hret hH hab
      u0 v0 u v)).le.trans
  exact (norm_add_le _ _).trans (add_le_add
    (actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b (u0-v0))
    (hartreeDuhamelMap_sub_norm_of_gradient_bound hDensity hSob h0 hfree hret hH hab v0 u v hB))

end HartreeF.FreeDataDependence
