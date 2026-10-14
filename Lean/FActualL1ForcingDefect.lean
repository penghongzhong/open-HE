import FActualDuhamelDefectStability
import FL1RetardedCriticalPath
import FActualFreePathDifference

/-! Quantitative defect production from the actual L1-source forced mild
identity. This file does not assume that a distributional PDE has already
been converted to this identity; that conversion is a separate bridge. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped NNReal Topology
namespace HartreeF.ActualPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient hartreeDuhamelMap criticalPathIntervalSource
  freeCriticalPath freeEnergyState

theorem actual_map_datum_difference (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f g : EnergyState) (q : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q =
    freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f) -
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) g) := by
  unfold hartreeDuhamelMap
  exact add_sub_add_right_eq_sub
    (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f))
    (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) g))
    (Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret
      (criticalPathIntervalSource hDensity hSob hH hab q 0))

theorem forcing_defect_algebra {E : Type*} [AddCommGroup E]
    (x y q z : E) (hq : q=y-z) : x-q=(x-y)+z := by rw [hq]; abel

/-- The defect uses only the actual initial-data difference and original
gradient source. The scalar error is L1, with no added L2 condition. -/
theorem actual_forced_mild_defect_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f g : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (E : CompatibleL1IntervalSource a b)
    (hforced : q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
      Complex.I • E.retardedCriticalPath hDensity hSob h0 hret) :
    ‖mildDefect hDensity hSob h0 hfree hret hH hab f q‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
        max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ := by
  let R := E.retardedCriticalPath hDensity hSob h0 hret
  let Φ := hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
  have heq : mildDefect hDensity hSob h0 hfree hret hH hab f q =
      (Φ f q-Φ g q)+Complex.I • R :=
    forcing_defect_algebra (Φ f q) (Φ g q) q (Complex.I • R) hforced
  have hdata : ‖Φ f q-Φ g q‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ :=
    (congrArg norm (actual_map_datum_difference hDensity hSob h0 hfree hret hH hab f g q)).trans_le
      (actual_shiftedFreeCriticalPath_difference_norm hDensity hSob hfree a b f g)
  have hR : ‖Complex.I • R‖ ≤ max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ :=
    (complexUnit_norm R).trans_le (E.retardedCriticalPath_norm_le hDensity hSob h0 hret)
  exact (congrArg norm heq).trans_le ((norm_add_le (Φ f q-Φ g q) (Complex.I • R)).trans (add_le_add hdata hR))

#print axioms actual_map_datum_difference
#print axioms forcing_defect_algebra
#print axioms actual_forced_mild_defect_bound
end HartreeF.ActualPerturbation
