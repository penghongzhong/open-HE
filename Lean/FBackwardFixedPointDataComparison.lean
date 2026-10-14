import FBackwardHartreeDataDifference
import FActualBackwardLocalComparison

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
namespace HartreeF.WaveCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open BackwardUniformData BackwardSolutionComparison
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource

/-- Different genuine terminal data are compared in the same full graph.
The small radius is produced from B, independently of the interval and data. -/
theorem exists_backward_two_data_comparison (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0 ≤ B) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f g : EnergyState) (u v : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ u‖ ≤ B → ‖energyPath _ v‖ ≤ B →
      ‖fun j => criticalGradient _ j u‖ ≤ rho →
      ‖fun j => criticalGradient _ j v‖ ≤ rho →
      (‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u -
          backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g v‖ ≤
        max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ + (1/2:ℝ)*‖u-v‖) ∧
      (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u →
       backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g v = v →
       ‖u-v‖ ≤ 2 * max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖) := by
  let chosen := exists_actual_backward_source_smallness_and_contraction
    hDensity hSob h0 hfree hret hH hB
  let rho : ℝ := Classical.choose chosen
  have hrho : 0 < rho := (Classical.choose_spec chosen).1
  have hrho1 : rho ≤ 1 := (Classical.choose_spec chosen).2.1
  refine ⟨rho,hrho,hrho1,?_⟩
  intro a b hab f g u v huE hvE huW hvW
  have hc := ((Classical.choose_spec chosen).2.2 hab g u v huE hvE huW hvW).2
  let P := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
  let z := freeCriticalPath hDensity hSob hfree a b
    (freeEnergyState hDensity hSob (-b) (f-g))
  have he : P f u-P g v = z+(P g u-P g v) :=
    actual_backwardHartreeDuhamelMap_two_data_split hDensity hSob h0 hfree hret hH hab f g u v
  have hz : ‖z‖ ≤ max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ :=
    actual_backwardFreeCriticalPath_norm_le hDensity hSob hfree a b (f-g)
  have hb := (congrArg norm he).le.trans
    ((norm_add_le z (P g u-P g v)).trans (add_le_add hz hc))
  refine ⟨hb,?_⟩
  intro hu hv
  have hefix : P f u-P g v=u-v :=
    congrArg₂ (fun x y : CriticalPath (intervalMeasure a b) => x-y) hu hv
  have hbound := (congrArg norm hefix).symm.le.trans hb
  linarith only [hbound]

end HartreeF.WaveCauchy
