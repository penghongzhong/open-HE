import FActualSourceCapContraction

/-! Quantitative comparison of actual Hartree fixed points on a common finite
interval. The small W radius is selected before the interval, datum, or paths.
No uniqueness, contraction, or source-smallness conclusion is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option diagnostics true
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalSolutionComparison
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath
open IntervalTimeTransport SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource energyPath criticalGradient

/-- Elementary absorption for two fixed points in any normed additive group. -/
theorem fixedPoints_eq_of_norm_half {E : Type*} [NormedAddCommGroup E]
    (Phi : E → E) (u v : E) (hu : Phi u = u) (hv : Phi v = v)
    (hc : ‖Phi u-Phi v‖ ≤ (1/2 : ℝ)*‖u-v‖) : u = v := by
  rw [hu, hv] at hc
  have hn : ‖u-v‖ = 0 := le_antisymm (by linarith) (norm_nonneg (u-v))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Any two actual fixed points for the same arbitrary datum are equal as
CriticalPaths when their actual E and W coordinates obey the produced caps.
The fixed-point and cap hypotheses define the two solutions being compared. -/
theorem exists_actual_local_fixedPoint_unique (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (u0 : EnergyState) (u v : CriticalPath (intervalMeasure a b)),
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u →
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v = v →
    ‖energyPath (intervalMeasure a b) u‖ ≤ B → ‖energyPath (intervalMeasure a b) v‖ ≤ B →
    ‖fun j => criticalGradient (intervalMeasure a b) j u‖ ≤ rho →
    ‖fun j => criticalGradient (intervalMeasure a b) j v‖ ≤ rho → u = v := by
  let comparisonChoice :=
    exists_actual_source_smallness_and_contraction hDensity hSob h0 hfree hret hH hB
  let rho : ℝ := Classical.choose comparisonChoice
  have hrho : 0 < rho := (Classical.choose_spec comparisonChoice).1
  have hrho1 : rho ≤ 1 := (Classical.choose_spec comparisonChoice).2.1
  refine ⟨rho, hrho, hrho1, ?_⟩
  intro a b hab u0 u v hfixu hfixv huE hvE huW hvW
  have hc := ((Classical.choose_spec comparisonChoice).2.2 hab u0 u v huE hvE huW hvW).2
  exact fixedPoints_eq_of_norm_half
    (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0) u v hfixu hfixv hc

end HartreeF.LocalSolutionComparison
