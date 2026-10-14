import FActualLocalFixedPoint

/-! Quantitative comparison of actual Hartree fixed points on a common finite
interval. The small W radius is selected before the interval, datum, or paths.
No uniqueness, contraction, or source-smallness conclusion is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalSolutionComparison
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath
open IntervalTimeTransport SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource energyPath criticalGradient

/-- Uniform source smallness and contraction for the literal map, with the
radius produced from a prescribed nonnegative energy cap. This is independent
of the finite interval and the arbitrary energy datum. -/
theorem exists_actual_source_smallness_and_contraction (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (u0 : EnergyState) (u v : CriticalPath (intervalMeasure a b)),
    ‖energyPath (intervalMeasure a b) u‖ ≤ B → ‖energyPath (intervalMeasure a b) v‖ ≤ B →
    ‖fun j => criticalGradient (intervalMeasure a b) j u‖ ≤ rho →
    ‖fun j => criticalGradient (intervalMeasure a b) j v‖ ≤ rho →
    (∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤
      (1 / (2 * (max (energyEndpointConstant K C0) Cr + 1))) * ‖u-v‖) ∧
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v‖ ≤ (1/2 : ℝ)*‖u-v‖ := by
  let Q := max (energyEndpointConstant K C0) Cr
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  let epsilon := 1 / (2 * (Q + 1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  let smallChoice := criticalPathIntervalSource_cap_uniform_smallness
    hDensity hSob hH hB hepsilon
  let rho : ℝ := Classical.choose smallChoice
  have hrho : 0 < rho := (Classical.choose_spec smallChoice).1
  have hrho1 : rho ≤ 1 := (Classical.choose_spec smallChoice).2.1
  refine ⟨rho, hrho, hrho1, ?_⟩
  intro a b hab u0 u v huE hvE huW hvW
  have hsrc := (Classical.choose_spec smallChoice).2.2 hab u v huE hvE huW hvW
  refine ⟨hsrc, ?_⟩
  have hdiff := hartreeDuhamelMap_sub_norm_of_gradient_bound hDensity hSob h0
    hfree hret hH hab u0 u v hsrc
  have hcoeff : Q * epsilon ≤ (1/2 : ℝ) := by
    dsimp [epsilon]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Q+1))).mpr
    linarith
  apply hdiff.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (u-v))

end HartreeF.LocalSolutionComparison
