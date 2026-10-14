import FCriticalPathL2DifferenceBound
import FNormBallContinuity
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingL2
open ForcingDomain TimeHolder EnergySpace CriticalPathSpace CriticalJointSources
open SobolevStretch StationarySelfTest CriticalSourceBounds ForcingL2Difference
attribute [local irreducible] jointFields l2Source criticalL2Source energyPath energyValue
  energySubmodule criticalPathSubmodule criticalGradient energyGradient

universe uTime
variable {T : Type uTime} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (mu : Measure T) [SigmaFinite mu]

/-- Every bounded path ball has a finite Lipschitz constant for its actual L² source. -/
theorem criticalL2Source_lipschitzOn_norm_ball (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (R : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (criticalL2Source mu hDensity hSob hH)
      {u : CriticalPath mu | ‖u‖ ≤ R} :=
  lipschitz_norm_ball_of_forcing_budget alpha hH.order_pos hH.order_lt_three
    (criticalL2Source mu hDensity hSob hH) (pathEnergySize mu) (pathValueSize mu)
    (fun u v => mixedNorm mu volume ∞ 6 (fun t => (jointFields mu u).u t - (jointFields mu v).u t))
    (fun u v => mixedNorm mu volume 10 10 (fun t => (jointFields mu u).u t - (jointFields mu v).u t))
    (criticalL2Source_difference_bound mu hDensity hSob hH)
    (critical_common_l2_input_bound mu hDensity hSob) R

/-- Continuity of the actual Bochner map in the canonical E+W path topology. -/
theorem criticalL2Source_continuous (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) :
    Continuous (criticalL2Source mu hDensity hSob hH) :=
  continuous_of_lipschitz_norm_balls (criticalL2Source mu hDensity hSob hH)
    (criticalL2Source_lipschitzOn_norm_ball mu hDensity hSob hH)

#print axioms criticalL2Source_lipschitzOn_norm_ball
#print axioms criticalL2Source_continuous
end HartreeF.ForcingL2
