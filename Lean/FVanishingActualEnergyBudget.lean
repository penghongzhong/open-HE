import FActualL2HartreeCommutator
import FActualGradientHartreeCommutator
import FUniformRegularizedEndpoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace HartreeF.Regularization.Actual
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest EndpointOutput
open ForcingDomain ForcingL2

attribute [local irreducible] energySubmodule criticalPathSubmodule criticalL2Source
  regularizeCriticalPath actualL2Commutator actualGradientCommutator

/-- The coefficient in the endpoint term is fixed before n. All residual
classes and the nonlinear L2 source are the actual previously constructed ones. -/
def actualEnergyErrorBudget (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) (n : ℕ) : ℝ :=
  (∑ j : Fin 3, (2 * ‖W.field j‖) *
    ‖actualGradientCommutator hDensity hSob hH hab Bw Bs n u j‖) +
    ‖criticalL2Source (intervalMeasure a b) hDensity hSob hH
      (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u)‖ *
      ‖actualL2Commutator (intervalMeasure a b) hDensity hSob hH Bw n u‖

theorem actualEnergyErrorBudget_nonneg (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) (n : ℕ) :
    0 ≤ actualEnergyErrorBudget hDensity hSob hH hab Bw Bs u W n := by
  unfold actualEnergyErrorBudget
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)

/-- The nonlinear factor itself has a finite limit; no assumed uniform
nonlinear bound is inserted into the error argument. -/
theorem regularized_actualL2Source_norm_tendsto (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (Bw : OrdinaryBesselLp criticalExponent) (u : CriticalPath (intervalMeasure a b)) :
    Tendsto (fun n => ‖criticalL2Source (intervalMeasure a b) hDensity hSob hH
      (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u)‖)
      atTop (𝓝 ‖criticalL2Source (intervalMeasure a b) hDensity hSob hH u‖) :=
  (((criticalL2Source_continuous (intervalMeasure a b) hDensity hSob hH).tendsto u).comp
    (regularizeCriticalPath_tendsto (intervalMeasure a b) hDensity hSob Bw u)).norm

/-- Every term of the actual conservation error budget tends to zero.
The subsequent increment identity must still connect energy change to this
budget; this theorem does not assume or assert conservation. -/
theorem actualEnergyErrorBudget_tendsto_zero (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) :
    Tendsto (actualEnergyErrorBudget hDensity hSob hH hab Bw Bs u W) atTop (𝓝 0) := by
  have hg (j : Fin 3) : Tendsto
      (fun n => (2 * ‖W.field j‖) *
        ‖actualGradientCommutator hDensity hSob hH hab Bw Bs n u j‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (actualGradientCommutator_norm_tendsto hDensity hSob hH hab Bw Bs u j).const_mul
        (2 * ‖W.field j‖)
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hg j)
  have hv := (regularized_actualL2Source_norm_tendsto hDensity hSob hH Bw u).mul
    (actualL2Commutator_norm_tendsto (intervalMeasure a b) hDensity hSob hH Bw u)
  change Tendsto (fun n => actualEnergyErrorBudget hDensity hSob hH hab Bw Bs u W n)
    atTop (𝓝 0)
  dsimp only [actualEnergyErrorBudget]
  simpa only [Finset.sum_const_zero, mul_zero, zero_add] using hs.add hv

#print axioms actualEnergyErrorBudget
#print axioms actualEnergyErrorBudget_nonneg
#print axioms regularized_actualL2Source_norm_tendsto
#print axioms actualEnergyErrorBudget_tendsto_zero
end HartreeF.Regularization.Actual
