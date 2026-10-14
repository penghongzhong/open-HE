import FActualEnergyErrorUniformBound
import FVanishingActualEnergyBudget

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest EndpointOutput
open ForcingDomain ForcingL2 IntervalTimeTransport
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  criticalL2Source regularizeCriticalPath actualL2Commutator actualGradientCommutator
  actualRegularizedEnergyError

/-- The integral of the actual, integrable error tends to zero. This result
uses the actual endpoint witness and the native strong regularization limits.
The identity between this error and the energy derivative is a separate node. -/
theorem actualRegularizedEnergyError_integral_tendsto_zero (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) :
    Tendsto (fun n => ∫ t, actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t
      ∂localMeasure a b) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := actualEnergyErrorBudget hDensity hSob hH hab Bw Bs u W)
  · intro n
    exact actualRegularizedEnergyError_uniform_integral_bound hDensity hSob hH hab Bw Bs B6 n u W
  · exact actualEnergyErrorBudget_tendsto_zero hDensity hSob hH hab Bw Bs u W

/-- A single result retains genuine Bochner integrability and convergence for
the same literal family, so the zero convention for undefined integrals cannot
supply the limiting conclusion. -/
theorem actualRegularizedEnergyError_integrable_and_vanishing (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) :
    (∀ n, Integrable (actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u)
      (localMeasure a b)) ∧
    Tendsto (fun n => ∫ t, actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t
      ∂localMeasure a b) atTop (𝓝 0) :=
  ⟨fun n => actualRegularizedEnergyError_integrable hDensity hSob hH hab Bw Bs n u,
    actualRegularizedEnergyError_integral_tendsto_zero hDensity hSob hH hab Bw Bs B6 u W⟩

#print axioms actualRegularizedEnergyError_integral_tendsto_zero
#print axioms actualRegularizedEnergyError_integrable_and_vanishing
end HartreeF.Regularization.Actual
