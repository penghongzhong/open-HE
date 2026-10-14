import FActualEnergyErrorBound
import FUniformRegularizedEndpoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace SobolevStretch StationarySelfTest CriticalPathSpace IntervalTimeTransport
open ForcingDomain ForcingL2 RegularizedEnergyPairing EndpointOutput
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  criticalL2Source regularizeCriticalPath actualL2Commutator actualGradientCommutator
  regularizedGradientLp regularizeEndpointWitness

theorem regularizedGradientLp_eq_endpoint (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b) (B6 : OrdinaryBesselLp 6) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) (j : Fin 3) :
    regularizedGradientLp hDensity hSob hab n u j =
      toLocalLp hab 2 ((regularizeEndpointWitness hDensity hSob B6 n W).field j) := by
  let R := regularizeEndpointWitness hDensity hSob B6 n W
  apply Lp.ext
  filter_upwards [regularizedGradientLp_agrees hDensity hSob hab n u j,
    toLocalLp_coeFn hab 2 (R.field j), ae_clamp hab (R.agrees j)] with t hv hr ha
  rw [hr]
  apply Lp.ext
  exact hv.trans (Filter.EventuallyEq.symm ha)

theorem regularizedGradientLp_uniform_bound (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b) (B6 : OrdinaryBesselLp 6) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) (j : Fin 3) :
    ‖regularizedGradientLp hDensity hSob hab n u j‖ ≤ 2 * ‖W.field j‖ := by
  let R := regularizeEndpointWitness hDensity hSob B6 n W
  calc
    _ = ‖toLocalLp hab 2 (R.field j)‖ :=
      congrArg norm (regularizedGradientLp_eq_endpoint hDensity hSob hab B6 n u W j)
    _ = ‖R.field j‖ := toLocalLp_norm hab 2 (R.field j)
    _ ≤ _ := regularizeEndpointWitness_norm_le hDensity hSob B6 n W j

/-- The error already has the exact parent n-uniform budget. W is an
actual endpoint witness, with its same-path agreement retained. -/
theorem actualRegularizedEnergyError_uniform_integral_bound (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (n : ℕ) (u : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) :
    ‖∫ t, actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t ∂localMeasure a b‖ ≤
      (∑ j : Fin 3, (2 * ‖W.field j‖) *
        ‖actualGradientCommutator hDensity hSob hH hab Bw Bs n u j‖) +
      ‖criticalL2Source (intervalMeasure a b) hDensity hSob hH
        (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u)‖ *
      ‖actualL2Commutator (intervalMeasure a b) hDensity hSob hH Bw n u‖ := by
  apply (actualRegularizedEnergyError_integral_bound hDensity hSob hH hab Bw Bs n u).trans
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right
    (regularizedGradientLp_uniform_bound hDensity hSob hab B6 n u W j) (norm_nonneg _)

#print axioms regularizedGradientLp_eq_endpoint
#print axioms regularizedGradientLp_uniform_bound
#print axioms actualRegularizedEnergyError_uniform_integral_bound
end HartreeF.Regularization.Actual
