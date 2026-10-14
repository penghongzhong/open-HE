import FRegularizedGradientPath
import FRealPairingBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace IntervalTimeTransport ForcingDomain ForcingL2 RegularizedEnergyPairing
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  criticalL2Source regularizeCriticalPath actualL2Commutator actualGradientCommutator

def actualRegularizedNonlinearityLocal (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) : Lp EnergySpace.L2 2 (localMeasure a b) :=
  toLocalLp hab 2 (criticalL2Source (intervalMeasure a b) hDensity hSob hH
    (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u))

def actualRegularizedResidualLocal (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) : Lp EnergySpace.L2 2 (localMeasure a b) :=
  toLocalLp hab 2 (actualL2Commutator (intervalMeasure a b) hDensity hSob hH Bw n u)

def actualRegularizedEnergyError (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (Bw : OrdinaryBesselLp criticalExponent) (Bs : OrdinaryBesselLp sourceExponent)
    (n : ℕ) (u : CriticalPath (intervalMeasure a b)) (t : ℝ) : ℝ :=
  (∑ j : Fin 3, sourceIPair (actualGradientCommutator hDensity hSob hH hab Bw Bs n u j t)
    (regularizedGradientLp hDensity hSob hab n u j t)) -
  inner ℝ (actualRegularizedNonlinearityLocal hDensity hSob hH hab Bw n u t)
    (Complex.I • actualRegularizedResidualLocal hDensity hSob hH hab Bw n u t)

/-- Both Bochner products have actual L2 representatives. Measurability and
integrability are proved before either the FTC substitution or the bound. -/
theorem actualRegularizedEnergyError_integrable (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (n : ℕ) (u : CriticalPath (intervalMeasure a b)) :
    Integrable (actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u) (localMeasure a b) := by
  apply Integrable.sub
  · apply integrable_finsetSum
    intro j _
    exact gradient_error_integrable (localMeasure a b)
      (actualGradientCommutator hDensity hSob hH hab Bw Bs n u j)
      (regularizedGradientLp hDensity hSob hab n u j)
  · exact scalar_error_integrable (localMeasure a b)
      (actualRegularizedResidualLocal hDensity hSob hH hab Bw n u)
      (actualRegularizedNonlinearityLocal hDensity hSob hH hab Bw n u)

/-- The exact coefficient-one error budget, evaluated on the actual
regularized path and actual Hartree residual classes. -/
theorem actualRegularizedEnergyError_integral_bound (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (n : ℕ) (u : CriticalPath (intervalMeasure a b)) :
    ‖∫ t, actualRegularizedEnergyError hDensity hSob hH hab Bw Bs n u t ∂localMeasure a b‖ ≤
      (∑ j : Fin 3, ‖regularizedGradientLp hDensity hSob hab n u j‖ *
        ‖actualGradientCommutator hDensity hSob hH hab Bw Bs n u j‖) +
      ‖criticalL2Source (intervalMeasure a b) hDensity hSob hH
        (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u)‖ *
      ‖actualL2Commutator (intervalMeasure a b) hDensity hSob hH Bw n u‖ := by
  let R := actualRegularizedResidualLocal hDensity hSob hH hab Bw n u
  let N := actualRegularizedNonlinearityLocal hDensity hSob hH hab Bw n u
  let A := fun j : Fin 3 => actualGradientCommutator hDensity hSob hH hab Bw Bs n u j
  let V := fun j : Fin 3 => regularizedGradientLp hDensity hSob hab n u j
  have hi (j : Fin 3) : Integrable (fun t => sourceIPair (A j t) (V j t)) (localMeasure a b) :=
    gradient_error_integrable (localMeasure a b) (A j) (V j)
  have hN := scalar_error_integrable (localMeasure a b) R N
  have hRnorm : ‖R‖ = ‖actualL2Commutator (intervalMeasure a b) hDensity hSob hH Bw n u‖ :=
    toLocalLp_norm hab 2 _
  have hNnorm : ‖N‖ = ‖criticalL2Source (intervalMeasure a b) hDensity hSob hH
      (regularizeCriticalPath (intervalMeasure a b) hDensity hSob Bw n u)‖ :=
    toLocalLp_norm hab 2 _
  change ‖∫ t, (∑ j : Fin 3, sourceIPair (A j t) (V j t)) -
    inner ℝ (N t) (Complex.I • R t) ∂localMeasure a b‖ ≤ _
  rw [integral_sub (integrable_finsetSum _ (fun j _ => hi j)) hN,
    integral_finsetSum _ (fun j _ => hi j)]
  calc
    _ ≤ ‖∑ j : Fin 3, ∫ t, sourceIPair (A j t) (V j t) ∂localMeasure a b‖ +
        ‖∫ t, inner ℝ (N t) (Complex.I • R t) ∂localMeasure a b‖ := norm_sub_le _ _
    _ ≤ (∑ j : Fin 3, ‖∫ t, sourceIPair (A j t) (V j t) ∂localMeasure a b‖) +
        ‖R‖ * ‖N‖ := add_le_add (norm_sum_le _ _)
          (scalar_error_integral_bound (localMeasure a b) R N)
    _ ≤ (∑ j : Fin 3, ‖A j‖ * ‖V j‖) + ‖R‖ * ‖N‖ := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro j _
      exact gradient_error_integral_bound (localMeasure a b) (A j) (V j)
    _ = _ := by
      apply congrArg₂ (fun x y : ℝ => x + y)
      · apply Finset.sum_congr rfl
        intro j _
        exact mul_comm (‖A j‖) (‖V j‖)
      · rw [hRnorm, hNnorm]
        exact mul_comm _ _

#print axioms actualRegularizedEnergyError_integrable
#print axioms actualRegularizedEnergyError_integral_bound
end HartreeF.Regularization.Actual
