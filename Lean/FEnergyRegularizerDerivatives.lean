import FEnergyRegularizerLaplacian

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

theorem derivativeSymbol_norm_le (j : Fin 3) (ξ : V) :
    ‖derivativeSymbol j ξ‖ ≤ (2 * Real.pi) * ‖ξ‖ := by
  have he : ‖derivativeSymbol j ξ‖ = (2 * Real.pi) * ‖ξ j‖ := by
    simp [derivativeSymbol, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [he]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ j) (by positivity)

def firstSymbol (n : ℕ) (j : Fin 3) := derivativeSymbol j * symbol n

theorem firstSymbol_temperate (n : ℕ) (j : Fin 3) :
    (firstSymbol n j).HasTemperateGrowth :=
  (derivativeSymbol_temperate j).mul (symbol_temperate n)

theorem firstSymbol_bound (n : ℕ) (j : Fin 3) (ξ : V) :
    ‖firstSymbol n j ξ‖ ≤ (2 * Real.pi) * scale n := by
  calc
    _ = ‖derivativeSymbol j ξ‖ * ‖symbol n ξ‖ := norm_mul _ _
    _ ≤ ((2 * Real.pi) * ‖ξ‖) * ‖symbol n ξ‖ :=
      mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le j ξ) (norm_nonneg _)
    _ = (2 * Real.pi) * (‖ξ‖ * ‖symbol n ξ‖) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (symbol_weighted_norm_le n ξ) (by positivity)

def firstCutoff (n : ℕ) (j : Fin 3) : BoundedSymbol where
  symbol := firstSymbol n j
  temperate := firstSymbol_temperate n j
  bound := (2 * Real.pi) * scale n
  bound_nonneg := mul_nonneg (by positivity) (scale_pos n).le
  norm_le := firstSymbol_bound n j

def secondSymbol (n : ℕ) (j k : Fin 3) := derivativeSymbol j * firstSymbol n k

theorem secondSymbol_temperate (n : ℕ) (j k : Fin 3) :
    (secondSymbol n j k).HasTemperateGrowth :=
  (derivativeSymbol_temperate j).mul (firstSymbol_temperate n k)

theorem secondSymbol_bound (n : ℕ) (j k : Fin 3) (ξ : V) :
    ‖secondSymbol n j k ξ‖ ≤ (2 * Real.pi)^2 * scale n^2 := by
  calc
    _ = (‖derivativeSymbol j ξ‖ * ‖derivativeSymbol k ξ‖) * ‖symbol n ξ‖ := by
      simp only [secondSymbol, firstSymbol, Pi.mul_apply, norm_mul, mul_assoc]
    _ ≤ (((2 * Real.pi) * ‖ξ‖) * ((2 * Real.pi) * ‖ξ‖)) * ‖symbol n ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (derivativeSymbol_norm_le j ξ) (derivativeSymbol_norm_le k ξ)
        (norm_nonneg _) (by positivity)
    _ = (2 * Real.pi)^2 * (‖ξ‖^2 * ‖symbol n ξ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (symbol_sq_weighted_norm_le n ξ) (sq_nonneg _)

def secondCutoff (n : ℕ) (j k : Fin 3) : BoundedSymbol where
  symbol := secondSymbol n j k
  temperate := secondSymbol_temperate n j k
  bound := (2 * Real.pi)^2 * scale n^2
  bound_nonneg := by positivity
  norm_le := secondSymbol_bound n j k

theorem first_distribution (n : ℕ) (j : Fin 3) (T : TD) :
    (firstCutoff n j).distribution T = ∂_{coordinate j} ((cutoff n).distribution T) := by
  rw [derivative_as_multiplier]
  change TemperedDistribution.fourierMultiplierCLM ℂ (firstSymbol n j) T =
    TemperedDistribution.fourierMultiplierCLM ℂ (derivativeSymbol j)
      (TemperedDistribution.fourierMultiplierCLM ℂ (symbol n) T)
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (symbol_temperate n) (derivativeSymbol_temperate j)]
  simp only [firstSymbol, mul_comm]

theorem second_distribution (n : ℕ) (j k : Fin 3) (T : TD) :
    (secondCutoff n j k).distribution T =
      ∂_{coordinate j} (∂_{coordinate k} ((cutoff n).distribution T)) := by
  rw [← first_distribution, derivative_as_multiplier]
  change TemperedDistribution.fourierMultiplierCLM ℂ (secondSymbol n j k) T =
    TemperedDistribution.fourierMultiplierCLM ℂ (derivativeSymbol j)
      (TemperedDistribution.fourierMultiplierCLM ℂ (firstSymbol n k) T)
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (firstSymbol_temperate n k) (derivativeSymbol_temperate j)]
  simp only [secondSymbol, mul_comm]

/-- The first and second distributional derivatives of J_n u are themselves
constructed C43 states. Their L6 values and L2 weak gradients are native. -/
theorem J_first_two_derivatives (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) :
    (∀ j, energyDistribution ((firstCutoff n j).energyCLM hDensity hSob u) =
      ∂_{coordinate j} (energyDistribution (J hDensity hSob n u))) ∧
    (∀ j k, energyDistribution ((secondCutoff n j k).energyCLM hDensity hSob u) =
      ∂_{coordinate j} (∂_{coordinate k} (energyDistribution (J hDensity hSob n u)))) := by
  constructor
  · intro j
    rw [BoundedSymbol.energyCLM_distribution, J_distribution]
    exact first_distribution n j _
  · intro j k
    rw [BoundedSymbol.energyCLM_distribution, J_distribution]
    exact second_distribution n j k _

end HartreeF.Regularization.Actual

#print axioms HartreeF.Regularization.Actual.J_first_two_derivatives
