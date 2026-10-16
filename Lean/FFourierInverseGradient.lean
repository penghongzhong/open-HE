import FSchwartzYoungDistribution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.AnnularL1
open EnergySpace YoungSource MassRecovery

/-- The literal coordinate derivative multiplier in mathlib's cyclic Fourier convention. -/
def coordinateDerivativeSymbol (j : Fin 3) (ξ : V) : ℂ :=
  (2 * Real.pi * Complex.I) * (ξ j : ℂ)

theorem coordinateDerivativeSymbol_temperate (j : Fin 3) :
    (coordinateDerivativeSymbol j).HasTemperateGrowth := by
  have hc : (fun ξ : V => (ξ j : ℂ)).HasTemperateGrowth := by
    convert Complex.ofRealCLM.hasTemperateGrowth.comp
      (Function.hasTemperateGrowth_inner_left (coordinate j)) using 1
    funext ξ
    simp [coordinate, EuclideanSpace.inner_single_right]
  exact Function.HasTemperateGrowth.mul (by fun_prop) hc

theorem actual_coordinate_derivative_multiplier (T : TD) (j : Fin 3) :
    ∂_{coordinate j} T =
      TemperedDistribution.fourierMultiplierCLM ℂ (coordinateDerivativeSymbol j) T := by
  rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM]
  rw [← smul_apply,
    ← TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop)]
  congr 2
  funext ξ
  simp [coordinateDerivativeSymbol, coordinate, EuclideanSpace.inner_single_right]

/-- A genuine multiplier identity converts actual coordinate derivatives into
an exact distributional inverse-gradient formula. Concrete cutoff symbols are
constructed separately; this lemma supplies no realization or norm as a premise. -/
theorem inverseGradient_multiplier_identity (a : Fin 3 → Test) (m : V → ℂ)
    (hm : ∀ ξ : V, (∑ j : Fin 3, coordinateDerivativeSymbol j ξ * a j ξ) = m ξ)
    (T : TD) :
    (∑ j : Fin 3, TemperedDistribution.fourierMultiplierCLM ℂ (a j : V → ℂ)
      (∂_{coordinate j} T)) = TemperedDistribution.fourierMultiplierCLM ℂ m T := by
  have he (j : Fin 3) :
      TemperedDistribution.fourierMultiplierCLM ℂ (a j : V → ℂ) (∂_{coordinate j} T) =
        TemperedDistribution.fourierMultiplierCLM ℂ
          (coordinateDerivativeSymbol j * (a j : V → ℂ)) T := by
    rw [actual_coordinate_derivative_multiplier,
      TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
        (coordinateDerivativeSymbol_temperate j) (a j).hasTemperateGrowth]
  simp_rw [he]
  have hs := congrArg (fun P : TD →L[ℂ] TD => P T)
    (TemperedDistribution.fourierMultiplierCLM_sum ℂ
      (s := Finset.univ) (g := fun j : Fin 3 => coordinateDerivativeSymbol j * (a j : V → ℂ))
      (fun j _ => (coordinateDerivativeSymbol_temperate j).mul (a j).hasTemperateGrowth))
  simp only [sum_apply] at hs
  rw [← hs]
  congr 2
  funext ξ
  exact hm ξ

theorem one_distribution_injective :
    Function.Injective (Lp.toTemperedDistribution : OneSpace → TD) :=
  LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure V)) (p := 1))

/-- Construct an actual L1 class by integrating the given actual L1 gradients
against genuine Schwartz kernels. -/
def inverseGradientL1 (k : Fin 3 → Test) (H : Fin 3 → OneSpace) : OneSpace :=
  ∑ j : Fin 3, youngCLM (by simp : (1 : ℝ≥0∞) ≠ ∞) ((k j).toLp 1 volume) (H j)

theorem inverseGradientL1_norm (k : Fin 3 → Test) (H : Fin 3 → OneSpace) :
    ‖inverseGradientL1 k H‖ ≤ ∑ j : Fin 3, ‖(k j).toLp 1 volume‖ * ‖H j‖ := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => youngValue_norm _ _)

/-- No L1 realization of T itself is needed. The output is constructed and tied
to exactly the original tempered distribution by its actual derivative equations. -/
theorem inverseGradientL1_distribution (k : Fin 3 → Test) (m : V → ℂ)
    (hm : ∀ ξ : V, (∑ j : Fin 3, coordinateDerivativeSymbol j ξ * (𝓕 (k j) : Test) ξ) = m ξ)
    (T : TD) (H : Fin 3 → OneSpace)
    (hH : ∀ j : Fin 3, ∂_{coordinate j} T = Lp.toTemperedDistribution (H j)) :
    Lp.toTemperedDistribution (inverseGradientL1 k H) =
      TemperedDistribution.fourierMultiplierCLM ℂ m T := by
  change (Lp.toTemperedDistributionCLM ℂ volume 1) (inverseGradientL1 k H) = _
  unfold inverseGradientL1
  rw [map_sum]
  simp only [Lp.toTemperedDistributionCLM_apply, young_schwartz_distribution]
  simp_rw [← hH]
  exact inverseGradient_multiplier_identity (fun j => (𝓕 (k j) : Test)) m hm T

end HartreeF.AnnularL1
