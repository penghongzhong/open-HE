import FEnergyRegularizerConstruction
import FRealRegularizerSymbols
import FL2EnergyConstruction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization
open EnergySpace SobolevStretch StationarySelfTest
namespace Actual
open EnergyRegularizer

def cutoff (n : ℕ) : BoundedSymbol where
  symbol := EnergyRegularizer.symbol n
  temperate := symbol_temperate n
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := symbol_norm_le_one n

def recovery (n : ℕ) (j : Fin 3) : BoundedSymbol where
  symbol := reconstruction n j
  temperate := reconstruction_temperate n j
  bound := scale n / (2 * Real.pi)
  bound_nonneg := div_nonneg (scale_pos n).le (by positivity)
  norm_le := reconstruction_norm_le n j

theorem derivativeSymbol_temperate (j : Fin 3) :
    (derivativeSymbol j).HasTemperateGrowth := by
  have hj := (EuclideanSpace.proj (𝕜 := ℝ) j).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.const _).mul (Complex.hasTemperateGrowth_ofReal.comp hj)

theorem derivative_as_multiplier (j : Fin 3) (T : TD) :
    ∂_{coordinate j} T = TemperedDistribution.fourierMultiplierCLM ℂ (derivativeSymbol j) T := by
  rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM]
  have hi : (fun ξ : V => (inner ℝ ξ (coordinate j) : ℂ)).HasTemperateGrowth := by fun_prop
  have he : derivativeSymbol j =
      (2 * Real.pi * Complex.I) • (fun ξ : V => (inner ℝ ξ (coordinate j) : ℂ)) := by
    funext ξ
    exact derivativeSymbol_eq_coordinate j ξ
  rw [he, TemperedDistribution.fourierMultiplierCLM_smul hi]
  rfl

/-- A recovery certificate consists only of bounded scalar symbols and their
pointwise algebraic identity. It does not assert an EnergyState or L2 value. -/
structure RecoverySystem (m : BoundedSymbol) where
  coefficient : Fin 3 → BoundedSymbol
  identity : ∀ ξ, ∑ j, (coefficient j).symbol ξ * derivativeSymbol j ξ = m.symbol ξ

namespace RecoverySystem

def valueL2 {m : BoundedSymbol} (r : RecoverySystem m) : EnergyState →L[ℂ] L2 :=
  ∑ j : Fin 3, (r.coefficient j).l2 ∘L energyGradient j

theorem distribution_identity {m : BoundedSymbol} (r : RecoverySystem m) (T : TD) :
    (∑ j : Fin 3, (r.coefficient j).distribution (∂_{coordinate j} T)) = m.distribution T := by
  simp_rw [derivative_as_multiplier, BoundedSymbol.distribution,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (derivativeSymbol_temperate _) (r.coefficient _).temperate]
  have ht : ∀ j (hj : j ∈ (Finset.univ : Finset (Fin 3))),
      (derivativeSymbol j * (r.coefficient j).symbol).HasTemperateGrowth :=
    fun j _ => (derivativeSymbol_temperate j).mul (r.coefficient j).temperate
  rw [← sum_apply, ← TemperedDistribution.fourierMultiplierCLM_sum ℂ ht]
  congr 2
  funext ξ
  simpa only [Pi.mul_apply, mul_comm] using r.identity ξ

theorem valueL2_distribution {m : BoundedSymbol} (r : RecoverySystem m) (u : EnergyState) :
    Lp.toTemperedDistribution (r.valueL2 u) = m.distribution (energyDistribution u) := by
  change (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2)
    ((∑ j : Fin 3, (r.coefficient j).l2 ∘L energyGradient j) u) = _
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  change (∑ j, Lp.toTemperedDistribution ((r.coefficient j).l2 (energyGradient j u))) = _
  simp_rw [BoundedSymbol.l2_distribution]
  change (∑ j, (r.coefficient j).distribution (energyGradientDistribution j u)) = _
  simp_rw [← energyDistribution_derivative]
  exact r.distribution_identity _

theorem valueL2_derivative {m : BoundedSymbol} (r : RecoverySystem m) (u : EnergyState)
    (j : Fin 3) : ∂_{coordinate j} (Lp.toTemperedDistribution (r.valueL2 u)) =
      Lp.toTemperedDistribution (m.l2 (energyGradient j u)) := by
  rw [r.valueL2_distribution, m.derivative_distribution, energyDistribution_derivative,
    m.l2_distribution]
  rfl

/-- Literal almost-everywhere L2 realization of the already constructed C43
state; the original u is not assumed to have mass. -/
theorem energy_value_ae {m : BoundedSymbol} (r : RecoverySystem m)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    (energyValue (m.energyCLM hDensity hSob u) : V → ℂ) =ᵐ[volume] r.valueL2 u := by
  let w := l2EnergyState hDensity hSob (r.valueL2 u)
    (fun j => m.l2 (energyGradient j u)) (r.valueL2_derivative u)
  have he : m.energyCLM hDensity hSob u = w := by
    apply energyDistribution_injective
    rw [m.energyCLM_distribution]
    exact (r.valueL2_distribution u).symm.trans
      (l2EnergyState_distribution hDensity hSob _ _ _).symm
  rw [he]
  exact l2EnergyState_value_ae hDensity hSob _ _ _

end RecoverySystem

def cutoffRecovery (n : ℕ) : RecoverySystem (cutoff n) where
  coefficient := recovery n
  identity := reconstruction_sum n

def J (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) : EnergyState →L[ℂ] EnergyState := (cutoff n).energyCLM hDensity hSob

def JvalueL2 (n : ℕ) : EnergyState →L[ℂ] L2 := (cutoffRecovery n).valueL2

theorem J_value_ae (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) :
    (energyValue (J hDensity hSob n u) : V → ℂ) =ᵐ[volume] JvalueL2 n u :=
  (cutoffRecovery n).energy_value_ae hDensity hSob u

theorem J_distribution (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) :
    energyDistribution (J hDensity hSob n u) =
      TemperedDistribution.fourierMultiplierCLM ℂ (symbol n) (energyDistribution u) :=
  (cutoff n).energyCLM_distribution hDensity hSob u

theorem J_gradient (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) (j : Fin 3) :
    energyGradient j (J hDensity hSob n u) = (cutoff n).l2 (energyGradient j u) :=
  (cutoff n).energyCLM_gradient hDensity hSob u j

theorem J_strong (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) : Tendsto (fun n => J hDensity hSob n u) atTop (𝓝 u) := by
  apply BoundedSymbol.energyCLM_tendsto cutoff hDensity hSob (C := 1) (fun _ => le_rfl)
  filter_upwards [(volume : Measure V).ae_ne (0 : V)] with ξ hξ
  exact symbol_tendsto ξ hξ

theorem J_uniform_bound (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) :
    ‖J hDensity hSob n u‖ ≤ (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖u‖ := by
  change ‖(cutoff n).energy hDensity hSob u‖ ≤ _
  simpa only [cutoff, mul_one] using (cutoff n).energy_norm_bound hDensity hSob u

theorem J_selfAdjointL2 (n : ℕ) (f g : L2) :
    inner ℂ ((cutoff n).l2 f) g = inner ℂ f ((cutoff n).l2 g) :=
  (cutoff n).l2_selfAdjoint (star_symbol n) f g

theorem J_free (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (t : ℝ) (u : EnergyState) :
    J hDensity hSob n (freeEnergyState hDensity hSob t u) =
      freeEnergyState hDensity hSob t (J hDensity hSob n u) :=
  (cutoff n).energyCLM_free hDensity hSob t u

end Actual
end HartreeF.Regularization

#print axioms HartreeF.Regularization.Actual.J_value_ae
#print axioms HartreeF.Regularization.Actual.J_strong
#print axioms HartreeF.Regularization.Actual.J_selfAdjointL2
#print axioms HartreeF.Regularization.Actual.J_free
