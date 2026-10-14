import FActualEnergyRegularizers

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

def normSqSymbol (ξ : V) : ℂ := ‖ξ‖^2

theorem normSqSymbol_temperate : normSqSymbol.HasTemperateGrowth := by
  have h := Function.hasTemperateGrowth_norm_sq (H := V)
  convert! Complex.hasTemperateGrowth_ofReal.comp h using 1
  funext ξ
  simp [normSqSymbol]

def laplaceSymbol (n : ℕ) : V → ℂ :=
  (-(2 * Real.pi)^2 : ℂ) • (symbol n * normSqSymbol)

theorem laplaceSymbol_temperate (n : ℕ) : (laplaceSymbol n).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const _).mul ((symbol_temperate n).mul normSqSymbol_temperate)

theorem laplaceSymbol_bound (n : ℕ) (ξ : V) :
    ‖laplaceSymbol n ξ‖ ≤ (2 * Real.pi)^2 * scale n^2 := by
  have he : ‖laplaceSymbol n ξ‖ = (2 * Real.pi)^2 * (‖ξ‖^2 * ‖symbol n ξ‖) := by
    simp [laplaceSymbol, normSqSymbol, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, mul_comm]
  rw [he]
  exact mul_le_mul_of_nonneg_left (symbol_sq_weighted_norm_le n ξ) (sq_nonneg _)

def laplaceCutoff (n : ℕ) : BoundedSymbol where
  symbol := laplaceSymbol n
  temperate := laplaceSymbol_temperate n
  bound := (2 * Real.pi)^2 * scale n^2
  bound_nonneg := by positivity
  norm_le := laplaceSymbol_bound n

theorem laplacian_cutoff_distribution (n : ℕ) (T : TD) :
    Δ ((cutoff n).distribution T) = (laplaceCutoff n).distribution T := by
  rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  change (-(2 * Real.pi)^2 : ℂ) •
      TemperedDistribution.fourierMultiplierCLM ℂ normSqSymbol
        (TemperedDistribution.fourierMultiplierCLM ℂ (symbol n) T) =
    TemperedDistribution.fourierMultiplierCLM ℂ (laplaceSymbol n) T
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (symbol_temperate n) normSqSymbol_temperate]
  rw [laplaceSymbol, TemperedDistribution.fourierMultiplierCLM_smul
    ((symbol_temperate n).mul normSqSymbol_temperate)]
  rfl

/-- Bounded actual EnergyState realization of ΔJ_n, requiring no extra domain
or H3 premise on the original homogeneous-energy state. -/
def deltaJ (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) : EnergyState →L[ℂ] EnergyState := (laplaceCutoff n).energyCLM hDensity hSob

theorem deltaJ_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) :
    energyDistribution (deltaJ hDensity hSob n u) =
      Δ (energyDistribution (J hDensity hSob n u)) := by
  change energyDistribution ((laplaceCutoff n).energyCLM hDensity hSob u) = _
  rw [BoundedSymbol.energyCLM_distribution, J_distribution]
  exact (laplacian_cutoff_distribution n _).symm

theorem deltaJ_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) (j : Fin 3) :
    energyGradient j (deltaJ hDensity hSob n u) =
      (laplaceCutoff n).l2 (energyGradient j u) :=
  (laplaceCutoff n).energyCLM_gradient hDensity hSob u j

theorem deltaJ_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) :
    ‖deltaJ hDensity hSob n u‖ ≤
      (max (K^((6:ℝ)⁻¹)) 1 * ((2 * Real.pi)^2 * scale n^2) * Real.sqrt 3) * ‖u‖ :=
  (laplaceCutoff n).energy_norm_bound hDensity hSob u

end HartreeF.Regularization.Actual

#print axioms HartreeF.Regularization.Actual.deltaJ_distribution
#print axioms HartreeF.Regularization.Actual.deltaJ_bound
