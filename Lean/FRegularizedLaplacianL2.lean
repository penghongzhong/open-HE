import FEnergyRegularizerDerivatives
import FCriticalPathSpace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

attribute [local irreducible] energySubmodule

/-- The Laplacian's L2 value is recovered directly from the original three
L2 gradient coordinates. No L2 assumption on the original value is made. -/
def deltaJValueL2 (n : ℕ) : EnergyState →L[ℂ] L2 :=
  ∑ j : Fin 3, (firstCutoff n j).l2 ∘L energyGradient j

theorem deltaJValueL2_distribution (n : ℕ) (u : EnergyState) :
    Lp.toTemperedDistribution (deltaJValueL2 n u) =
      Δ ((cutoff n).distribution (energyDistribution u)) := by
  change (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2)
    ((∑ j : Fin 3, (firstCutoff n j).l2 ∘L energyGradient j) u) = _
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  change (∑ j : Fin 3, Lp.toTemperedDistribution
    ((firstCutoff n j).l2 (energyGradient j u))) = _
  simp_rw [BoundedSymbol.l2_distribution]
  change (∑ j : Fin 3, (firstCutoff n j).distribution (energyGradientDistribution j u)) = _
  calc
    _ = ∑ j : Fin 3, ∂_{coordinate j}
        (∂_{coordinate j} ((cutoff n).distribution (energyDistribution u))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← energyDistribution_derivative,
        ← BoundedSymbol.derivative_distribution, first_distribution]
    _ = _ := by
      simpa only [EuclideanSpace.basisFun_apply, coordinate] using
        (TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ)
          ((cutoff n).distribution (energyDistribution u))).symm

theorem deltaJ_value_ae (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) :
    (energyValue (deltaJ hDensity hSob n u) : V → ℂ) =ᵐ[volume]
      deltaJValueL2 n u := by
  apply CriticalPathSpace.spatial_ae_eq_of_distribution_eq
  change energyDistribution (deltaJ hDensity hSob n u) =
    Lp.toTemperedDistribution (deltaJValueL2 n u)
  rw [deltaJ_distribution, J_distribution]
  exact (deltaJValueL2_distribution n u).symm

theorem deltaJValueL2_bound (n : ℕ) (u : EnergyState) :
    ‖deltaJValueL2 n u‖ ≤ (3 * (2 * Real.pi) * scale n) * ‖u‖ := by
  change ‖∑ j : Fin 3, (firstCutoff n j).l2 (energyGradient j u)‖ ≤ _
  calc
    _ ≤ ∑ j : Fin 3, ‖(firstCutoff n j).l2 (energyGradient j u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ((2 * Real.pi) * scale n) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact ((firstCutoff n j).l2_norm_le _).trans
        (mul_le_mul_of_nonneg_left (energyState_gradient_norm_le u j)
          (firstCutoff n j).bound_nonneg)
    _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

/-- The required L2 Laplacian trajectory is strongly continuous whenever
the original actual EnergyState trajectory is continuous. -/
theorem deltaJValueL2_continuous {T : Type*} [TopologicalSpace T]
    (n : ℕ) {u : T → EnergyState} (hu : Continuous u) :
    Continuous (fun t => deltaJValueL2 n (u t)) :=
  (deltaJValueL2 n).continuous.comp hu

#print axioms deltaJValueL2
#print axioms deltaJValueL2_distribution
#print axioms deltaJ_value_ae
#print axioms deltaJValueL2_bound
#print axioms deltaJValueL2_continuous
end HartreeF.Regularization.Actual
