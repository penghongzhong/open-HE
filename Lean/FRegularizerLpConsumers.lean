import FRegularizerBesselLp
import FCriticalPathSpace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

theorem J_Lp_value_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : OrdinaryBesselLp p)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) (f : LpV p)
    (hf : Lp.toTemperedDistribution f = energyDistribution u) :
    (energyValue (J hDensity hSob n u) : V → ℂ) =ᵐ[volume] B.cutoffLp n f := by
  apply CriticalPathSpace.spatial_ae_eq_of_distribution_eq
  change energyDistribution (J hDensity hSob n u) = _
  rw [J_distribution, B.cutoffLp_distribution, hf]
  rfl

theorem J_Lp_gradient_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : OrdinaryBesselLp p)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) (j : Fin 3) (f : LpV p)
    (hf : Lp.toTemperedDistribution f = energyGradientDistribution j u) :
    (energyGradient j (J hDensity hSob n u) : V → ℂ) =ᵐ[volume] B.cutoffLp n f := by
  apply CriticalPathSpace.spatial_ae_eq_of_distribution_eq
  rw [J_gradient, BoundedSymbol.l2_distribution, B.cutoffLp_distribution, hf]
  rfl

/-- Every additional Lp value of the actual input has actual Lp regularized
values, uniformly bounded and strongly convergent. Applies in particular
to p=6/5,6,10 and the gradient p=30/13. -/
theorem J_additionalLp_value {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : OrdinaryBesselLp p)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) (f : LpV p)
    (hf : Lp.toTemperedDistribution f = energyDistribution u) :
    ∃ v : ℕ → LpV p,
      (∀ n, (energyValue (J hDensity hSob n u) : V → ℂ) =ᵐ[volume] v n) ∧
      (∀ n, ‖v n‖ ≤ 2 * ‖f‖) ∧ Tendsto v atTop (𝓝 f) :=
  ⟨fun n => B.cutoffLp n f, fun n => J_Lp_value_ae B hDensity hSob n u f hf,
    fun n => B.cutoffLp_bound n f, B.cutoffLp_strong f⟩

theorem J_additionalLp_gradient {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : OrdinaryBesselLp p)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (u : EnergyState) (j : Fin 3) (f : LpV p)
    (hf : Lp.toTemperedDistribution f = energyGradientDistribution j u) :
    ∃ v : ℕ → LpV p,
      (∀ n, (energyGradient j (J hDensity hSob n u) : V → ℂ) =ᵐ[volume] v n) ∧
      (∀ n, ‖v n‖ ≤ 2 * ‖f‖) ∧ Tendsto v atTop (𝓝 f) :=
  ⟨fun n => B.cutoffLp n f, fun n => J_Lp_gradient_ae B hDensity hSob n u j f hf,
    fun n => B.cutoffLp_bound n f, B.cutoffLp_strong f⟩

end HartreeF.Regularization.Actual

#print axioms HartreeF.Regularization.Actual.J_additionalLp_value
#print axioms HartreeF.Regularization.Actual.J_additionalLp_gradient
