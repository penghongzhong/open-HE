import FEnergyRegularizerDerivatives
import FRegularizerBesselLp

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

theorem energyCLM_schwartz (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (φ : Test) :
    m.energyCLM hDensity hSob (schwartzEnergyState φ) = schwartzEnergyState (m.schwartz φ) := by
  apply energyDistribution_injective
  rw [m.energyCLM_distribution, m.schwartz_distribution]

theorem schwartz_energy_approximation (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {φ : ℕ → Test} {u : EnergyState}
    (hφ : Tendsto (fun n => schwartzEnergyState (φ n)) atTop (𝓝 u)) :
    Tendsto (fun n => schwartzEnergyState (m.schwartz (φ n))) atTop
      (𝓝 (m.energyCLM hDensity hSob u)) := by
  have h := (m.energyCLM hDensity hSob).continuous.tendsto u |>.comp hφ
  simpa only [Function.comp_def, energyCLM_schwartz] using h

theorem first_schwartz_derivative_state (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (j k : Fin 3) (φ : Test) :
    schwartzEnergyState (∂_{coordinate k} ((firstCutoff n j).schwartz φ)) =
      (secondCutoff n k j).energyCLM hDensity hSob (schwartzEnergyState φ) := by
  apply energyDistribution_injective
  rw [BoundedSymbol.energyCLM_distribution, second_distribution,
    ← first_distribution, ← BoundedSymbol.schwartz_distribution]
  simp only [schwartzEnergyState_distribution]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
    ((firstCutoff n j).schwartz φ) (coordinate k)).symm

/-- A single genuine Schwartz sequence approximates ∂j J_n u and its ∂k
in L6. This is the precise input to the weak-source integration-by-parts
limit and adds no H2-density assumption. -/
theorem derivative_schwartz_L6_limits (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) (j k : Fin 3) :
    ∃ φ : ℕ → Test,
      Tendsto (fun l => (φ l).toLp 6 volume) atTop
        (𝓝 (energyValue ((firstCutoff n j).energyCLM hDensity hSob u))) ∧
      Tendsto (fun l => (∂_{coordinate k} (φ l)).toLp 6 volume) atTop
        (𝓝 (energyValue ((secondCutoff n k j).energyCLM hDensity hSob u))) := by
  obtain ⟨ψ, hψ⟩ := schwartzEnergyState_approximation hDensity hSob u
  refine ⟨fun l => (firstCutoff n j).schwartz (ψ l), ?_, ?_⟩
  · exact energyValue.continuous.tendsto _ |>.comp
      (schwartz_energy_approximation _ hDensity hSob hψ)
  · have h := ((energyValue.comp ((secondCutoff n k j).energyCLM hDensity hSob)).continuous.tendsto u).comp hψ
    have he (l : ℕ) : (∂_{coordinate k} ((firstCutoff n j).schwartz (ψ l))).toLp 6 volume =
        energyValue ((secondCutoff n k j).energyCLM hDensity hSob (schwartzEnergyState (ψ l))) :=
      congrArg energyValue (first_schwartz_derivative_state hDensity hSob n j k (ψ l))
    simpa only [he, ContinuousLinearMap.comp_apply, Function.comp_def] using h

theorem JvalueL2_bound (n : ℕ) (u : EnergyState) :
    ‖JvalueL2 n u‖ ≤ (3 * (scale n / (2 * Real.pi))) * ‖u‖ := by
  change ‖∑ j : Fin 3, (recovery n j).l2 (energyGradient j u)‖ ≤ _
  calc
    _ ≤ ∑ j : Fin 3, ‖(recovery n j).l2 (energyGradient j u)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (scale n / (2 * Real.pi)) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact ((recovery n j).l2_norm_le _).trans
        (mul_le_mul_of_nonneg_left (energyState_gradient_norm_le u j) (recovery n j).bound_nonneg)
    _ = _ := by simp; ring

/-- Concrete continuous regularized paths and vector-field inputs on the
same actual EnergyState. This does not assert that a mild trajectory is C1. -/
theorem regularized_continuous_paths (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (u : ℝ → EnergyState) (f : ℝ → SourceLp)
    (hu : Continuous u) (hf : Continuous f) (n : ℕ) :
    Continuous (fun t => J hDensity hSob n (u t)) ∧
    Continuous (fun t => JvalueL2 n (u t)) ∧
    Continuous (fun t => deltaJ hDensity hSob n (u t)) ∧
    Continuous (fun t => S.sourceJ B n (f t)) ∧
    (∀ t, (energyValue (J hDensity hSob n (u t)) : V → ℂ) =ᵐ[volume] JvalueL2 n (u t)) ∧
    (∀ t, Tendsto (fun l => J hDensity hSob l (u t)) atTop (𝓝 (u t))) :=
  ⟨(J hDensity hSob n).continuous.comp hu, (JvalueL2 n).continuous.comp hu,
    (deltaJ hDensity hSob n).continuous.comp hu, (S.sourceJ B n).continuous.comp hf,
    fun t => J_value_ae hDensity hSob n (u t), fun t => J_strong hDensity hSob (u t)⟩

end HartreeF.Regularization.Actual

#print axioms HartreeF.Regularization.Actual.derivative_schwartz_L6_limits
#print axioms HartreeF.Regularization.Actual.JvalueL2_bound
#print axioms HartreeF.Regularization.Actual.regularized_continuous_paths
