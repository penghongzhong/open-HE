import FBoundedFourierRegularizer

/-! Actual homogeneous-energy regularizer construction by the accepted
Schwartz density and native completeness of C43's closed graph. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization
open EnergySpace SobolevStretch StationarySelfTest
namespace BoundedSymbol

theorem pureGradient_bound {u v : EnergyState} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j, ‖energyGradient j u‖ ≤ B * ‖energyGradient j v‖) :
    pureGradientNorm u ≤ B * pureGradientNorm v := by
  have hs : gradientSquared u ≤ B^2 * gradientSquared v := by
    calc
      _ ≤ ∑ j : Fin 3, (B * ‖energyGradient j v‖)^2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h j) 2)
      _ = _ := by simp only [mul_pow, gradientSquared, Finset.mul_sum]
  calc
    _ ≤ Real.sqrt (B^2 * gradientSquared v) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]; rfl

theorem schwartz_difference_bound (m : BoundedSymbol) {K : ℝ} (hSob : OrdinarySobolev K)
    (φ ψ : Test) :
    ‖schwartzEnergyState (m.schwartz φ) - schwartzEnergyState (m.schwartz ψ)‖ ≤
      (max (K^((6:ℝ)⁻¹)) 1 * (m.bound + 1) * Real.sqrt 3) *
        ‖schwartzEnergyState φ - schwartzEnergyState ψ‖ := by
  have hg : pureGradientNorm (schwartzEnergyState (m.schwartz φ) -
      schwartzEnergyState (m.schwartz ψ)) ≤ m.bound *
        pureGradientNorm (schwartzEnergyState φ - schwartzEnergyState ψ) := by
    apply pureGradient_bound m.bound_nonneg
    intro j
    rw [map_sub, map_sub, m.schwartz_gradient, m.schwartz_gradient, ← map_sub]
    exact m.l2_norm_le _
  have hp : 0 ≤ max (K^((6:ℝ)⁻¹)) 1 := le_trans zero_le_one (le_max_right _ _)
  calc
    _ ≤ max (K^((6:ℝ)⁻¹)) 1 * pureGradientNorm
        (schwartzEnergyState (m.schwartz φ) - schwartzEnergyState (m.schwartz ψ)) :=
      energyState_le_pureGradient hSob _
    _ ≤ max (K^((6:ℝ)⁻¹)) 1 * (m.bound *
        pureGradientNorm (schwartzEnergyState φ - schwartzEnergyState ψ)) :=
      mul_le_mul_of_nonneg_left hg hp
    _ ≤ max (K^((6:ℝ)⁻¹)) 1 * ((m.bound+1) *
        (Real.sqrt 3 * ‖schwartzEnergyState φ - schwartzEnergyState ψ‖)) := by
      apply mul_le_mul_of_nonneg_left _ hp
      exact mul_le_mul (by linarith) (pureGradient_le_sqrt_three_energyState _)
        (pureGradientNorm_nonneg _) (by linarith [m.bound_nonneg])
    _ = _ := by ring

theorem schwartz_cauchy (m : BoundedSymbol) {K : ℝ} (hSob : OrdinarySobolev K)
    (φ : ℕ → Test) (hφ : CauchySeq (fun n => schwartzEnergyState (φ n))) :
    CauchySeq (fun n => schwartzEnergyState (m.schwartz (φ n))) := by
  let C := max (K^((6:ℝ)⁻¹)) 1 * (m.bound+1) * Real.sqrt 3
  have hC : 0 < C := mul_pos
    (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (by linarith [m.bound_nonneg]))
    (Real.sqrt_pos.mpr (by norm_num))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hφ (ε/C) (div_pos hε hC)
  refine ⟨N, fun i hi j hj => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ C * ‖schwartzEnergyState (φ i) - schwartzEnergyState (φ j)‖ :=
      m.schwartz_difference_bound hSob _ _
    _ < C * (ε/C) := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hN i hi j hj) hC
    _ = ε := by field_simp

/-- Existence is proved by Cauchy completion, before any target is selected. -/
theorem exists_energy (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) :
    ∃ w : EnergyState,
      (∀ j, energyGradient j w = m.l2 (energyGradient j u)) ∧
      energyDistribution w = m.distribution (energyDistribution u) := by
  obtain ⟨φ, hφ⟩ := schwartzEnergyState_approximation hDensity hSob u
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (m.schwartz_cauchy hSob φ hφ.cauchySeq)
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hl := (energyGradient j).continuous.tendsto w |>.comp hw
    have hr := m.l2.continuous.tendsto (energyGradient j u) |>.comp
      ((energyGradient j).continuous.tendsto u |>.comp hφ)
    exact tendsto_nhds_unique hl (by simpa only [Function.comp_def, m.schwartz_gradient] using hr)
  · have hl := energyDistribution.continuous.tendsto w |>.comp hw
    have hr := m.distribution.continuous.tendsto (energyDistribution u) |>.comp
      (energyDistribution.continuous.tendsto u |>.comp hφ)
    exact tendsto_nhds_unique hl (by simpa only [Function.comp_def, m.schwartz_distribution] using hr)

def energy (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) : EnergyState :=
  (m.exists_energy hDensity hSob u).choose

theorem energy_gradient (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) (j : Fin 3) :
    energyGradient j (m.energy hDensity hSob u) = m.l2 (energyGradient j u) :=
  (m.exists_energy hDensity hSob u).choose_spec.1 j

theorem energy_distribution (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) :
    energyDistribution (m.energy hDensity hSob u) = m.distribution (energyDistribution u) :=
  (m.exists_energy hDensity hSob u).choose_spec.2

theorem energy_norm_bound (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) :
    ‖m.energy hDensity hSob u‖ ≤ (max (K^((6:ℝ)⁻¹)) 1 * m.bound * Real.sqrt 3) * ‖u‖ := by
  have hp : 0 ≤ max (K^((6:ℝ)⁻¹)) 1 := le_trans zero_le_one (le_max_right _ _)
  have hg : pureGradientNorm (m.energy hDensity hSob u) ≤ m.bound * pureGradientNorm u := by
    apply pureGradient_bound m.bound_nonneg
    intro j
    rw [m.energy_gradient]
    exact m.l2_norm_le _
  calc
    _ ≤ max (K^((6:ℝ)⁻¹)) 1 * pureGradientNorm (m.energy hDensity hSob u) :=
      energyState_le_pureGradient hSob _
    _ ≤ max (K^((6:ℝ)⁻¹)) 1 * (m.bound * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left hg hp
    _ ≤ max (K^((6:ℝ)⁻¹)) 1 * (m.bound * (Real.sqrt 3 * ‖u‖)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pureGradient_le_sqrt_three_energyState u) m.bound_nonneg) hp
    _ = _ := by ring

def energyCLM (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) : EnergyState →L[ℂ] EnergyState :=
  LinearMap.mkContinuous
    { toFun := m.energy hDensity hSob
      map_add' := by
        intro u v
        apply energyDistribution_injective
        simp only [m.energy_distribution, map_add]
      map_smul' := by
        intro c u
        apply energyDistribution_injective
        simp only [m.energy_distribution, map_smul, RingHom.id_apply] }
    (max (K^((6:ℝ)⁻¹)) 1 * m.bound * Real.sqrt 3)
    (m.energy_norm_bound hDensity hSob)

theorem energyCLM_gradient (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) (j : Fin 3) :
    energyGradient j (m.energyCLM hDensity hSob u) = m.l2 (energyGradient j u) :=
  m.energy_gradient hDensity hSob u j

theorem energyCLM_distribution (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) :
    energyDistribution (m.energyCLM hDensity hSob u) = m.distribution (energyDistribution u) :=
  m.energy_distribution hDensity hSob u

theorem energyCLM_free (m : BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (u : EnergyState) :
    m.energyCLM hDensity hSob (freeEnergyState hDensity hSob t u) =
      freeEnergyState hDensity hSob t (m.energyCLM hDensity hSob u) := by
  apply energyDistribution_injective
  rw [m.energyCLM_distribution, freeEnergyState_distribution, freeEnergyState_distribution,
    m.energyCLM_distribution, m.distribution_free]

theorem energyCLM_tendsto (m : ℕ → BoundedSymbol) (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C : ℝ} (hC : ∀ n, (m n).bound ≤ C)
    (hlim : ∀ᵐ ξ ∂(volume : Measure V), Tendsto (fun n => (m n).symbol ξ) atTop (𝓝 1))
    (u : EnergyState) : Tendsto (fun n => (m n).energyCLM hDensity hSob u) atTop (𝓝 u) := by
  apply tendsto_of_gradientTendsto hSob
  intro j
  simpa only [energyCLM_gradient] using l2_tendsto m hC hlim (energyGradient j u)

end BoundedSymbol
end HartreeF.Regularization

#print axioms HartreeF.Regularization.BoundedSymbol.exists_energy
#print axioms HartreeF.Regularization.BoundedSymbol.energyCLM_tendsto
#print axioms HartreeF.Regularization.BoundedSymbol.energyCLM_free
