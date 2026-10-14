import FEnergySchwartzDensity
import FFreeFlowContinuity

/-! A genuine complete-space construction of the Fourier free orbit on the
actual C43 homogeneous EnergyState. Ordinary density and Sobolev remain explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest

theorem schwartzEnergyState_distribution (φ : Test) :
    energyDistribution (schwartzEnergyState φ) = SchwartzMap.toTemperedDistributionCLM V ℂ volume φ := by
  change Lp.toTemperedDistribution (φ.toLp 6 volume) = _
  exact Lp.toTemperedDistribution_toLp_eq φ

theorem freeSchwartz_energyDistribution (t : ℝ) (φ : Test) :
    energyDistribution (schwartzEnergyState (FreeFlow.freeSchwartz t φ)) =
      FreeFlow.free t (energyDistribution (schwartzEnergyState φ)) := by
  rw [schwartzEnergyState_distribution, schwartzEnergyState_distribution]
  exact (TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (FreeFlow.phase_temperate t) φ).symm

/-- The actual weak-gradient coordinate, proved through injectivity of the
native L2-to-distribution map and actual derivative commutation. -/
theorem freeSchwartz_energyGradient (t : ℝ) (φ : Test) (j : Fin 3) :
    energyGradient j (schwartzEnergyState (FreeFlow.freeSchwartz t φ)) =
      FreeFlow.freeL2 t (energyGradient j (schwartzEnergyState φ)) := by
  apply FreeFlow.l2_distribution_injective
  rw [FreeFlow.freeL2_distribution]
  change energyGradientDistribution j (schwartzEnergyState (FreeFlow.freeSchwartz t φ)) =
    FreeFlow.free t (energyGradientDistribution j (schwartzEnergyState φ))
  rw [← energyDistribution_derivative, ← energyDistribution_derivative,
    freeSchwartz_energyDistribution, FreeFlow.derivative_free]

theorem freeSchwartz_difference_pureGradient (t : ℝ) (φ ψ : Test) :
    pureGradientNorm (schwartzEnergyState (FreeFlow.freeSchwartz t φ) -
      schwartzEnergyState (FreeFlow.freeSchwartz t ψ)) =
    pureGradientNorm (schwartzEnergyState φ - schwartzEnergyState ψ) := by
  unfold pureGradientNorm gradientSquared
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sub, map_sub, freeSchwartz_energyGradient, freeSchwartz_energyGradient,
    ← map_sub, FreeFlow.freeL2_norm]

/-- A quantitative estimate in the existing C43 graph norm. -/
theorem freeSchwartz_difference_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (t : ℝ) (φ ψ : Test) :
    ‖schwartzEnergyState (FreeFlow.freeSchwartz t φ) -
      schwartzEnergyState (FreeFlow.freeSchwartz t ψ)‖ ≤
    (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) *
      ‖schwartzEnergyState φ - schwartzEnergyState ψ‖ := by
  calc
    _ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm
        (schwartzEnergyState (FreeFlow.freeSchwartz t φ) -
          schwartzEnergyState (FreeFlow.freeSchwartz t ψ)) := energyState_le_pureGradient hSob _
    _ = max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm
        (schwartzEnergyState φ - schwartzEnergyState ψ) := by rw [freeSchwartz_difference_pureGradient]
    _ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * (Real.sqrt 3 *
        ‖schwartzEnergyState φ - schwartzEnergyState ψ‖) :=
      mul_le_mul_of_nonneg_left (pureGradient_le_sqrt_three_energyState _)
        (le_trans (by norm_num) (le_max_right _ _))
    _ = _ := (mul_assoc _ _ _).symm

/-- For any single actual approximating sequence, its propagated states are
Cauchy before any target state is assumed or selected. -/
theorem freeSchwartz_cauchy {K : ℝ} (hSob : OrdinarySobolev K)
    (t : ℝ) (φ : ℕ → Test) (hφ : CauchySeq (fun n => schwartzEnergyState (φ n))) :
    CauchySeq (fun n => schwartzEnergyState (FreeFlow.freeSchwartz t (φ n))) := by
  let C : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3
  have hC : 0 < C := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (Real.sqrt_pos.mpr (by norm_num))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hφ (ε / C) (div_pos hε hC)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ C * ‖schwartzEnergyState (φ m) - schwartzEnergyState (φ n)‖ :=
      freeSchwartz_difference_bound hSob t _ _
    _ < C * (ε / C) := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hN m hm n hn) hC
    _ = ε := by field_simp

/-- CompleteSpace produces a target for every approximating sequence. -/
theorem freeSchwartz_exists_limit {K : ℝ} (hSob : OrdinarySobolev K)
    (t : ℝ) (φ : ℕ → Test) {u : EnergyState}
    (hφ : Tendsto (fun n => schwartzEnergyState (φ n)) atTop (𝓝 u)) :
    ∃ w : EnergyState,
      Tendsto (fun n => schwartzEnergyState (FreeFlow.freeSchwartz t (φ n))) atTop (𝓝 w) :=
  cauchySeq_tendsto_of_complete (freeSchwartz_cauchy hSob t φ hφ.cauchySeq)

/-- The target is actually constructed by Cauchy completion of the same
Schwartz sequence supplied by the proved density theorem. -/
theorem exists_freeEnergyState (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (u : EnergyState) :
    ∃ w : EnergyState,
      (∀ j : Fin 3, energyGradient j w = FreeFlow.freeL2 t (energyGradient j u)) ∧
      energyDistribution w = FreeFlow.free t (energyDistribution u) := by
  obtain ⟨φ, hφ⟩ := schwartzEnergyState_approximation hDensity hSob u
  obtain ⟨w, hw⟩ := freeSchwartz_exists_limit hSob t φ hφ
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hleft := (energyGradient j).continuous.tendsto w |>.comp hw
    have hright := (FreeFlow.freeL2 t).continuous.tendsto (energyGradient j u) |>.comp
      ((energyGradient j).continuous.tendsto u |>.comp hφ)
    exact tendsto_nhds_unique hleft (by simpa only [Function.comp_def, freeSchwartz_energyGradient] using hright)
  · have hleft := energyDistribution.continuous.tendsto w |>.comp hw
    have hright := (FreeFlow.free t).continuous.tendsto (energyDistribution u) |>.comp
      (energyDistribution.continuous.tendsto u |>.comp hφ)
    exact tendsto_nhds_unique hleft (by simpa only [Function.comp_def, freeSchwartz_energyDistribution] using hright)

/-- An actual full-state free orbit, chosen only after complete-space existence. -/
def freeEnergyState (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (t : ℝ) (u : EnergyState) : EnergyState :=
  (exists_freeEnergyState hDensity hSob t u).choose

theorem freeEnergyState_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (u : EnergyState) (j : Fin 3) :
    energyGradient j (freeEnergyState hDensity hSob t u) = FreeFlow.freeL2 t (energyGradient j u) :=
  (exists_freeEnergyState hDensity hSob t u).choose_spec.1 j

theorem freeEnergyState_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (u : EnergyState) :
    energyDistribution (freeEnergyState hDensity hSob t u) = FreeFlow.free t (energyDistribution u) :=
  (exists_freeEnergyState hDensity hSob t u).choose_spec.2

end HartreeF.EnergySpace
