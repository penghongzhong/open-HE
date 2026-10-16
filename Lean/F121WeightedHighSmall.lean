import F121CutoffMaps

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Paper121SmallFrequency
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest

theorem scaled_high_bound (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    M*‖highValueL2CLM hDensity hSob q hM u‖ ≤ pureGradientNorm u := by
  calc
    _ ≤ M*(M⁻¹*pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left (highValueL2_bound hDensity hSob q hM u) hM.le
    _ = _ := by field_simp [ne_of_gt hM]

theorem scaled_high_difference (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u v : EnergyState) :
    M*‖highValueL2CLM hDensity hSob q hM u-highValueL2CLM hDensity hSob q hM v‖ ≤
      pureGradientNorm (u-v) := by
  rw [← map_sub]
  exact scaled_high_bound hDensity hSob q hM (u-v)

theorem high_schwartz_identification (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (φ : Test) :
    highValueL2CLM hDensity hSob q hM (schwartzEnergyState φ) =
      highL2 q M (φ.toLp 2 volume) := by
  exact (highValueL2_unique hDensity hSob q hM (schwartzEnergyState φ)
    (highL2 q M (φ.toLp 2 volume)) (by
      rw [highL2_distribution, Lp.toTemperedDistribution_toLp_eq,
        schwartzEnergyState_distribution])).symm

theorem scaled_high_approximation (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M)
    (u : EnergyState) (φ : Test) :
    M*‖highValueL2CLM hDensity hSob q hM u‖ ≤
      pureGradientNorm (u-schwartzEnergyState φ)+M*‖φ.toLp 2 volume‖ := by
  let H := highValueL2CLM hDensity hSob q hM
  have ht := norm_add_le (H u-H (schwartzEnergyState φ)) (H (schwartzEnergyState φ))
  rw [sub_add_cancel] at ht
  have hp := scaled_high_difference hDensity hSob q hM u (schwartzEnergyState φ)
  have hs : ‖H (schwartzEnergyState φ)‖ ≤ ‖φ.toLp 2 volume‖ := by
    change ‖highValueL2CLM hDensity hSob q hM (schwartzEnergyState φ)‖ ≤ _
    rw [high_schwartz_identification]
    exact highL2_contraction q M _
  have h1 := mul_le_mul_of_nonneg_left ht hM.le
  have h2 := mul_le_mul_of_nonneg_left hs hM.le
  change M*‖H u‖ ≤ _
  change M*‖H u-H (schwartzEnergyState φ)‖ ≤ _ at hp
  nlinarith

/-- The small-frequency weighted-mass limit for every homogeneous-energy state.
The chosen upper bound controls every positive frequency below it; no cutoff monotonicity. -/
theorem small_weighted_high (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) (u : EnergyState) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 < M), M ≤ δ →
      M*‖highValueL2CLM hDensity hSob q hM u‖ < ε := by
  obtain ⟨φ, hφ⟩ := schwartzEnergyState_approximation hDensity hSob u
  have hg := difference_pureGradientNorm_tendsto (gradientTendsto_of_tendsto hφ)
  obtain ⟨n, hn⟩ := (hg.eventually (gt_mem_nhds (show (0 : ℝ) < ε/2 by linarith))).exists
  have hd : pureGradientNorm (u-schwartzEnergyState (φ n)) < ε/2 := by
    have he : pureGradientNorm (u-schwartzEnergyState (φ n)) =
        pureGradientNorm (schwartzEnergyState (φ n)-u) := by
      simp only [pureGradientNorm_eq_norm_gradientVector, map_sub]
      exact norm_sub_rev _ _
    rw [he]
    exact hn
  let δ : ℝ := ε/(4*(‖(φ n).toLp 2 volume‖+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : δ*(‖(φ n).toLp 2 volume‖+1) = ε/4 := by
    dsimp [δ]
    field_simp
    <;> ring
  refine ⟨δ, hδ, ?_⟩
  intro M hM hMδ
  have hm := mul_le_mul_of_nonneg_right hMδ (norm_nonneg ((φ n).toLp 2 volume))
  have hb := scaled_high_approximation hDensity hSob q hM u (φ n)
  nlinarith

end HartreeF.Paper121SmallFrequency
