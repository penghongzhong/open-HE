import F121LowGradientSmall
import F121WeightedHighCompact

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace HartreeF.Paper121SmallFrequency
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest Paper121CutoffMaps

/-- Uniform low-frequency gradient smallness on the actual compact energy carrier.
The conclusion controls every smaller positive cutoff, without monotonicity. -/
theorem compact_small_low_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {Q : Set EnergyState}
    (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 < M), M ≤ δ →
      ∀ u ∈ Q, pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) < ε := by
  classical
  let C : ℝ := Real.sqrt 3
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCp : 0 < C+1 := by linarith
  let τ : ℝ := ε/(2*(C+1))
  have hτ : 0 < τ := div_pos hε (by positivity)
  have herror : C*τ < ε/2 := by
    have hid : (C+1)*τ = ε/2 := by
      dsimp [τ]
      field_simp [ne_of_gt hCp]
    nlinarith
  obtain ⟨S, _hSQ, hSfin, hcover⟩ := hQ.finite_cover_balls hτ
  let r : EnergyState → ℝ := fun u =>
    Classical.choose (small_low_gradient hDensity hSob q u (half_pos hε))
  have hr (u : EnergyState) : 0 < r u :=
    (Classical.choose_spec (small_low_gradient hDensity hSob q u (half_pos hε))).1
  have hs (u : EnergyState) (M : ℝ) (hM : 0 < M) : M ≤ r u →
      pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) < ε/2 :=
    (Classical.choose_spec (small_low_gradient hDensity hSob q u (half_pos hε))).2 M hM
  have hex : ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ S, δ ≤ r v := by
    by_cases hSne : S.Nonempty
    · obtain ⟨v, _hv, hmin⟩ := Set.exists_min_image S r hSfin hSne
      exact ⟨r v, hr v, hmin⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      intro v hv
      exact False.elim (hSne ⟨v, hv⟩)
  obtain ⟨δ, hδ, hbelow⟩ := hex
  refine ⟨δ, hδ, ?_⟩
  intro M hM hMδ u hu
  obtain ⟨v, hv, huv⟩ : ∃ v ∈ S, u ∈ ball v τ := by
    simpa only [mem_iUnion, exists_prop] using hcover hu
  have hnear : ‖u-v‖ < τ := by
    simpa only [mem_ball, dist_eq_norm] using huv
  have hd : pureGradientNorm (u-v) ≤ C*τ :=
    (pureGradient_le_sqrt_three_energyState (u-v)).trans
      (mul_le_mul_of_nonneg_left hnear.le hC)
  have hb := low_gradient_compare hDensity hSob q hM u v
  have hvsmall := hs v M hM (hMδ.trans (hbelow v hv))
  linarith


/-- Both frequency defects are small for the same threshold and the same carrier. -/
theorem compact_small_frequency_pair (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {Q : Set EnergyState}
    (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 < M), M ≤ δ → ∀ u ∈ Q,
      pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) < ε ∧
      M*‖highValueL2CLM hDensity hSob q hM u‖ < ε := by
  obtain ⟨a, ha, hlow⟩ := compact_small_low_gradient hDensity hSob q hQ hε
  obtain ⟨b, hb, hhigh⟩ := compact_small_weighted_high hDensity hSob q hQ hε
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro M hM hMb u hu
  exact ⟨hlow M hM (hMb.trans (min_le_left _ _)) u hu,
    hhigh M hM (hMb.trans (min_le_right _ _)) u hu⟩

end HartreeF.Paper121SmallFrequency
