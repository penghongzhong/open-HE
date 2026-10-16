import F121LowFrequencyL2
import F121CutoffMaps

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Paper121SmallFrequency
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest Paper121CutoffMaps

/-- The size of the actual low Fourier multipliers on the three weak gradients. -/
def lowGradientSize (q : Cutoff) (M : ℝ) (u : EnergyState) : ℝ :=
  Real.sqrt (∑ j : Fin 3, ‖lowL2 q M (energyGradient j u)‖^2)

theorem lowGradientSize_eq (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) = lowGradientSize q M u := by
  simp only [lowEnergyCLM_apply, pureGradientNorm, gradientSquared,
    lowEnergyState_gradient, lowGradientSize]

theorem lowGradientSize_small_limit (q : Cutoff) (u : EnergyState) :
    Tendsto (fun M : ℝ => lowGradientSize q M u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hs : Tendsto (fun M : ℝ => ∑ j : Fin 3, ‖lowL2 q M (energyGradient j u)‖^2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => (lowL2_norm_small_limit q (energyGradient j u)).pow 2)
  simpa only [Function.comp_def, lowGradientSize, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

theorem small_low_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) (u : EnergyState) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 < M), M ≤ δ →
      pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) < ε := by
  have he := (lowGradientSize_small_limit q u).eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨r/2, half_pos hr, ?_⟩
  intro M hM hMr
  rw [lowGradientSize_eq]
  apply hball
  refine ⟨?_, hM⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hM] using
    hMr.trans_lt (half_lt_self hr)

theorem low_gradient_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) ≤ pureGradientNorm u := by
  rw [lowGradientSize_eq]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (lowL2_norm q M (energyGradient j u)) 2)

theorem low_gradient_compare (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u v : EnergyState) :
    pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) ≤ pureGradientNorm (u-v) +
      pureGradientNorm (lowEnergyCLM hDensity hSob q hM v) := by
  have ht := pureGradientNorm_add_le
    (lowEnergyCLM hDensity hSob q hM (u-v)) (lowEnergyCLM hDensity hSob q hM v)
  rw [← map_add, sub_add_cancel] at ht
  exact ht.trans (add_le_add_right (low_gradient_bound hDensity hSob q hM (u-v)) _)

end HartreeF.Paper121SmallFrequency
