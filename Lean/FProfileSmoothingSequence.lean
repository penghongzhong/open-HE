import FSpatialMollifierMixedBound

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileSpatialSmoothing
open CutoffApproximation

/-- An explicit shrinking family of normalized smooth spatial kernels. -/
def shrinkingBump (m : ℕ) : ContDiffBump (0 : Space) :=
  ⟨cutoffScale m, 2 * cutoffScale m, cutoffScale_pos m, by linarith [cutoffScale_pos m]⟩

theorem shrinkingBump_rOut_tendsto :
    Tendsto (fun m => (shrinkingBump m).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => cutoffScale m) atTop (𝓝 0) := by
    simpa only [cutoffScale, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [shrinkingBump, mul_zero] using h.const_mul 2

def smoothingPrecision (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (cutoffScale n)

theorem smoothingPrecision_pos (n : ℕ) : 0 < smoothingPrecision n :=
  ENNReal.ofReal_pos.mpr (cutoffScale_pos n)

theorem smoothingPrecision_tendsto : Tendsto smoothingPrecision atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => cutoffScale m) atTop (𝓝 0) := by
    simpa only [cutoffScale, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun n => ENNReal.ofReal (cutoffScale n)) atTop (𝓝 0)
  simpa only [ENNReal.ofReal_zero, Function.comp_def] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp h

/-- One common smoothing scale simultaneously realizes two vanishing errors at every cutoff index. -/
theorem exists_common_smoothing_scale {a b : ℕ → ℕ → ℝ≥0∞}
    (ha : ∀ n, Tendsto (a n) atTop (𝓝 0)) (hb : ∀ n, Tendsto (b n) atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, (∀ n, a n (m n) ≤ smoothingPrecision n) ∧
      (∀ n, b n (m n) ≤ smoothingPrecision n) := by
  have hex (n : ℕ) : ∃ m : ℕ, a n m ≤ smoothingPrecision n ∧ b n m ≤ smoothingPrecision n := by
    have hs := (ha n).eventually (eventually_lt_nhds (smoothingPrecision_pos n))
    have hw := (hb n).eventually (eventually_lt_nhds (smoothingPrecision_pos n))
    obtain ⟨m, hma, hmb⟩ := (hs.and hw).exists
    exact ⟨m, hma.le, hmb.le⟩
  choose m hm using hex
  exact ⟨m, fun n => (hm n).1, fun n => (hm n).2⟩

#print axioms exists_common_smoothing_scale
end HartreeF.ProfileSpatialSmoothing
