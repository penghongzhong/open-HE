import FGeneralMixedDomains

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing CompactCross CrossContinuity

/-- Uniform approximation error is chosen before the original filter index. -/
theorem tendsto_zero_of_uniform_approximation {ι : Type*} {l : Filter ι}
    {f : ι → ℝ≥0∞} {b : ℕ → ι → ℝ≥0∞} {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) (hb : ∀ n, Tendsto (b n) l (𝓝 0))
    (hbound : ∀ n i, f i ≤ e n + b n i) : Tendsto f l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hh : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨n,hn⟩ := (ENNReal.tendsto_nhds_zero.mp he (ε/2) hh).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hb n) (ε/2) hh] with i hi
  exact (hbound n i).trans ((add_le_add hn hi).trans_eq (ENNReal.add_halves ε))

/-- Data for literal scalar functions. Later constructors derive these fields from actual
EnergyState spatial convolution, including the common value/gradient approximation index. -/
structure ScalarCompactApproximation (u h : ℝ → Space → ℂ) where
  value : ℕ → ℝ → Space → ℂ
  gradient : ℕ → ℝ → Space → ℂ
  profile : ScalarProfile u h
  approximate_profile : ∀ n, ScalarProfile (value n) (gradient n)
  value_continuous : ∀ n, Continuous (fun z : ℝ × Space => value n z.1 z.2)
  gradient_continuous : ∀ n, Continuous (fun z : ℝ × Space => gradient n z.1 z.2)
  value_compact : ∀ n, HasCompactSupport (fun z : ℝ × Space => value n z.1 z.2)
  gradient_compact : ∀ n, HasCompactSupport (fun z : ℝ × Space => gradient n z.1 z.2)
  bound : ℝ≥0
  value_V_bound : mixedNorm volume volume ∞ 6 u ≤ bound
  value_S_bound : mixedNorm volume volume 10 10 u ≤ bound
  approximate_V_bound : ∀ n, mixedNorm volume volume ∞ 6 (value n) ≤ bound
  approximate_S_bound : ∀ n, mixedNorm volume volume 10 10 (value n) ≤ bound
  approximate_W_bound : ∀ n, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (gradient n) ≤ bound
  value_error : ∀ n, mixedNorm volume volume 10 10 (fun t x => u t x - value n t x) ≤ smoothingPrecision n
  gradient_error : ∀ n, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => h t x - gradient n t x) ≤ smoothingPrecision n

/-- Triangle estimate in the actual N norm. -/
theorem forcingNorm_le_difference_add (f g : ℝ → Space → ℂ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume)) :
    forcingNorm f ≤ forcingNorm (f-g) + forcingNorm g := by
  have ht := mixed_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6/5 : ℝ)) (by norm_num)
    (f-g) g (hf.sub hg) hg
  have hs : (fun t x => (f-g) t x + g t x) = f := by
    funext t x
    simp only [Pi.sub_apply, sub_add_cancel]
  rw [hs] at ht
  exact ht

#print axioms tendsto_zero_of_uniform_approximation
#print axioms forcingNorm_le_difference_add
end HartreeF.GeneralProfileCross
