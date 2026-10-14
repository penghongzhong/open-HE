import FCompactCrossSpatial

/-! Finite-support space-time estimate for the literal Riesz cross-potential. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain DerivativeMajorization TimeHolder

/-- Spatial convolution remains jointly measurable in time and output space. -/
theorem riesz_joint_measurable (α c : ℝ) {g : ℝ → Space → ℝ}
    (hg : Measurable (fun z : ℝ × Space => g z.1 z.2)) :
    Measurable (fun z : ℝ × Space => rieszConvolution α c (g z.1) z.2) := by
  have hk : Measurable (fun z : (ℝ × Space) × Space =>
      rieszKernel α c (z.1.2 - z.2)) := by
    unfold rieszKernel
    fun_prop
  have hgi : Measurable (fun z : (ℝ × Space) × Space => g z.1.1 z.2) :=
    hg.comp (measurable_fst.fst.prodMk measurable_snd)
  exact (hk.mul hgi).stronglyMeasurable.integral_prod_right'.measurable

/-- Time localization produces the exact square-root support factor.
The conclusion includes finite actual mixed norm, without toReal truncation. -/
theorem convolution_product_time_support_bound {α c q r s : ℝ} (hH : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3 / α) (hr : 0 < r)
    (hrel : 1 / r = 1 / q - α / 3) (hholder : Real.HolderTriple r s (6 / 5)) :
    ∃ C : ℝ≥0, ∀ (S T : Set Space) (I : Set ℝ),
      MeasurableSet S → MeasurableSet T → MeasurableSet I →
      volume S ≠ ∞ → volume T ≠ ∞ → volume I ≠ ∞ →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      ∀ (g : ℝ → Space → ℝ) (f : ℝ → Space → ℂ),
      Measurable (fun z : ℝ × Space => g z.1 z.2) →
      Measurable (fun z : ℝ × Space => f z.1 z.2) →
      (∀ t x, ‖g t x‖ ≤ A) → (∀ t x, x ∉ S → g t x = 0) →
      (∀ t x, ‖f t x‖ ≤ B) → (∀ t x, x ∉ T → f t x = 0) →
      (∀ t, t ∉ I → (∀ x, g t x = 0) ∨ (∀ x, f t x = 0)) →
      (∀ t, ∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) * g t y) volume) ∧
      mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t x => rieszConvolution α c (g t) x • f t x) ≠ ∞ ∧
      mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t x => rieszConvolution α c (g t) x • f t x) ≤
        (C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
          (ENNReal.ofReal B * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ) := by
  obtain ⟨C,hC⟩ := convolution_product_support_bound hH hq1 hqα hr hrel hholder
  refine ⟨C, fun S T I hS hT hI hSf hTf hIf A B hA hB g f hg hf hga hgs hfb hfs htime => ?_⟩
  have hslice (t : ℝ) := hC S T hS hT hSf hTf A B hA hB (g t) (f t)
    (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (hga t) (hgs t) (hfb t) (hfs t)
  let F : ℝ → Space → ℂ := fun t x => rieszConvolution α c (g t) x • f t x
  let D : ℝ≥0∞ := (C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
    (ENNReal.ofReal B * volume T ^ (1/s))
  have hDm : D ≠ ∞ := by
    dsimp [D]
    have hq : 0 ≤ 1/q := by positivity
    have hs : 0 ≤ 1/s := one_div_nonneg.mpr hholder.symm.pos.le
    finiteness
  have hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2)
      (volume.prod volume) := ((riesz_joint_measurable α c hg).smul hf).aestronglyMeasurable
  have hnmeas := spatial_lp_time_measurable volume volume (ENNReal.ofReal (6/5 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top F hFm
  have hzero (t : ℝ) (ht : t ∉ I) : F t = 0 := by
    funext x
    rcases htime t ht with h | h
    · simp [F, rieszConvolution, h]
    · simp [F, h]
  have hnorm : mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) F ≤
      eLpNorm (I.indicator (fun _ : ℝ => D)) 2 volume := by
    apply eLpNorm_mono_enorm_ae hnmeas
    filter_upwards [] with t
    simp only [enorm_eq_self]
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      exact (hslice t).2.2
    · rw [indicator_of_notMem ht, hzero t ht]
      simp
  rw [eLpNorm_indicator_const hI.nullMeasurableSet (by norm_num) (by norm_num)] at hnorm
  norm_num only [enorm_eq_self, ENNReal.toReal_ofNat] at hnorm
  have hfinite : D * volume I ^ (1/2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hDm (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hIf)
  exact ⟨fun t => (hslice t).1, ne_top_of_le_ne_top hfinite hnorm, hnorm⟩

#print axioms riesz_joint_measurable
#print axioms convolution_product_time_support_bound
end HartreeF.CompactCross
