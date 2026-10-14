import FCompactCrossSeeds

/-! Literal off-diagonal kernel bounds. The singular kernel is never differentiated. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain DerivativeMajorization TimeHolder

theorem riesz_offDiagonal_bound {α c D A : ℝ} (ha3 : α < 3) (hc : 0 ≤ c)
    (hD : 0 < D) (hA : 0 ≤ A) {S : Set Space}
    (hS : MeasurableSet S) (hSf : volume S ≠ ∞) {g : Space → ℝ}
    (hg : AEStronglyMeasurable g volume) (hgA : ∀ y, ‖g y‖ ≤ A)
    (hgS : ∀ y, y ∉ S → g y = 0) (x : Space)
    (hsep : ∀ y ∈ S, D ≤ ‖x-y‖) :
    Integrable (fun y => rieszKernel α c (x-y)*g y) volume ∧
      ‖rieszConvolution α c g x‖ ≤ c*D^(α-3)*A*(volume S).toReal := by
  have hm : AEStronglyMeasurable (fun y => rieszKernel α c (x-y)*g y) volume :=
    (riesz_fibre_measurable α c x).aestronglyMeasurable.mul hg
  have hcap : 0 ≤ c*D^(α-3)*A := by positivity
  have hb (y : Space) : ‖rieszKernel α c (x-y)*g y‖ ≤ c*D^(α-3)*A := by
    by_cases hy : y ∈ S
    · rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (riesz_kernel_nonneg hc _)]
      have hk : rieszKernel α c (x-y) ≤ c*D^(α-3) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hD (hsep y hy) (by linarith)) hc
      exact mul_le_mul hk (hgA y) (norm_nonneg _) (by positivity)
    · simpa only [hgS y hy,mul_zero,norm_zero] using hcap
  obtain ⟨hp,hn⟩ := finite_support_lp_bound volume (by norm_num : (0:ℝ)<1) hcap hS hSf hm hb
    (by intro y hy; change rieszKernel α c (x-y)*g y=0; rw [hgS y hy,mul_zero])
  norm_num only [ENNReal.ofReal_one,one_div_one,ENNReal.rpow_one] at hp hn
  have hi : Integrable (fun y => rieszKernel α c (x-y)*g y) volume := memLp_one_iff_integrable.mp hp
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y, ‖rieszKernel α c (x-y)*g y‖ := norm_integral_le_integral_norm _
    _ = (eLpNorm (fun y => rieszKernel α c (x-y)*g y) 1 volume).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hm,integral_norm_eq_lintegral_enorm hm]
    _ ≤ (ENNReal.ofReal (c*D^(α-3)*A)*volume S).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf) hn
    _ = _ := by rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hcap]

/-- A literal measurable complex spacetime field bounded in a finite rectangle. -/
theorem rectangular_forcing_bound {B : ℝ} (hB : 0 ≤ B) {T : Set Space} {I : Set ℝ}
    (hT : MeasurableSet T) (hI : MeasurableSet I) (hTf : volume T ≠ ∞) (hIf : volume I ≠ ∞)
    {F : ℝ → Space → ℂ} (hF : Measurable (fun z : ℝ × Space => F z.1 z.2))
    (hamp : ∀ t x, ‖F t x‖ ≤ B)
    (hspace : ∀ t x, x ∉ T → F t x = 0) (htime : ∀ t, t ∉ I → F t = 0) :
    forcingNorm F ≠ ∞ ∧ forcingNorm F ≤
      ENNReal.ofReal B * volume T ^ (5/6 : ℝ) * volume I ^ (1/2 : ℝ) := by
  have hslice (t : ℝ) := finite_support_lp_bound volume (by norm_num : (0:ℝ)<6/5) hB hT hTf
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (hamp t) (hspace t)
  have hnmeas := spatial_lp_time_measurable volume volume (ENNReal.ofReal (6/5 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top F hF.aestronglyMeasurable
  let E : ℝ≥0∞ := ENNReal.ofReal B * volume T ^ (5/6 : ℝ)
  have hb : forcingNorm F ≤ eLpNorm (I.indicator (fun _ : ℝ => E)) 2 volume := by
    apply eLpNorm_mono_enorm_ae hnmeas
    filter_upwards [] with t
    simp only [enorm_eq_self]
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      simpa only [E,Function.comp_def,id_eq,show (1:ℝ)/(6/5)=5/6 by norm_num] using (hslice t).2
    · rw [indicator_of_notMem ht,htime t ht]
      simp
  rw [eLpNorm_indicator_const hI.nullMeasurableSet (by norm_num) (by norm_num)] at hb
  norm_num only [enorm_eq_self, ENNReal.toReal_ofNat] at hb
  have hfinite : E * volume I ^ (1/2 : ℝ) ≠ ∞ := by dsimp [E]; finiteness
  exact ⟨ne_top_of_le_ne_top hfinite hb,hb⟩

/-- Off-diagonal actual convolution product in the exact forcing norm. -/
theorem convolution_product_offDiagonal {α c D A B : ℝ} (ha3 : α < 3) (hc : 0 ≤ c)
    (hD : 0 < D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {S T : Set Space} {I : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hI : MeasurableSet I)
    (hSf : volume S ≠ ∞) (hTf : volume T ≠ ∞) (hIf : volume I ≠ ∞)
    {g : ℝ → Space → ℝ} {f : ℝ → Space → ℂ}
    (hg : Measurable (fun z : ℝ × Space => g z.1 z.2))
    (hf : Measurable (fun z : ℝ × Space => f z.1 z.2))
    (hgA : ∀ t x, ‖g t x‖ ≤ A) (hfB : ∀ t x, ‖f t x‖ ≤ B)
    (hgS : ∀ t x, x ∉ S → g t x = 0) (hfT : ∀ t x, x ∉ T → f t x = 0)
    (htime : ∀ t, t ∉ I → (∀ x, g t x = 0) ∨ (∀ x, f t x = 0))
    (hsep : ∀ x ∈ T, ∀ y ∈ S, D ≤ ‖x-y‖) :
    (∀ t, ∀ x ∈ T, Integrable (fun y => rieszKernel α c (x-y)*g t y) volume) ∧
    forcingNorm (fun t x => rieszConvolution α c (g t) x • f t x) ≠ ∞ ∧
    forcingNorm (fun t x => rieszConvolution α c (g t) x • f t x) ≤
      ENNReal.ofReal (c*D^(α-3)*A*(volume S).toReal*B) *
        volume T ^ (5/6 : ℝ) * volume I ^ (1/2 : ℝ) := by
  have hpoint (t : ℝ) (x : Space) (hx : x ∈ T) := riesz_offDiagonal_bound ha3 hc hD hA hS hSf
    (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (hgA t) (hgS t) x (hsep x hx)
  refine ⟨fun t x hx => (hpoint t x hx).1,?_⟩
  apply rectangular_forcing_bound (by positivity) hT hI hTf hIf
    ((riesz_joint_measurable α c hg).smul hf)
  · intro t x
    by_cases hx : x ∈ T
    · rw [norm_smul]
      exact mul_le_mul (hpoint t x hx).2 (hfB t x) (norm_nonneg _) (by positivity)
    · simp only [hfT t x hx,smul_zero,norm_zero]
      positivity
  · intro t x hx
    simp only [hfT t x hx,smul_zero]
  · intro t ht
    funext x
    rcases htime t ht with h | h
    · simp [rieszConvolution,h]
    · simp [h]

#print axioms riesz_offDiagonal_bound
#print axioms rectangular_forcing_bound
#print axioms convolution_product_offDiagonal
end HartreeF.CompactCross
