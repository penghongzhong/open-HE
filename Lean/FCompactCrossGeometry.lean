import FAffineMixedNormIdentity
import FCompactCrossTerms

/-! Exact support geometry and pointwise amplitudes for the project's existing
literal parabolicField, with its original time-center convention. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain TimeHolder CriticalAffine AffineMixed

theorem affine_preimage_volume {a : ℝ} (ha : 0 < a) (b : Space)
    {S : Set Space} (hS : MeasurableSet S) :
    volume ((affine a b) ⁻¹' S) = ENNReal.ofReal ((a^3)⁻¹) * volume S := by
  rw [← Measure.map_apply (by unfold affine; fun_prop) hS, affine_map_volume ha b,
    Measure.smul_apply, smul_eq_mul]

theorem timeAffine_preimage_volume {a : ℝ} (ha : 0 < a) (c : ℝ)
    {I : Set ℝ} (hI : MeasurableSet I) :
    volume ((timeAffine a c) ⁻¹' I) = ENNReal.ofReal ((a^2)⁻¹) * volume I := by
  rw [← Measure.map_apply (by unfold timeAffine; fun_prop) hI, timeAffine_map_volume ha c,
    Measure.smul_apply, smul_eq_mul]

theorem parabolicField_continuous {a : ℝ} (b : Space) (c w : ℝ)
    {f : ℝ → Space → ℂ} (hf : Continuous (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => parabolicField a b c w f z.1 z.2) := by
  unfold parabolicField
  exact continuous_const.smul (hf.comp (show Continuous (fun z : ℝ × Space =>
    (timeAffine a c z.1, affine a b z.2)) from by unfold timeAffine affine; fun_prop))

theorem parabolicField_amplitude {a M : ℝ} (ha : 0 < a) (b : Space) (c w : ℝ)
    {f : ℝ → Space → ℂ} (hf : ∀ t x, ‖f t x‖ ≤ M) :
    ∀ t x, ‖parabolicField a b c w f t x‖ ≤ a^w * M := by
  intro t x
  rw [parabolicField,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg ha.le _)]
  exact mul_le_mul_of_nonneg_left (hf _ _) (Real.rpow_nonneg ha.le _)

theorem parabolicField_space_support (a : ℝ) (b : Space) (c w : ℝ)
    {S : Set Space} {f : ℝ → Space → ℂ} (hf : ∀ t x, x ∉ S → f t x = 0) :
    ∀ t x, x ∉ (affine a b) ⁻¹' S → parabolicField a b c w f t x = 0 := by
  intro t x hx
  simp only [mem_preimage] at hx
  simp only [parabolicField,hf _ _ hx,smul_zero]

theorem parabolicField_time_support (a : ℝ) (b : Space) (c w : ℝ)
    {I : Set ℝ} {f : ℝ → Space → ℂ} (hf : ∀ t, t ∉ I → ∀ x, f t x = 0) :
    ∀ t, t ∉ (timeAffine a c) ⁻¹' I → ∀ x, parabolicField a b c w f t x = 0 := by
  intro t ht x
  simp only [mem_preimage] at ht
  simp only [parabolicField,hf _ ht _,smul_zero]

#print axioms affine_preimage_volume
#print axioms timeAffine_preimage_volume
#print axioms parabolicField_continuous
#print axioms parabolicField_amplitude
#print axioms parabolicField_space_support
#print axioms parabolicField_time_support
end HartreeF.CompactCross
