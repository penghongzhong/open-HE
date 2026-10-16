import GradientLpBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open GradientMajorants

/-- Pointwise norm domination transfers a genuine finite bound on the same measure. -/
theorem spatialBound_of_ae_norm_le {f g : Space → ℝ} {s B : ℝ}
    (hf : SpatialBound f s B) (hg : AEStronglyMeasurable g volume)
    (hgf : ∀ᵐ x ∂volume, ‖g x‖ ≤ ‖f x‖) : SpatialBound g s B := by
  refine ⟨hf.reciprocal_pos, hf.memLp.of_le hg hgf, ?_⟩
  exact (ENNReal.toReal_mono hf.memLp.eLpNorm_ne_top (eLpNorm_mono_ae hg hgf)).trans hf.bound

theorem spatialBound_const_mul {f : Space → ℝ} {s B C : ℝ}
    (hf : SpatialBound f s B) (hC : 0 ≤ C) :
    SpatialBound (fun x => C * f x) s (C * B) := by
  refine ⟨hf.reciprocal_pos, hf.memLp.const_smul C, ?_⟩
  change (eLpNorm (C • f) (ENNReal.ofReal (1 / s)) volume).toReal ≤ C * B
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm,
    Real.norm_eq_abs, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_left hf.bound hC

/-- A bounded actual factor costs only its essential bound, not a fictitious finite-volume norm. -/
theorem spatialBound_mul_bounded {f g : Space → ℝ} {s B M : ℝ}
    (hf : SpatialBound f s B) (hg : AEStronglyMeasurable g volume)
    (hM : 0 ≤ M) (hgM : ∀ᵐ x ∂volume, ‖g x‖ ≤ M) :
    SpatialBound (fun x => g x * f x) s (M * B) := by
  apply spatialBound_of_ae_norm_le (spatialBound_const_mul hf hM)
    (hg.mul hf.memLp.aestronglyMeasurable)
  filter_upwards [hgM] with x hx
  change ‖g x * f x‖ ≤ ‖M * f x‖
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

theorem spatialBound_power_six {f : Space → ℝ} {a : ℝ}
    (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 6 volume) (ha : 0 < a) :
    SpatialBound (fun x => f x ^ a) (a / 6) (spatialNorm 6 f ^ a) := by
  convert (spatialBound_self (q := 6) (by norm_num) (by simpa using hf)).rpow hn ha using 1
  ring

end HartreeF.BoundedHartreeGradient
