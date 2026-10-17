import FBoundedSpatialBounds

/-!
Author candidate. Exact per-attempt receipts determine native status.
Ordinary actual-function Holder and nonnegative-power bookkeeping only.
All input memberships refer to the literal same functions throughout.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace HartreeF.MixedRemainderLp
open GradientMajorants BoundedHartreeGradient

/-- The real-valued eLpNorm. Every estimate below also retains actual MemLp
membership, so ENNReal.toReal is never used to conceal an infinite norm. -/
def actualNorm {E : Type*} [NormedAddCommGroup E]
    (q : ℝ≥0∞) (f : Space → E) : ℝ := (eLpNorm f q volume).toReal

/-- The scalar norm function retains the exact original-function Lq norm. -/
theorem norm_spatialBound {E : Type*} [NormedAddCommGroup E]
    {q : ℝ} (hq : 0 < q) {f : Space → E}
    (hf : MemLp f (ENNReal.ofReal q) volume) :
    SpatialBound (fun x => ‖f x‖) (1 / q) (actualNorm (ENNReal.ofReal q) f) := by
  have h := spatialBound_self hq hf.norm
  have hn : spatialNorm q (fun x => ‖f x‖) = actualNorm (ENNReal.ofReal q) f := by
    unfold spatialNorm actualNorm
    rw [eLpNorm_norm f hf.aestronglyMeasurable]
  rw [hn] at h
  exact h

/-- The essential bound is obtained from the actual L-infinity membership. -/
theorem ae_norm_le_actualNorm_top {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : MemLp f ∞ volume) :
    ∀ᵐ x ∂volume, ‖f x‖ ≤ actualNorm ∞ f := by
  have he : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ eLpNorm f ∞ volume := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using
      enorm_ae_le_eLpNormEssSup f volume
  filter_upwards [he] with x hx
  simpa only [toReal_enorm, actualNorm] using
    ENNReal.toReal_mono hf.eLpNorm_ne_top hx

/-- Ordinary domination transfers a scalar finite bound to any actual measurable
normed-group-valued function. Actual remainder theorems discharge `hgf` themselves. -/
theorem domain_bound_of_spatialBound {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} {f : Space → ℝ} {s B : ℝ}
    (hf : SpatialBound f s B) (hg : AEStronglyMeasurable g volume)
    (hgf : ∀ᵐ x ∂volume, ‖g x‖ ≤ f x) :
    MemLp g (ENNReal.ofReal (1 / s)) volume ∧
      actualNorm (ENNReal.ofReal (1 / s)) g ≤ B := by
  refine ⟨hf.memLp.mono' hg hgf, ?_⟩
  exact (ENNReal.toReal_mono hf.memLp.eLpNorm_ne_top
    (eLpNorm_mono_ae_real hg hgf)).trans hf.bound

/-- Literal mixed majorant, with one bounded factor and one L2 factor. -/
def mixedMajorant (t : ℝ) (r z : Space → ℂ) (x : Space) : ℝ :=
  ‖r x‖ * (‖z x‖ * (‖r x‖ + ‖z x‖) ^ t)

/-- A genuine AE amplitude on r times L2 times L^(6/t). The bound is
attached to the original r, not an abstract gradient or source budget. -/
theorem mixedMajorant_amplitude_spatialBound {t A : ℝ} (ht : 0 < t)
    {r z : Space → ℂ} (hr6 : MemLp r 6 volume)
    (hz2 : MemLp z 2 volume) (hz6 : MemLp z 6 volume)
    (hA : 0 ≤ A) (hrA : ∀ᵐ x ∂volume, ‖r x‖ ≤ A) :
    SpatialBound (mixedMajorant t r z) ((3 + t) / 6)
      (A * actualNorm 2 z * (actualNorm 6 r + actualNorm 6 z) ^ t) := by
  have hR : SpatialBound (fun x => ‖r x‖) (1 / 6) (actualNorm 6 r) := by
    simpa only [ENNReal.ofReal_ofNat] using
      norm_spatialBound (q := 6) (by norm_num) (by simpa using hr6)
  have hZ : SpatialBound (fun x => ‖z x‖) (1 / 6) (actualNorm 6 z) := by
    simpa only [ENNReal.ofReal_ofNat] using
      norm_spatialBound (q := 6) (by norm_num) (by simpa using hz6)
  have hZ2 : SpatialBound (fun x => ‖z x‖) (1 / 2) (actualNorm 2 z) := by
    simpa only [ENNReal.ofReal_ofNat] using
      norm_spatialBound (q := 2) (by norm_num) (by simpa using hz2)
  have hsum := hR.add hZ (by norm_num : (1 : ℝ) / 6 ≤ 1)
  have hp := hsum.rpow (fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)) ht
  have htop : ∀ᵐ x ∂volume, ‖(‖r x‖ : ℝ)‖ ≤ A := by
    simpa only [norm_norm] using hrA
  have hb := spatialBound_mul_bounded (hZ2.mul hp)
    hr6.aestronglyMeasurable.norm hA htop
  convert hb using 1
  all_goals first | rfl | ring

/-- Numerical constants are multiplied only after the actual Holder estimate. -/
theorem mixedMajorant_const_amplitude_spatialBound {t C A : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C)
    {r z : Space → ℂ} (hr6 : MemLp r 6 volume)
    (hz2 : MemLp z 2 volume) (hz6 : MemLp z 6 volume)
    (hA : 0 ≤ A) (hrA : ∀ᵐ x ∂volume, ‖r x‖ ≤ A) :
    SpatialBound (fun x => C * mixedMajorant t r z x) ((3 + t) / 6)
      (C * A * actualNorm 2 z * (actualNorm 6 r + actualNorm 6 z) ^ t) := by
  convert spatialBound_const_mul
    (mixedMajorant_amplitude_spatialBound ht hr6 hz2 hz6 hA hrA) hC using 1
  ring

/-- Actual L-infinity membership provides the genuine amplitude without a new premise. -/
theorem mixedMajorant_spatialBound {t : ℝ} (ht : 0 < t)
    {r z : Space → ℂ} (hrtop : MemLp r ∞ volume)
    (hr6 : MemLp r 6 volume) (hz2 : MemLp z 2 volume) (hz6 : MemLp z 6 volume) :
    SpatialBound (mixedMajorant t r z) ((3 + t) / 6)
      (actualNorm ∞ r * actualNorm 2 z *
        (actualNorm 6 r + actualNorm 6 z) ^ t) :=
  mixedMajorant_amplitude_spatialBound ht hr6 hz2 hz6
    ENNReal.toReal_nonneg (ae_norm_le_actualNorm_top hrtop)

theorem mixedMajorant_const_spatialBound {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    {r z : Space → ℂ} (hrtop : MemLp r ∞ volume)
    (hr6 : MemLp r 6 volume) (hz2 : MemLp z 2 volume) (hz6 : MemLp z 6 volume) :
    SpatialBound (fun x => C * mixedMajorant t r z x) ((3 + t) / 6)
      (C * actualNorm ∞ r * actualNorm 2 z *
        (actualNorm 6 r + actualNorm 6 z) ^ t) :=
  mixedMajorant_const_amplitude_spatialBound ht hC hr6 hz2 hz6
    ENNReal.toReal_nonneg (ae_norm_le_actualNorm_top hrtop)

/-- Two powers of |z| are assigned to L4; the remaining t powers are assigned
to L6. The reciprocal target exponent is 2/4+t/6=(3+t)/6. -/
theorem purePower_spatialBound {t : ℝ} (ht : 0 < t)
    {z : Space → ℂ} (hz4 : MemLp z 4 volume) (hz6 : MemLp z 6 volume) :
    SpatialBound (fun x => ‖z x‖ ^ (2 + t)) ((3 + t) / 6)
      (actualNorm 4 z ^ 2 * actualNorm 6 z ^ t) := by
  have h4 : SpatialBound (fun x => ‖z x‖) (1 / 4) (actualNorm 4 z) := by
    simpa only [ENNReal.ofReal_ofNat] using
      norm_spatialBound (q := 4) (by norm_num) (by simpa using hz4)
  have h6 : SpatialBound (fun x => ‖z x‖) (1 / 6) (actualNorm 6 z) := by
    simpa only [ENNReal.ofReal_ofNat] using
      norm_spatialBound (q := 6) (by norm_num) (by simpa using hz6)
  have ha := h4.rpow (fun x => norm_nonneg (z x)) (by norm_num : (0 : ℝ) < 2)
  have hb := h6.rpow (fun x => norm_nonneg (z x)) ht
  convert ha.mul hb using 1
  · funext x
    exact Real.rpow_add' (norm_nonneg _) (by linarith : 2 + t ≠ 0)
  · ring
  · rw [Real.rpow_two]

/-- Requested Banach-space ranges, with the density endpoint distinguished. -/
theorem local_target_range {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    1 < 6 / (3 + α) ∧ 6 / (3 + α) < 2 := by
  have hd : 0 < 3 + α := by linarith
  constructor
  · exact (lt_div_iff₀ hd).2 (by linarith)
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem density_target_range {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    1 < 6 / (4 + α) ∧ 6 / (4 + α) < 3 / 2 := by
  have hd : 0 < 4 + α := by linarith
  constructor
  · exact (lt_div_iff₀ hd).2 (by linarith)
  · exact (div_lt_iff₀ hd).2 (by linarith)

end HartreeF.MixedRemainderLp
