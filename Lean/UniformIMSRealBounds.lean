import CompactHomogeneousTails

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation SobolevStretch

/-- The fixed, finite critical IMS multiplier constant. -/
def imsGradientConstant : ℝ :=
  ‖-(Real.pi / 2)‖ * (eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume).toReal

theorem imsGradientConstant_nonneg : 0 ≤ imsGradientConstant := by
  unfold imsGradientConstant
  positivity

theorem exteriorTail_memLp {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    {p : ℝ≥0∞} (hf : MemLp f p volume) (n : ℕ) : MemLp (exteriorTail n f) p volume :=
  MemLp.indicator (isOpen_lt continuous_const continuous_norm).measurableSet.nullMeasurableSet hf

/-- Quantitative real norm estimate for the actual angle-gradient correction. -/
theorem angle_correction_real_le_tail {f : Space → ℝ} (hf : MemLp f 6 volume) (n : ℕ) :
    (eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume).toReal ≤
      imsGradientConstant * (eLpNorm (exteriorTail n f) 6 volume).toReal := by
  have hfinite : ‖-(Real.pi / 2)‖ₑ *
      (eLpNorm (exteriorTail n f) 6 volume *
        eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (exteriorTail_memLp hf n).eLpNorm_ne_top
      cutoff_gradient_eLpNorm_lt_top.ne)
  have hh := ENNReal.toReal_mono hfinite (angle_correction_eLpNorm_le_tail f n)
  simpa only [ENNReal.toReal_mul, enorm, ENNReal.coe_toReal, coe_nnnorm,
    imsGradientConstant, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Real and imaginary component tails are controlled by the actual complex L6 tail. -/
theorem component_tail_real_le {u : Space → ℂ} (hu : MemLp u 6 volume)
    {f : Space → ℝ} (hf : MemLp f 6 volume) (hfu : ∀ x, ‖f x‖ ≤ ‖u x‖) (n : ℕ) :
    (eLpNorm (exteriorTail n f) 6 volume).toReal ≤
      (eLpNorm (exteriorTail n u) 6 volume).toReal := by
  apply ENNReal.toReal_mono (exteriorTail_memLp hu n).eLpNorm_ne_top
  apply eLpNorm_mono (exteriorTail_memLp hf n).aestronglyMeasurable
  intro x
  unfold exteriorTail
  by_cases hx : (n : ℝ) < ‖x‖
  · simpa [Set.indicator, hx] using hfu x
  · simp [Set.indicator, hx]

/-- Explicit uniform-ready complete weak-gradient estimates for both IMS pieces. -/
theorem gradient_real_bounds {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) (n : ℕ) :
    (eLpNorm (fun x => coreGradient (cutoffAngle n) f G x - G x) 2 volume).toReal ≤
      (eLpNorm (exteriorTail n G) 2 volume).toReal +
        imsGradientConstant * (eLpNorm (exteriorTail n f) 6 volume).toReal ∧
    (eLpNorm (tailGradient (cutoffAngle n) f G) 2 volume).toReal ≤
      (eLpNorm (exteriorTail n G) 2 volume).toReal +
        imsGradientConstant * (eLpNorm (exteriorTail n f) 6 volume).toReal := by
  have he := function_smul_angle_gradient_L2 (cutoffAngle_valid n) hf
  have hfin := ENNReal.add_ne_top.mpr ⟨(exteriorTail_memLp hG n).eLpNorm_ne_top, he.eLpNorm_ne_top⟩
  have hc := ENNReal.toReal_mono hfin (core_gradient_error_eLpNorm_le hf hG n)
  have ht := ENNReal.toReal_mono hfin (tail_gradient_eLpNorm_le hf hG n)
  rw [ENNReal.toReal_add (exteriorTail_memLp hG n).eLpNorm_ne_top he.eLpNorm_ne_top] at hc ht
  have he' := angle_correction_real_le_tail hf n
  exact ⟨hc.trans (add_le_add le_rfl he'), ht.trans (add_le_add le_rfl he')⟩

/-- Uniform-ready complex core and tail L6 estimates. -/
theorem function_real_bounds {u : Space → ℂ} (hu : MemLp u 6 volume) (n : ℕ) :
    (eLpNorm (fun x => core (cutoffAngle n) u x - u x) 6 volume).toReal ≤
      (eLpNorm (exteriorTail n u) 6 volume).toReal ∧
    (eLpNorm (tail (cutoffAngle n) u) 6 volume).toReal ≤
      (eLpNorm (exteriorTail n u) 6 volume).toReal := by
  exact ⟨ENNReal.toReal_mono (exteriorTail_memLp hu n).eLpNorm_ne_top
    (core_error_eLpNorm_le_tail hu.aestronglyMeasurable n),
    ENNReal.toReal_mono (exteriorTail_memLp hu n).eLpNorm_ne_top
    (tail_eLpNorm_le_tail hu.aestronglyMeasurable n)⟩

#print axioms imsGradientConstant_nonneg
#print axioms exteriorTail_memLp
#print axioms angle_correction_real_le_tail
#print axioms component_tail_real_le
#print axioms gradient_real_bounds
#print axioms function_real_bounds
end HartreeF.ComplexIMS
