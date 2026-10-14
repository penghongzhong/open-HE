import ComplexIMSInstances
import CutoffConvergence

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch CutoffApproximation

/-- Exact chain rule for the literal expanding IMS angle. -/
theorem cutoffAngle_gradient (n : ℕ) (x : Space) :
    gradient (cutoffAngle n) x = -(Real.pi / 2) • gradient (cutoff n) x := by
  have hd : DifferentiableAt ℝ (fun y => 1 - cutoff n y) x :=
    (contDiff_const.sub (cutoff_smooth n)).differentiable (by simp) x
  change gradient (fun y => (Real.pi / 2) * (1 - cutoff n y)) x = _
  simp only [gradient, fderiv_const_mul hd, fderiv_const_sub,
    map_smul, map_neg, smul_neg, neg_smul]

/-- A bounded multiplier supported outside the expanding ball inherits the actual tail bound. -/
theorem exterior_multiplier_eLpNorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {a : Space → ℝ} {p : ℝ≥0∞} (n : ℕ)
    (hf : AEStronglyMeasurable f volume) (ha : Continuous a)
    (hab : ∀ x, |a x| ≤ 1) (haz : ∀ x, ‖x‖ ≤ (n : ℝ) → a x = 0) :
    eLpNorm (fun x => a x • f x) p volume ≤ eLpNorm (exteriorTail n f) p volume := by
  apply eLpNorm_mono (ha.aestronglyMeasurable.smul hf)
  intro x
  simp only [Pi.smul_apply']
  by_cases hx : (n : ℝ) < ‖x‖
  · rw [exteriorTail, Set.indicator_of_mem (s := {y : Space | (n : ℝ) < ‖y‖}) hx, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)).trans_eq (one_mul _)
  · rw [haz x (le_of_not_gt hx), zero_smul, norm_zero]
    exact norm_nonneg _

/-- Cosine-core error is controlled by the actual exterior Lp tail. -/
theorem core_error_eLpNorm_le_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume) (n : ℕ) :
    eLpNorm (fun x => Real.cos (cutoffAngle n x) • f x - f x) p volume ≤
      eLpNorm (exteriorTail n f) p volume := by
  have he : (fun x => Real.cos (cutoffAngle n x) • f x - f x) =
      (fun x => (Real.cos (cutoffAngle n x) - 1) • f x) := by
    funext x
    rw [sub_smul, one_smul]
  rw [he]
  apply exterior_multiplier_eLpNorm_le n hf ((cutoffAngle_valid n).smooth.cos.continuous.sub continuous_const)
  · intro x
    simp only [Pi.sub_apply]
    rw [abs_le]
    have hr := (cutoffAngle_valid n).trigonometric_range x
    exact ⟨by linarith [hr.1], by linarith [hr.2.1]⟩
  · intro x hx
    simp only [Pi.sub_apply]
    rw [cutoffAngle_zero_inside n (by linarith), Real.cos_zero, sub_self]

/-- Sine-tail is controlled by the same actual exterior Lp tail. -/
theorem tail_eLpNorm_le_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume) (n : ℕ) :
    eLpNorm (fun x => Real.sin (cutoffAngle n x) • f x) p volume ≤
      eLpNorm (exteriorTail n f) p volume := by
  apply exterior_multiplier_eLpNorm_le n hf (cutoffAngle_valid n).smooth.sin.continuous
  · intro x
    exact Real.abs_sin_le_one _
  · intro x hx
    rw [cutoffAngle_zero_inside n (by linarith), Real.sin_zero]

/-- The literal angle-gradient correction is a fixed scalar multiple of the verified correction. -/
theorem angle_correction_eLpNorm (f : Space → ℝ) (n : ℕ) :
    eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume =
      ‖-(Real.pi / 2)‖ₑ * eLpNorm (fun x => f x • gradient (cutoff n) x) 2 volume := by
  have he : (fun x => f x • gradient (cutoffAngle n) x) =
      -(Real.pi / 2) • (fun x => f x • gradient (cutoff n) x) := by
    funext x
    simp only [cutoffAngle_gradient, Pi.smul_apply, smul_smul]
    rw [mul_comm]
  rw [he, eLpNorm_const_smul]

/-- Critical L6-to-L2 control of the actual IMS correction, uniformly in n. -/
theorem angle_correction_eLpNorm_le_tail (f : Space → ℝ) (n : ℕ) :
    eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume ≤
      ‖-(Real.pi / 2)‖ₑ *
        (eLpNorm (exteriorTail n f) 6 volume *
          eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume) := by
  rw [angle_correction_eLpNorm]
  gcongr
  exact cutoff_gradient_correction_eLpNorm_le_tail f n

/-- Trigonometric factors contract the angle-gradient correction. -/
theorem angle_correction_multiplier_le {f : Space → ℝ} (hf : MemLp f 6 volume)
    {a : Space → ℝ} (ha : Continuous a) (hab : ∀ x, |a x| ≤ 1) (n : ℕ) :
    eLpNorm (fun x => (a x * f x) • gradient (cutoffAngle n) x) 2 volume ≤
      eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume := by
  have he := function_smul_angle_gradient_L2 (cutoffAngle_valid n) hf
  have hm : AEStronglyMeasurable (fun x => a x • (f x • gradient (cutoffAngle n) x)) volume :=
    ha.aestronglyMeasurable.smul he.aestronglyMeasurable
  apply eLpNorm_mono (by simpa only [smul_smul] using hm)
  intro x
  rw [← smul_smul, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)).trans_eq (one_mul _)

/-- Bound the complete core weak-gradient error, including its cutoff derivative term. -/
theorem core_gradient_error_eLpNorm_le {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) (n : ℕ) :
    eLpNorm (fun x => coreGradient (cutoffAngle n) f G x - G x) 2 volume ≤
      eLpNorm (exteriorTail n G) 2 volume +
        eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume := by
  have he : (fun x => coreGradient (cutoffAngle n) f G x - G x) =
      (fun x => Real.cos (cutoffAngle n x) • G x - G x) -
      (fun x => (Real.sin (cutoffAngle n x) * f x) • gradient (cutoffAngle n) x) := by
    funext x
    simp only [coreGradient, Pi.sub_apply]
    abel
  rw [he]
  exact (eLpNorm_sub_le (by norm_num)).trans (add_le_add
    (core_error_eLpNorm_le_tail hG.aestronglyMeasurable n)
    (angle_correction_multiplier_le hf (cutoffAngle_valid n).smooth.sin.continuous
      (fun _ => Real.abs_sin_le_one _) n))

/-- Bound the complete sine-tail weak gradient. -/
theorem tail_gradient_eLpNorm_le {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) (n : ℕ) :
    eLpNorm (tailGradient (cutoffAngle n) f G) 2 volume ≤
      eLpNorm (exteriorTail n G) 2 volume +
        eLpNorm (fun x => f x • gradient (cutoffAngle n) x) 2 volume := by
  change eLpNorm ((fun x => Real.sin (cutoffAngle n x) • G x) +
    (fun x => (Real.cos (cutoffAngle n x) * f x) • gradient (cutoffAngle n) x)) 2 volume ≤ _
  exact (eLpNorm_add_le (by norm_num)).trans (add_le_add
    (tail_eLpNorm_le_tail hG.aestronglyMeasurable n)
    (angle_correction_multiplier_le hf (cutoffAngle_valid n).smooth.cos.continuous
      (fun _ => Real.abs_cos_le_one _) n))

#print axioms cutoffAngle_gradient
#print axioms exterior_multiplier_eLpNorm_le
#print axioms core_error_eLpNorm_le_tail
#print axioms tail_eLpNorm_le_tail
#print axioms angle_correction_eLpNorm
#print axioms angle_correction_eLpNorm_le_tail
#print axioms angle_correction_multiplier_le
#print axioms core_gradient_error_eLpNorm_le
#print axioms tail_gradient_eLpNorm_le
end HartreeF.ComplexIMS
