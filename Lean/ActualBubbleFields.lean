import SobolevKineticStretch
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Native classical bubble and its genuine L6 / L2 gradient domains. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.Bubble

/-- The unnormalized three dimensional Sobolev bubble. -/
def bubble (x : Space) : ℝ := (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)

/-- The actual classical gradient of the bubble. -/
def bubbleGradient (x : Space) : Space := -(1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) • x

theorem one_add_norm_sq_pos (x : Space) : 0 < 1 + ‖x‖ ^ 2 := by positivity

theorem bubble_pos (x : Space) : 0 < bubble x :=
  Real.rpow_pos_of_pos (one_add_norm_sq_pos x) _

theorem contDiff_bubble : ContDiff ℝ (⊤ : ℕ∞) bubble := by
  exact (contDiff_const.add (contDiff_id.norm_sq ℝ)).rpow_const_of_ne
    (fun x => (one_add_norm_sq_pos x).ne')

theorem continuous_bubble : Continuous bubble := contDiff_bubble.continuous

theorem differentiable_bubble : Differentiable ℝ bubble :=
  contDiff_bubble.differentiable (by simp)

theorem hasFDerivAt_bubble (x : Space) :
    HasFDerivAt bubble (innerSL ℝ (bubbleGradient x)) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).rpow_const
    (p := (-1 / 2 : ℝ)) (Or.inl (one_add_norm_sq_pos x).ne')
  convert h using 1
  · rfl
  · ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      bubbleGradient, real_inner_smul_left]
    norm_num
    ring

theorem fderiv_bubble_apply (x v : Space) :
    fderiv ℝ bubble x v = ⟪bubbleGradient x, v⟫ := by
  rw [(hasFDerivAt_bubble x).fderiv]
  rfl

theorem contDiff_bubbleGradient : ContDiff ℝ (⊤ : ℕ∞) bubbleGradient := by
  exact ((contDiff_const.add (contDiff_id.norm_sq ℝ)).rpow_const_of_ne
    (fun x => (one_add_norm_sq_pos x).ne')).neg.smul contDiff_id

theorem continuous_bubbleGradient : Continuous bubbleGradient :=
  contDiff_bubbleGradient.continuous

theorem bubble_norm_sixth (x : Space) :
    ‖bubble x‖ ^ 6 = (1 + ‖x‖ ^ 2) ^ (-6 / 2 : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_pos (bubble_pos x), bubble,
    ← Real.rpow_mul_natCast (one_add_norm_sq_pos x).le]
  norm_num

theorem bubbleGradient_norm_sq (x : Space) :
    ‖bubbleGradient x‖ ^ 2 = (1 + ‖x‖ ^ 2) ^ (-3 : ℝ) * ‖x‖ ^ 2 := by
  rw [bubbleGradient, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos (one_add_norm_sq_pos x) _), mul_pow,
    ← Real.rpow_mul_natCast (one_add_norm_sq_pos x).le]
  norm_num

theorem bubbleGradient_norm_sq_le (x : Space) :
    ‖bubbleGradient x‖ ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ (-4 / 2 : ℝ) := by
  rw [bubbleGradient_norm_sq]
  calc
    _ ≤ (1 + ‖x‖ ^ 2) ^ (-3 : ℝ) * (1 + ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (one_add_norm_sq_pos x).le _)
    _ = (1 + ‖x‖ ^ 2) ^ (-4 / 2 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one (1 + ‖x‖ ^ 2)]
      rw [← Real.rpow_add (one_add_norm_sq_pos x)]
      norm_num

theorem integrable_bubble_norm_sixth : Integrable (fun x : Space => ‖bubble x‖ ^ 6) := by
  simp only [bubble_norm_sixth]
  exact integrable_rpow_neg_one_add_norm_sq (by norm_num [Space])

theorem memLp_bubble_six : MemLp bubble 6 volume := by
  apply (integrable_norm_rpow_iff continuous_bubble.aestronglyMeasurable
    (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  simpa using integrable_bubble_norm_sixth

theorem integrable_bubbleGradient_norm_sq :
    Integrable (fun x : Space => ‖bubbleGradient x‖ ^ 2) := by
  have h : Integrable (fun x : Space => (1 + ‖x‖ ^ 2) ^ (-4 / 2 : ℝ)) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num [Space])
  apply h.mono' (continuous_bubbleGradient.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact bubbleGradient_norm_sq_le x)

theorem memLp_bubbleGradient_two : MemLp bubbleGradient 2 volume := by
  apply (integrable_norm_rpow_iff continuous_bubbleGradient.aestronglyMeasurable
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  simpa using integrable_bubbleGradient_norm_sq

#print axioms one_add_norm_sq_pos
#print axioms bubble_pos
#print axioms contDiff_bubble
#print axioms continuous_bubble
#print axioms differentiable_bubble
#print axioms hasFDerivAt_bubble
#print axioms fderiv_bubble_apply
#print axioms contDiff_bubbleGradient
#print axioms continuous_bubbleGradient
#print axioms bubble_norm_sixth
#print axioms bubbleGradient_norm_sq
#print axioms bubbleGradient_norm_sq_le
#print axioms integrable_bubble_norm_sixth
#print axioms integrable_bubbleGradient_norm_sq
#print axioms memLp_bubble_six
#print axioms memLp_bubbleGradient_two
end HartreeF.Bubble
