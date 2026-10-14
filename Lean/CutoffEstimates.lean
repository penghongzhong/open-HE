import CutoffNorm

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace HartreeF.CutoffApproximation

/-- The bounded cutoff error lives only outside the growing ball. -/
theorem cutoff_sub_norm_le_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) (n : ℕ) (x : Space) :
    ‖cutoff n x • f x - f x‖ ≤ ‖({y : Space | (n : ℝ) < ‖y‖}.indicator f) x‖ := by
  by_cases hx : (n : ℝ) < ‖x‖
  · have heq : cutoff n x • f x - f x = (cutoff n x - 1) • f x := by
      rw [sub_smul, one_smul]
    rw [Set.indicator_of_mem (s := {y : Space | (n : ℝ) < ‖y‖}) hx, heq, norm_smul, Real.norm_eq_abs]
    have hχ : |cutoff n x - 1| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [cutoff_nonneg n x], by linarith [cutoff_le_one n x]⟩
    exact (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans_eq (one_mul _)
  · rw [Set.indicator_of_notMem (s := {y : Space | (n : ℝ) < ‖y‖}) hx,
      cutoff_eq_one n (by linarith [le_of_not_gt hx])]
    simp

theorem cutoff_sub_eLpNorm_le_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {p : ℝ≥0∞} (hf : AEStronglyMeasurable f volume) (n : ℕ) :
    eLpNorm (fun x => cutoff n x • f x - f x) p volume ≤
      eLpNorm ({x : Space | (n : ℝ) < ‖x‖}.indicator f) p volume := by
  exact eLpNorm_mono (((cutoff_smooth n).continuous.aestronglyMeasurable.smul hf).sub hf)
    (cutoff_sub_norm_le_tail f n)

/-- The literal gradient correction is exactly its exterior-ball version. -/
theorem cutoff_gradient_correction_eq_tail (u : Space → ℝ) (n : ℕ) :
    (fun x => u x • gradient (cutoff n) x) =
      (fun x => ({y : Space | (n : ℝ) < ‖y‖}.indicator u) x •
        gradient (cutoff n) x) := by
  funext x
  by_cases hx : (n : ℝ) < ‖x‖
  · rw [Set.indicator_of_mem (s := {y : Space | (n : ℝ) < ‖y‖}) hx]
  · rw [Set.indicator_of_notMem (s := {y : Space | (n : ℝ) < ‖y‖}) hx, cutoff_gradient_zero n (le_of_not_gt hx)]
    simp

/-- Critical Holder bounds the correction by a vanishing L6 tail and a fixed L3 norm. -/
theorem cutoff_gradient_correction_eLpNorm_le_tail (u : Space → ℝ) (n : ℕ) :
    eLpNorm (fun x => u x • gradient (cutoff n) x) 2 volume ≤
      eLpNorm ({x : Space | (n : ℝ) < ‖x‖}.indicator u) 6 volume *
        eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume := by
  let : ENNReal.HolderTriple 6 3 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num⟩
  rw [cutoff_gradient_correction_eq_tail]
  calc
    _ ≤ eLpNorm ({x : Space | (n : ℝ) < ‖x‖}.indicator u) 6 volume *
        eLpNorm (gradient (cutoff n)) 3 volume :=
      eLpNorm_smul_le_mul_eLpNorm_of_pos (by norm_num)
    _ = _ := by rw [cutoff_gradient_eLpNorm]

/-- Triangle estimate for the actual product weak gradient. -/
theorem cutoff_full_gradient_error_le (u : Space → ℝ) (G : Space → Space)
    (hG : AEStronglyMeasurable G volume) (n : ℕ) :
    eLpNorm (fun x => cutoff n x • G x + u x • gradient (cutoff n) x - G x) 2 volume ≤
      eLpNorm ({x : Space | (n : ℝ) < ‖x‖}.indicator G) 2 volume +
        eLpNorm ({x : Space | (n : ℝ) < ‖x‖}.indicator u) 6 volume *
          eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume := by
  have hfun : (fun x => cutoff n x • G x + u x • gradient (cutoff n) x - G x) =
      (fun x => cutoff n x • G x - G x) + (fun x => u x • gradient (cutoff n) x) := by
    ext x
    simp only [Pi.add_apply]
    abel_nf
  rw [hfun]
  exact (eLpNorm_add_le (by norm_num)).trans
    (add_le_add (cutoff_sub_eLpNorm_le_tail hG n)
      (cutoff_gradient_correction_eLpNorm_le_tail u n))

#print axioms cutoff_sub_norm_le_tail
#print axioms cutoff_sub_eLpNorm_le_tail
#print axioms cutoff_gradient_correction_eq_tail
#print axioms cutoff_gradient_correction_eLpNorm_le_tail
#print axioms cutoff_full_gradient_error_le
end HartreeF.CutoffApproximation
