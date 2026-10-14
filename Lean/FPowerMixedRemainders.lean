import DensityDerivativeDifference
import LocalFactorDerivativeDifference
import Mathlib.Tactic

/-!
Pointwise mixed power remainders from the audited genuine first derivatives.

Author candidate; exact per-attempt receipts determine native status. This file introduces no analytic axiom or remainder premise.
The generic calculus lemma is discharged below using the existing derivative theorems.
Its only mean-value input is Mathlib's ordinary convex-set inequality on [0,r].
-/

noncomputable section
set_option autoImplicit false

open Set

namespace HartreeF.WeakHartreeChain

/-- The harmless factor `2 ^ t` permits one uniform derivative bound on `[0,r]`. -/
def densityMixedConstant (p : ℝ) : ℝ := p * (p - 1) * (2 : ℝ) ^ (p - 2)

def localFactorMixedConstant (q : ℝ) : ℝ := q * (q + 5) * (2 : ℝ) ^ (q - 1)

/-- Ordinary first-derivative calculus. In each power specialization below, both
`hderiv` and `hdiff` are supplied by previously proved genuine derivative theorems. -/
theorem mixed_remainder_bound_of_derivative_difference
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℂ → G} {DF : ℂ → ℂ →L[ℝ] G} {K t : ℝ}
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hzero : F 0 = 0)
    (hderiv : ∀ w : ℂ, HasFDerivAt F (DF w) w)
    (hdiff : ∀ a b : ℂ, ‖DF a - DF b‖ ≤
      K * (‖a‖ + ‖b‖) ^ t * ‖a - b‖)
    (r z : ℂ) :
    ‖F (r + z) - F r - F z‖ ≤
      (K * (2 : ℝ) ^ t) * ‖r‖ * ‖z‖ * (‖r‖ + ‖z‖) ^ t := by
  have hshift (w : ℂ) :
      HasFDerivAt (fun a : ℂ => F (a + z) - F a)
        (DF (w + z) - DF w) w := by
    have hf : HasFDerivAt (fun a : ℂ => F (a + z)) (DF (w + z)) w :=
      (hasFDerivAt_comp_add_right z).2 (hderiv (w + z))
    change HasFDerivAt ((fun a : ℂ => F (a + z)) - F) (DF (w + z) - DF w) w
    exact hf.sub (hderiv w)
  have hbound (w : ℂ) (hw : w ∈ segment ℝ (0 : ℂ) r) :
      ‖DF (w + z) - DF w‖ ≤
        (K * (2 : ℝ) ^ t) * ‖z‖ * (‖r‖ + ‖z‖) ^ t := by
    have hwr : ‖w‖ ≤ ‖r‖ := by
      simpa only [sub_zero] using norm_sub_le_of_mem_segment hw
    have hrad : ‖w + z‖ + ‖w‖ ≤ 2 * (‖r‖ + ‖z‖) := by
      calc
        ‖w + z‖ + ‖w‖ ≤ (‖w‖ + ‖z‖) + ‖w‖ :=
          add_le_add (norm_add_le w z) le_rfl
        _ ≤ 2 * (‖r‖ + ‖z‖) := by linarith [norm_nonneg z]
    have hpow : (‖w + z‖ + ‖w‖) ^ t ≤ (2 * (‖r‖ + ‖z‖)) ^ t :=
      Real.rpow_le_rpow (add_nonneg (norm_nonneg _) (norm_nonneg _)) hrad ht
    calc
      ‖DF (w + z) - DF w‖ ≤ K * (‖w + z‖ + ‖w‖) ^ t * ‖z‖ := by
        simpa only [add_sub_cancel_left] using hdiff (w + z) w
      _ ≤ K * (2 * (‖r‖ + ‖z‖)) ^ t * ‖z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) (norm_nonneg z)
      _ = (K * (2 : ℝ) ^ t) * ‖z‖ * (‖r‖ + ‖z‖) ^ t := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (add_nonneg (norm_nonneg r) (norm_nonneg z))]
        ring
  have hmean :=
    (convex_segment (0 : ℂ) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w _ => (hshift w).hasFDerivWithinAt) hbound
      (left_mem_segment ℝ (0 : ℂ) r) (right_mem_segment ℝ (0 : ℂ) r)
  calc
    ‖F (r + z) - F r - F z‖ ≤
        ((K * (2 : ℝ) ^ t) * ‖z‖ * (‖r‖ + ‖z‖) ^ t) * ‖r‖ := by
      simpa only [zero_add, hzero, sub_zero] using hmean
    _ = (K * (2 : ℝ) ^ t) * ‖r‖ * ‖z‖ * (‖r‖ + ‖z‖) ^ t := by ring

/-- Valid in particular for `p = 3 + α`, for every positive `α`. -/
theorem density_mixed_remainder_bound {p : ℝ} (hp : 3 < p) (r z : ℂ) :
    ‖density p (r + z) - density p r - density p z‖ ≤
      densityMixedConstant p * ‖r‖ * ‖z‖ * (‖r‖ + ‖z‖) ^ (p - 2) := by
  have hzero : density p (0 : ℂ) = 0 := by
    simp [density, Real.zero_rpow (show p ≠ 0 by linarith)]
  simpa only [densityMixedConstant] using
    mixed_remainder_bound_of_derivative_difference
      (F := density p) (DF := densityDerivative p) (K := p * (p - 1)) (t := p - 2)
      (mul_nonneg (by linarith) (by linarith))
      (by linarith) hzero
      (density_hasFDerivAt (by linarith : 1 < p))
      (densityDerivative_difference_bound hp) r z

theorem density_mixed_remainder_abs_bound {p : ℝ} (hp : 3 < p) (r z : ℂ) :
    |density p (r + z) - density p r - density p z| ≤
      densityMixedConstant p * ‖r‖ * ‖z‖ * (‖r‖ + ‖z‖) ^ (p - 2) := by
  simpa only [Real.norm_eq_abs] using density_mixed_remainder_bound hp r z

/-- Valid for `q = 1 + α`, including the noninteger range `0 < α < 1`. -/
theorem localFactor_mixed_remainder_bound {q : ℝ} (hq : 1 < q) (r z : ℂ) :
    ‖localFactor q (r + z) - localFactor q r - localFactor q z‖ ≤
      localFactorMixedConstant q * ‖r‖ * ‖z‖ * (‖r‖ + ‖z‖) ^ (q - 1) := by
  have hzero : localFactor q (0 : ℂ) = 0 := by simp [localFactor]
  simpa only [localFactorMixedConstant] using
    mixed_remainder_bound_of_derivative_difference
      (F := localFactor q) (DF := localFactorDerivative q)
      (K := q * (q + 5)) (t := q - 1)
      (mul_nonneg (by linarith) (by linarith))
      (by linarith) hzero
      (localFactor_hasFDerivAt hq) (localFactorDerivative_difference_bound hq) r z

theorem densityMixedConstant_pos {p : ℝ} (hp : 3 < p) : 0 < densityMixedConstant p := by
  unfold densityMixedConstant
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  positivity

theorem localFactorMixedConstant_pos {q : ℝ} (hq : 1 < q) :
    0 < localFactorMixedConstant q := by
  unfold localFactorMixedConstant
  have hq0 : 0 < q := by linarith
  have hq5 : 0 < q + 5 := by linarith
  positivity

#print axioms mixed_remainder_bound_of_derivative_difference
#print axioms density_mixed_remainder_bound
#print axioms density_mixed_remainder_abs_bound
#print axioms localFactor_mixed_remainder_bound
#print axioms densityMixedConstant_pos
#print axioms localFactorMixedConstant_pos

end HartreeF.WeakHartreeChain
