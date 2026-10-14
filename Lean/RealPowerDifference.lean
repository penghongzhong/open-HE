import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace HartreeEnergy

/-- The scalar real-power estimate used to control Hartree densities. -/
theorem abs_rpow_sub_rpow_le
    {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ p - b ^ p| ≤ p * (a ^ (p - 1) + b ^ (p - 1)) * |a - b| := by
  have ordered : ∀ (x y : ℝ), 0 ≤ x → x ≤ y →
      |y ^ p - x ^ p| ≤ p * (x ^ (p - 1) + y ^ (p - 1)) * |y - x| := by
    intro x y hx hxy
    have hp0 : 0 ≤ p := zero_le_one.trans hp
    have hpow : 0 ≤ p - 1 := sub_nonneg.mpr hp
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun t : ℝ => t ^ p)
      (C := p * (x ^ (p - 1) + y ^ (p - 1)))
      (fun t (_ht : t ∈ Set.Icc x y) =>
        (Real.hasDerivAt_rpow_const (Or.inr hp)).differentiableAt)
      (fun t ht => ?_) (convex_Icc x y) (Set.left_mem_Icc.mpr hxy)
      (Set.right_mem_Icc.mpr hxy)
    · simpa only [Real.norm_eq_abs] using h
    · rw [Real.deriv_rpow_const, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hp0 (Real.rpow_nonneg (hx.trans ht.1) _))]
      apply mul_le_mul_of_nonneg_left _ hp0
      exact (Real.rpow_le_rpow (hx.trans ht.1) ht.2 hpow).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hx _))
  rcases le_total a b with hab | hba
  · simpa only [abs_sub_comm a b, abs_sub_comm (a ^ p) (b ^ p)] using
      ordered a b ha hab
  · simpa only [add_comm] using ordered b a hb hba

/-- The norm-power estimate on any real or complex normed additive group. -/
theorem abs_norm_rpow_sub_norm_rpow_le
    {E : Type*} [SeminormedAddCommGroup E] {p : ℝ} (hp : 1 ≤ p) (u v : E) :
    |‖u‖ ^ p - ‖v‖ ^ p| ≤
      p * (‖u‖ ^ (p - 1) + ‖v‖ ^ (p - 1)) * ‖u - v‖ := by
  exact (abs_rpow_sub_rpow_le hp (norm_nonneg u) (norm_nonneg v)).trans
    (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le u v)
      (mul_nonneg (zero_le_one.trans hp)
        (add_nonneg (Real.rpow_nonneg (norm_nonneg u) _)
          (Real.rpow_nonneg (norm_nonneg v) _))))

end HartreeEnergy
