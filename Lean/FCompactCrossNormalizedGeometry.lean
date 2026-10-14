import FCompactCrossFrameGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
namespace HartreeF.CompactCross

theorem physical_ratio_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a/b+b/a+2)*(a*b)=(a+b)^2 := by
  field_simp
  ring

theorem normalized_space_gap {a b R d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hX : 4*R^2*(a/b+b/a+2) < d^2/(a*b)) :
    0 < d/2 ∧ d/2+R*(a+b) ≤ d := by
  have hp := mul_pos ha hb
  have hX' := (lt_div_iff₀ hp).mp hX
  have he := physical_ratio_identity ha hb
  have hh : 4*R^2*(a+b)^2 < d^2 := by nlinarith
  have hnon : 0 ≤ R*(a+b) := mul_nonneg hR (by linarith)
  constructor <;> nlinarith [sq_nonneg (d-2*R*(a+b))]

theorem normalized_time_gap {a b L t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : L*(a/b+b/a) < t/(a*b)) : L*(a^2+b^2) < t := by
  have hh := (lt_div_iff₀ (mul_pos ha hb)).mp ht
  have he : (a/b+b/a)*(a*b)=a^2+b^2 := by field_simp
  rw [mul_assoc,he] at hh
  exact hh

/-- Exact conversion from support distance to the squared normalized separation. -/
theorem normalized_kernel_power {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 ≤ d) (α : ℝ) :
    ((d/2)*Real.sqrt (a⁻¹*b⁻¹))^(α-3) =
      (2:ℝ)^(3-α)*(d^2/(a*b))^(-(3-α)/2) := by
  have hp : 0 < a*b := mul_pos ha hb
  have he : a⁻¹*b⁻¹=(a*b)⁻¹ := by simp [mul_inv_rev,mul_comm]
  have hs : (d/2)*Real.sqrt (a⁻¹*b⁻¹)=Real.sqrt (d^2/(a*b))/2 := by
    rw [he,Real.sqrt_inv,Real.sqrt_div (sq_nonneg d),Real.sqrt_sq hd]
    ring
  rw [hs,Real.div_rpow (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
    Real.sqrt_eq_rpow,←Real.rpow_mul (div_nonneg (sq_nonneg d) hp.le)]
  have he1 : (1/2:ℝ)*(α-3)=(-(3-α)/2) := by ring
  have he2 : 3-α=-(α-3) := by ring
  rw [he1,he2,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  ring

#print axioms physical_ratio_identity
#print axioms normalized_space_gap
#print axioms normalized_time_gap
#print axioms normalized_kernel_power
end HartreeF.CompactCross
