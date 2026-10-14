import FCompactCrossBudgets

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open CriticalAffine AffineMixed

theorem source_spaceBudget_scale {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (C : ℝ≥0) (s k : ℝ) (b : Space) {S T : Set Space} (I : Set ℝ)
    (hS : MeasurableSet S) (A B : ℝ) :
    supportBudget C q s ((affine a b) ⁻¹' S) T I (a^k*A) B =
      ENNReal.ofReal (a^(k-3/q)) * supportBudget C q s S T I A B := by
  unfold supportBudget
  rw [affine_preimage_volume ha b hS,ENNReal.ofReal_mul (Real.rpow_nonneg ha.le k),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq.le),jacobian_rpow ha 3]
  calc
    _ = (ENNReal.ofReal (a^k)*ENNReal.ofReal (a^(-(3:ℝ)*(1/q)))) *
      ((C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
        (ENNReal.ofReal B * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ)) := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),← Real.rpow_add ha]
      congr 3
      ring

theorem recipient_spaceBudget_scale {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (C : ℝ≥0) (q k : ℝ) (b : Space) {S T : Set Space} (I : Set ℝ)
    (hT : MeasurableSet T) (A B : ℝ) :
    supportBudget C q s S ((affine a b) ⁻¹' T) I A (a^k*B) =
      ENNReal.ofReal (a^(k-3/s)) * supportBudget C q s S T I A B := by
  unfold supportBudget
  rw [affine_preimage_volume ha b hT,ENNReal.ofReal_mul (Real.rpow_nonneg ha.le k),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hs.le),jacobian_rpow ha 3]
  calc
    _ = (ENNReal.ofReal (a^k)*ENNReal.ofReal (a^(-(3:ℝ)*(1/s)))) *
      ((C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
        (ENNReal.ofReal B * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ)) := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),← Real.rpow_add ha]
      congr 3
      ring

theorem two_scale_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (δ : ℝ) :
    ENNReal.ofReal (a^(-δ)) * ENNReal.ofReal (b^δ) = ENNReal.ofReal ((b/a)^δ) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),Real.rpow_neg ha.le,
    Real.div_rpow hb.le ha.le]
  congr 1
  ring

#print axioms source_spaceBudget_scale
#print axioms recipient_spaceBudget_scale
#print axioms two_scale_rpow
end HartreeF.CompactCross
