import FCompactCrossGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open CriticalAffine AffineMixed

def supportBudget (C : ℝ≥0) (q s : ℝ) (S T : Set Space) (I : Set ℝ) (A B : ℝ) : ℝ≥0∞ :=
  (C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
    (ENNReal.ofReal B * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ)

theorem supportBudget_ne_top (C : ℝ≥0) {q s : ℝ} (hq : 0 < q) (hs : 0 < s)
    {S T : Set Space} {I : Set ℝ} (hS : volume S ≠ ∞) (hT : volume T ≠ ∞)
    (hI : volume I ≠ ∞) (A B : ℝ) : supportBudget C q s S T I A B ≠ ∞ := by
  unfold supportBudget
  finiteness

theorem ofReal_rpow_triple {a : ℝ} (ha : 0 < a) (x y z : ℝ) :
    ENNReal.ofReal (a^x) * ENNReal.ofReal (a^y) * ENNReal.ofReal (a^z) =
      ENNReal.ofReal (a^(x+y+z)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)),
    ← Real.rpow_add ha, ← Real.rpow_add ha]

/-- The spatial Jacobian and time support jointly produce a^(k-3/q-1). -/
theorem source_supportBudget_scale {a q : ℝ} (ha : 0 < a) (hq : 0 < q)
    (C : ℝ≥0) (s k : ℝ) (b : Space) (c : ℝ) {S T : Set Space} {I : Set ℝ}
    (hS : MeasurableSet S) (hI : MeasurableSet I) (A B : ℝ) :
    supportBudget C q s ((affine a b) ⁻¹' S) T ((timeAffine a c) ⁻¹' I) (a^k*A) B =
      ENNReal.ofReal (a^(k-3/q-1)) * supportBudget C q s S T I A B := by
  unfold supportBudget
  rw [affine_preimage_volume ha b hS,timeAffine_preimage_volume ha c hI,
    ENNReal.ofReal_mul (Real.rpow_nonneg ha.le k),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq.le),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    jacobian_rpow ha 3,jacobian_rpow ha 2]
  calc
    _ = (ENNReal.ofReal (a^k) * ENNReal.ofReal (a^(-(3:ℝ)*(1/q))) *
        ENNReal.ofReal (a^(-(2:ℝ)*(1/2)))) *
      ((C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
        (ENNReal.ofReal B * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ)) := by ring
    _ = _ := by
      rw [ofReal_rpow_triple ha]
      congr 3
      ring

/-- The reciprocal allocation is in the local recipient factor. -/
theorem recipient_supportBudget_scale {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (C : ℝ≥0) (q k : ℝ) (b : Space) (c : ℝ) {S T : Set Space} {I : Set ℝ}
    (hT : MeasurableSet T) (hI : MeasurableSet I) (A B : ℝ) :
    supportBudget C q s S ((affine a b) ⁻¹' T) ((timeAffine a c) ⁻¹' I) A (a^k*B) =
      ENNReal.ofReal (a^(k-3/s-1)) * supportBudget C q s S T I A B := by
  unfold supportBudget
  rw [affine_preimage_volume ha b hT,timeAffine_preimage_volume ha c hI,
    ENNReal.ofReal_mul (Real.rpow_nonneg ha.le k),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hs.le),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    jacobian_rpow ha 3,jacobian_rpow ha 2]
  calc
    _ = (ENNReal.ofReal (a^k) * ENNReal.ofReal (a^(-(3:ℝ)*(1/s))) *
        ENNReal.ofReal (a^(-(2:ℝ)*(1/2)))) *
      ((C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
        (ENNReal.ofReal B * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ)) := by ring
    _ = _ := by
      rw [ofReal_rpow_triple ha]
      congr 3
      ring

theorem scaled_power {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (w p : ℝ) :
    (a^w*M)^p = a^(w*p)*M^p := by
  rw [Real.mul_rpow (Real.rpow_nonneg ha.le _) hM, ← Real.rpow_mul ha.le]

theorem scaled_power_product {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (w v p H K : ℝ) :
    K * (a^w*M)^p * (a^v*H) = a^(w*p+v) * (K*M^p*H) := by
  rw [scaled_power ha hM,Real.rpow_add ha]
  ring

#print axioms supportBudget_ne_top
#print axioms ofReal_rpow_triple
#print axioms source_supportBudget_scale
#print axioms recipient_supportBudget_scale
#print axioms scaled_power
#print axioms scaled_power_product
end HartreeF.CompactCross
