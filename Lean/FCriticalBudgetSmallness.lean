import FComplementaryPowerSmallness
import FVectorDifferenceBudget

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace HartreeF.TimeHolder
open GradientMajorants
open scoped ENNReal NNReal

/-- Common smallness of the two function differences makes both difference terms linear.
All inputs are extended-valued: zero and infinite coefficients and bounds are allowed. -/
theorem criticalBudget_le_of_difference_smallness {alpha : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (M N D E Y Z delta : ℝ≥0∞)
    (hD : D ≤ delta) (hE : E ≤ delta) :
    criticalBudget alpha M N D E Y Z ≤
      M ^ (2 * alpha) * N ^ (4 : ℝ) * Z +
        (M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
          M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y) * delta := by
  have hp := ennreal_complementary_power_smallness ha ha3 hD hE
  calc
    criticalBudget alpha M N D E Y Z ≤
        M ^ (2 * alpha) * N ^ (4 : ℝ) * Z +
          M ^ (2 * alpha) * N ^ (3 : ℝ) * Y * delta +
          M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y * delta := by
      unfold criticalBudget
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul' le_rfl hE)
      · simpa only [mul_assoc] using
          mul_le_mul' (le_refl (M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y)) hp
    _ = _ := by rw [add_mul, add_assoc]

/-- If the gradient difference is also at most delta, the whole critical budget is linear.
No finite-norm hypothesis is required for this ENNReal inequality. -/
theorem criticalBudget_le_delta {alpha : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (M N D E Y Z delta : ℝ≥0∞)
    (hD : D ≤ delta) (hE : E ≤ delta) (hZ : Z ≤ delta) :
    criticalBudget alpha M N D E Y Z ≤
      (M ^ (2 * alpha) * N ^ (4 : ℝ) +
        M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
        M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y) * delta := by
  calc
    criticalBudget alpha M N D E Y Z ≤
        M ^ (2 * alpha) * N ^ (4 : ℝ) * Z +
          (M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
            M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y) * delta :=
      criticalBudget_le_of_difference_smallness ha ha3 M N D E Y Z delta hD hE
    _ ≤ M ^ (2 * alpha) * N ^ (4 : ℝ) * delta +
          (M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
            M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y) * delta :=
      add_le_add (mul_le_mul' le_rfl hZ) le_rfl
    _ = _ := by rw [← add_mul, ← add_assoc]

end HartreeF.TimeHolder
