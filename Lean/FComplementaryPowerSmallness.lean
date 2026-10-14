import HartreeGradientDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace HartreeF.TimeHolder
open GradientMajorants
open scoped ENNReal NNReal

/-- The two difference exponents in the third critical-budget term sum to one. -/
theorem complementary_exponents_sum (alpha : ℝ) :
    alpha / 3 + theta alpha = 1 := by
  dsimp [theta]
  ring

/-- Both difference exponents are positive throughout the full Hartree range. -/
theorem complementary_exponents_pos {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3) :
    0 < alpha / 3 ∧ 0 < theta alpha := by
  constructor
  · positivity
  · dsimp [theta]
    linarith

/-- The real complementary-power identity includes the zero base. -/
theorem real_complementary_power_identity (alpha : ℝ) {delta : ℝ} (hd : 0 ≤ delta) :
    delta ^ (alpha / 3) * delta ^ theta alpha = delta := by
  rw [← Real.rpow_add' hd (by rw [complementary_exponents_sum]; norm_num),
    complementary_exponents_sum, Real.rpow_one]

/-- A common nonnegative bound controls the real mixed power, also when the bound is zero. -/
theorem real_complementary_power_smallness {alpha D E delta : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (hD0 : 0 ≤ D) (hE0 : 0 ≤ E)
    (hD : D ≤ delta) (hE : E ≤ delta) :
    D ^ (alpha / 3) * E ^ theta alpha ≤ delta := by
  obtain ⟨hap, htp⟩ := complementary_exponents_pos ha ha3
  calc
    D ^ (alpha / 3) * E ^ theta alpha ≤
        delta ^ (alpha / 3) * delta ^ theta alpha :=
      mul_le_mul (Real.rpow_le_rpow hD0 hD hap.le)
        (Real.rpow_le_rpow hE0 hE htp.le) (Real.rpow_nonneg hE0 _)
        (Real.rpow_nonneg (hD0.trans hD) _)
    _ = delta := real_complementary_power_identity alpha (hD0.trans hD)

/-- The extended identity needs no finiteness or nonzero-base assumption. -/
theorem ennreal_complementary_power_identity {alpha : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (delta : ℝ≥0∞) :
    delta ^ (alpha / 3) * delta ^ theta alpha = delta := by
  obtain ⟨hap, htp⟩ := complementary_exponents_pos ha ha3
  rw [← ENNReal.rpow_add_of_nonneg _ _ hap.le htp.le,
    complementary_exponents_sum, ENNReal.rpow_one]

/-- The extended mixed-power bound is valid for delta = 0 and delta = infinity. -/
theorem ennreal_complementary_power_smallness {alpha : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) {D E delta : ℝ≥0∞}
    (hD : D ≤ delta) (hE : E ≤ delta) :
    D ^ (alpha / 3) * E ^ theta alpha ≤ delta := by
  obtain ⟨hap, htp⟩ := complementary_exponents_pos ha ha3
  calc
    D ^ (alpha / 3) * E ^ theta alpha ≤
        delta ^ (alpha / 3) * delta ^ theta alpha :=
      mul_le_mul' (ENNReal.rpow_le_rpow hD hap.le) (ENNReal.rpow_le_rpow hE htp.le)
    _ = delta := ennreal_complementary_power_identity ha ha3 delta

end HartreeF.TimeHolder
