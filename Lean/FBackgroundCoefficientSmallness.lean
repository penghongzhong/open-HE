import FVectorBudgetSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace HartreeF.TimeHolder
open MeasureTheory GradientMajorants
open scoped ENNReal NNReal

/-- The literal coefficient of the common difference bound in C36, with the
three background sizes exposed as arguments. -/
def backgroundSmallnessCoefficient (alpha : ℝ) (M N Y : ℝ≥0∞) : ℝ≥0∞ :=
  M ^ (2 * alpha) * N ^ (4 : ℝ) + M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
    M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y

/-- This exposed coefficient is definitionally the existing vector coefficient. -/
theorem vectorSmallnessCoefficient_eq_backgroundSmallnessCoefficient
    {T : Type*} [MeasurableSpace T] (alpha : ℝ) (mu : Measure T)
    (u v : T → Space → ℂ) (P Q : T → Space → Space) :
    vectorSmallnessCoefficient alpha mu u v P Q =
      backgroundSmallnessCoefficient alpha
        (mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v)
        (mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v)
        (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P +
          mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q) := rfl

/-- A bounded background and two sizes below eta give a quartic bound.
This estimate is directly in ENNReal and uses no conversion through toReal. -/
theorem backgroundSmallnessCoefficient_le_quartic {alpha : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (B eta M N Y : ℝ≥0∞)
    (heta : eta ≤ 1) (hM : M ≤ B) (hN : N ≤ eta) (hY : Y ≤ eta) :
    backgroundSmallnessCoefficient alpha M N Y ≤
      (2 * B ^ (2 * alpha) + B ^ (5 * alpha / 3)) * eta ^ (4 : ℝ) := by
  have ht : 0 < theta alpha ∧ theta alpha < 1 := by
    dsimp [theta]
    constructor <;> linarith
  have hp : 0 ≤ 4 - theta alpha := by linarith [ht.2]
  have hthird : N ^ (4 - theta alpha) ≤ eta ^ (3 : ℝ) :=
    (ENNReal.rpow_le_rpow hN hp).trans
      (ENNReal.rpow_le_rpow_of_exponent_ge heta (by linarith [ht.2]))
  have hMa := ENNReal.rpow_le_rpow hM (show 0 ≤ 2 * alpha by positivity)
  have hMb := ENNReal.rpow_le_rpow hM (show 0 ≤ 5 * alpha / 3 by positivity)
  calc
    backgroundSmallnessCoefficient alpha M N Y ≤
        B ^ (2 * alpha) * eta ^ (4 : ℝ) +
          B ^ (2 * alpha) * eta ^ (3 : ℝ) * eta +
          B ^ (5 * alpha / 3) * eta ^ (3 : ℝ) * eta := by
      unfold backgroundSmallnessCoefficient
      exact add_le_add
        (add_le_add (mul_le_mul' hMa (ENNReal.rpow_le_rpow hN (by norm_num)))
          (mul_le_mul' (mul_le_mul' hMa (ENNReal.rpow_le_rpow hN (by norm_num))) hY))
        (mul_le_mul' (mul_le_mul' hMb hthird) hY)
    _ = (2 * B ^ (2 * alpha) + B ^ (5 * alpha / 3)) * eta ^ (4 : ℝ) := by
      simp only [ENNReal.rpow_ofNat]
      ring

/-- The finite real cap is transported to ENNReal without discarding infinities. -/
theorem backgroundSmallnessCoefficient_le_ofReal_quartic {alpha B eta : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (hB : 0 ≤ B)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (M N Y : ℝ≥0∞)
    (hM : M ≤ ENNReal.ofReal B) (hN : N ≤ ENNReal.ofReal eta)
    (hY : Y ≤ ENNReal.ofReal eta) :
    backgroundSmallnessCoefficient alpha M N Y ≤
      ENNReal.ofReal ((2 * B ^ (2 * alpha) + B ^ (5 * alpha / 3)) * eta ^ 4) := by
  have hb := backgroundSmallnessCoefficient_le_quartic ha ha3
    (ENNReal.ofReal B) (ENNReal.ofReal eta) M N Y
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal heta1) hM hN hY
  have hBa : 0 ≤ B ^ (2 * alpha) := Real.rpow_nonneg hB _
  have hBb : 0 ≤ B ^ (5 * alpha / 3) := Real.rpow_nonneg hB _
  have hK : 0 ≤ 2 * B ^ (2 * alpha) + B ^ (5 * alpha / 3) := by positivity
  rw [ENNReal.ofReal_mul hK,
    ENNReal.ofReal_add (mul_nonneg (by norm_num) hBa) hBb,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow heta0]
  simpa only [ENNReal.ofReal_rpow_of_nonneg hB (show 0 ≤ 2 * alpha by positivity),
    ENNReal.ofReal_rpow_of_nonneg hB (show 0 ≤ 5 * alpha / 3 by positivity),
    ENNReal.rpow_ofNat] using hb

/-- A concrete positive threshold works for every nonnegative quartic coefficient.
The choice min(1, epsilon/(K+1)) also covers K=0. -/
theorem exists_positive_quartic_threshold {K epsilon : ℝ}
    (hK : 0 ≤ K) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ K * eta ^ 4 ≤ epsilon := by
  have hden : 0 < K + 1 := by linarith
  let eta := min 1 (epsilon / (K + 1))
  have heta0 : 0 < eta := lt_min zero_lt_one (div_pos hepsilon hden)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetaE : eta * (K + 1) ≤ epsilon :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hpow : eta ^ 4 ≤ eta := by
    calc
      eta ^ 4 = eta ^ 3 * eta := by ring
      _ ≤ 1 * eta := mul_le_mul_of_nonneg_right (pow_le_one₀ heta0.le heta1) heta0.le
      _ = eta := one_mul _
  refine ⟨eta, heta0, heta1, ?_⟩
  exact (mul_le_mul_of_nonneg_left hpow hK).trans (by nlinarith)

/-- Uniform smallness for every extended-valued triple below the finite caps.
The threshold depends only on alpha, B and epsilon. No interval or field is selected. -/
theorem exists_backgroundSmallnessCoefficient_le {alpha B epsilon : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ M N Y : ℝ≥0∞,
      M ≤ ENNReal.ofReal B → N ≤ ENNReal.ofReal eta → Y ≤ ENNReal.ofReal eta →
      backgroundSmallnessCoefficient alpha M N Y ≤ ENNReal.ofReal epsilon := by
  have hK : 0 ≤ 2 * B ^ (2 * alpha) + B ^ (5 * alpha / 3) := by positivity
  obtain ⟨eta, heta0, heta1, hsmall⟩ := exists_positive_quartic_threshold hK hepsilon
  refine ⟨eta, heta0, heta1, ?_⟩
  intro M N Y hM hN hY
  exact (backgroundSmallnessCoefficient_le_ofReal_quartic ha ha3 hB heta0.le heta1
    M N Y hM hN hY).trans (ENNReal.ofReal_le_ofReal hsmall)

/-- The quartic estimate applies to the actual C36 vector coefficient, with
the background and both small norm sums explicitly bounded. -/
theorem vectorSmallnessCoefficient_le_ofReal_quartic {alpha B eta : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (hB : 0 ≤ B)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u v : T → Space → ℂ) (P Q : T → Space → Space)
    (hM : mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v ≤ ENNReal.ofReal B)
    (hN : mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v ≤ ENNReal.ofReal eta)
    (hY : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q ≤ ENNReal.ofReal eta) :
    vectorSmallnessCoefficient alpha mu u v P Q ≤
      ENNReal.ofReal ((2 * B ^ (2 * alpha) + B ^ (5 * alpha / 3)) * eta ^ 4) := by
  rw [vectorSmallnessCoefficient_eq_backgroundSmallnessCoefficient]
  exact backgroundSmallnessCoefficient_le_ofReal_quartic ha ha3 hB heta0 heta1
    _ _ _ hM hN hY

/-- A single positive threshold controls the C36 coefficient uniformly over
all time spaces, measures and fields satisfying the three norm caps. This is
a conditional estimate; it makes no assertion that such an interval or fields exist. -/
theorem exists_vectorSmallnessCoefficient_le {alpha B epsilon : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀
      {T : Type*} [MeasurableSpace T] (mu : Measure T)
      (u v : T → Space → ℂ) (P Q : T → Space → Space),
      mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v ≤ ENNReal.ofReal B →
      mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v ≤ ENNReal.ofReal eta →
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P +
        mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q ≤ ENNReal.ofReal eta →
      vectorSmallnessCoefficient alpha mu u v P Q ≤ ENNReal.ofReal epsilon := by
  obtain ⟨eta, heta0, heta1, hsmall⟩ :=
    exists_backgroundSmallnessCoefficient_le ha ha3 hB hepsilon
  refine ⟨eta, heta0, heta1, ?_⟩
  intro T _ mu u v P Q hM hN hY
  rw [vectorSmallnessCoefficient_eq_backgroundSmallnessCoefficient]
  exact hsmall _ _ _ hM hN hY

end HartreeF.TimeHolder
