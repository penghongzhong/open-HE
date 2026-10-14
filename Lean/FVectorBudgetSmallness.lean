import FCriticalBudgetSmallness
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory GradientMajorants
open scoped ENNReal NNReal

/-- The coefficient left after controlling the three actual difference norms.
It contains only the sizes of the two fields and the reference gradient. -/
def vectorSmallnessCoefficient {T : Type*} [MeasurableSpace T] (alpha : ℝ)
    (mu : Measure T) (u v : T → Space → ℂ) (P Q : T → Space → Space) : ℝ≥0∞ :=
  let M := mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v
  let N := mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v
  let Y := mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P +
    mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q
  M ^ (2 * alpha) * N ^ (4 : ℝ) + M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
    M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y

/-- Literal function and vector-gradient differences give a linear delta budget.
This is extended-valued and does not assume any interval or norm is finite. -/
theorem vectorDifferenceBudget_le_delta {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space) (delta : ℝ≥0∞)
    (hD : mixedNorm mu volume ∞ 6 (fun t => u t - v t) ≤ delta)
    (hE : mixedNorm mu volume 10 10 (fun t => u t - v t) ≤ delta)
    (hZ : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => U t - P t) +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => V t - Q t) ≤ delta) :
    vectorDifferenceBudget alpha mu u v U V P Q ≤
      vectorSmallnessCoefficient alpha mu u v P Q * delta := by
  unfold vectorDifferenceBudget vectorSmallnessCoefficient
  exact criticalBudget_le_delta ha ha3 _ _ _ _ _ _ delta hD hE hZ

end HartreeF.TimeHolder
