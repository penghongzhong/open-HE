import FTimeThreeWeightBudget

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory GradientMajorants
open scoped ENNReal NNReal

/-- Finite six input time norms make the full three-weight budget finite.
No finiteness is inferred from toReal of an infinite spatial slice. -/
theorem threeWeightBudget_ne_top {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) (V W Y Z : T → Space → ℝ)
    (hM : eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ≠ ∞)
    (hN : eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ≠ ∞)
    (hD : eLpNorm (fun t => spatialNorm 6 (W t)) ∞ mu ≠ ∞)
    (hE : eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu ≠ ∞)
    (hY : eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu ≠ ∞)
    (hZ : eLpNorm (fun t => spatialNorm (30/13) (Z t)) 10 mu ≠ ∞) :
    threeWeightBudget alpha mu V W Y Z ≠ ∞ := by
  have h2 : 0 ≤ 2 * alpha := by positivity
  have h5 : 0 ≤ 5 * alpha / 3 := by positivity
  have hthird : 0 ≤ alpha / 3 := by positivity
  have ht : 0 ≤ theta alpha := by dsimp [theta]; linarith
  have h4t : 0 ≤ 4 - theta alpha := by dsimp [theta]; linarith
  unfold threeWeightBudget
  finiteness

/-- A finite extended mixed bound implies L2 membership of the actual slice
norm map. This is the precise scalar formulation of the mixed norm here. -/
theorem mixed_norm_memLp_of_finite_bound {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞) (f : T → X → E)
    (B : ℝ≥0∞) (hB : B ≠ ∞) (hbound : mixedNorm mu nu 2 q f ≤ B) :
    MemLp (fun t => eLpNorm (f t) q nu) 2 mu := by
  exact hbound.trans_lt (lt_top_iff_ne_top.mpr hB)

end HartreeF.TimeHolder
