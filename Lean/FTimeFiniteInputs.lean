import FMixedNormMembership
import FActualDirectionalReducedTimeBudget
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal

/-- Six literal C26 amplitude time norms, with infinity retained. Spatial
membership is supplied separately by the actual directional consumer. -/
def FiniteTimeInputs {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (V W Y Z : T → Space → ℝ) : Prop :=
  eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ≠ ∞ ∧
  eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ≠ ∞ ∧
  eLpNorm (fun t => spatialNorm 6 (W t)) ∞ mu ≠ ∞ ∧
  eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu ≠ ∞ ∧
  eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu ≠ ∞ ∧
  eLpNorm (fun t => spatialNorm (30/13) (Z t)) 10 mu ≠ ∞

theorem finite_time_inputs_budget {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) (V W Y Z : T → Space → ℝ)
    (h : FiniteTimeInputs mu V W Y Z) : threeWeightBudget alpha mu V W Y Z ≠ ∞ := by
  rcases h with ⟨hM, hN, hD, hE, hY, hZ⟩
  exact threeWeightBudget_ne_top ha ha3 mu V W Y Z hM hN hD hE hY hZ

end HartreeF.TimeHolder
