import FActualFullGradientMixed
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- The literal C29 three-weight budget in one real coordinate direction. -/
def coordinateGradientBudget {T : Type*} [MeasurableSpace T] (alpha : ℝ)
    (mu : Measure T) (u v : T → Space → ℂ) (U V P Q : T → Space → Space) (i : Fin 3) : ℝ≥0∞ :=
  threeWeightBudget alpha mu
    (fun t => sumAmplitude (u t) (v t))
    (fun t => differenceAmplitude (u t) (v t))
    (fun t x => ‖directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x‖)
    (fun t x => ‖directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x -
      directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x‖)

/-- Three coordinate budgets, without an interval-length factor. -/
def fullGradientBudget {T : Type*} [MeasurableSpace T] (alpha : ℝ)
    (mu : Measure T) (u v : T → Space → ℂ) (U V P Q : T → Space → Space) : ℝ≥0∞ :=
  coordinateGradientBudget alpha mu u v U V P Q 0 +
    coordinateGradientBudget alpha mu u v U V P Q 1 +
    coordinateGradientBudget alpha mu u v U V P Q 2

theorem fullGradientBudget_ne_top {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (hInputs : ∀ i : Fin 3, FiniteTimeInputs mu
        (fun t => sumAmplitude (u t) (v t))
        (fun t => differenceAmplitude (u t) (v t))
        (fun t x => ‖directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x‖)
        (fun t x => ‖directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x - directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x‖)) :
    fullGradientBudget alpha mu u v U V P Q ≠ ∞ := by
  have h : ∀ i : Fin 3, coordinateGradientBudget alpha mu u v U V P Q i ≠ ∞ := by
    intro i
    exact finite_time_inputs_budget ha ha3 mu _ _ _ _ (hInputs i)
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h 0, h 1⟩, h 2⟩

end HartreeF.TimeHolder
