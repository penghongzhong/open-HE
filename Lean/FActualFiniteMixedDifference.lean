import FTimeFiniteInputs
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal

/-- A uniform actual bound and finiteness from the six explicit input norms.
The constant is selected before the time measure, fields, and direction. -/
theorem actual_directional_finite_mixed_difference {alpha c : ℝ}
    (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
      (u v : T → Space → ℂ) (U V P Q : T → Space → Space) (e : Space),
      (∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume) →
      AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume) →
      AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume) →
      AEStronglyMeasurable (fun z : T × Space => directionalField (U z.1) (V z.1) e z.2)
        (mu.prod volume) →
      AEStronglyMeasurable (fun z : T × Space => directionalField (P z.1) (Q z.1) e z.2)
        (mu.prod volume) →
      FiniteTimeInputs mu
        (fun t => sumAmplitude (u t) (v t))
        (fun t => differenceAmplitude (u t) (v t))
        (fun t x => ‖directionalField (P t) (Q t) e x‖)
        (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) →
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
          actualDirectionalDerivative alpha c (v t) (P t) (Q t) e) ≤
      (C : ℝ≥0∞) * threeWeightBudget alpha mu
        (fun t => sumAmplitude (u t) (v t))
        (fun t => differenceAmplitude (u t) (v t))
        (fun t x => ‖directionalField (P t) (Q t) e x‖)
        (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) ∧
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
          actualDirectionalDerivative alpha c (v t) (P t) (Q t) e) ≠ ∞ := by
  obtain ⟨C, hC⟩ := actual_directional_mixed_difference_reduced hH
  refine ⟨C, ?_⟩
  intro T _ mu _ u v U V P Q e hSlices hu hv hG hK hInputs
  have hb := hC mu u v U V P Q e hSlices hu hv hG hK
  have hBudget := finite_time_inputs_budget hH.order_pos hH.order_lt_three mu
    (fun t => sumAmplitude (u t) (v t)) (fun t => differenceAmplitude (u t) (v t))
    (fun t x => ‖directionalField (P t) (Q t) e x‖)
    (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) hInputs
  have hRight : (C : ℝ≥0∞) * threeWeightBudget alpha mu
    (fun t => sumAmplitude (u t) (v t)) (fun t => differenceAmplitude (u t) (v t))
    (fun t x => ‖directionalField (P t) (Q t) e x‖)
    (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) ≠ ∞ := by finiteness
  exact ⟨hb, ne_top_of_le_ne_top hRight hb⟩

end HartreeF.TimeHolder
