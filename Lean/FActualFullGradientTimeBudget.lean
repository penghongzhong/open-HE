import FActualFullGradientControl
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- One constant, chosen before the time measure, fields and coordinates,
controls the actual Euclidean full-gradient difference by literal budgets. -/
theorem actual_full_gradient_mixed_difference_budget {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (_ : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (_ : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (_ : ∀ i : Fin 3, AEStronglyMeasurable (fun z : T × Space => directionalField (U z.1) (V z.1) (EuclideanSpace.basisFun (Fin 3) ℝ i) z.2)
        (mu.prod volume))
    (_ : ∀ i : Fin 3, AEStronglyMeasurable (fun z : T × Space => directionalField (P z.1) (Q z.1) (EuclideanSpace.basisFun (Fin 3) ℝ i) z.2)
        (mu.prod volume)),
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≤
      (C : ℝ≥0∞) * fullGradientBudget alpha mu u v U V P Q := by
  obtain ⟨C, hC⟩ := actual_directional_mixed_difference_reduced hH
  refine ⟨C, ?_⟩
  intro T _ mu _ u v U V P Q hSlices hu hv hG hK
  have h0 := hC mu u v U V P Q (EuclideanSpace.basisFun (Fin 3) ℝ 0)
    hSlices hu hv (hG 0) (hK 0)
  have h1 := hC mu u v U V P Q (EuclideanSpace.basisFun (Fin 3) ℝ 1)
    hSlices hu hv (hG 1) (hK 1)
  have h2 := hC mu u v U V P Q (EuclideanSpace.basisFun (Fin 3) ℝ 2)
    hSlices hu hv (hG 2) (hK 2)
  have hsum := (actual_full_gradient_norm_control hH mu u v U V P Q
    hSlices hu hv hG hK).2.trans (add_le_add (add_le_add h0 h1) h2)
  simpa only [fullGradientBudget, coordinateGradientBudget, mul_add] using hsum

end HartreeF.TimeHolder
