import FActualFullGradientTimeBudget
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- A finite full budget yields L2-time membership of the actual spatial
L6/5 norm. Infinity is retained throughout the estimate. -/
theorem actual_full_gradient_difference_time_memLp {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (hSlices : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (hG : ∀ i : Fin 3, AEStronglyMeasurable (fun z : T × Space => directionalField (U z.1) (V z.1) (EuclideanSpace.basisFun (Fin 3) ℝ i) z.2)
        (mu.prod volume))
    (hK : ∀ i : Fin 3, AEStronglyMeasurable (fun z : T × Space => directionalField (P z.1) (Q z.1) (EuclideanSpace.basisFun (Fin 3) ℝ i) z.2)
        (mu.prod volume))

    (hBudget : fullGradientBudget alpha mu u v U V P Q ≠ ∞) :
    MemLp (fun t => eLpNorm (actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t))
      (ENNReal.ofReal (6/5 : ℝ)) volume) 2 mu := by
  obtain ⟨C, hC⟩ := actual_full_gradient_mixed_difference_budget hH
  exact mixed_norm_memLp_of_finite_bound mu volume (ENNReal.ofReal (6/5 : ℝ))
    (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ((C : ℝ≥0∞) * fullGradientBudget alpha mu u v U V P Q)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hBudget)
    (hC mu u v U V P Q hSlices hu hv hG hK)

end HartreeF.TimeHolder
