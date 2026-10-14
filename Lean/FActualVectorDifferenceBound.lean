import FVectorDifferenceBudget
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

theorem full_gradient_budget_le_vector {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
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
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hP : AEStronglyMeasurable (fun z : T × Space => P z.1 z.2) (mu.prod volume))
    (hQ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (mu.prod volume))
 :
    fullGradientBudget alpha mu u v U V P Q ≤
      vectorDifferenceBudget alpha mu u v U V P Q + vectorDifferenceBudget alpha mu u v U V P Q +
      vectorDifferenceBudget alpha mu u v U V P Q := by
  have h : ∀ i : Fin 3, coordinateGradientBudget alpha mu u v U V P Q i ≤
      vectorDifferenceBudget alpha mu u v U V P Q := by
    intro i
    exact directional_budget_le_vector ha ha3 mu u v U V P Q hSlices hu hv hU hV hP hQ
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (OrthonormalBasis.norm_eq_one _ i)
  exact add_le_add (add_le_add (h 0) (h 1)) (h 2)

/-- One uniform constant controls the actual full gradient by a budget
retaining u-v, U-P and V-Q. All spatial and input measurability premises remain. -/
theorem actual_full_gradient_vector_difference_bound {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
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
    (_ : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => P z.1 z.2) (mu.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (mu.prod volume)),
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≤
      (C : ℝ≥0∞) * vectorDifferenceBudget alpha mu u v U V P Q := by
  obtain ⟨C, hC⟩ := actual_full_gradient_mixed_difference_budget hH
  refine ⟨C + C + C, ?_⟩
  intro T _ mu _ u v U V P Q hSlices hu hv hU hV hP hQ
  have hG : ∀ i : Fin 3, AEStronglyMeasurable (fun z : T × Space =>
      directionalField (U z.1) (V z.1) (EuclideanSpace.basisFun (Fin 3) ℝ i) z.2) (mu.prod volume) :=
    fun i => directional_field_joint_measurable mu U V (EuclideanSpace.basisFun (Fin 3) ℝ i) hU hV
  have hK : ∀ i : Fin 3, AEStronglyMeasurable (fun z : T × Space =>
      directionalField (P z.1) (Q z.1) (EuclideanSpace.basisFun (Fin 3) ℝ i) z.2) (mu.prod volume) :=
    fun i => directional_field_joint_measurable mu P Q (EuclideanSpace.basisFun (Fin 3) ℝ i) hP hQ
  have hb := full_gradient_budget_le_vector hH.order_pos hH.order_lt_three mu u v U V P Q
    hSlices hu hv hU hV hP hQ
  have hfinal := (hC mu u v U V P Q hSlices hu hv hG hK).trans (mul_le_mul' le_rfl hb)
  simpa only [ENNReal.coe_add, mul_add, add_mul] using hfinal

end HartreeF.TimeHolder
