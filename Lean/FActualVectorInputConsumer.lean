import FVectorTimeInputs
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- The full-gradient conclusion consumes original vector mixed norms;
no per-coordinate time finiteness or directional measurability is assumed. -/
theorem actual_full_gradient_from_vector_inputs {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
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
    (hInputs : VectorTimeInputs mu u v U V P Q) :
    fullGradientBudget alpha mu u v U V P Q ≠ ∞ ∧
    MemLp (fun t => eLpNorm (actualFullGradient alpha c (u t) (U t) (V t) -
      actualFullGradient alpha c (v t) (P t) (Q t)) (ENNReal.ofReal (6/5 : ℝ)) volume) 2 mu := by
  have hi : ∀ i : Fin 3, FiniteTimeInputs mu
      (fun t => sumAmplitude (u t) (v t)) (fun t => differenceAmplitude (u t) (v t))
      (fun t x => ‖directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x‖)
      (fun t x => ‖directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x -
        directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i) x‖) := by
    intro i
    exact vector_time_inputs_directional mu u v U V P Q hSlices hu hv hU hV hP hQ hInputs
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (OrthonormalBasis.norm_eq_one _ i)
  have hb := fullGradientBudget_ne_top hH.order_pos hH.order_lt_three mu u v U V P Q hi
  refine ⟨hb, actual_full_gradient_difference_time_memLp hH mu u v U V P Q hSlices hu hv ?_ ?_ hb⟩
  · intro i
    exact directional_field_joint_measurable mu U V (EuclideanSpace.basisFun (Fin 3) ℝ i) hU hV
  · intro i
    exact directional_field_joint_measurable mu P Q (EuclideanSpace.basisFun (Fin 3) ℝ i) hP hQ

end HartreeF.TimeHolder
