import FVectorBudgetSmallness
import FActualVectorDifferenceBound
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- The genuine full forcing-gradient difference is controlled linearly by the
common bound on the actual function and vector-gradient differences. The C35
slice and joint-measurability hypotheses remain explicit. The constant is chosen
before the time space, measure, fields and delta. No PDE existence is asserted. -/
theorem actual_full_gradient_difference_smallness {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu] (delta : ℝ≥0∞)
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
    (_ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (mu.prod volume))
    (_ : mixedNorm mu volume ∞ 6 (fun t => u t - v t) ≤ delta)
    (_ : mixedNorm mu volume 10 10 (fun t => u t - v t) ≤ delta)
    (_ : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => U t - P t) +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => V t - Q t) ≤ delta),
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≤
      (C : ℝ≥0∞) * vectorSmallnessCoefficient alpha mu u v P Q * delta := by
  obtain ⟨C, hC⟩ := actual_full_gradient_vector_difference_bound hH
  refine ⟨C, ?_⟩
  intro T _ mu _ delta u v U V P Q hSlices hu hv hU hV hP hQ hD hE hZ
  have hb := vectorDifferenceBudget_le_delta hH.order_pos hH.order_lt_three
    mu u v U V P Q delta hD hE hZ
  have hfinal := (hC mu u v U V P Q hSlices hu hv hU hV hP hQ).trans
    (mul_le_mul' le_rfl hb)
  simpa only [mul_assoc] using hfinal

end HartreeF.TimeHolder
