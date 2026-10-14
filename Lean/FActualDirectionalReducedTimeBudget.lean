import FTimeThreeWeightBudget
import FActualDirectionalSliceNorm

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal

/-- The C29 budget with no separate joint measurability premise for the
actual forcing derivative. Its scalar slice norm measurability is derived. -/
theorem actual_directional_mixed_difference_reduced {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
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
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
          actualDirectionalDerivative alpha c (v t) (P t) (Q t) e) ≤
      (C : ℝ≥0∞) * threeWeightBudget alpha mu
        (fun t => sumAmplitude (u t) (v t))
        (fun t => differenceAmplitude (u t) (v t))
        (fun t x => ‖directionalField (P t) (Q t) e x‖)
        (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) := by
  obtain ⟨C, hC⟩ := actual_directional_critical_difference hH
  refine ⟨C, ?_⟩
  intro T _ mu _ u v U V P Q e hSlices huJoint hvJoint hGJoint hKJoint
  let F : T → Space → ℂ := fun t =>
    actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
    actualDirectionalDerivative alpha c (v t) (P t) (Q t) e
  let a : T → ℝ≥0∞ := fun t => eLpNorm (F t) (ENNReal.ofReal (6/5 : ℝ)) volume
  have hMeas : AEStronglyMeasurable a mu :=
    actual_directional_difference_norm_measurable hH mu u v U V P Q e
      hSlices huJoint hvJoint hGJoint hKJoint
  have hFin : ∀ᵐ t ∂mu, a t ≠ ∞ := by
    filter_upwards [hSlices] with t ht
    rcases ht with ⟨hu, hv, hu10, hv10, hU, hV, hP, hQ⟩
    exact (hC (u t) (v t) (U t) (V t) (P t) (Q t)
      hu hv hu10 hv10 hU hV hP hQ e).1.eLpNorm_ne_top
  have hb : ∀ᵐ t ∂mu, (a t).toReal ≤ (C : ℝ) *
      (singleWeight alpha (sumAmplitude (u t) (v t))
        (fun x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖) +
       spacetimeDifferenceWeight alpha (sumAmplitude (u t) (v t)) (differenceAmplitude (u t) (v t))
        (fun x => ‖directionalField (P t) (Q t) e x‖) +
       mixedDifferenceWeight alpha (sumAmplitude (u t) (v t)) (differenceAmplitude (u t) (v t))
        (fun x => ‖directionalField (P t) (Q t) e x‖)) := by
    filter_upwards [hSlices] with t ht
    rcases ht with ⟨hu, hv, hu10, hv10, hU, hV, hP, hQ⟩
    exact (hC (u t) (v t) (U t) (V t) (P t) (Q t)
      hu hv hu10 hv10 hU hV hP hQ e).2
  exact finite_dominated_three_weights hH.order_pos hH.order_lt_three mu C a
    (fun t => sumAmplitude (u t) (v t)) (fun t => differenceAmplitude (u t) (v t))
    (fun t x => ‖directionalField (P t) (Q t) e x‖)
    (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖)
    hMeas hFin (huJoint.norm.add hvJoint.norm) (huJoint.sub hvJoint).norm
    hKJoint.norm (hGJoint.sub hKJoint).norm hb

end HartreeF.TimeHolder
