import FJointDirectionalCandidate
import FTimeSliceMeasurability
import CandidateWeakGradientConsumer
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain WeakHartreeChain WeakHartreeProduct
open DerivativeMajorization DerivativeMajorizationReview SobolevStretch GradientMajorants
open scoped ENNReal NNReal

/-- Only the scalar slice norm is transferred from the measurable candidate.
No converse Fubini assertion for an unmeasurable actual field is used. -/
theorem actual_directional_difference_norm_measurable {alpha c : ℝ}
    (hH : OrdinaryHLS alpha c) {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu]
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space) (e : Space)
    (hSlices : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
      MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
      MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (hG : AEStronglyMeasurable (fun z : T × Space =>
      directionalField (U z.1) (V z.1) e z.2) (mu.prod volume))
    (hK : AEStronglyMeasurable (fun z : T × Space =>
      directionalField (P z.1) (Q z.1) e z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun t => eLpNorm
      (actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
       actualDirectionalDerivative alpha c (v t) (P t) (Q t) e)
      (ENNReal.ofReal (6/5 : ℝ)) volume) mu := by
  have hCandidate := (joint_directional_candidate_measurable mu alpha c u
    (fun t => directionalField (U t) (V t) e) hu hG).sub
    (joint_directional_candidate_measurable mu alpha c v
      (fun t => directionalField (P t) (Q t) e) hv hK)
  have hm := spatial_lp_time_measurable mu volume (ENNReal.ofReal (6/5 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top
    (fun t => directionalCandidate alpha c (u t) (directionalField (U t) (V t) e) -
      directionalCandidate alpha c (v t) (directionalField (P t) (Q t) e)) hCandidate
  apply hm.congr
  filter_upwards [hSlices] with t ht
  rcases ht with ⟨hu1, hv1, hu10, hv10, hU, hV, hP, hQ⟩
  have heq := (actual_directional_candidate_ae hH hu1.function_L6 hu10 hU hV e).sub
    (actual_directional_candidate_ae hH hv1.function_L6 hv10 hP hQ e)
  exact (eLpNorm_congr_ae heq).symm

end HartreeF.TimeHolder
