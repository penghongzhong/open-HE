import FJointLpRealization
import FActualGradientTimeLocalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

local instance gradientSourceExponent_one_le : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) :=
  ⟨by norm_num⟩
local instance gradientSourceExponent_ne_top : Fact (ENNReal.ofReal (6/5 : ℝ) ≠ ∞) :=
  ⟨ENNReal.ofReal_ne_top⟩

/-- A joint-measurable representative assembled from the three genuine Hartree candidates. -/
def candidateFullGradient (alpha c : ℝ) (u : Space → ℂ) (U V : Space → Space)
    (x : Space) : EuclideanSpace ℂ (Fin 3) :=
  packGradient
    (directionalCandidate alpha c u (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ 0)) x)
    (directionalCandidate alpha c u (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ 1)) x)
    (directionalCandidate alpha c u (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ 2)) x)

/-- Joint measurability is produced from u and its real and imaginary gradient fields. -/
theorem candidateFullGradient_joint_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (alpha c : ℝ)
    (u : T → Space → ℂ) (U V : T → Space → Space)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun z : T × Space =>
      candidateFullGradient alpha c (u z.1) (U z.1) (V z.1) z.2) (mu.prod volume) := by
  have hd (i : Fin 3) := joint_directional_candidate_measurable mu alpha c u
    (fun t => directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i)) hu
    (directional_field_joint_measurable mu U V (EuclideanSpace.basisFun (Fin 3) ℝ i) hU hV)
  exact (((hd 0).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 0)).add
    ((hd 1).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 1))).add
    ((hd 2).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 2))

/-- The literal actual weak gradient agrees with the candidate on each admissible slice. -/
theorem actualFullGradient_candidate_ae {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : Space → ℂ) (U V : Space → Space) (hu1 : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    actualFullGradient alpha c u U V =ᵐ[volume] candidateFullGradient alpha c u U V := by
  have hd (i : Fin 3) := actual_directional_candidate_ae hH hu1.function_L6 hu10 hU hV
    (EuclideanSpace.basisFun (Fin 3) ℝ i)
  filter_upwards [hd 0, hd 1, hd 2] with x h0 h1 h2
  simp only [actualFullGradient, candidateFullGradient, h0, h1, h2]

/-- The actual full-gradient difference has a genuine iterated Bochner realization.
The only forcing norm hypothesis is extended mixed-norm finiteness. Joint
measurability of the actual weak gradient is never a hypothesis or inferred
from nested AE equality. -/
theorem exists_actual_full_gradient_bochnerSource {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
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
    (hfin : mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≠ ∞) :
    ∃ G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 mu,
      (∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space), G t x =
        actualFullGradient alpha c (u t) (U t) (V t) x -
          actualFullGradient alpha c (v t) (P t) (Q t) x) ∧
      ‖G‖ₑ = mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
          actualFullGradient alpha c (v t) (P t) (Q t)) := by
  let F : T × Space → EuclideanSpace ℂ (Fin 3) := fun z =>
    candidateFullGradient alpha c (u z.1) (U z.1) (V z.1) z.2 -
      candidateFullGradient alpha c (v z.1) (P z.1) (Q z.1) z.2
  have hF : AEStronglyMeasurable F (mu.prod volume) :=
    (candidateFullGradient_joint_measurable mu alpha c u U V hu hU hV).sub
      (candidateFullGradient_joint_measurable mu alpha c v P Q hv hP hQ)
  have heq : ∀ᵐ t ∂mu, (fun x => F (t, x)) =ᵐ[volume]
      (actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) := by
    filter_upwards [hSlices] with t ht
    rcases ht with ⟨hu1, hv1, hu10, hv10, hUt, hVt, hPt, hQt⟩
    exact ((actualFullGradient_candidate_ae hH (u t) (U t) (V t) hu1 hu10 hUt hVt).sub
      (actualFullGradient_candidate_ae hH (v t) (P t) (Q t) hv1 hv10 hPt hQt)).symm
  have hnorm : mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ)) (fun t x => F (t, x)) =
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
          actualFullGradient alpha c (v t) (P t) (Q t)) := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with t ht
    exact eLpNorm_congr_ae ht
  have hFfin : mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => F (t, x)) ≠ ∞ := by rwa [hnorm]
  have hFslice := finite_mixedNorm_ae_slice_memLp mu volume 2
    (ENNReal.ofReal (6/5 : ℝ)) (by norm_num) (by norm_num) (fun t x => F (t, x)) hFfin
  refine ⟨jointLpRealization mu volume 2 (ENNReal.ofReal (6/5 : ℝ)) F hF hFslice hFfin, ?_, ?_⟩
  · filter_upwards [jointLpRealization_coeFn mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      F hF hFslice hFfin, heq] with t ht hteq
    exact Filter.EventuallyEq.trans ht hteq
  · exact (jointLpRealization_enorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      F hF hFslice hFfin).trans hnorm

/-- An iterated Bochner element is uniquely determined by its nested AE representative. -/
theorem gradient_bochnerSource_unique {T : Type*} [MeasurableSpace T]
    (mu : Measure T)
    (G H : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 mu)
    (f : T → Space → EuclideanSpace ℂ (Fin 3))
    (hG : ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space), G t x = f t x)
    (hH : ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space), H t x = f t x) : G = H := by
  apply Lp.ext
  filter_upwards [hG, hH] with t htG htH
  exact Lp.ext (Filter.EventuallyEq.trans htG (Filter.EventuallyEq.symm htH))

end HartreeF.TimeHolder
