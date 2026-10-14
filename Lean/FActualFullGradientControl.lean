import FFullGradientBudget
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- Measurability of the scalar slice norm and its coordinate mixed bound.
No finite time-input or actual joint-measurability premise is used. -/
theorem actual_full_gradient_norm_control {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
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
 :
    AEStronglyMeasurable (fun t => eLpNorm (actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t))
      (ENNReal.ofReal (6/5 : ℝ)) volume) mu ∧
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≤
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualDirectionalDerivative alpha c (u t) (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ 0) -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ 0)) +
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualDirectionalDerivative alpha c (u t) (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ 1) -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ 1)) +
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualDirectionalDerivative alpha c (u t) (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ 2) -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ 2)) := by
  let F : Fin 3 → T → Space → ℂ := fun i t =>
    actualDirectionalDerivative alpha c (u t) (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i) -
    actualDirectionalDerivative alpha c (v t) (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i)
  let G : Fin 3 → T → Space → ℂ := fun i t =>
    directionalCandidate alpha c (u t) (directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i)) -
    directionalCandidate alpha c (v t) (directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hg : ∀ i, AEStronglyMeasurable (fun z : T × Space => G i z.1 z.2) (mu.prod volume) := by
    intro i
    dsimp only [G, Pi.sub_apply]
    exact (joint_directional_candidate_measurable mu alpha c u
      (fun t => directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ i)) hu (hG i)).sub
      (joint_directional_candidate_measurable mu alpha c v
        (fun t => directionalField (P t) (Q t) (EuclideanSpace.basisFun (Fin 3) ℝ i)) hv (hK i))
  have heq : ∀ i, ∀ᵐ t ∂mu, F i t =ᵐ[volume] G i t := by
    intro i
    filter_upwards [hSlices] with t ht
    rcases ht with ⟨hu1, hv1, hu10, hv10, hU, hV, hP, hQ⟩
    dsimp only [F, G]
    exact (actual_directional_candidate_ae hH hu1.function_L6 hu10 hU hV
      (EuclideanSpace.basisFun (Fin 3) ℝ i)).sub
      (actual_directional_candidate_ae hH hv1.function_L6 hv10 hP hQ
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hm := pack_slice_norm_measurable mu F G hg heq
  have hp := pack_mixed_norm_le mu F G hg heq
  have hid : (fun t x => packGradient (F 0 t x) (F 1 t x) (F 2 t x)) =
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) := by
    funext t x
    dsimp only [F, actualFullGradient, Pi.sub_apply]
    exact packGradient_sub _ _ _ _ _ _
  rw [hid] at hp
  refine ⟨?_, hp⟩
  exact (congrArg
    (fun f : T → Space → EuclideanSpace ℂ (Fin 3) =>
      AEStronglyMeasurable (fun t => eLpNorm (f t) (ENNReal.ofReal (6/5 : ℝ)) volume) mu)
    hid).mp hm

end HartreeF.TimeHolder
