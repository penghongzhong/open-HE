import FMixedVectorQuantitative
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

theorem directional_field_sub (U V P Q : Space → Space) (e : Space) :
    directionalField U V e - directionalField P Q e = directionalField (U - P) (V - Q) e := by
  funext x
  change Complex.equivRealProdCLM.symm (⟪U x, e⟫, ⟪V x, e⟫) -
    Complex.equivRealProdCLM.symm (⟪P x, e⟫, ⟪Q x, e⟫) =
    Complex.equivRealProdCLM.symm (⟪U x - P x, e⟫, ⟪V x - Q x, e⟫)
  rw [inner_sub_left, inner_sub_left]
  exact (map_sub Complex.equivRealProdCLM.symm (⟪U x, e⟫, ⟪V x, e⟫)
    (⟪P x, e⟫, ⟪Q x, e⟫)).symm

theorem unit_directional_mixed_le {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (U V : T → Space → Space) (e : Space) (he : ‖e‖ = 1)
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume)) :
    mixedNorm mu volume p q (fun t => directionalField (U t) (V t) e) ≤
      mixedNorm mu volume p q U + mixedNorm mu volume p q V := by
  apply mixed_norm_le_add_of_domination mu p q hp hq hqtop
    (fun t => directionalField (U t) (V t) e) U V
    (directional_field_joint_measurable mu U V e hU hV) hU hV
  exact Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x =>
    unit_directional_norm_le (U t) (V t) e he x

/-- The upper bound retains U-P and V-Q, rather than separate field sizes. -/
theorem unit_directional_difference_mixed_le {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (U V P Q : T → Space → Space) (e : Space) (he : ‖e‖ = 1)
    (hU : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hP : AEStronglyMeasurable (fun z : T × Space => P z.1 z.2) (mu.prod volume))
    (hQ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (mu.prod volume)) :
    mixedNorm mu volume p q (fun t => directionalField (U t) (V t) e - directionalField (P t) (Q t) e) ≤
      mixedNorm mu volume p q (fun t => U t - P t) + mixedNorm mu volume p q (fun t => V t - Q t) := by
  have hid : (fun t => directionalField (U t) (V t) e - directionalField (P t) (Q t) e) =
      (fun t => directionalField (U t - P t) (V t - Q t) e) := by
    funext t
    exact directional_field_sub (U t) (V t) (P t) (Q t) e
  rw [hid]
  exact unit_directional_mixed_le mu p q hp hq hqtop
    (fun t => U t - P t) (fun t => V t - Q t) e he (hU.sub hP) (hV.sub hQ)

theorem sum_amplitude_mixed_le {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hqtop : q ≠ ∞) (u v : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume)) :
    mixedNorm mu volume p q (fun t => sumAmplitude (u t) (v t)) ≤
      mixedNorm mu volume p q u + mixedNorm mu volume p q v := by
  apply mixed_norm_le_add_of_domination mu p q hp hq hqtop
    (fun t => sumAmplitude (u t) (v t)) u v (hu.norm.add hv.norm) hu hv
  exact Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => by
    dsimp only [sumAmplitude]
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]

end HartreeF.TimeHolder
