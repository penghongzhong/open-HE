import FActualFiniteMixedDifference
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal

theorem actual_directional_difference_time_memLp {alpha c : ℝ}
    (hH : OrdinaryHLS alpha c)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space) (e : Space)
    (hSlices : ∀ᵐ t ∂mu, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume))
    (hG : AEStronglyMeasurable (fun z : T × Space => directionalField (U z.1) (V z.1) e z.2)
        (mu.prod volume))
    (hK : AEStronglyMeasurable (fun z : T × Space => directionalField (P z.1) (Q z.1) e z.2)
        (mu.prod volume))
    (hInputs : FiniteTimeInputs mu
        (fun t => sumAmplitude (u t) (v t))
        (fun t => differenceAmplitude (u t) (v t))
        (fun t x => ‖directionalField (P t) (Q t) e x‖)
        (fun t x => ‖directionalField (U t) (V t) e x - directionalField (P t) (Q t) e x‖)) :
    MemLp (fun t => eLpNorm (actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) e)
      (ENNReal.ofReal (6/5 : ℝ)) volume) 2 mu := by
  obtain ⟨C, hC⟩ := actual_directional_finite_mixed_difference hH
  have hFin := (hC mu u v U V P Q e hSlices hu hv hG hK hInputs).2
  exact lt_top_iff_ne_top.mpr hFin

end HartreeF.TimeHolder
