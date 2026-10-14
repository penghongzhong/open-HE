import FActualMixedMembership
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal

/-- Real slice norms are legitimate only after actual a.e. spatial finiteness
has been derived; infinity is never silently sent to zero. -/
theorem actual_directional_difference_real_time_memLp {alpha c : ℝ}
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
    MemLp (fun t => (eLpNorm (actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) e)
      (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) 2 mu := by
  have hm := actual_directional_difference_time_memLp hH mu u v U V P Q e
    hSlices hu hv hG hK hInputs
  obtain ⟨C, hC⟩ := actual_directional_critical_difference hH
  have hFin : ∀ᵐ t ∂mu, eLpNorm (actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) e)
      (ENNReal.ofReal (6/5 : ℝ)) volume ≠ ∞ := by
    filter_upwards [hSlices] with t ht
    rcases ht with ⟨hu1, hv1, hu10, hv10, hU, hV, hP, hQ⟩
    exact (hC (u t) (v t) (U t) (V t) (P t) (Q t)
      hu1 hv1 hu10 hv10 hU hV hP hQ e).1.eLpNorm_ne_top
  change eLpNorm (fun t => (eLpNorm (actualDirectionalDerivative alpha c (u t) (U t) (V t) e -
        actualDirectionalDerivative alpha c (v t) (P t) (Q t) e)
    (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) 2 mu < ∞
  rw [← finite_extended_norm_bridge mu 2 _ hm.aestronglyMeasurable hFin]
  exact hm

end HartreeF.TimeHolder
