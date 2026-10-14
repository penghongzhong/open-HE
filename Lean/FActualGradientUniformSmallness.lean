import FBackgroundCoefficientSmallness
import FActualGradientSmallness
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- At each finite background cap, one positive threshold gives any prescribed
coefficient in the actual full-gradient difference estimate. The threshold is
chosen before the time space, measure and fields. The norm caps and C35 slice
and joint-measurability premises are explicit; no short interval or solution
is constructed by this theorem. -/
theorem actual_full_gradient_uniform_smallness {alpha c B epsilon : ℝ}
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀
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
    (_ : mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v ≤ ENNReal.ofReal B)
    (_ : mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v ≤ ENNReal.ofReal eta)
    (_ : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q ≤ ENNReal.ofReal eta)
    (_ : mixedNorm mu volume ∞ 6 (fun t => u t - v t) ≤ delta)
    (_ : mixedNorm mu volume 10 10 (fun t => u t - v t) ≤ delta)
    (_ : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => U t - P t) +
      mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t => V t - Q t) ≤ delta),
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≤
      ENNReal.ofReal epsilon * delta := by
  obtain ⟨C, hC⟩ := actual_full_gradient_difference_smallness hH
  have hC0 : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hden : 0 < (C : ℝ) + 1 := by linarith
  have he : 0 < epsilon / ((C : ℝ) + 1) := div_pos hepsilon hden
  obtain ⟨eta, heta0, heta1, hsmall⟩ := exists_vectorSmallnessCoefficient_le
    hH.order_pos hH.order_lt_three hB he
  refine ⟨eta, heta0, heta1, ?_⟩
  intro T _ mu _ delta u v U V P Q hSlices hu hv hU hV hP hQ hM hN hY hD hE hZ
  have hcoef := hsmall mu u v P Q hM hN hY
  have hproduct : (C : ℝ) * (epsilon / ((C : ℝ) + 1)) ≤ epsilon := by
    have hmul : epsilon / ((C : ℝ) + 1) * ((C : ℝ) + 1) = epsilon :=
      div_mul_cancel₀ epsilon (ne_of_gt hden)
    nlinarith [he.le]
  have hconstant : (C : ℝ≥0∞) * ENNReal.ofReal (epsilon / ((C : ℝ) + 1)) ≤
      ENNReal.ofReal epsilon := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal hproduct
  exact (hC mu delta u v U V P Q hSlices hu hv hU hV hP hQ hD hE hZ).trans
    (mul_le_mul' ((mul_le_mul' le_rfl hcoef).trans hconstant) le_rfl)

end HartreeF.TimeHolder
