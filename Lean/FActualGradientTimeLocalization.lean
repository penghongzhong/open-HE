import FFourInputLocalization
import FActualGradientUniformSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- C38 consumes the C37 coefficient theorem. Finite actual L10 time inputs
produce a positive time radius; no time-smallness premise is assumed.
The four input spatial membership assertions are derived from their finite
extended mixed norms. The remaining Sobolev, gradient-slice, and joint
measurability assumptions are explicit. This is a conditional forcing
estimate for given fields, not a construction of a PDE solution. -/
theorem actual_full_gradient_exists_time_localization {alpha c B epsilon : ℝ}
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (mu : Measure ℝ) (hmu : mu ≤ volume)
    (u v : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hSobolev : ∀ᵐ t ∂mu,
      InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t))
    (hUV : ∀ᵐ t ∂mu,
      MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (mu.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (mu.prod volume))
    (hU : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) (mu.prod volume))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2) (mu.prod volume))
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) (mu.prod volume))
    (hQ : AEStronglyMeasurable (fun z : ℝ × Space => Q z.1 z.2) (mu.prod volume))
    (huFin : mixedNorm mu volume 10 10 u ≠ ∞)
    (hvFin : mixedNorm mu volume 10 10 v ≠ ∞)
    (hPFin : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) P ≠ ∞)
    (hQFin : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) Q ≠ ∞)
    (hM : mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v ≤ ENNReal.ofReal B)
    (t0 : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ delta : ℝ≥0∞,
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume ∞ 6 (fun t => u t - v t) ≤ delta →
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 10 10 (fun t => u t - v t) ≤ delta →
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t => U t - P t) +
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t => V t - Q t) ≤ delta →
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
          actualFullGradient alpha c (v t) (P t) (Q t)) ≤ ENNReal.ofReal epsilon * delta := by
  obtain ⟨eta, heta, _hetaOne, hsmall⟩ := actual_full_gradient_uniform_smallness hH hB hepsilon
  obtain ⟨r, hr, hN, hY⟩ := finite_four_mixedNorm_exists_small_ball mu hmu volume 10
    (ENNReal.ofReal (30/13 : ℝ)) u v P Q huFin hvFin hPFin hQFin t0 eta heta
  let : SigmaFinite (mu.restrict (Metric.ball t0 r)) :=
    time_restrict_sigmaFinite_of_le_volume mu hmu _
  have hFour := finite_four_mixedNorm_restrict_slice_memLp mu volume 10
    (ENNReal.ofReal (30/13 : ℝ)) u v P Q huFin hvFin hPFin hQFin (Metric.ball t0 r)
  have hS := hSobolev.filter_mono (ae_restrict_le (s := Metric.ball t0 r))
  have hG := hUV.filter_mono (ae_restrict_le (s := Metric.ball t0 r))
  have hSlices : ∀ᵐ t ∂mu.restrict (Metric.ball t0 r),
      InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
      MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
      MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [hS, hG, hFour] with t htS htG htFour
    exact ⟨htS.1, htS.2, htFour.1, htFour.2.1, htG.1, htG.2, htFour.2.2.1, htFour.2.2.2⟩
  refine ⟨r, hr, fun delta hD hE hZ => ?_⟩
  exact hsmall (mu.restrict (Metric.ball t0 r)) delta u v U V P Q hSlices
    (joint_aestronglyMeasurable_time_restrict mu volume u hu _)
    (joint_aestronglyMeasurable_time_restrict mu volume v hv _)
    (joint_aestronglyMeasurable_time_restrict mu volume U hU _)
    (joint_aestronglyMeasurable_time_restrict mu volume V hV _)
    (joint_aestronglyMeasurable_time_restrict mu volume P hP _)
    (joint_aestronglyMeasurable_time_restrict mu volume Q hQ _)
    (mixedNorm_background_pair_restrict_le mu volume 6 u v _ hM _) hN hY hD hE hZ

end HartreeF.TimeHolder
