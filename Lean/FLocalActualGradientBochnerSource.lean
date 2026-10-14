import FActualGradientBochnerSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

attribute [local instance] gradientSourceExponent_one_le gradientSourceExponent_ne_top

/-- Finite original time inputs produce a positive radius and an actual local
Bochner forcing-gradient difference. Its nested AE representative is the literal
actual gradient difference, and its extended norm is at most epsilon times the
finite delta. No measurability or Bochner-membership premise for the forcing is
assumed. This is a conditional source construction for given fields, not PDE
existence. -/
theorem actual_full_gradient_exists_local_bochnerSource {alpha c B epsilon : ℝ}
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
    ∃ r : ℝ, 0 < r ∧ ∀ delta : ℝ≥0,
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume ∞ 6 (fun t => u t - v t) ≤ delta →
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 10 10 (fun t => u t - v t) ≤ delta →
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t => U t - P t) +
      mixedNorm (mu.restrict (Metric.ball t0 r)) volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t => V t - Q t) ≤ delta →
      ∃ G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
        (volume : Measure Space)) 2 (mu.restrict (Metric.ball t0 r)),
        (∀ᵐ t ∂mu.restrict (Metric.ball t0 r), ∀ᵐ x ∂(volume : Measure Space),
          G t x = actualFullGradient alpha c (u t) (U t) (V t) x -
            actualFullGradient alpha c (v t) (P t) (Q t) x) ∧
        ‖G‖ₑ = mixedNorm (mu.restrict (Metric.ball t0 r)) volume 2 (ENNReal.ofReal (6/5 : ℝ))
          (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
            actualFullGradient alpha c (v t) (P t) (Q t)) ∧
        ‖G‖ₑ ≤ ENNReal.ofReal epsilon * (delta : ℝ≥0∞) := by
  obtain ⟨r, hr, hbound⟩ := actual_full_gradient_exists_time_localization hH hB hepsilon
    mu hmu u v U V P Q hSobolev hUV hu hv hU hV hP hQ huFin hvFin hPFin hQFin hM t0
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
  have hb := hbound (delta : ℝ≥0∞) hD hE hZ
  have hfin := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) hb
  obtain ⟨G, hrep, hnorm⟩ := exists_actual_full_gradient_bochnerSource hH
    (mu.restrict (Metric.ball t0 r)) u v U V P Q hSlices
    (joint_aestronglyMeasurable_time_restrict mu volume u hu _)
    (joint_aestronglyMeasurable_time_restrict mu volume v hv _)
    (joint_aestronglyMeasurable_time_restrict mu volume U hU _)
    (joint_aestronglyMeasurable_time_restrict mu volume V hV _)
    (joint_aestronglyMeasurable_time_restrict mu volume P hP _)
    (joint_aestronglyMeasurable_time_restrict mu volume Q hQ _) hfin
  exact ⟨G, hrep, hnorm, hnorm.trans_le hb⟩

end HartreeF.TimeHolder
