import StationaryWeakEquation

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.StationarySelfTest
open SobolevStretch ForcingDomain WeakCutoffLp

theorem weakGradient_sub {u v : Space → ℝ} {U V : Space → Space}
    (hu : HasWeakGradient u U) (hv : HasWeakGradient v V) :
    HasWeakGradient (fun x => u x - v x) (fun x => U x - V x) := by
  refine ⟨hu.function_local.sub hv.function_local, hu.gradient_local.sub hv.gradient_local, ?_⟩
  intro w φ hφ hc
  have hiu := hu.test_integrable hφ hc w
  have hiv := hv.test_integrable hφ hc w
  simp only [sub_mul, inner_sub_left, integral_sub hiu.1 hiv.1,
    integral_sub hiu.2 hiv.2, hu.integration_by_parts w φ hφ hc,
    hv.integration_by_parts w φ hφ hc]
  ring

theorem smooth_hasWeakGradient {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : HasWeakGradient φ (gradient φ) := by
  apply hasWeakGradient_of_differentiable (hφ.differentiable (by simp))
    (smooth_gradient_continuous hφ)
  intro x v
  exact inner_gradient_left.symm

theorem real_inDotH1 {v : Space → ℝ} {V : Space → Space}
    (hv : MemLp v 6 volume) (hV : MemLp V 2 volume) (hw : HasWeakGradient v V) :
    InDotH1 (fun x => (v x : ℂ)) V (fun _ => 0) := by
  refine ⟨hv.continuousLinearMap_comp Complex.ofRealCLM, hV, MemLp.zero', ?_, ?_⟩
  · simpa using hw
  · simpa using hasWeakGradient_zero

theorem real_sobolev_integral_bound {K : ℝ} (hSob : OrdinarySobolev K)
    {v : Space → ℝ} {V : Space → Space}
    (hv : MemLp v 6 volume) (hV : MemLp V 2 volume) (hw : HasWeakGradient v V) :
    (∫ x, ‖v x‖ ^ 6) ≤ K * (∫ x, ‖V x‖ ^ 2) ^ 3 := by
  have h := hSob.bound (real_inDotH1 hv hV hw)
  simpa only [Complex.norm_real, kinetic_eq_sum hV MemLp.zero',
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
    add_zero] using h

/-- Exact finite real norm moment, avoiding convergence of totalized infinite norms. -/
theorem norm_moment_eq_eLpNorm {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} {n : ℕ} (hn : n ≠ 0) (hf : MemLp f (n : ℝ≥0∞) volume) :
    (∫ x, ‖f x‖ ^ n) = (eLpNorm f (n : ℝ≥0∞) volume).toReal ^ n := by
  have hnn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ n := integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by simpa using hn) (by simp) hf]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
    ← Real.rpow_natCast, ← Real.rpow_mul hnonneg, inv_mul_cancel₀ hnn.ne', Real.rpow_one]

/-- The ordinary Sobolev inequality promotes actual L2 gradient convergence
of real weakly differentiable L6 functions to their actual L6 convergence. -/
theorem sobolev_eLpNorm_tendsto_zero {K : ℝ} (hSob : OrdinarySobolev K)
    {v : ℕ → Space → ℝ} {V : ℕ → Space → Space}
    (hv : ∀ n, MemLp (v n) 6 volume) (hV : ∀ n, MemLp (V n) 2 volume)
    (hw : ∀ n, HasWeakGradient (v n) (V n))
    (ht : Tendsto (fun n => eLpNorm (V n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (v n) 6 volume) atTop (𝓝 0) := by
  have htReal : Tendsto (fun n => (eLpNorm (V n) 2 volume).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp ht
  have htMoment : Tendsto (fun n => ∫ x, ‖V n x‖ ^ 2) atTop (𝓝 0) := by
    convert htReal.pow 2 using 1 <;> norm_num [norm_moment_eq_eLpNorm (by decide : (2 : ℕ) ≠ 0) (hV _)]
  have htBound : Tendsto (fun n => K * (∫ x, ‖V n x‖ ^ 2) ^ 3) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (htMoment.pow 3)
  have htSixth : Tendsto (fun n => ∫ x, ‖v n x‖ ^ 6) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _))
      (fun n => real_sobolev_integral_bound hSob (hv n) (hV n) (hw n)) htBound
  have htRoot : Tendsto (fun n => (∫ x, ‖v n x‖ ^ 6) ^ (6 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow (by norm_num : (6 : ℝ)⁻¹ ≠ 0)] using (Real.continuousAt_rpow_const (0 : ℝ) ((6 : ℝ)⁻¹)
      (Or.inr (by norm_num))).tendsto.comp htSixth
  have := ENNReal.continuous_ofReal.continuousAt.tendsto.comp htRoot
  convert this using 1
  · funext n
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (6 : ℝ≥0∞) ≠ 0)
      (by norm_num : (6 : ℝ≥0∞) ≠ ∞) (hv n)]
    norm_num [Function.comp_def]
  · simp


#print axioms weakGradient_sub
#print axioms smooth_hasWeakGradient
#print axioms real_inDotH1
#print axioms real_sobolev_integral_bound
#print axioms norm_moment_eq_eLpNorm
#print axioms sobolev_eLpNorm_tendsto_zero
end HartreeF.StationarySelfTest
