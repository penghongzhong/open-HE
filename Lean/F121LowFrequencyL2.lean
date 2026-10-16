import FHighpassContraction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
namespace HartreeF.Paper121SmallFrequency
open EnergySpace EnergySpace.Highpass

theorem lowSymbol_small_limit (q : Cutoff) {ξ : V} (hξ : ξ ≠ 0) :
    Tendsto (fun M : ℝ => lowSymbol q M ξ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpos : 0 < Real.pi*‖ξ‖ := mul_pos Real.pi_pos (norm_pos_iff.mpr hξ)
  have hsmall : ∀ᶠ M : ℝ in 𝓝[>] (0 : ℝ), M < Real.pi*‖ξ‖ :=
    nhdsWithin_le_nhds (gt_mem_nhds hpos)
  have he : (fun M : ℝ => lowSymbol q M ξ) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with M hM hbound
    exact lowSymbol_zero q hM ξ (by linarith)
  exact tendsto_const_nhds.congr' he.symm

theorem lowL2_norm_sq_fourier (q : Cutoff) (M : ℝ) (f : L2) :
    ‖lowL2 q M f‖^2 = ∫ ξ : V, ‖lowSymbol q M ξ * (𝓕 f) ξ‖^2 := by
  rw [← Lp.norm_fourier_eq (lowL2 q M f), lowL2_fourier, FreeFlow.l2_norm_sq_integral]
  exact integral_congr_ae ((lowMultiply_coe q M (𝓕 f)).fun_comp (fun z : ℂ => ‖z‖^2))

/-- Native dominated convergence for the actual L2 Fourier multiplier.
Only the zero frequency is discarded, using nonatomic Lebesgue measure. -/
theorem lowL2_norm_small_limit (q : Cutoff) (f : L2) :
    Tendsto (fun M : ℝ => ‖lowL2 q M f‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let g : L2 := 𝓕 f
  have hg : Integrable (fun ξ : V => ‖g ξ‖^2) := (Lp.memLp g).norm.integrable_sq
  have hae : ∀ᵐ ξ : V ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (0 : V) : (volume : Measure V) {0} = 0)
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (F := fun M ξ => ‖lowSymbol q M ξ * g ξ‖^2)
    (f := fun _ => (0 : ℝ)) (fun ξ => ‖g ξ‖^2)
    (Eventually.of_forall fun M =>
      (((lowSymbol_continuous q M).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable g)).norm.pow 2))
    (Eventually.of_forall fun M => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
      apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (lowSymbol_norm_le_one q M ξ) (norm_nonneg (g ξ)))
    hg (by
      filter_upwards [hae] with ξ hξ
      simpa only [zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((lowSymbol_small_limit q hξ).mul_const (g ξ)).norm.pow 2)
  have hsq : Tendsto (fun M : ℝ => ‖lowL2 q M f‖^2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [lowL2_norm_sq_fourier, integral_zero] using hd
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

theorem lowL2_small (q : Cutoff) (f : L2) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ), 0 < M → M ≤ δ → ‖lowL2 q M f‖ < ε := by
  have he := (lowL2_norm_small_limit q f).eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨r/2, half_pos hr, ?_⟩
  intro M hM hMr
  apply hball
  refine ⟨?_, hM⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hM] using
    hMr.trans_lt (half_lt_self hr)

end HartreeF.Paper121SmallFrequency
