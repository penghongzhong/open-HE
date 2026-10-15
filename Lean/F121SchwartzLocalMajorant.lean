import F121ConvolutionC0
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Paper121SmoothConvolution
open EnergySpace

/-- Polynomial weight comparison on a genuine spatial neighborhood. -/
theorem local_weight_comparison (x₀ x y : V) (hx : x ∈ Metric.ball x₀ 1) :
    1+‖y‖ ≤ (2+‖x₀‖)*(1+‖x-y‖) := by
  have hx' : ‖x-x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hnx : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
  have hny : ‖y‖ ≤ ‖x‖+‖x-y‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le x (x-y)
  nlinarith [norm_nonneg x₀, norm_nonneg (x-y), mul_nonneg (norm_nonneg x₀) (norm_nonneg (x-y))]

/-- Every translated Schwartz kernel has a uniform polynomial majorant locally in x. -/
theorem schwartz_local_majorant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : 𝓢(V, E)) (d : ℕ) (x₀ : V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.ball x₀ 1, ∀ y : V,
      ‖k (x-y)‖ ≤ C*(1+‖y‖)^(-(d : ℝ)) := by
  let A : ℝ := 2^d * (Finset.Iic (d, 0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) k
  have hA (z : V) : (1+‖z‖)^d*‖k z‖ ≤ A := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d, 0))
        (k := d) (n := 0) le_rfl le_rfl k z)
  have hA0 : 0 ≤ A := (mul_nonneg (by positivity) (norm_nonneg (k 0))).trans (hA 0)
  refine ⟨(2+‖x₀‖)^d*A, mul_nonneg (by positivity) hA0, ?_⟩
  intro x hx y
  have hb : (1+‖y‖)^d*‖k (x-y)‖ ≤ (2+‖x₀‖)^d*A := by
    calc
      _ ≤ ((2+‖x₀‖)*(1+‖x-y‖))^d*‖k (x-y)‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (local_weight_comparison x₀ x y hx) d)
          (norm_nonneg _)
      _ = (2+‖x₀‖)^d*((1+‖x-y‖)^d*‖k (x-y)‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hA (x-y)) (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hb

/-- The polynomial integrable weight is derived from the actual Lp hypothesis. -/
theorem lp_weight_integrable {p r : ℝ≥0∞} [p.HolderConjugate r]
    (f : Lp ℂ p (volume : Measure V)) :
    ∃ d : ℕ, Integrable (fun y : V => ‖f y‖*(1+‖y‖)^(-(d : ℝ))) volume := by
  obtain ⟨d, hd⟩ := (inferInstance : (volume : Measure V).HasTemperateGrowth).exists_eLpNorm_lt_top r
  exact ⟨d, (Lp.memLp f).norm.integrable_mul hd⟩

end HartreeF.Paper121SmoothConvolution
