import WeakGradientClosure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Function-level dominated L2 convergence on the actual infinite-volume space.
The dominating L2 function produces finiteness before any use of powers of the
Lebesgue integral. No Bochner integral is used outside its true domain. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ModulusGradient

theorem strong_l2_zero_of_ae_dominated
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {fn : ℕ → Space → E} {g : Space → F}
    (hmeas : ∀ n, AEStronglyMeasurable (fn n) volume)
    (hg : MemLp g 2 volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖fn n x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => fn n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fn n) 2 volume) atTop (𝓝 0) := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hi : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume) ≠ ∞ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
      hg.aestronglyMeasurable).mp hg.eLpNorm_lt_top).ne
  have hlim' : Tendsto (fun n => ∫⁻ x, ‖fn n x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume)
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_of_dominated_convergence'
        (fun x => ‖g x‖ₑ ^ (2 : ℝ≥0∞).toReal)
        (fun n => (hmeas n).enorm.pow_const _)
        (fun n => (hbound n).mono (fun x hx =>
          ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr hx) hp.le))
        hi (show ∀ᵐ x ∂volume, Tendsto
          (fun n => ‖fn n x‖ₑ ^ (2 : ℝ≥0∞).toReal) atTop (𝓝 (0 : ℝ≥0∞)) from by
          filter_upwards [hlim] with x hx
          have he := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto
            (0 : ℝ≥0∞)
          simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos hp] using he.comp (show Tendsto (fun n => ‖fn n x‖ₑ) atTop (𝓝 0) by simpa using hx.enorm)))
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto
    (0 : ℝ≥0∞)
  simpa only [Function.comp_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
    (hmeas _), ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using hpow.comp hlim'

/-- Bounded scalar coefficients converging a.e. can be multiplied by a fixed
actual L2 gradient, and the resulting gradients converge strongly in L2. -/
theorem bounded_coefficient_smul_strong_l2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {cn : ℕ → Space → ℝ} {c : Space → ℝ} {G : Space → E} {B : ℝ}
    (hcn : ∀ n, AEStronglyMeasurable (cn n) volume)
    (hc : AEStronglyMeasurable c volume) (hG : MemLp G 2 volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖cn n x - c x‖ ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => cn n x) atTop (𝓝 (c x))) :
    Tendsto (fun n => eLpNorm (fun x => (cn n x - c x) • G x) 2 volume)
      atTop (𝓝 0) := by
  apply strong_l2_zero_of_ae_dominated
    (fun n => ((hcn n).sub hc).smul hG.aestronglyMeasurable)
    (hG.const_smul B)
  · intro n
    filter_upwards [hbound n] with x hx
    change ‖(cn n x - c x) • G x‖ ≤ ‖B • G x‖
    simp only [norm_smul]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self B)) (norm_nonneg _)
  · filter_upwards [hlim] with x hx
    change Tendsto (fun n => (cn n x - c x) • G x) atTop (𝓝 (0 : E))
    simpa only [sub_self, zero_smul] using
      (hx.sub (tendsto_const_nhds (x := c x))).smul (tendsto_const_nhds (x := G x))

#print axioms strong_l2_zero_of_ae_dominated
#print axioms bounded_coefficient_smul_strong_l2
end HartreeF.ModulusGradient
