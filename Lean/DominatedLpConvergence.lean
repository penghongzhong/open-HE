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
namespace HartreeF.WeakHartreeChain

theorem strong_lp_zero_of_ae_dominated
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {fn : ℕ → Space → E} {g : Space → F}
    (hmeas : ∀ n, AEStronglyMeasurable (fn n) volume)
    (hg : MemLp g p volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖fn n x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => fn n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fn n) p volume) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hi : (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume) ≠ ∞ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
      hg.aestronglyMeasurable).mp hg.eLpNorm_lt_top).ne
  have hlim' : Tendsto (fun n => ∫⁻ x, ‖fn n x‖ₑ ^ p.toReal ∂volume)
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_of_dominated_convergence'
        (fun x => ‖g x‖ₑ ^ p.toReal)
        (fun n => (hmeas n).enorm.pow_const _)
        (fun n => (hbound n).mono (fun x hx =>
          ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr hx) hp.le))
        hi (show ∀ᵐ x ∂volume, Tendsto
          (fun n => ‖fn n x‖ₑ ^ p.toReal) atTop (𝓝 (0 : ℝ≥0∞)) from by
          filter_upwards [hlim] with x hx
          have he := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto
            (0 : ℝ≥0∞)
          simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos hp] using he.comp (show Tendsto (fun n => ‖fn n x‖ₑ) atTop (𝓝 0) by simpa using hx.enorm)))
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto
    (0 : ℝ≥0∞)
  simpa only [Function.comp_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
    (hmeas _), ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using hpow.comp hlim'


#print axioms strong_lp_zero_of_ae_dominated
end HartreeF.WeakHartreeChain
