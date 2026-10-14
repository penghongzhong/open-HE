import WeakCutoffLpDomains
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HartreeF.CutoffApproximation

theorem tendsto_eLpNorm_indicator_eventually_empty
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hempty : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n) :
    Tendsto (fun n => eLpNorm ((s n).indicator f) p μ) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hi : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≠ ∞ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
      hf.aestronglyMeasurable).mp hf.eLpNorm_lt_top).ne
  have hlim : Tendsto (fun n => ∫⁻ x, ‖(s n).indicator f x‖ₑ ^ p.toReal ∂μ)
      atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_of_dominated_convergence'
        (fun x => ‖f x‖ₑ ^ p.toReal)
        (fun n => (hf.aestronglyMeasurable.indicator (hs n)).enorm.pow_const _)
        (fun n => ae_of_all _ (fun x =>
          ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self (s := s n) f x) hp.le))
        hi (show ∀ᵐ x ∂μ, Tendsto
          (fun n => ‖(s n).indicator f x‖ₑ ^ p.toReal) atTop (𝓝 (0 : ℝ≥0∞)) from by
            filter_upwards [hempty] with x hx
            apply tendsto_const_nhds.congr'
            filter_upwards [hx] with n hn
            simp [Set.indicator_of_notMem hn, ENNReal.zero_rpow_of_pos hp]))
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto (0 : ℝ≥0∞)
  have hfinal := hpow.comp hlim
  simpa only [Function.comp_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
      (hf.aestronglyMeasurable.indicator (hs _)), ENNReal.zero_rpow_of_pos
      (one_div_pos.mpr hp)] using hfinal

def exteriorTail {E : Type*} [Zero E] (n : ℕ) (f : Space → E) : Space → E :=
  ({x : Space | (n : ℝ) < ‖x‖}).indicator f

theorem exteriorTail_eLpNorm_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} {p : ℝ≥0∞} (hf : MemLp f p volume)
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    Tendsto (fun n : ℕ => eLpNorm (exteriorTail n f) p volume) atTop (𝓝 0) := by
  unfold exteriorTail
  apply tendsto_eLpNorm_indicator_eventually_empty hf hp0 hpt
  · intro n
    exact isOpen_lt continuous_const continuous_norm |>.measurableSet
  · filter_upwards [] with x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [not_lt]
    exact hN.le.trans (Nat.cast_le.mpr hn)

end HartreeF.CutoffApproximation

#print axioms HartreeF.CutoffApproximation.tendsto_eLpNorm_indicator_eventually_empty
#print axioms HartreeF.CutoffApproximation.exteriorTail_eLpNorm_tendsto_zero
