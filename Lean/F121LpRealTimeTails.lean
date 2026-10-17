import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HartreeF.RealTimeTails

/-- Finite time-exponent integrability gives a literal right-half-line tail.
No decay or tail estimate is assumed. -/
theorem lp_restrict_Ici_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Lp E p (volume : Measure ℝ)) :
    Tendsto (fun a : ℝ => eLpNorm F p (volume.restrict (Ici a))) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have htail : Tendsto (fun a : ℝ => ∫ t in Ici a, ‖F t‖ ^ p.toReal) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  have hpow := (Real.continuous_rpow_const (inv_nonneg.mpr hpr.le)).continuousAt.tendsto.comp htail
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpow
  have heq (a : ℝ) := (Lp.memLp F).restrict (s := Ici a)
  simp_rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hp (heq _)]
  simpa only [Function.comp_def, Real.zero_rpow (inv_ne_zero hpr.ne'), ENNReal.ofReal_zero] using h

/-- The same literal-tail conclusion at the negative end of real time. -/
theorem lp_restrict_Iic_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Lp E p (volume : Measure ℝ)) :
    Tendsto (fun a : ℝ => eLpNorm F p (volume.restrict (Iic a))) atBot (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have htail : Tendsto (fun a : ℝ => ∫ t in Iic a, ‖F t‖ ^ p.toReal) atBot (𝓝 0) :=
    tendsto_integral_Iic_zero tendsto_id
  have hpow := (Real.continuous_rpow_const (inv_nonneg.mpr hpr.le)).continuousAt.tendsto.comp htail
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpow
  have heq (a : ℝ) := (Lp.memLp F).restrict (s := Iic a)
  simp_rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 hp (heq _)]
  simpa only [Function.comp_def, Real.zero_rpow (inv_ne_zero hpr.ne'), ENNReal.ofReal_zero] using h

end HartreeF.RealTimeTails
