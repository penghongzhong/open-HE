import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace HartreeF.StrongOperatorPaths

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [MeasurableSpace T] (μ : Measure T)

omit [NormedSpace ℂ E] in
theorem lp_norm_pow_eq_integral {q : ℕ} (hq : q ≠ 0)
    [Fact ((1 : ℝ≥0∞) ≤ q)] (f : Lp E q μ) :
    ‖f‖^q = ∫ t, ‖f t‖^q ∂μ := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)
  have hn : 0 ≤ ∫ t, ‖f t‖^q ∂μ :=
    integral_nonneg (fun t => pow_nonneg (norm_nonneg _) _)
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm (by simpa using hq)
    (by simp) (Lp.memLp f)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hn _),
    ← Real.rpow_natCast, ← Real.rpow_mul hn, inv_mul_cancel₀ hqpos.ne', Real.rpow_one]

/-- Actual Bochner Lq convergence follows from strong convergence and one
uniform operator bound, for finite positive natural q (in particular 2,10). -/
theorem compLp_tendsto {q : ℕ} (hq : q ≠ 0) [Fact ((1 : ℝ≥0∞) ≤ q)]
    (P : ℕ → E →L[ℂ] E) (C : ℝ≥0) (hbound : ∀ n, ‖P n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) (f : Lp E q μ) :
    Tendsto (fun n => (P n).compLp f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hint : Integrable (fun t => ‖f t‖^q) μ :=
    (Lp.memLp f).integrable_norm_pow hq
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := fun n t => ‖P n (f t) - f t‖^q)
    (f := fun _ => (0 : ℝ)) (fun t => ((C : ℝ)+1)^q * ‖f t‖^q)
    (Eventually.of_forall fun n =>
      (((P n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).sub
        (Lp.aestronglyMeasurable f)).norm.pow q)
    (Eventually.of_forall fun n => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      have hp : ‖P n (f t)‖ ≤ (C : ℝ)*‖f t‖ :=
        ((P n).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
      have he : ‖P n (f t)-f t‖ ≤ ((C : ℝ)+1)*‖f t‖ := by
        have hx := norm_sub_le (P n (f t)) (f t)
        nlinarith
      exact (pow_le_pow_left₀ (norm_nonneg _) he q).trans_eq (mul_pow _ _ _))
    (hint.const_mul _) (Eventually.of_forall fun t => by
      have hs := (hstrong (f t)).sub (tendsto_const_nhds (x := f t))
      simpa only [sub_self, norm_zero, zero_pow hq] using hs.norm.pow q)
  have hid (n : ℕ) : ‖(P n).compLp f - f‖^q =
      ∫ t, ‖P n (f t)-f t‖^q ∂μ := by
    rw [lp_norm_pow_eq_integral μ hq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((P n).compLp f) f, (P n).coeFn_compLp f] with t ht hp
    rw [ht, Pi.sub_apply, hp]
  have hpow : Tendsto (fun n => ‖(P n).compLp f - f‖^q) atTop (𝓝 0) := by
    simpa only [hid, integral_zero] using hd
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)
  have hr := (Real.continuous_rpow_const
    (show 0 ≤ ((q : ℝ)⁻¹) by positivity)).tendsto 0 |>.comp hpow
  simpa only [Function.comp_def,
    Real.pow_rpow_inv_natCast (norm_nonneg _) hq,
    Real.zero_rpow (inv_pos.mpr hqpos).ne'] using hr

#print axioms lp_norm_pow_eq_integral
#print axioms compLp_tendsto
end HartreeF.StrongOperatorPaths
