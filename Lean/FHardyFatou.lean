import FEnergyGradientNorm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Author candidate imported from preserved uncompiled proof text.
Exact per-attempt native receipts determine status.
It is intended for Lean 4.35.0-rc3 and the mapped mathlib a98628 environment.
The first lemma is ordinary nonnegative Fatou with a convergent majorant of
integrals. The second lemma converts an already finite squared integral to L2.
Neither is a new Hardy assumption or a replacement for a missing producer.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.SameStateHardy
open EnergySpace

/-- Nonnegative Fatou; there is no Bochner integral or `toReal` in this step. -/
lemma lintegral_le_of_ae_tendsto_of_bounds
    {F : ℕ → V → ℝ≥0∞} {f : V → ℝ≥0∞} {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) volume)
    (hf : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫⁻ x, F n x) ≤ b n)
    (hB : Tendsto b atTop (𝓝 B)) :
    (∫⁻ x, f x) ≤ B := by
  calc
    (∫⁻ x, f x) = ∫⁻ x, liminf (fun n => F n x) atTop := by
      apply lintegral_congr_ae
      filter_upwards [hf] with x hx
      exact hx.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, F n x) atTop := lintegral_liminf_le' hF
    _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hb)
    _ = B := hB.liminf_eq

/-- Algebraic conversion only, after the nonnegative squared integral is finite.
Its input bound is supplied by the genuine Hardy producers in later modules. -/
lemma l2_of_square_lintegral_bound {f : V → ℂ} {E : ℝ}
    (hf : AEStronglyMeasurable f volume) (hE : 0 ≤ E)
    (hb : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) ≤ ENNReal.ofReal (4 * E)) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) < ∞ ∧
    Integrable (fun x => ‖f x‖ ^ 2) volume ∧
    (∫ x, ‖f x‖ ^ 2) ≤ 4 * E ∧
    MemLp f 2 volume ∧
    eLpNorm f 2 volume ≤ ENNReal.ofReal (2 * Real.sqrt E) := by
  have hfinite : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) < ∞ :=
    hb.trans_lt ENNReal.ofReal_lt_top
  have hnonneg : 0 ≤ᵐ[volume] (fun x => ‖f x‖ ^ 2) :=
    Eventually.of_forall (fun x => sq_nonneg ‖f x‖)
  have hsq : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) volume := hf.norm.pow 2
  have hint : Integrable (fun x => ‖f x‖ ^ 2) volume :=
    (lintegral_ofReal_ne_top_iff_integrable hsq hnonneg).mp hfinite.ne
  -- Only now, after hfinite and hint, pass to the real-valued integral.
  have hreal : (∫ x, ‖f x‖ ^ 2) ≤ 4 * E := by
    rw [integral_eq_lintegral_of_nonneg_ae hnonneg hsq]
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hE)]
      using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hmem : MemLp f 2 volume := (memLp_two_iff_integrable_sq_norm hf).mpr hint
  have hnorm : eLpNorm f 2 volume ≤ ENNReal.ofReal (2 * Real.sqrt E) := by
    have htwo : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hmem,
      htwo]
    simp only [Real.rpow_two]
    apply ENNReal.ofReal_le_ofReal
    have hsqrt : (∫ x, ‖f x‖ ^ 2) ^ (2 : ℝ)⁻¹ =
        Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
      rw [Real.sqrt_eq_rpow, one_div]
    rw [hsqrt]
    calc
      Real.sqrt (∫ x, ‖f x‖ ^ 2) ≤ Real.sqrt (4 * E) := Real.sqrt_le_sqrt hreal
      _ = 2 * Real.sqrt E := by
        have heq : 4 * E = (2 * Real.sqrt E) ^ 2 := by
          nlinarith [Real.sq_sqrt hE]
        rw [heq, Real.sqrt_sq (mul_nonneg (by norm_num) (Real.sqrt_nonneg E))]
  exact ⟨hfinite, hint, hreal, hmem, hnorm⟩

end HartreeF.SameStateHardy
