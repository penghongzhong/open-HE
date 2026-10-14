import Mathlib

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

def lpFromReciprocal (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal s⁻¹

theorem lp_from_reciprocal_inv {s : ℝ} (hs : 0 < s) :
    (lpFromReciprocal s)⁻¹ = ENNReal.ofReal s := by
  unfold lpFromReciprocal
  rw [ENNReal.ofReal_inv_of_pos hs, inv_inv]

theorem holder_from_real_reciprocals {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : a + b = c) :
    ENNReal.HolderTriple (lpFromReciprocal a) (lpFromReciprocal b) (lpFromReciprocal c) := by
  constructor
  rw [lp_from_reciprocal_inv ha, lp_from_reciprocal_inv hb, lp_from_reciprocal_inv hc,
    ← ENNReal.ofReal_add ha.le hb.le, he]

theorem lp_one_tenth : lpFromReciprocal (1 / 10) = 10 := by
  norm_num [lpFromReciprocal]

theorem temporal_real_product_norm {T : Type*} [MeasurableSpace T]
    (mu : Measure T) {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (f g : T → ℝ) (hf : AEStronglyMeasurable f mu) (hg : AEStronglyMeasurable g mu) :
    eLpNorm (fun t => f t * g t) r mu ≤ eLpNorm f p mu * eLpNorm g q mu := by
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := r) hf hg
  have he : f • g = (fun t => f t * g t) := by funext t; rfl
  rw [he] at hh
  exact hh

theorem temporal_native_power_norm {T : Type*} [MeasurableSpace T]
    (mu : Measure T) {N a : ℝ} (hN : 0 < N) (ha : 0 < a)
    (f : T → ℝ) (hf : AEStronglyMeasurable f mu) :
    eLpNorm (fun t => ‖f t‖ ^ a) (lpFromReciprocal (a / N)) mu =
      eLpNorm f (ENNReal.ofReal N) mu ^ a := by
  have he : lpFromReciprocal (a / N) * ENNReal.ofReal a = ENNReal.ofReal N := by
    unfold lpFromReciprocal
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (div_nonneg ha.le hN.le))]
    congr 1
    field_simp
  rw [eLpNorm_norm_rpow f hf ha, he]

theorem temporal_native_infinity_power_norm {T : Type*} [MeasurableSpace T]
    (mu : Measure T) {a : ℝ} (ha : 0 < a) (f : T → ℝ) (hf : AEStronglyMeasurable f mu) :
    eLpNorm (fun t => ‖f t‖ ^ a) ∞ mu = eLpNorm f ∞ mu ^ a := by
  have he : (∞ : ℝ≥0∞) * ENNReal.ofReal a = ∞ :=
    ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
  rw [eLpNorm_norm_rpow f hf ha, he]

end HartreeF.TimeHolder

