import FTimeHolderCore

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

theorem temporal_value_difference_holder {alpha : ℝ} (ha : 0 < alpha)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) (A S W D : T → ℝ)
    (hA : AEStronglyMeasurable A mu) (hS : AEStronglyMeasurable S mu)
    (hW : AEStronglyMeasurable W mu) (hD : AEStronglyMeasurable D mu) :
    eLpNorm (fun t => ‖A t‖ ^ (2 * alpha) * (‖S t‖ ^ (3 : ℝ) * W t * D t)) 2 mu ≤
      eLpNorm A ∞ mu ^ (2 * alpha) * eLpNorm S 10 mu ^ (3 : ℝ) *
      eLpNorm W 10 mu * eLpNorm D 10 mu := by
  let : ENNReal.HolderTriple (lpFromReciprocal (3 / 10)) 10 (lpFromReciprocal (4 / 10)) := by
    have hh := holder_from_real_reciprocals (by norm_num : (0 : ℝ) < 3 / 10)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 4 / 10)
      (by norm_num : (3 : ℝ) / 10 + 1 / 10 = 4 / 10)
    rw [lp_one_tenth] at hh
    exact hh
  let : ENNReal.HolderTriple (lpFromReciprocal (4 / 10)) 10 2 := by
    have hh := holder_from_real_reciprocals (by norm_num : (0 : ℝ) < 4 / 10)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (4 : ℝ) / 10 + 1 / 10 = 1 / 2)
    norm_num [lpFromReciprocal] at hh ⊢
    exact hh
  have hSp : AEStronglyMeasurable (fun t => ‖S t‖ ^ (3 : ℝ)) mu :=
    (hS.norm.aemeasurable.pow_const (3 : ℝ)).aestronglyMeasurable
  have hAp : AEStronglyMeasurable (fun t => ‖A t‖ ^ (2 * alpha)) mu :=
    (hA.norm.aemeasurable.pow_const (2 * alpha)).aestronglyMeasurable
  have hSW := temporal_real_product_norm mu (p := lpFromReciprocal (3 / 10))
    (q := 10) (r := lpFromReciprocal (4 / 10)) _ _ hSp hW
  rw [temporal_native_power_norm mu (by norm_num : (0 : ℝ) < 10)
    (by norm_num : (0 : ℝ) < 3) S hS, ENNReal.ofReal_ofNat] at hSW
  have hSWD := temporal_real_product_norm mu (p := lpFromReciprocal (4 / 10))
    (q := 10) (r := 2) (fun t => ‖S t‖ ^ (3 : ℝ) * W t) D (hSp.mul hW) hD
  have hsmall := hSWD.trans (mul_le_mul' hSW (le_refl (eLpNorm D 10 mu)))
  have hFull := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
    (fun t => ‖A t‖ ^ (2 * alpha)) (fun t => ‖S t‖ ^ (3 : ℝ) * W t * D t)
    hAp ((hSp.mul hW).mul hD)
  rw [temporal_native_infinity_power_norm mu (by positivity : 0 < 2 * alpha) A hA] at hFull
  have hb := hFull.trans (mul_le_mul' (le_refl (eLpNorm A ∞ mu ^ (2 * alpha))) hsmall)
  simpa only [mul_assoc] using hb

end HartreeF.TimeHolder

