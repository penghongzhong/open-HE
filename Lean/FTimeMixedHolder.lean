import FTimeHolderCore

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

theorem temporal_uniform_holders {θ : ℝ} (ht0 : 0 < θ) (ht4 : θ < 4) :
    ENNReal.HolderTriple (lpFromReciprocal ((4 - θ) / 10))
      (lpFromReciprocal (θ / 10)) (lpFromReciprocal (4 / 10)) ∧
    ENNReal.HolderTriple (lpFromReciprocal (4 / 10)) 10 2 := by
  constructor
  · apply holder_from_real_reciprocals (div_pos (sub_pos.mpr ht4) (by norm_num))
      (div_pos ht0 (by norm_num)) (by norm_num)
    ring
  · have hh := holder_from_real_reciprocals (by norm_num : (0 : ℝ) < 4 / 10)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (4 : ℝ) / 10 + 1 / 10 = 1 / 2)
    norm_num [lpFromReciprocal] at hh ⊢
    exact hh

theorem temporal_uniform_difference_holder {alpha θ : ℝ} (ha : 0 < alpha) (ht0 : 0 < θ) (ht4 : θ < 4)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) (A S B W D : T → ℝ)
    (hA : AEStronglyMeasurable A mu) (hS : AEStronglyMeasurable S mu)
    (hB : AEStronglyMeasurable B mu) (hW : AEStronglyMeasurable W mu)
    (hD : AEStronglyMeasurable D mu) :
    eLpNorm (fun t => ‖A t‖ ^ (5 * alpha / 3) * ‖S t‖ ^ (4 - θ) *
      ‖B t‖ ^ (alpha / 3) * ‖W t‖ ^ θ * D t) 2 mu ≤
      eLpNorm A ∞ mu ^ (5 * alpha / 3) * eLpNorm S 10 mu ^ (4 - θ) *
      eLpNorm B ∞ mu ^ (alpha / 3) * eLpNorm W 10 mu ^ θ * eLpNorm D 10 mu := by
  let := (temporal_uniform_holders ht0 ht4).1
  let := (temporal_uniform_holders ht0 ht4).2
  have hc : 0 < 4 - θ := by linarith
  have hAp : AEStronglyMeasurable (fun t => ‖A t‖ ^ (5 * alpha / 3)) mu :=
    (hA.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hBp : AEStronglyMeasurable (fun t => ‖B t‖ ^ (alpha / 3)) mu :=
    (hB.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hSp : AEStronglyMeasurable (fun t => ‖S t‖ ^ (4 - θ)) mu :=
    (hS.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hWp : AEStronglyMeasurable (fun t => ‖W t‖ ^ θ) mu :=
    (hW.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hSW := temporal_real_product_norm mu
    (p := lpFromReciprocal ((4 - θ) / 10))
    (q := lpFromReciprocal (θ / 10)) (r := lpFromReciprocal (4 / 10))
    _ _ hSp hWp
  rw [temporal_native_power_norm mu (by norm_num : (0 : ℝ) < 10) hc S hS,
    temporal_native_power_norm mu (by norm_num : (0 : ℝ) < 10) ht0 W hW, ENNReal.ofReal_ofNat] at hSW
  have hSWD := temporal_real_product_norm mu (p := lpFromReciprocal (4 / 10)) (q := 10) (r := 2)
    (fun t => ‖S t‖ ^ (4 - θ) * ‖W t‖ ^ θ)
    D (hSp.mul hWp) hD
  have hsmall := hSWD.trans (mul_le_mul' hSW (le_refl (eLpNorm D 10 mu)))
  have hsmallMeas := (hSp.mul hWp).mul hD
  have hBsmall := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
    (fun t => ‖B t‖ ^ (alpha / 3))
    (fun t => (‖S t‖ ^ (4 - θ) * ‖W t‖ ^ θ) * D t)
    hBp hsmallMeas
  rw [temporal_native_infinity_power_norm mu (by positivity : 0 < alpha / 3) B hB] at hBsmall
  have hbs := hBsmall.trans (mul_le_mul' (le_refl (eLpNorm B ∞ mu ^ (alpha / 3))) hsmall)
  have hFull := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
    (fun t => ‖A t‖ ^ (5 * alpha / 3))
    (fun t => ‖B t‖ ^ (alpha / 3) *
      ((‖S t‖ ^ (4 - θ) * ‖W t‖ ^ θ) * D t))
    hAp (hBp.mul hsmallMeas)
  rw [temporal_native_infinity_power_norm mu (by positivity : 0 < 5 * alpha / 3) A hA] at hFull
  have hb := hFull.trans (mul_le_mul' (le_refl (eLpNorm A ∞ mu ^ (5 * alpha / 3))) hbs)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hb

end HartreeF.TimeHolder

