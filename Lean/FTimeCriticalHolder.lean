import FTimeHolderCore

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

theorem temporal_critical_holder {alpha : ℝ} (ha : 0 < alpha)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) (A S D : T → ℝ)
    (hA : AEStronglyMeasurable A mu) (hS : AEStronglyMeasurable S mu)
    (hD : AEStronglyMeasurable D mu) :
    eLpNorm (fun t => ‖A t‖ ^ (2 * alpha) * ‖S t‖ ^ (4 : ℝ) * D t) 2 mu ≤
      eLpNorm A ∞ mu ^ (2 * alpha) * eLpNorm S 10 mu ^ (4 : ℝ) * eLpNorm D 10 mu := by
  let : ENNReal.HolderTriple (lpFromReciprocal (4 / 10)) 10 2 := by
    have hh := holder_from_real_reciprocals (by norm_num : (0 : ℝ) < 4 / 10)
      (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (4 : ℝ) / 10 + 1 / 10 = 1 / 2)
    norm_num [lpFromReciprocal] at hh ⊢
    exact hh
  have hAp : AEStronglyMeasurable (fun t => ‖A t‖ ^ (2 * alpha)) mu :=
    (hA.norm.aemeasurable.pow_const (2 * alpha)).aestronglyMeasurable
  have hSp : AEStronglyMeasurable (fun t => ‖S t‖ ^ (4 : ℝ)) mu :=
    (hS.norm.aemeasurable.pow_const (4 : ℝ)).aestronglyMeasurable
  have hSD := temporal_real_product_norm mu (p := lpFromReciprocal (4 / 10))
    (q := 10) (r := 2) _ _ hSp hD
  have hexp : lpFromReciprocal (4 / 10) * ENNReal.ofReal (4 : ℝ) = 10 := by
    unfold lpFromReciprocal
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 / 10)⁻¹)]
    norm_num
  rw [eLpNorm_norm_rpow S hS (by norm_num : (0 : ℝ) < 4), hexp] at hSD
  have hFull := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
    (fun t => ‖A t‖ ^ (2 * alpha)) (fun t => ‖S t‖ ^ (4 : ℝ) * D t) hAp (hSp.mul hD)
  have ha2 : 0 < 2 * alpha := by linarith
  have hexpA : (∞ : ℝ≥0∞) * ENNReal.ofReal (2 * alpha) = ∞ := by
    exact ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr ha2))
  rw [eLpNorm_norm_rpow A hA ha2, hexpA] at hFull
  have hh := hFull.trans (mul_le_mul' (le_refl (eLpNorm A ∞ mu ^ (2 * alpha))) hSD)
  have he : (fun t => ‖A t‖ ^ (2 * alpha) * (‖S t‖ ^ (4 : ℝ) * D t)) =
      (fun t => ‖A t‖ ^ (2 * alpha) * ‖S t‖ ^ (4 : ℝ) * D t) := by
    funext t; exact (mul_assoc _ _ _).symm
  rw [he] at hh
  simpa only [mul_assoc] using hh

end HartreeF.TimeHolder

