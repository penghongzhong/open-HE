import WeakCutoffLpDomains
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace HartreeF.CutoffApproximation

theorem haar_smul_map_three {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : Space => a • x) volume =
      ENNReal.ofReal ((a ^ 3)⁻¹) • volume := by
  simpa [Space, abs_of_pos (inv_pos.mpr (pow_pos ha 3))] using
    (Measure.map_addHaar_smul (volume : Measure Space) (ne_of_gt ha))

theorem eLpNorm_comp_smul_three {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : AEStronglyMeasurable g volume) {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun x => g (a • x)) 3 volume =
      (ENNReal.ofReal a)⁻¹ * eLpNorm g 3 volume := by
  have hmap : AEStronglyMeasurable g
      (Measure.map (fun x : Space => a • x) volume) := by
    rw [haar_smul_map_three ha]
    exact hg.smul_measure _
  change eLpNorm (g ∘ (fun x : Space => a • x)) 3 volume = _
  rw [← eLpNorm_map_measure hmap (measurable_const_smul a).aemeasurable,
    haar_smul_map_three ha,
    eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hg]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (pow_pos ha 3), ENNReal.ofReal_pow ha.le,
    ENNReal.inv_rpow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_scale_critical_three {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Space → E} (hg : AEStronglyMeasurable g volume)
    {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun x => a • g (a • x)) 3 volume = eLpNorm g 3 volume := by
  change eLpNorm (a • (fun x => g (a • x))) 3 volume = _
  rw [eLpNorm_const_smul, eLpNorm_comp_smul_three hg ha]
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos ha, ← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,
    one_mul]

theorem memLp_scale_critical_three {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Space → E} (hg : MemLp g 3 volume)
    {a : ℝ} (ha : 0 < a) : MemLp (fun x => a • g (a • x)) 3 volume := by
  show eLpNorm (fun x => a • g (a • x)) 3 volume < ∞
  rw [eLpNorm_scale_critical_three hg.aestronglyMeasurable ha]
  exact hg.eLpNorm_lt_top

end HartreeF.CutoffApproximation

#print axioms HartreeF.CutoffApproximation.haar_smul_map_three
#print axioms HartreeF.CutoffApproximation.eLpNorm_comp_smul_three
#print axioms HartreeF.CutoffApproximation.eLpNorm_scale_critical_three
#print axioms HartreeF.CutoffApproximation.memLp_scale_critical_three
