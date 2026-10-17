import FSameStateWeightedHardy
import Mathlib.MeasureTheory.Integral.Prod

/-! STATIC-ONLY CANDIDATE. Ordinary Tonelli/Fubini for actual nonnegative kernels.
This generic lemma is immediately instantiated by proved weighted-Hardy slices;
it is not an HLS or Hartree estimate axiom. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.WeightedRieszProduct
open EnergySpace WeightedHardy GradientMajorants

/-- Reverse conversion retains actual integrability and the nonnegative representative. -/
theorem spatialBound_one_of_nonnegative_integral {f : V → ℝ} {B : ℝ}
    (hf : Integrable f volume) (hn : ∀ x, 0 ≤ f x) (hb : (∫ x, f x) ≤ B) :
    SpatialBound f 1 B := by
  have hm : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
  refine ⟨by norm_num, by simpa only [one_div_one, ENNReal.ofReal_one] using hm, ?_⟩
  change (eLpNorm f (ENNReal.ofReal (1 / (1 : ℝ))) volume).toReal ≤ B
  rw [one_div_one, ENNReal.ofReal_one]
  have heq : (eLpNorm f 1 volume).toReal = ∫ x, f x := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hm]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one]
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg (f x)))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => (Real.norm_eq_abs _).trans (abs_of_nonneg (hn x))
  rw [heq]
  exact hb

/-- Genuine two-point and pointwise-integral domains from uniformly bounded slices.
No pointwise source boundedness, compact support, or finite ambient volume is used. -/
theorem nonnegative_kernel_tonelli {Q : V × V → ℝ} {h : V → ℝ} {B : ℝ}
    (hQm : AEStronglyMeasurable Q (volume.prod volume))
    (hQn : ∀ z, 0 ≤ Q z)
    (hSlices : ∀ y, Integrable (fun x => Q (x, y)) volume ∧
      (∫ x, Q (x, y)) ≤ B)
    (hh : Integrable h volume) :
    Integrable (fun z : V × V => ‖h z.2‖ * Q z) (volume.prod volume) ∧
    (∀ᵐ x ∂volume, Integrable (fun y => ‖h y‖ * Q (x, y)) volume) ∧
    SpatialBound (fun x => ∫ y, ‖h y‖ * Q (x, y)) 1 (B * ∫ y, ‖h y‖) := by
  let J : V × V → ℝ := fun z => ‖h z.2‖ * Q z
  have hJn (z : V × V) : 0 ≤ J z := mul_nonneg (norm_nonneg _) (hQn z)
  have hJm : AEStronglyMeasurable J (volume.prod volume) :=
    hh.norm.aestronglyMeasurable.comp_snd.mul hQm
  have hinner (y : V) : (∫ x, ‖J (x, y)‖) = ‖h y‖ * ∫ x, Q (x, y) := by
    calc
      (∫ x, ‖J (x, y)‖) = ∫ x, J (x, y) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          (Real.norm_eq_abs _).trans (abs_of_nonneg (hJn (x, y)))
      _ = _ := by
        change (∫ x, ‖h y‖ * Q (x,y)) = _
        exact integral_const_mul _ _
  have hinnerBound (y : V) : (∫ x, ‖J (x, y)‖) ≤ ‖h y‖ * B := by
    rw [hinner]
    exact mul_le_mul_of_nonneg_left (hSlices y).2 (norm_nonneg _)
  have hinnerInt : Integrable (fun y => ∫ x, ‖J (x, y)‖) volume := by
    apply (hh.norm.mul_const B).mono' hJm.norm.prod_swap.integral_prod_right'
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
    exact hinnerBound y
  have hJ : Integrable J (volume.prod volume) := by
    apply (integrable_prod_iff' hJm).mpr
    refine ⟨Eventually.of_forall (fun y => ?_), hinnerInt⟩
    exact (hSlices y).1.const_mul ‖h y‖
  have hIntegral : (∫ x, ∫ y, J (x, y)) ≤ B * ∫ y, ‖h y‖ := by
    rw [integral_integral_swap hJ]
    calc
      (∫ y, ∫ x, J (x, y)) ≤ ∫ y, B * ‖h y‖ := by
        apply integral_mono hJ.integral_prod_right (hh.norm.const_mul B)
        intro y
        change (∫ x, ‖h y‖ * Q (x, y)) ≤ B * ‖h y‖
        rw [integral_const_mul]
        exact (mul_le_mul_of_nonneg_left (hSlices y).2 (norm_nonneg _)).trans_eq
          (mul_comm _ _)
      _ = _ := integral_const_mul _ _
  refine ⟨hJ, hJ.prod_right_ae, ?_⟩
  exact spatialBound_one_of_nonnegative_integral hJ.integral_prod_left
    (fun x => integral_nonneg (fun y => hJn (x, y))) hIntegral

end HartreeF.WeightedRieszProduct
