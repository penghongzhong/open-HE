import PowerDensityDifference

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ForcingContinuity
open ForcingDomain

/-- The complex radial power map has a quantitative difference bound, including phase. -/
theorem norm_radialPower_sub_le {s : ℝ} (hs : 1 ≤ s) (u v : ℂ) :
    ‖‖u‖ ^ s • u - ‖v‖ ^ s • v‖ ≤
      (s+1) * (‖u‖ ^ s + ‖v‖ ^ s) * ‖u-v‖ := by
  have ordered : ∀ a b : ℂ, ‖b‖ ≤ ‖a‖ →
      ‖‖a‖ ^ s • a - ‖b‖ ^ s • b‖ ≤
        (s+1) * (‖a‖ ^ s + ‖b‖ ^ s) * ‖a-b‖ := by
    intro a b hab
    have hs0 : 0 ≤ s := by linarith
    have hsa : 0 ≤ ‖a‖^s := Real.rpow_nonneg (norm_nonneg _) _
    have hsb : 0 ≤ ‖b‖^s := Real.rpow_nonneg (norm_nonneg _) _
    have hex : ‖a‖ ^ s • a - ‖b‖ ^ s • b =
        ‖a‖^s • (a-b) + (‖a‖^s-‖b‖^s) • b := by module
    have habp : (‖a‖^(s-1)+‖b‖^(s-1))*‖b‖ ≤ ‖a‖^s+‖b‖^s := by
      calc
        _ ≤ ‖a‖^(s-1)*‖a‖+‖b‖^(s-1)*‖b‖ := by
          rw [add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hab
            (Real.rpow_nonneg (norm_nonneg a) _)) le_rfl
        _ = _ := by
          rw [← Real.rpow_add_one' (norm_nonneg a) (by linarith : s-1+1 ≠ 0),
            ← Real.rpow_add_one' (norm_nonneg b) (by linarith : s-1+1 ≠ 0)]
          congr 2 <;> ring
    rw [hex]
    calc
      _ ≤ ‖‖a‖^s • (a-b)‖ + ‖(‖a‖^s-‖b‖^s) • b‖ := norm_add_le _ _
      _ = ‖a‖^s*‖a-b‖ + |‖a‖^s-‖b‖^s| *‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsa]
      _ ≤ ‖a‖^s*‖a-b‖ +
          (s*(‖a‖^(s-1)+‖b‖^(s-1))*‖a-b‖)*‖b‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (HartreeEnergy.abs_norm_rpow_sub_norm_rpow_le hs a b) (norm_nonneg b))
      _ = (‖a‖^s+s*((‖a‖^(s-1)+‖b‖^(s-1))*‖b‖))*‖a-b‖ := by ring
      _ ≤ (‖a‖^s+s*(‖a‖^s+‖b‖^s))*‖a-b‖ := by gcongr
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith
  rcases le_total ‖v‖ ‖u‖ with h | h
  · exact ordered u v h
  · simpa only [norm_sub_rev, add_comm] using ordered v u h

/-- Actual local Hartree factor difference for every positive alpha. -/
theorem localFactor_pointwise_difference {α : ℝ} (hα : 0 < α)
    (u v : Space → ℂ) (x : Space) :
    ‖localFactor α u x-localFactor α v x‖ ≤
      (2+α)*(‖u x‖^(1+α)+‖v x‖^(1+α))*‖u x-v x‖ := by
  simpa only [localFactor, show 1+α+1 = 2+α by ring] using
    norm_radialPower_sub_le (show 1 ≤ 1+α by linarith) (u x) (v x)

#print axioms norm_radialPower_sub_le
#print axioms localFactor_pointwise_difference
end HartreeF.ForcingContinuity
