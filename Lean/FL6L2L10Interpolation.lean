import FEnergyCriticalTimeConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.FreeTimeDecay

/-- The exact polynomial form of L6 ≤ L2^(1/6)L10^(5/6), obtained by Holder. -/
theorem l6_twelfth_le_l2_sq_mul_l10_tenth {f : Space → ℂ}
    (h2 : MemLp f 2 volume) (h10 : MemLp f 10 volume) :
    (eLpNorm f 6 volume).toReal^12 ≤
      (eLpNorm f 2 volume).toReal^2*(eLpNorm f 10 volume).toReal^10 := by
  have hm := h2.aestronglyMeasurable
  have hp : AEStronglyMeasurable (fun x => ‖f x‖^(5:ℝ)) volume :=
    (hm.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hh := eLpNorm_smul_le_mul_eLpNorm (p:=2) (q:=2) (r:=1) hm.norm hp
  have he : ((fun x => ‖f x‖) • (fun x => ‖f x‖^(5:ℝ))) = (fun x => ‖f x‖^(6:ℝ)) := by
    funext x
    change ‖f x‖*‖f x‖^(5:ℝ)=‖f x‖^(6:ℝ)
    simp only [show (5:ℝ)=(5:ℕ) by norm_num,
      show (6:ℝ)=(6:ℕ) by norm_num, Real.rpow_natCast]
    ring
  rw [he, eLpNorm_norm_rpow f hm (by norm_num : (0:ℝ)<6),
    eLpNorm_norm f hm, eLpNorm_norm_rpow f hm (by norm_num : (0:ℝ)<5)] at hh
  norm_num only [ENNReal.ofReal_ofNat, one_mul, show (2:ℝ≥0∞)*5=10 by norm_num] at hh
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top h2.eLpNorm_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h10.eLpNorm_ne_top)) hh
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hr
  have hs := pow_le_pow_left₀ (by positivity) hr 2
  simpa only [show (6:ℝ)=(6:ℕ) by norm_num, show (5:ℝ)=(5:ℕ) by norm_num,
    Real.rpow_natCast, mul_pow, ← pow_mul, show (6:ℕ)*2=12 by norm_num,
    show (5:ℕ)*2=10 by norm_num] using hs

#print axioms l6_twelfth_le_l2_sq_mul_l10_tenth
end HartreeF.FreeTimeDecay
