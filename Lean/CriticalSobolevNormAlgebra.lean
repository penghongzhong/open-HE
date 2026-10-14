import RealSobolevApproximation

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace HartreeF.CriticalSobolevNormAlgebra

/-- Extract the exact sixth-root coefficient from a nonnegative sixth-power bound. -/
theorem sixth_root_bound {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hpow : a ^ (6 : ℕ) ≤ K * b ^ (6 : ℕ)) :
    a ≤ K ^ (1 / 6 : ℝ) * b := by
  apply (pow_le_pow_iff_left₀ ha
    (mul_nonneg (Real.rpow_nonneg hK _) hb) (by decide : (6 : ℕ) ≠ 0)).mp
  rw [mul_pow]
  have hroot : (K ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = K := by
    simpa [one_div] using Real.rpow_inv_natCast_pow hK (by decide : (6 : ℕ) ≠ 0)
  rw [hroot]
  exact hpow

/-- The critical saturation estimate after cancellation of the two-fifths power.
All powers with fractional exponents are real powers, including at zero. -/
theorem critical_saturation_numeric {a b K N : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hpow : a ^ (6 : ℕ) ≤ K * b ^ (6 : ℕ))
    (hgrad : b ≤ (5 / 3 : ℝ) * a ^ (2 / 5 : ℝ) * N) :
    a ^ (3 / 5 : ℝ) ≤ ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ)) * N := by
  by_cases ha0 : a = 0
  · subst a
    rw [Real.zero_rpow (by norm_num : (3 / 5 : ℝ) ≠ 0)]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hK _)) hN
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hcancel : 0 < a ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos ha_pos _
  have hsplit : a ^ (2 / 5 : ℝ) * a ^ (3 / 5 : ℝ) = a := by
    rw [← Real.rpow_add ha_pos]
    norm_num
  apply (mul_le_mul_iff_right₀ hcancel).mp
  calc
    a ^ (2 / 5 : ℝ) * a ^ (3 / 5 : ℝ) = a := hsplit
    _ ≤ K ^ (1 / 6 : ℝ) * b := sixth_root_bound ha hb hK hpow
    _ ≤ K ^ (1 / 6 : ℝ) * ((5 / 3 : ℝ) * a ^ (2 / 5 : ℝ) * N) :=
      mul_le_mul_of_nonneg_left hgrad (Real.rpow_nonneg hK _)
    _ = a ^ (2 / 5 : ℝ) * (((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ)) * N) := by ring

open SobolevStretch StationarySelfTest

/-- The integral Sobolev interface supplies the exact sixth-power norm bound. -/
theorem sobolev_norm_sixth_power_bound {K : ℝ} (hSob : OrdinarySobolev K)
    {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) (hw : HasWeakGradient f G) :
    (eLpNorm f 6 volume).toReal ^ (6 : ℕ) ≤
      K * (eLpNorm G 2 volume).toReal ^ (6 : ℕ) := by
  have h := real_sobolev_integral_bound hSob hf hG hw
  rw [norm_moment_eq_eLpNorm (by decide : (6 : ℕ) ≠ 0) hf,
    norm_moment_eq_eLpNorm (by decide : (2 : ℕ) ≠ 0) hG] at h
  simpa [← pow_mul] using h

/-- Exact norm consequence for an already established L6 function and L2 weak gradient.
The gradient estimate is an explicit premise; no conclusion membership is assumed. -/
theorem critical_saturation_norm_bound {K N : ℝ} (hSob : OrdinarySobolev K)
    {f : Space → ℝ} {G : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume) (hw : HasWeakGradient f G)
    (hN : 0 ≤ N)
    (hgrad : (eLpNorm G 2 volume).toReal ≤
      (5 / 3 : ℝ) * ((eLpNorm f 6 volume).toReal) ^ (2 / 5 : ℝ) * N) :
    ((eLpNorm f 6 volume).toReal) ^ (3 / 5 : ℝ) ≤
      ((5 / 3 : ℝ) * K ^ (1 / 6 : ℝ)) * N := by
  exact critical_saturation_numeric ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hSob.nonneg hN (sobolev_norm_sixth_power_bound hSob hf hG hw) hgrad

end HartreeF.CriticalSobolevNormAlgebra

#print axioms HartreeF.CriticalSobolevNormAlgebra.sixth_root_bound
#print axioms HartreeF.CriticalSobolevNormAlgebra.critical_saturation_numeric
#print axioms HartreeF.CriticalSobolevNormAlgebra.sobolev_norm_sixth_power_bound
#print axioms HartreeF.CriticalSobolevNormAlgebra.critical_saturation_norm_bound
