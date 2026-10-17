import FEnergyGradientNorm

/-! Actual scalar identities for translated Hardy-Sobolev interpolation.
No weighted estimate, Hardy statement, or Hartree conclusion is an input. -/
noncomputable section
set_option autoImplicit false
namespace HartreeF.WeightedHardy
open EnergySpace

def weightedDensity (s : ℝ) (y : V) (f : V → ℂ) (x : V) : ℝ :=
  ‖f x‖ ^ (6 - 4 * s) / ‖x - y‖ ^ (2 * s)

def weightedConstant (K s N : ℝ) : ℝ :=
  4 ^ s * K ^ (1 - s) * N ^ (6 - 4 * s)

theorem weightedDensity_nonneg (s : ℝ) (y : V) (f : V → ℂ) (x : V) :
    0 ≤ weightedDensity s y f x :=
  div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem scalar_weight_identity {a d s : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hs1 : s < 1) :
    (d⁻¹ * a) ^ (2 * s) * a ^ (6 * (1 - s)) =
      a ^ (6 - 4 * s) / d ^ (2 * s) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hd) ha, Real.inv_rpow hd]
  have hsum : 2 * s + 6 * (1 - s) = 6 - 4 * s := by ring
  have hadd := Real.rpow_add' ha (by linarith : 2 * s + 6 * (1 - s) ≠ 0)
  rw [hsum] at hadd
  rw [div_eq_mul_inv, hadd]
  ring

/-- The coefficient remains valid for K=0 and N=0; no division by them. -/
theorem interpolation_constant {K N s : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hs1 : s < 1) :
    (2 * N) ^ (2 * s) * (K ^ ((6 : ℝ)⁻¹) * N) ^ (6 * (1 - s)) =
      weightedConstant K s N := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN,
    Real.mul_rpow (Real.rpow_nonneg hK _) hN]
  have htwo : (2 : ℝ) ^ (2 * s) = 4 ^ s := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hKpow : (K ^ ((6 : ℝ)⁻¹)) ^ (6 * (1 - s)) = K ^ (1 - s) := by
    rw [← Real.rpow_mul hK]
    congr 1
    ring
  have hsum : 2 * s + 6 * (1 - s) = 6 - 4 * s := by ring
  have hadd := Real.rpow_add' hN (by linarith : 2 * s + 6 * (1 - s) ≠ 0)
  rw [hsum] at hadd
  rw [htwo, hKpow]
  unfold weightedConstant
  rw [hadd]
  ring

end HartreeF.WeightedHardy
