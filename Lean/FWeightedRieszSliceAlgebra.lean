import FWeightedHardyAlgebra

/-! STATIC-ONLY CANDIDATE. No native compilation has been run.
Pointwise identities retain the actual distance-zero convention of Real.rpow. -/
noncomputable section
set_option autoImplicit false
namespace HartreeF.WeightedRieszProduct
open EnergySpace WeightedHardy

/-- The exact derivative-kernel slice. -/
def derivativeSlice (α : ℝ) (u : EnergyState) (y x : V) : ℝ :=
  ‖x - y‖ ^ (α - 4) * ‖energyValue u x‖ ^ (α + 2)

/-- The exact potential-kernel slice with an actual coordinate gradient. -/
def localGradientSlice (α : ℝ) (u : EnergyState) (j : Fin 3) (y x : V) : ℝ :=
  ‖x - y‖ ^ (α - 3) * ‖energyValue u x‖ ^ (α + 1) * ‖energyGradient j u x‖

def derivativeConstant (K α N : ℝ) : ℝ :=
  4 ^ ((4 - α) / 2) * K ^ ((α - 2) / 2) * N ^ (2 * α - 2)

def localGradientConstant (K α N : ℝ) : ℝ :=
  2 ^ (3 - α) * K ^ ((α - 2) / 2) * N ^ (2 * α - 2)

theorem derivativeSlice_nonneg (α : ℝ) (u : EnergyState) (y x : V) :
    0 ≤ derivativeSlice α u y x := by
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem localGradientSlice_nonneg (α : ℝ) (u : EnergyState) (j : Fin 3) (y x : V) :
    0 ≤ localGradientSlice α u j y x := by
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)

/-- Split only the value power. All singular factors retain their literal meaning. -/
theorem derivativeSlice_split {α : ℝ} (hα : 2 ≤ α) (u : EnergyState) (y x : V) :
    derivativeSlice α u y x = ‖energyValue u x‖ ^ (4 - α) *
      weightedDensity ((4 - α) / 2) y (energyValue u) x := by
  have ha := norm_nonneg (energyValue u x)
  have hd := norm_nonneg (x - y)
  have he : (4 - α) + (2 * α - 2) = α + 2 := by ring
  have hp := Real.rpow_add' ha (by linarith : (4 - α) + (2 * α - 2) ≠ 0)
  rw [he] at hp
  unfold derivativeSlice weightedDensity
  rw [show 6 - 4 * ((4 - α) / 2) = 2 * α - 2 by ring,
    show 2 * ((4 - α) / 2) = 4 - α by ring,
    show α - 4 = -(4 - α) by ring, Real.rpow_neg hd, hp]
  ring

/-- The square root of the genuine weighted Hardy density. No zero division is used. -/
theorem weightedDensity_half (s : ℝ) (y : V) (u : EnergyState) (x : V) :
    weightedDensity s y (energyValue u) x ^ (1 / 2 : ℝ) =
      ‖energyValue u x‖ ^ (3 - 2 * s) / ‖x - y‖ ^ s := by
  unfold weightedDensity
  rw [Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg (energyValue u x)),
    ← Real.rpow_mul (norm_nonneg (x - y))]
  rw [show (6 - 4 * s) * (1 / 2) = 3 - 2 * s by ring,
    show (2 * s) * (1 / 2) = s by ring]

theorem localGradientSlice_split {α : ℝ} (hα : 2 ≤ α)
    (u : EnergyState) (j : Fin 3) (y x : V) :
    localGradientSlice α u j y x = ‖energyValue u x‖ ^ (4 - α) *
      (weightedDensity (3 - α) y (energyValue u) x ^ (1 / 2 : ℝ) *
        ‖energyGradient j u x‖) := by
  have ha := norm_nonneg (energyValue u x)
  have hd := norm_nonneg (x - y)
  have he : (4 - α) + (2 * α - 3) = α + 1 := by ring
  have hp := Real.rpow_add' ha (by linarith : (4 - α) + (2 * α - 3) ≠ 0)
  rw [he] at hp
  rw [weightedDensity_half, show 3 - 2 * (3 - α) = 2 * α - 3 by ring]
  unfold localGradientSlice
  rw [show α - 3 = -(3 - α) by ring, Real.rpow_neg hd, hp]
  ring

theorem derivative_weightedConstant (K α N : ℝ) :
    weightedConstant K ((4 - α) / 2) N = derivativeConstant K α N := by
  simp only [weightedConstant, derivativeConstant,
    show 1 - (4 - α) / 2 = (α - 2) / 2 by ring,
    show 6 - 4 * ((4 - α) / 2) = 2 * α - 2 by ring]

/-- The Cauchy constant, valid also when K or N vanishes. -/
theorem local_gradient_weightedConstant {K α N : ℝ}
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hα : 2 ≤ α) :
    weightedConstant K (3 - α) N ^ (1 / 2 : ℝ) * N =
      localGradientConstant K α N := by
  unfold weightedConstant localGradientConstant
  rw [Real.mul_rpow
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _) (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hN _),
    Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _) (Real.rpow_nonneg hK _),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← Real.rpow_mul hK, ← Real.rpow_mul hN]
  have hfour : (4 : ℝ) ^ ((3 - α) * (1 / 2)) = 2 ^ (3 - α) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hfour, show (1 - (3 - α)) * (1 / 2) = (α - 2) / 2 by ring,
    show (6 - 4 * (3 - α)) * (1 / 2) = 2 * α - 3 by ring]
  have hn := Real.rpow_add' hN (by linarith : (2 * α - 3) + 1 ≠ 0)
  rw [Real.rpow_one, show (2 * α - 3) + 1 = 2 * α - 2 by ring] at hn
  rw [mul_assoc, ← hn]

end HartreeF.WeightedRieszProduct
