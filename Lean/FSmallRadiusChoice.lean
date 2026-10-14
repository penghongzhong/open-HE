import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A simultaneous radius choice for the single-source fifth power and the
fourth-power contraction coefficient. All coefficients enter before choosing
the radius, so the self-map estimate does not depend circularly on a later
Lipschitz tolerance. -/
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.CriticalPathBall

theorem exists_small_fifth_power_radius (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ B / 8 ∧
      A * η ^ 4 ≤ 1 / 2 ∧ A * η ^ 5 ≤ η / 2 ∧ A * η ^ 5 ≤ B / 16 := by
  let η := min 1 (min (B / 8) (1 / (2 * (A + 1))))
  have hden : 0 < 2 * (A + 1) := by positivity
  have hη : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηB : η ≤ B / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hηA : η ≤ 1 / (2 * (A + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hmul : η * (2 * (A + 1)) ≤ 1 := (le_div_iff₀ hden).mp hηA
  have hAη : A * η ≤ 1 / 2 := by nlinarith
  have hpow : η ^ 4 ≤ η := by
    calc
      η ^ 4 = η ^ 3 * η := by ring
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right (pow_le_one₀ hη.le hη1) hη.le
      _ = η := one_mul η
  have hfour : A * η ^ 4 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hpow hA).trans hAη
  have hfive : A * η ^ 5 ≤ η / 2 := by
    have h := mul_le_mul_of_nonneg_right hfour hη.le
    nlinarith [h]
  refine ⟨η, hη, hη1, hηB, hfour, hfive, ?_⟩
  linarith

/-- The same radius may be chosen below the independently produced uniform
Lipschitz threshold. Shrinking preserves the fourth-power coefficient first,
and the fifth-power estimates are then re-derived at the smaller radius. -/
theorem exists_small_fifth_power_radius_below (A B ρ : ℝ) (hA : 0 ≤ A)
    (hB : 0 < B) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ρ ∧ η ≤ 1 ∧ η ≤ B / 8 ∧
      A * η ^ 4 ≤ 1 / 2 ∧ A * η ^ 5 ≤ η / 2 ∧ A * η ^ 5 ≤ B / 16 := by
  obtain ⟨r, hr, hr1, hrB, hr4, _, _⟩ := exists_small_fifth_power_radius A B hA hB
  let η := min r ρ
  have hη : 0 < η := lt_min hr hρ
  have hηr : η ≤ r := min_le_left _ _
  have hηB : η ≤ B / 8 := hηr.trans hrB
  have hfour : A * η ^ 4 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hηr 4) hA).trans hr4
  have hfive : A * η ^ 5 ≤ η / 2 := by
    have h := mul_le_mul_of_nonneg_right hfour hη.le
    nlinarith [h]
  refine ⟨η, hη, min_le_right _ _, hηr.trans hr1, hηB, hfour, hfive, ?_⟩
  linarith

end HartreeF.CriticalPathBall
