import Mathlib.Tactic

/-! One fixed smallness threshold controls every produced partition whose
integer length is bounded by N. This is finite real arithmetic, not a solver
or a partition premise. The PDE consumer produces the partition separately. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.CompactLongTimePerturbation

theorem exists_uniform_iteration_allowance {r D Cs : ℝ}
    (hr : 0 < r) (hD : 1 ≤ D) (hCs : 0 < Cs) (N : ℕ) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ (n : ℕ), n ≤ N → ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ epsilon0 →
        D^(n+1)*epsilon ≤ r/2 ∧
        (n : ℝ)*D^n*epsilon ≤ C*epsilon ∧
        Cs*(n : ℝ)*D^n*epsilon ≤ C*epsilon := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  let denominator := 2*D^(N+1)+1
  have hden : 0 < denominator := by dsimp [denominator]; positivity
  let epsilon0 := min 1 (r/denominator)
  let A := ((N : ℝ)+1)*D^N
  let C := (Cs+1)*A
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := mul_pos (by linarith only [hCs]) hA
  refine ⟨epsilon0,C,lt_min zero_lt_one (div_pos hr hden),min_le_left _ _,hC,?_⟩
  intro n hn epsilon heps hepsSmall
  have hsmallN : D^(N+1)*epsilon ≤ r/2 := by
    have hle : epsilon ≤ r/denominator := hepsSmall.trans (min_le_right _ _)
    have hm := (le_div_iff₀ hden).mp hle
    dsimp only [denominator] at hm
    nlinarith
  have hsmall : D^(n+1)*epsilon ≤ r/2 :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.succ_le_succ hn)) heps).trans hsmallN
  have hfac : (n : ℝ)*D^n ≤ A := by
    have hn' : (n : ℝ) ≤ (N : ℝ)+1 :=
      (show (n : ℝ) ≤ N by exact_mod_cast hn).trans (le_add_of_nonneg_right zero_le_one)
    exact mul_le_mul hn' (pow_le_pow_right₀ hD hn) (pow_nonneg hDpos.le _) (by positivity)
  have hfacC : (n : ℝ)*D^n ≤ C :=
    hfac.trans (by dsimp [C]; nlinarith only [hA, hCs])
  have hsizeC : Cs*(n : ℝ)*D^n ≤ C := by
    calc
      _ = Cs*((n : ℝ)*D^n) := by ring
      _ ≤ Cs*A := mul_le_mul_of_nonneg_left hfac hCs.le
      _ ≤ (Cs+1)*A := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hA.le
      _ = C := rfl
  exact ⟨hsmall,mul_le_mul_of_nonneg_right hfacC heps,
    mul_le_mul_of_nonneg_right hsizeC heps⟩

#print axioms exists_uniform_iteration_allowance
end HartreeF.CompactLongTimePerturbation
