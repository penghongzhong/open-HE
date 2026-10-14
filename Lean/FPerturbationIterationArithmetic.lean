import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.FinitePerturbation

/-- The explicit recurrence multiplier retains the free and forced graph constants. -/
def iterationMultiplier (Cf Q : ℝ) : ℝ := 2*Cf+2*Q+1

theorem iterationMultiplier_one_le {Cf Q : ℝ} (hf : 0 ≤ Cf) (hq : 0 ≤ Q) :
    1 ≤ iterationMultiplier Cf Q := by unfold iterationMultiplier; linarith

/-- Both the contraction seed and the next true terminal error are bounded. -/
theorem iteration_seed_bounds {Cf Q epsilon r delta e : ℝ} {i N : ℕ}
    (hf : 0 ≤ Cf) (hq : 0 ≤ Q) (heps : 0 ≤ epsilon)
    (hi : i < N) (hd : delta ≤ iterationMultiplier Cf Q ^ i * epsilon)
    (he : e ≤ epsilon)
    (hsmall : iterationMultiplier Cf Q ^ (N+1) * epsilon ≤ r/2) :
    Cf*delta+Q*e ≤ r/2 ∧
    2*(Cf*delta+Q*e) ≤ iterationMultiplier Cf Q ^ (i+1)*epsilon := by
  let D := iterationMultiplier Cf Q
  have hD : 1 ≤ D := iterationMultiplier_one_le hf hq
  have hp : (1 : ℝ) ≤ D^i := one_le_pow₀ hD
  have hep : epsilon ≤ D^i*epsilon := by nlinarith
  have hs : Cf*delta+Q*e ≤ (Cf+Q)*(D^i*epsilon) :=
    (add_le_add (mul_le_mul_of_nonneg_left hd hf)
      (mul_le_mul_of_nonneg_left (he.trans hep) hq)).trans_eq (by ring)
  have hcoeff : 2*(Cf+Q) ≤ D := by dsimp [D,iterationMultiplier]; linarith
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hn' : 0 ≤ D^i*epsilon := by positivity
  have hnext : 2*(Cf*delta+Q*e) ≤ D^(i+1)*epsilon := by
    calc
      _ ≤ 2*((Cf+Q)*(D^i*epsilon)) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = (2*(Cf+Q))*(D^i*epsilon) := by ring
      _ ≤ D*(D^i*epsilon) := mul_le_mul_of_nonneg_right hcoeff hn'
      _ = D^(i+1)*epsilon := by rw [pow_succ]; ring
  have hpow : D^(i+1)*epsilon ≤ D^(N+1)*epsilon :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (by omega)) heps
  have hnonneg : 0 ≤ D^(i+1)*epsilon := by positivity
  refine ⟨?_,hnext⟩
  have hseed : Cf*delta+Q*e ≤ D^(i+1)*epsilon := by linarith
  exact hseed.trans (hpow.trans hsmall)

theorem iteration_piece_size_bound {D epsilon delta e C : ℝ} {i N : ℕ}
    (hD : 1 ≤ D) (heps : 0 ≤ epsilon) (hC : 0 ≤ C) (hi : i ≤ N)
    (hd : delta ≤ D^i*epsilon) (he : e ≤ epsilon) :
    C*(delta+e) ≤ 2*C*D^N*epsilon := by
  have hp : D^i*epsilon ≤ D^N*epsilon :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hi) heps
  have heN : epsilon ≤ D^N*epsilon := by nlinarith [one_le_pow₀ hD (n:=N)]
  exact (mul_le_mul_of_nonneg_left (add_le_add (hd.trans hp) (he.trans heN)) hC).trans_eq (by ring)

end HartreeF.FinitePerturbation
