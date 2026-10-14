import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Genuine square tails and higher real powers

Source-only draft. The caller supplies genuine square summability; no analytic
interface or family-selection hypothesis is introduced here. All power estimates
are valid at exponent two and at zero tail, with no division by a tail norm.
-/

noncomputable section

open Filter Finset
open scoped Topology

namespace HartreeF.R2SquareTail

/-- The nonnegative square tail of a sequence, indexed by the first retained label. -/
def squareTail (a : ℕ → ℝ) (L : ℕ) : ℝ :=
  Real.sqrt (∑' k : ℕ, a (L + k) ^ 2)

variable {a : ℕ → ℝ}

/-- This premise certifies that the defining tail sum is a genuine convergent sum. -/
theorem summable_tail_sq (hs : Summable (fun j => a j ^ 2)) (L : ℕ) :
    Summable (fun k : ℕ => a (L + k) ^ 2) := by
  simpa only [Nat.add_comm] using (summable_nat_add_iff L).2 hs

theorem squareTail_nonneg (a : ℕ → ℝ) (L : ℕ) : 0 ≤ squareTail a L :=
  Real.sqrt_nonneg _

theorem squareTail_sq (a : ℕ → ℝ) (L : ℕ) :
    squareTail a L ^ 2 = ∑' k : ℕ, a (L + k) ^ 2 := by
  exact Real.sq_sqrt (tsum_nonneg (fun k => sq_nonneg (a (L + k))))

set_option backward.isDefEq.respectTransparency false in
/-- The proof uses the genuine partial-sum limit supplied by `hs`. -/
theorem squareTail_tendsto_zero (hs : Summable (fun j => a j ^ 2)) :
    Tendsto (squareTail a) atTop (𝓝 0) := by
  have htail : (fun L : ℕ => ∑' k : ℕ, a (L + k) ^ 2) =
      (fun L : ℕ => (∑' j : ℕ, a j ^ 2) - ∑ j ∈ range L, a j ^ 2) := by
    funext L
    have hsum : (∑ j ∈ range L, a j ^ 2) +
        (∑' k : ℕ, a (L + k) ^ 2) = ∑' j : ℕ, a j ^ 2 := by
      simpa only [Nat.add_comm] using hs.sum_add_tsum_nat_add L
    linarith
  have ht : Tendsto (fun L : ℕ => ∑' k : ℕ, a (L + k) ^ 2) atTop (𝓝 0) := by
    rw [htail]
    have hlim := (tendsto_const_nhds (x := ∑' j : ℕ, a j ^ 2)).sub
      hs.hasSum.tendsto_sum_nat
    rw [sub_self] at hlim
    exact hlim
  change Tendsto (fun L : ℕ => Real.sqrt (∑' k : ℕ, a (L + k) ^ 2)) atTop (𝓝 0)
  simpa only [Real.sqrt_zero] using ht.sqrt

theorem le_squareTail (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {L j : ℕ} (hLj : L ≤ j) :
    a j ≤ squareTail a L := by
  have hterm := (summable_tail_sq hs L).le_tsum (j - L)
    (fun k _ => sq_nonneg (a (L + k)))
  rw [Nat.add_sub_of_le hLj, ← squareTail_sq a L] at hterm
  exact (sq_le_sq₀ (ha j) (squareTail_nonneg a L)).mp hterm

/-- Zero square tail forces every retained nonnegative term to vanish. -/
theorem eq_zero_of_squareTail_eq_zero (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {L j : ℕ}
    (hzero : squareTail a L = 0) (hLj : L ≤ j) : a j = 0 := by
  have hle := le_squareTail ha hs hLj
  rw [hzero] at hle
  exact le_antisymm hle (ha j)

/-- No order assumption on the endpoints is needed: an empty interval has sum zero. -/
theorem sum_Ico_sq_le_squareTail_sq (hs : Summable (fun j => a j ^ 2))
    (L J : ℕ) :
    (∑ j ∈ Ico L J, a j ^ 2) ≤ squareTail a L ^ 2 := by
  rw [sum_Ico_eq_sum_range, squareTail_sq]
  exact Summable.sum_le_tsum (range (J - L))
    (fun k _ => sq_nonneg (a (L + k))) (summable_tail_sq hs L)

/-- Nonnegative additivity of real powers includes both `x = 0` and `m = 2`. -/
private theorem rpow_eq_sq_mul_rpow {x m : ℝ} (hx : 0 ≤ x) (hm : 2 ≤ m) :
    x ^ m = x ^ 2 * x ^ (m - 2) := by
  calc
    x ^ m = x ^ ((2 : ℝ) + (m - 2)) := by congr 1; ring
    _ = x ^ (2 : ℝ) * x ^ (m - 2) :=
      Real.rpow_add_of_nonneg hx (by norm_num) (sub_nonneg.mpr hm)
    _ = x ^ 2 * x ^ (m - 2) := by rw [Real.rpow_ofNat]

private theorem rpow_le_sq_mul_squareTail_rpow (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {m : ℝ} (hm : 2 ≤ m)
    {L j : ℕ} (hLj : L ≤ j) :
    a j ^ m ≤ a j ^ 2 * squareTail a L ^ (m - 2) := by
  rw [rpow_eq_sq_mul_rpow (ha j) hm]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (ha j) (le_squareTail ha hs hLj) (sub_nonneg.mpr hm))
    (sq_nonneg (a j))

/-- A bound for an arbitrary finite subset of the shifted tail. -/
theorem sum_tail_rpow_le_squareTail_rpow (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {m : ℝ} (hm : 2 ≤ m)
    (L : ℕ) (s : Finset ℕ) :
    (∑ k ∈ s, a (L + k) ^ m) ≤ squareTail a L ^ m := by
  have hsq : (∑ k ∈ s, a (L + k) ^ 2) ≤ squareTail a L ^ 2 := by
    rw [squareTail_sq]
    exact Summable.sum_le_tsum s (fun k _ => sq_nonneg (a (L + k)))
      (summable_tail_sq hs L)
  calc
    (∑ k ∈ s, a (L + k) ^ m) ≤
        ∑ k ∈ s, a (L + k) ^ 2 * squareTail a L ^ (m - 2) := by
      exact Finset.sum_le_sum (fun k _ =>
        rpow_le_sq_mul_squareTail_rpow ha hs hm (Nat.le_add_right L k))
    _ = (∑ k ∈ s, a (L + k) ^ 2) * squareTail a L ^ (m - 2) :=
      (Finset.sum_mul s (fun k => a (L + k) ^ 2) _).symm
    _ ≤ squareTail a L ^ 2 * squareTail a L ^ (m - 2) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (squareTail_nonneg a L) _)
    _ = squareTail a L ^ m :=
      (rpow_eq_sq_mul_rpow (squareTail_nonneg a L) hm).symm

theorem sum_Ico_rpow_le_squareTail_rpow (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {m : ℝ} (hm : 2 ≤ m)
    (L J : ℕ) :
    (∑ j ∈ Ico L J, a j ^ m) ≤ squareTail a L ^ m := by
  rw [sum_Ico_eq_sum_range]
  exact sum_tail_rpow_le_squareTail_rpow ha hs hm L (range (J - L))

/-- Higher tail powers really are summable; this precedes the `tsum` bound. -/
theorem summable_tail_rpow (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {m : ℝ} (hm : 2 ≤ m) (L : ℕ) :
    Summable (fun k : ℕ => a (L + k) ^ m) := by
  exact summable_of_sum_le (fun k => Real.rpow_nonneg (ha (L + k)) m)
    (fun s => sum_tail_rpow_le_squareTail_rpow ha hs hm L s)

theorem tsum_tail_rpow_le_squareTail_rpow (ha : ∀ j, 0 ≤ a j)
    (hs : Summable (fun j => a j ^ 2)) {m : ℝ} (hm : 2 ≤ m) (L : ℕ) :
    (∑' k : ℕ, a (L + k) ^ m) ≤ squareTail a L ^ m := by
  exact (summable_tail_rpow ha hs hm L).tsum_le_of_sum_le
    (fun s => sum_tail_rpow_le_squareTail_rpow ha hs hm L s)

#print axioms squareTail_tendsto_zero
#print axioms sum_tail_rpow_le_squareTail_rpow
#print axioms tsum_tail_rpow_le_squareTail_rpow

end HartreeF.R2SquareTail
