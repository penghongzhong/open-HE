import FL10TimePartition

/-! Native assembly on a produced finite partition. Bounds on the genuine
restrictions control the original whole-interval L10 norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace HartreeF.TimePartition

theorem integral_eq_sum_partition {a b : ℝ} (hab : a ≤ b) (P : Partition a b)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, g t) =
      ∑ i : Fin P.count, ∫ t in P.time i.castSucc..P.time i.succ, g t := by
  let f : Fin (P.count + 1) → ℝ := fun i => ∫ t in a..P.time i, g t
  have hpiece (i : Fin P.count) :
      (∫ t in P.time i.castSucc..P.time i.succ, g t) = f i.succ - f i.castSucc :=
    (intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_to_member hab hg (P.mem_interval i.succ))
      (intervalIntegrable_to_member hab hg (P.mem_interval i.castSucc))).symm
  simp_rw [hpiece]
  rw [Finset.sum_sub_distrib]
  have hs := Fin.sum_univ_succ f
  have hl := Fin.sum_univ_castSucc f
  have hf0 : f 0 = 0 := by simp [f, P.left]
  have hfl : f (Fin.last P.count) = ∫ t in a..b, g t := by simp [f, P.right]
  linarith

theorem lpNorm_ten_pow_eq_sum_partition {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) (P : Partition a b) {f : ℝ → E}
    (hf : MemLp f 10 (volume.restrict (Icc a b))) :
    lpNorm f 10 (volume.restrict (Icc a b)) ^ (10 : ℕ) =
      ∑ i : Fin P.count,
        lpNorm f 10 (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ^ (10 : ℕ) := by
  rw [← integral_norm_ten_eq_lpNorm_pow hab hf,
    integral_eq_sum_partition hab P (intervalIntegrable_norm_ten hab hf)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : P.time i.castSucc ≤ P.time i.succ :=
    P.ordered (by exact_mod_cast Nat.le_succ i.val)
  exact integral_norm_ten_eq_lpNorm_pow hi
    (hf.mono_measure (Measure.restrict_mono_set volume
      (Icc_subset_Icc (P.mem_interval i.castSucc).1 (P.mem_interval i.succ).2)))

theorem lpNorm_le_count_mul_piece_bound {E : Type*} [NormedAddCommGroup E]
    {a b C : ℝ} (hab : a ≤ b) (P : Partition a b) {f : ℝ → E}
    (hf : MemLp f 10 (volume.restrict (Icc a b))) (hC : 0 ≤ C)
    (hpieces : ∀ i : Fin P.count,
      lpNorm f 10 (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ≤ C) :
    lpNorm f 10 (volume.restrict (Icc a b)) ≤ (P.count : ℝ) * C := by
  have hn : (1 : ℝ) ≤ P.count := by exact_mod_cast P.positive
  apply (pow_le_pow_iff_left₀ lpNorm_nonneg (mul_nonneg (by positivity) hC)
    (by decide : (10 : ℕ) ≠ 0)).mp
  rw [lpNorm_ten_pow_eq_sum_partition hab P hf]
  calc
    _ ≤ ∑ _i : Fin P.count, C ^ (10 : ℕ) :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ lpNorm_nonneg (hpieces i) _
    _ = (P.count : ℝ) * C ^ (10 : ℕ) := by simp
    _ ≤ (P.count : ℝ) ^ (10 : ℕ) * C ^ (10 : ℕ) :=
      mul_le_mul_of_nonneg_right (le_self_pow₀ hn (by decide : (10 : ℕ) ≠ 0)) (pow_nonneg hC _)
    _ = ((P.count : ℝ) * C) ^ (10 : ℕ) := (mul_pow _ _ _).symm

#print axioms integral_eq_sum_partition
#print axioms lpNorm_ten_pow_eq_sum_partition
#print axioms lpNorm_le_count_mul_piece_bound
end HartreeF.TimePartition
