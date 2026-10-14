import FL10PartitionAssembly

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace HartreeF.TimePartition

theorem integral_norm_two_eq_lpNorm_pow {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖f t‖ ^ (2 : ℕ)) =
      lpNorm f 2 (volume.restrict (Icc a b)) ^ (2 : ℕ) := by
  have hn : 0 ≤ ∫ t in Icc a b, ‖f t‖ ^ (2 : ℕ) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hnorm := lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    hf.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  have hp : (fun t => ‖f t‖ ^ (2 : ℝ)) = (fun t => ‖f t‖ ^ (2 : ℕ)) := by
    funext t
    exact Real.rpow_natCast (‖f t‖) (2 : ℕ)
  rw [hp] at hnorm
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, hnorm]
  simpa only [one_div, Nat.cast_ofNat] using
    (Real.rpow_inv_natCast_pow hn (by decide : (2 : ℕ) ≠ 0)).symm

theorem intervalIntegrable_norm_two {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => ‖f t‖ ^ (2 : ℕ)) volume a b := by
  have h : IntegrableOn (fun t => ‖f t‖ ^ (2 : ℕ)) (Icc a b) :=
    hf.integrable_norm_pow (by decide)
  exact (show IntegrableOn (fun t => ‖f t‖ ^ (2 : ℕ)) (uIcc a b) by
    simpa only [uIcc_of_le hab] using h).intervalIntegrable

theorem lpNorm_two_pow_eq_sum_partition {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) (P : Partition a b) {f : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    lpNorm f 2 (volume.restrict (Icc a b)) ^ (2 : ℕ) =
      ∑ i : Fin P.count,
        lpNorm f 2 (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ^ (2 : ℕ) := by
  rw [← integral_norm_two_eq_lpNorm_pow hab hf,
    integral_eq_sum_partition hab P (intervalIntegrable_norm_two hab hf)]
  apply Finset.sum_congr rfl
  intro i _
  have hi : P.time i.castSucc ≤ P.time i.succ :=
    P.ordered (by exact_mod_cast Nat.le_succ i.val)
  exact integral_norm_two_eq_lpNorm_pow hi
    (hf.mono_measure (Measure.restrict_mono_set volume
      (Icc_subset_Icc (P.mem_interval i.castSucc).1 (P.mem_interval i.succ).2)))

theorem lpNorm_two_le_count_mul_piece_bound {E : Type*} [NormedAddCommGroup E]
    {a b C : ℝ} (hab : a ≤ b) (P : Partition a b) {f : ℝ → E}
    (hf : MemLp f 2 (volume.restrict (Icc a b))) (hC : 0 ≤ C)
    (hpieces : ∀ i : Fin P.count,
      lpNorm f 2 (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ≤ C) :
    lpNorm f 2 (volume.restrict (Icc a b)) ≤ (P.count : ℝ) * C := by
  have hn : (1 : ℝ) ≤ P.count := by exact_mod_cast P.positive
  apply (pow_le_pow_iff_left₀ lpNorm_nonneg (mul_nonneg (by positivity) hC)
    (by decide : (2 : ℕ) ≠ 0)).mp
  rw [lpNorm_two_pow_eq_sum_partition hab P hf]
  calc
    _ ≤ ∑ _i : Fin P.count, C ^ (2 : ℕ) :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ lpNorm_nonneg (hpieces i) _
    _ = (P.count : ℝ) * C ^ (2 : ℕ) := by simp
    _ ≤ (P.count : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (le_self_pow₀ hn (by decide : (2 : ℕ) ≠ 0)) (pow_nonneg hC _)
    _ = ((P.count : ℝ) * C) ^ (2 : ℕ) := (mul_pow _ _ _).symm

end HartreeF.TimePartition
