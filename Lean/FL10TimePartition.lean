import FIntegralTimePartition
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Quantitative partition of an actual L10 time field, including its exact
Bochner norm and the norm of every genuine interval restriction. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open Set MeasureTheory
open scoped ENNReal
namespace HartreeF.TimePartition

theorem integral_norm_ten_eq_lpNorm_pow {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → E}
    (hf : MemLp f 10 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖f t‖ ^ (10 : ℕ)) =
      lpNorm f 10 (volume.restrict (Icc a b)) ^ (10 : ℕ) := by
  have hn : 0 ≤ ∫ t in Icc a b, ‖f t‖ ^ (10 : ℕ) :=
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hnorm := lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num : (10 : ℝ≥0∞) ≠ 0) (by norm_num : (10 : ℝ≥0∞) ≠ ∞)
    hf.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat] at hnorm
  have hp : (fun t => ‖f t‖ ^ (10 : ℝ)) = (fun t => ‖f t‖ ^ (10 : ℕ)) := by
    funext t
    exact Real.rpow_natCast (‖f t‖) (10 : ℕ)
  rw [hp] at hnorm
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, hnorm]
  simpa only [one_div, Nat.cast_ofNat] using
    (Real.rpow_inv_natCast_pow hn (by decide : (10 : ℕ) ≠ 0)).symm

theorem intervalIntegrable_norm_ten {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → E}
    (hf : MemLp f 10 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => ‖f t‖ ^ (10 : ℕ)) volume a b := by
  have h : IntegrableOn (fun t => ‖f t‖ ^ (10 : ℕ)) (Icc a b) :=
    hf.integrable_norm_pow (by decide)
  exact (show IntegrableOn (fun t => ‖f t‖ ^ (10 : ℕ)) (uIcc a b) by
    simpa only [uIcc_of_le hab] using h).intervalIntegrable

theorem exists_partition_small_L10 {E : Type*} [NormedAddCommGroup E]
    {a b eta : ℝ} (hab : a ≤ b) {f : ℝ → E}
    (hf : MemLp f 10 (volume.restrict (Icc a b))) (heta : 0 < eta) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ lpNorm f 10 (volume.restrict (Icc a b)) ^ (10 : ℕ) /
        eta ^ (10 : ℕ) + 1 ∧
      ∀ i : Fin P.count,
        eLpNorm f 10 (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ≤
          ENNReal.ofReal eta := by
  obtain ⟨P, hc, hp⟩ := exists_partition_of_integral hab
    (intervalIntegrable_norm_ten hab hf) (fun _ => pow_nonneg (norm_nonneg _) _)
    (pow_pos heta (10 : ℕ))
  refine ⟨P, ?_, ?_⟩
  · simpa only [integral_norm_ten_eq_lpNorm_pow hab hf] using hc
  · intro i
    have hi : P.time i.castSucc ≤ P.time i.succ := P.ordered (by exact_mod_cast Nat.le_succ i.val)
    have hsub : Icc (P.time i.castSucc) (P.time i.succ) ⊆ Icc a b :=
      Icc_subset_Icc (P.mem_interval i.castSucc).1 (P.mem_interval i.succ).2
    have hfi : MemLp f 10
        (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) :=
      hf.mono_measure (Measure.restrict_mono_set volume hsub)
    have hpower := hp i
    rw [integral_norm_ten_eq_lpNorm_pow hi hfi] at hpower
    have hreal : lpNorm f 10
        (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ≤ eta :=
      (pow_le_pow_iff_left₀ lpNorm_nonneg heta.le (by decide : (10 : ℕ) ≠ 0)).mp hpower
    rw [← ofReal_lpNorm hfi]
    exact ENNReal.ofReal_le_ofReal hreal

#print axioms integral_norm_ten_eq_lpNorm_pow
#print axioms intervalIntegrable_norm_ten
#print axioms exists_partition_small_L10
end HartreeF.TimePartition
