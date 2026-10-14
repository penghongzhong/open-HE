import FL10TimePartition

/-! One partition controls every member of the same finite family of actual
time fields. The count uses their original global L10 norms. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace HartreeF.TimePartition

theorem exists_partition_small_L10_family {E J : Type*} [NormedAddCommGroup E]
    [Fintype J] {a b eta : ℝ} (hab : a ≤ b) (f : J → ℝ → E)
    (hf : ∀ j, MemLp (f j) 10 (volume.restrict (Icc a b))) (heta : 0 < eta) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ (∑ j, lpNorm (f j) 10 (volume.restrict (Icc a b))) ^ (10 : ℕ) /
        eta ^ (10 : ℕ) + 1 ∧
      ∀ (i : Fin P.count) (j : J),
        eLpNorm (f j) 10 (volume.restrict (Icc (P.time i.castSucc) (P.time i.succ))) ≤
          ENNReal.ofReal eta := by
  classical
  let g : ℝ → ℝ := fun t => ∑ j, ‖f j t‖
  have hg : MemLp g 10 (volume.restrict (Icc a b)) :=
    memLp_finsetSum Finset.univ (fun j _ => (hf j).norm)
  have hgnorm : lpNorm g 10 (volume.restrict (Icc a b)) ≤
      ∑ j, lpNorm (f j) 10 (volume.restrict (Icc a b)) := by
    have h := lpNorm_sum_le (s := Finset.univ)
      (f := fun j t => ‖f j t‖) (fun j _ => (hf j).norm) (by norm_num : (1 : ℝ≥0∞) ≤ 10)
    have he : (∑ j, fun t => ‖f j t‖) = g := by
      funext t
      simp [g]
    rw [he] at h
    simpa only [lpNorm_norm (hf _).aestronglyMeasurable] using h
  obtain ⟨P, hc, hp⟩ := exists_partition_small_L10 hab hg heta
  refine ⟨P, ?_, ?_⟩
  · exact hc.trans (add_le_add (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ lpNorm_nonneg hgnorm (10 : ℕ)) (pow_nonneg heta.le _)) le_rfl)
  · intro i j
    have hsub : Icc (P.time i.castSucc) (P.time i.succ) ⊆ Icc a b :=
      Icc_subset_Icc (P.mem_interval i.castSucc).1 (P.mem_interval i.succ).2
    have hfj := (hf j).mono_measure (Measure.restrict_mono_set volume hsub)
    apply (eLpNorm_mono_real hfj.aestronglyMeasurable ?_).trans (hp i)
    intro t
    exact Finset.single_le_sum (fun k _ => norm_nonneg (f k t)) (Finset.mem_univ j)

#print axioms exists_partition_small_L10_family
end HartreeF.TimePartition
