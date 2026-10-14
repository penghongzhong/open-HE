import FQuantitativeTimePartition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Finite partitions of an actual nonnegative integrable time density.
The partition and its quantitative cardinality are produced from its
continuous primitive, rather than assumed as an analytical interface. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open Set MeasureTheory
namespace HartreeF.TimePartition

theorem intervalIntegrable_to_member {a b x : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b) (hx : x ∈ Icc a b) :
    IntervalIntegrable g volume a x := by
  apply hg.mono_set
  rw [uIcc_of_le hab, uIcc_of_le hx.1]
  exact Icc_subset_Icc le_rfl hx.2

theorem primitive_monotoneOn {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b) (hpos : ∀ t, 0 ≤ g t) :
    MonotoneOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
  intro x hx y hy hxy
  apply sub_nonneg.mp
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_to_member hab hg hy) (intervalIntegrable_to_member hab hg hx)]
  exact intervalIntegral.integral_nonneg_of_forall hxy hpos

theorem exists_partition_of_integral {a b delta : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hpos : ∀ t, 0 ≤ g t) (hd : 0 < delta) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ (∫ t in a..b, g t) / delta + 1 ∧
      ∀ i : Fin P.count, (∫ t in P.time i.castSucc..P.time i.succ, g t) ≤ delta := by
  have hc : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  obtain ⟨P, hcount, hpiece⟩ := exists_partition_of_cumulative hab
    (fun x => ∫ t in a..x, g t) hc (primitive_monotoneOn hab hg hpos) hd
  refine ⟨P, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_same, sub_zero] using hcount
  · intro i
    have hi := hpiece i
    rw [intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_to_member hab hg (P.mem_interval i.succ))
      (intervalIntegrable_to_member hab hg (P.mem_interval i.castSucc))] at hi
    exact hi

theorem exists_partition_of_integral_bound {a b delta mass : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hpos : ∀ t, 0 ≤ g t) (hd : 0 < delta)
    (hm : (∫ t in a..b, g t) ≤ mass) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ mass / delta + 1 ∧
      ∀ i : Fin P.count, (∫ t in P.time i.castSucc..P.time i.succ, g t) ≤ delta := by
  obtain ⟨P, hc, hp⟩ := exists_partition_of_integral hab hg hpos hd
  exact ⟨P, hc.trans (add_le_add (div_le_div_of_nonneg_right hm hd.le) le_rfl), hp⟩

#print axioms intervalIntegrable_to_member
#print axioms primitive_monotoneOn
#print axioms exists_partition_of_integral
#print axioms exists_partition_of_integral_bound
end HartreeF.TimePartition
