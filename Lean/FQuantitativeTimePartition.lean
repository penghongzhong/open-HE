import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! An actual finite partition with a quantitative count, constructed from
continuous cumulative mass. The later time-integral consumer must supply
that cumulative function; no small-piece partition is postulated. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open Set
namespace HartreeF.TimePartition

structure Partition (a b : ℝ) where
  count : ℕ
  positive : 0 < count
  time : Fin (count+1) → ℝ
  left : time 0 = a
  right : time (Fin.last count) = b
  ordered : Monotone time

theorem Partition.mem_interval {a b : ℝ} (P : Partition a b) (i : Fin (P.count+1)) :
    P.time i ∈ Icc a b := by
  constructor
  · exact P.left.symm.le.trans (P.ordered (Fin.zero_le i))
  · exact (P.ordered (Fin.le_last i)).trans P.right.le

theorem exists_partition_of_cumulative {a b delta : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ) (hc : ContinuousOn f (Icc a b))
    (hm : MonotoneOn f (Icc a b)) (hd : 0 < delta) :
    ∃ P : Partition a b,
      (P.count : ℝ) ≤ (f b-f a)/delta+1 ∧
      ∀ i : Fin P.count,
        f (P.time i.succ)-f (P.time i.castSucc) ≤ delta := by
  classical
  let m := f b-f a
  have hm0 : 0 ≤ m := sub_nonneg.mpr (hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)
  by_cases hz : m=0
  · let t : Fin 2 → ℝ := fun i => if i=0 then a else b
    have ht : Monotone t := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [t]
    let P : Partition a b := ⟨1, by decide, t, by simp [t], by simp [t], ht⟩
    refine ⟨P, ?_, ?_⟩
    · have hc : (P.count : ℝ) = 1 := by norm_num [P]
      rw [hc]
      have hz' : f b-f a=0 := hz
      rw [hz']
      norm_num
    · intro i
      fin_cases i
      have hb : f b-f a ≤ delta := by change m ≤ delta; rw [hz]; exact hd.le
      simpa [P, t] using hb
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hz)
  let n := Nat.floor (m/delta)+1
  have hn : 0 < n := Nat.succ_pos _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let step := m/(n : ℝ)
  have hstep : 0 < step := div_pos hmpos hnR
  have hsum : (n : ℝ)*step=m := by dsimp [step]; field_simp
  have hnBound : (n : ℝ) ≤ m/delta+1 := by
    dsimp [n]
    push_cast
    exact add_le_add (Nat.floor_le (div_nonneg hm0 hd.le)) le_rfl
  have hless : m/delta < (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (m/delta)
  have hstepSmall : step ≤ delta := by
    apply le_of_lt
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hd).mp hless
    nlinarith
  let level : Fin (n+1) → ℝ := fun j => f a + (j : ℝ)*step
  have hlevel0 : level 0=f a := by simp [level]
  have hlevelLast : level (Fin.last n)=f b := by
    dsimp [level]
    rw [hsum]
    dsimp [m]
    ring
  have hlevel (j : Fin (n+1)) : level j ∈ Icc (f a) (f b) := by
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    have hjstep := mul_le_mul_of_nonneg_right hjn hstep.le
    have hjpos := mul_nonneg hj0 hstep.le
    dsimp [level]
    constructor <;> dsimp [m] at hsum <;> linarith
  have preimage (j : Fin (n+1)) : ∃ x ∈ Icc a b, f x=level j :=
    intermediate_value_Icc hab hc (hlevel j)
  let t : Fin (n+1) → ℝ := fun j =>
    if j=0 then a else if j=Fin.last n then b else Classical.choose (preimage j)
  have hspec (j : Fin (n+1)) : t j ∈ Icc a b ∧ f (t j)=level j := by
    dsimp [t]
    split_ifs with hj0 hjn
    · subst j
      exact ⟨left_mem_Icc.mpr hab, hlevel0.symm⟩
    · subst j
      exact ⟨right_mem_Icc.mpr hab, hlevelLast.symm⟩
    · exact Classical.choose_spec (preimage j)
  have ht : Monotone t := by
    intro i j hij
    by_cases heq : i=j
    · subst j; exact le_rfl
    have hij' : i<j := lt_of_le_of_ne hij heq
    have hcast : (i : ℝ)<j := by exact_mod_cast hij'
    have hlevels : level i<level j := add_lt_add_of_le_of_lt (le_refl (f a)) (mul_lt_mul_of_pos_right hcast hstep)
    by_contra hnot
    have hji : t j ≤ t i := (lt_of_not_ge hnot).le
    have hrev := hm (hspec j).1 (hspec i).1 hji
    rw [(hspec i).2, (hspec j).2] at hrev
    exact (not_le_of_gt hlevels) hrev
  have hlast : (Fin.last n : Fin (n+1)) ≠ 0 := by
    intro heq
    have he := congrArg Fin.val heq
    exact (Nat.ne_of_gt hn) he
  let P : Partition a b := ⟨n, hn, t, by simp [t], by simp [t, hlast], ht⟩
  refine ⟨P, hnBound, ?_⟩
  intro i
  change f (t i.succ)-f (t i.castSucc) ≤ delta
  rw [(hspec i.succ).2, (hspec i.castSucc).2]
  have heq : level i.succ-level i.castSucc=step := by
    simp only [level, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  exact heq.le.trans hstepSmall

#print axioms Partition.mem_interval
#print axioms exists_partition_of_cumulative
end HartreeF.TimePartition
