import F121SubparabolicScalar

/-! The actual real running supremum, with boundedness proved before use.
The scale need not be measurable or continuous. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121SubparabolicScalar

def runningScaleSupremum (r : ℝ → ℝ) (T : ℝ) : ℝ := sSup (r '' Icc 0 T)

theorem running_supremum_subparabolic (r : ℝ → ℝ) (hr : ∀ t, 0 < r t)
    (hlocal : ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, r t ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ t : ℝ, R ≤ |t| → (r t) ^ 2 ≤ ε * |t|) :
    (∀ T : ℝ, 0 ≤ T → BddAbove (r '' Icc 0 T) ∧ 0 < runningScaleSupremum r T) ∧
    Tendsto (fun T => runningScaleSupremum r T / Real.sqrt T) atTop (𝓝 0) := by
  have hbounded (T : ℝ) (hT : 0 ≤ T) : BddAbove (r '' Icc 0 T) := by
    obtain ⟨C, _hC, hbound⟩ := hlocal T hT
    refine ⟨C, ?_⟩
    rintro a ⟨t, ht, rfl⟩
    exact hbound t ht
  have hpositive (T : ℝ) (hT : 0 ≤ T) : 0 < runningScaleSupremum r T :=
    (hr 0).trans_le (le_csSup (hbounded T hT) ⟨0, ⟨le_rfl, hT⟩, rfl⟩)
  refine ⟨fun T hT => ⟨hbounded T hT, hpositive T hT⟩, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d : ℝ := ε / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  obtain ⟨R, hR, htailR⟩ := htail (d ^ 2) (sq_pos_of_pos hd)
  obtain ⟨C, hC, hcompact⟩ := hlocal R (by linarith)
  filter_upwards [eventually_ge_atTop (max R ((C / d) ^ 2))] with T hT
  have hTR : R ≤ T := (le_max_left _ _).trans hT
  have hTsq : (C / d) ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hspos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hroot : C / d ≤ Real.sqrt T :=
    (Real.le_sqrt (div_nonneg hC.le hd.le) hTpos.le).2 hTsq
  have hCsmall : C ≤ d * Real.sqrt T := by
    have h := (div_le_iff₀ hd).mp hroot
    nlinarith
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : r t ≤ d * Real.sqrt T := by
    by_cases htR : t ≤ R
    · exact (hcompact t ⟨ht.1, htR⟩).trans hCsmall
    · have htailt : (r t) ^ 2 ≤ d ^ 2 * t := by
        simpa only [abs_of_nonneg ht.1] using
          htailR t (by simpa only [abs_of_nonneg ht.1] using (le_of_not_ge htR))
      have hlarge : (r t) ^ 2 ≤ d ^ 2 * T :=
        htailt.trans (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg d))
      have hsquare : (d * Real.sqrt T) ^ 2 = d ^ 2 * T := by
        rw [mul_pow, Real.sq_sqrt hTpos.le]
      have hprod : 0 ≤ d * Real.sqrt T := mul_nonneg hd.le hspos.le
      nlinarith [hr t]
  have hsup : runningScaleSupremum r T ≤ d * Real.sqrt T := by
    apply csSup_le ⟨r 0, ⟨0, ⟨le_rfl, hTpos.le⟩, rfl⟩⟩
    rintro a ⟨t, ht, rfl⟩
    exact hbound t ht
  have hratio : runningScaleSupremum r T / Real.sqrt T ≤ d :=
    (div_le_iff₀ hspos).2 hsup
  have hratio0 : 0 ≤ runningScaleSupremum r T / Real.sqrt T :=
    div_nonneg (hpositive T hTpos.le).le hspos.le
  have hdε : d < ε := by dsimp only [d]; linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hratio0] using hratio.trans_lt hdε

end HartreeF.Paper121SubparabolicScalar
