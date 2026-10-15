import F121RunningScaleSupremum

/-! R8.4 Theorem 5.8: near-maximal scales without attainment or regularity. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121ScaleSelection
open Paper121SubparabolicScalar

theorem exists_near_max_scale (r : ℝ → ℝ) (hr : ∀ t, 0 < r t)
    {T : ℝ} (hT : 0 ≤ T) (hb : BddAbove (r '' Icc 0 T)) :
    ∃ τ ∈ Icc 0 T, runningScaleSupremum r T / 2 < r τ ∧
      r τ ≤ runningScaleSupremum r T ∧
      ∀ t ∈ Icc 0 T, 0 < r t / r τ ∧ r t / r τ < 2 := by
  have hmem : r 0 ∈ r '' Icc 0 T := ⟨0, ⟨le_rfl, hT⟩, rfl⟩
  have hA : 0 < runningScaleSupremum r T := (hr 0).trans_le (le_csSup hb hmem)
  have hhalf : runningScaleSupremum r T / 2 < sSup (r '' Icc 0 T) := by
    change runningScaleSupremum r T / 2 < runningScaleSupremum r T
    linarith
  obtain ⟨v, ⟨τ, hτ, rfl⟩, hv⟩ := exists_lt_of_lt_csSup ⟨r 0, hmem⟩ hhalf
  refine ⟨τ, hτ, hv, le_csSup hb ⟨τ, hτ, rfl⟩, ?_⟩
  intro t ht
  refine ⟨div_pos (hr t) (hr τ), (div_lt_iff₀ (hr τ)).2 ?_⟩
  have htA : r t ≤ runningScaleSupremum r T := le_csSup hb ⟨t, ht, rfl⟩
  linarith

theorem normalized_length_tendsto_atTop (T A a : ℕ → ℝ)
    (hT : ∀ n, 0 < T n) (hA : ∀ n, 0 < A n) (ha : ∀ n, 0 < a n)
    (haA : ∀ n, a n ≤ A n)
    (hsmall : Tendsto (fun n => A n / Real.sqrt (T n)) atTop (𝓝 0)) :
    Tendsto (fun n => T n / (a n) ^ 2) atTop atTop := by
  have hsq : Tendsto (fun n => (A n / Real.sqrt (T n)) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsmall.pow 2
  have hratio : Tendsto (fun n => (A n) ^ 2 / T n) atTop (𝓝 0) :=
    hsq.congr' (Eventually.of_forall fun n => by rw [div_pow, Real.sq_sqrt (hT n).le])
  apply tendsto_atTop.2
  intro b
  let C : ℝ := max b 0 + 1
  have hC : 0 < C := by dsimp only [C]; have h := le_max_right b 0; linarith
  have hbC : b ≤ C := by dsimp only [C]; have h := le_max_left b 0; linarith
  filter_upwards [hratio.eventually_lt_const (one_div_pos.mpr hC)] with n hn
  have hmul : (A n) ^ 2 < (1 / C) * T n := (div_lt_iff₀ (hT n)).mp hn
  have hCT : (A n) ^ 2 * C < T n := (lt_div_iff₀ hC).mp (by
    simpa only [one_div, div_eq_mul_inv, mul_comm] using hmul)
  have ha2 : (a n) ^ 2 ≤ (A n) ^ 2 :=
    (sq_le_sq₀ (ha n).le (hA n).le).2 (haA n)
  have h1 : b * (a n) ^ 2 ≤ C * (a n) ^ 2 :=
    mul_le_mul_of_nonneg_right hbC (sq_nonneg _)
  have h2 : C * (a n) ^ 2 ≤ C * (A n) ^ 2 :=
    mul_le_mul_of_nonneg_left ha2 hC.le
  apply (le_div_iff₀ (sq_pos_of_pos (ha n))).2
  nlinarith

end HartreeF.Paper121ScaleSelection
