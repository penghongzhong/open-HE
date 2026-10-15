import FActualCriticalScaleEscape

/-! Compact return-time obstruction implies a two-sided subparabolic tail.
No regularity of the scalar scale function is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121SubparabolicScalar

theorem tail_of_no_compact_return
    {X : Type*} [MetricSpace X] (z : ℝ → X) (r : ℝ → ℝ)
    (hr : ∀ t, 0 < r t) (hcpt : IsCompact (closure (range z)))
    (hreturn : ∀ c : ℕ → ℝ, Tendsto (fun n => r (c n)) atTop atTop →
      ∀ p : X, Tendsto (fun n => z (c n)) atTop (𝓝 p) →
        ∀ τ : ℝ, ¬ Tendsto (fun n => -c n / (r (c n)) ^ 2) atTop (𝓝 τ)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ t : ℝ, R ≤ |t| → (r t) ^ 2 ≤ ε * |t| := by
  intro ε hε
  classical
  by_contra! hnot
  have hchoice (n : ℕ) : ∃ t : ℝ,
      (n : ℝ) + 1 ≤ |t| ∧ ε * |t| < (r t) ^ 2 :=
    hnot ((n : ℝ) + 1) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  choose c hc using hchoice
  have hscale : Tendsto (fun n => r (c n)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hn : ∀ᶠ n : ℕ in atTop, (max b 0) ^ 2 / ε ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hn] with n hn
    have hm : (max b 0) ^ 2 ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn
    have hcn := hc n
    have hrt := hr (c n)
    have hmax := le_max_left b 0
    have hmax0 := le_max_right b 0
    nlinarith
  let τ : ℕ → ℝ := fun n => -c n / (r (c n)) ^ 2
  have hτ (n : ℕ) : τ n ∈ Icc (-(1 / ε)) (1 / ε) := by
    have hs : 0 < (r (c n)) ^ 2 := sq_pos_of_pos (hr (c n))
    have hratio : |c n| / (r (c n)) ^ 2 ≤ 1 / ε :=
      (div_le_div_iff₀ hs hε).2 (by nlinarith [(hc n).2])
    apply abs_le.mp
    simpa only [τ, abs_div, abs_neg, abs_of_pos hs] using hratio
  have hp : IsCompact (closure (range z) ×ˢ Icc (-(1 / ε)) (1 / ε)) :=
    hcpt.prod isCompact_Icc
  have hmem : ∃ᶠ n in atTop, (z (c n), τ n) ∈
      closure (range z) ×ˢ Icc (-(1 / ε)) (1 / ε) :=
    (Filter.Eventually.of_forall fun n =>
      ⟨subset_closure (mem_range_self (c n)), hτ n⟩).frequently
  obtain ⟨p, _hp, k, hk, hlim⟩ := hp.tendsto_subseq' hmem
  have hz : Tendsto (fun n => z (c (k n))) atTop (𝓝 p.1) := hlim.fst_nhds
  have ht : Tendsto (fun n => -c (k n) / (r (c (k n))) ^ 2) atTop (𝓝 p.2) :=
    hlim.snd_nhds
  exact hreturn (fun n => c (k n)) (hscale.comp hk.tendsto_atTop) p.1 hz p.2 ht

theorem ratio_tendsto_of_tail (r : ℝ → ℝ)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ t : ℝ, R ≤ |t| → (r t) ^ 2 ≤ ε * |t|) :
    Tendsto (fun t => (r t) ^ 2 / |t|)
      (comap (fun t : ℝ => |t|) atTop) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := htail (ε / 2) (by positivity)
  apply eventually_comap.mpr
  filter_upwards [eventually_ge_atTop R] with b hb
  intro t ht
  have htR : R ≤ |t| := by simpa only [ht] using hb
  have htpos : 0 < |t| := lt_of_lt_of_le (by linarith) htR
  have hratio : (r t) ^ 2 / |t| ≤ ε / 2 :=
    (div_le_iff₀ htpos).2 (hbound t htR)
  have hnonneg : 0 ≤ (r t) ^ 2 / |t| := div_nonneg (sq_nonneg _) (abs_nonneg _)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hratio.trans_lt (by linarith : ε / 2 < ε)

end HartreeF.Paper121SubparabolicScalar
