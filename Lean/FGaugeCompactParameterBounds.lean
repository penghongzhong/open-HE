import FActualCompactOrbitGauge

/-! Local properness for intrinsic L6 gauges. This establishes compact-time
parameter bounds for the gauge used in the native compact normalization.
It does not assert subparabolic growth or the bounded-half-line selection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Filter Set
open scoped Topology
namespace HartreeF.L6OrbitGauge
open EnergySpace

/-- Every intrinsic gauge of a compact carrier avoiding zero lies in a common
positive scale and bounded center box. No regularity of gauge choices is used. -/
theorem gauge_parameters_bounded_on_compact {Q : Set EnergyState}
    (hQ : IsCompact Q) (hQzero : (0 : EnergyState) ∉ Q) :
    ∃ m : ℕ, ∀ u ∈ Q, ∀ (r : ℝ) (y : Space), Gauge u r y →
      1 / ((m : ℝ) + 1) ≤ r ∧ r ≤ 2 * ((m : ℝ) + 1) ∧
        ‖y‖ ≤ 3 * ((m : ℝ) + 1) := by
  classical
  by_contra hnot
  have hbad (n : ℕ) : ∃ u ∈ Q, ∃ (r : ℝ) (y : Space), Gauge u r y ∧
      ¬ (1 / ((n : ℝ) + 1) ≤ r ∧ r ≤ 2 * ((n : ℝ) + 1) ∧
        ‖y‖ ≤ 3 * ((n : ℝ) + 1)) := by
    by_contra hn
    apply hnot
    refine ⟨n, ?_⟩
    intro u hu r y hg
    by_contra hf
    exact hn ⟨u, hu, r, y, hg, hf⟩
  choose u hu r y hg hfail using hbad
  obtain ⟨v, hv, k, hk, huv⟩ := hQ.tendsto_subseq hu
  have hvzero : v ≠ 0 := by
    intro hz
    exact hQzero (hz ▸ hv)
  obtain ⟨r0, hr0, S, _hS, hbounds⟩ :=
    relative_parameter_bounds huv hvzero (fun n => hg (k n))
  have hrecip : Tendsto (fun n : ℕ => 1 / ((k n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hk.tendsto_atTop
  have hcast : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop
  obtain ⟨n, hn, hsmall, hlarge⟩ :=
    (hbounds.and ((hrecip.eventually_lt_const hr0).and
      (hcast.eventually (eventually_ge_atTop S)))).exists
  apply hfail (k n)
  exact ⟨hsmall.le.trans hn.1, by linarith [hn.2.1], by linarith [hn.2.2]⟩

/-- Intrinsic gauges on any nonzero continuous trajectory have compact-time
scale and center bounds. The trajectory need not have a global scalar L2 domain. -/
theorem gauge_parameters_bounded_on_compact_time {J : Set ℝ}
    (hJ : IsCompact J) (u : ℝ → EnergyState) (hu : ContinuousOn u J)
    (hne : ∀ t ∈ J, u t ≠ 0) (r : ℝ → ℝ) (y : ℝ → Space)
    (hg : ∀ t ∈ J, Gauge (u t) (r t) (y t)) :
    ∃ m : ℕ, ∀ t ∈ J,
      1 / ((m : ℝ) + 1) ≤ r t ∧ r t ≤ 2 * ((m : ℝ) + 1) ∧
        ‖y t‖ ≤ 3 * ((m : ℝ) + 1) := by
  have hz : (0 : EnergyState) ∉ u '' J := by
    rintro ⟨t, ht, he⟩
    exact hne t ht he
  obtain ⟨m, hm⟩ := gauge_parameters_bounded_on_compact
    (hJ.image_of_continuousOn hu) hz
  exact ⟨m, fun t ht => hm (u t) ⟨t, ht, rfl⟩ (r t) (y t) (hg t ht)⟩

end HartreeF.L6OrbitGauge
