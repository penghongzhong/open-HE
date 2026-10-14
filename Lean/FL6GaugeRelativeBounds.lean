import FL6GaugeAffineTransport

/-! No relative scale or center escape for intrinsic gauges of a strongly
convergent nonzero actual EnergyState sequence. This source is UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace HartreeF.L6OrbitGauge
open EnergySpace CriticalAffine

private theorem restricted_mass_bound {f : L6} {q : ℝ} (hq : 0 < q)
    (hnorm : q/2 ≤ ‖f‖) {A : Set Space} (hA : MeasurableSet A)
    (hrest : ‖restrictLp A hA f‖ ≤ q/4) : setMass f A ≤ ‖f‖^6/64 := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) hrest 6
  have h₂ := pow_le_pow_left₀ (show 0 ≤ q/2 by positivity) hnorm 6
  rw [restrictLp_norm_pow] at h₁
  nlinarith [h₁, h₂]

private theorem bounds_of_mass_controls {u : EnergyState} {rho r S : ℝ} {c : Space}
    (hg : Gauge u rho c) (hm : 0 < mass u)
    (hsmall : ∀ d : Space, ballMass u d r ≤ mass u/64)
    (htail : setMass (energyValue u) (ball (0 : Space) S)ᶜ ≤ mass u/64) :
    r ≤ rho ∧ rho ≤ 2*S ∧ ‖c‖ ≤ 3*S := by
  have hlower : r < rho := by
    by_contra! h
    have hmono : ballMass u c rho ≤ ballMass u c r :=
      setMass_mono (energyValue u) (ball_subset_ball h)
    have hs := hsmall c
    have hglo := hg.lower
    linarith
  have hsplit := setMass_add_compl (energyValue u) (ball (0 : Space) S) measurableSet_ball
  have hupper : rho < 2*S := by
    by_contra! h
    have hmono : ballMass u 0 S ≤ ballMass u 0 (rho/2) :=
      setMass_mono (energyValue u) (ball_subset_ball (by linarith))
    have hgup := hg.half_upper 0
    change ballMass u 0 S + setMass (energyValue u) (ball (0 : Space) S)ᶜ = mass u at hsplit
    linarith
  have hcenter : ‖c‖ < S+rho := by
    by_contra! h
    have hsub : ball c rho ⊆ (ball (0 : Space) S)ᶜ := by
      intro z hz
      apply (mem_compl_iff _ _).mpr
      intro hz0
      have hz' : ‖z-c‖ < rho := by simpa only [mem_ball, dist_eq_norm] using hz
      have hz0' : ‖z‖ < S := by simpa only [mem_ball, dist_zero_right] using hz0
      have htri : ‖c‖ ≤ ‖z-c‖ + ‖z‖ := by
        simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le (c-z) z
      linarith
    have hmono := setMass_mono (energyValue u) hsub
    have hglo := hg.lower
    change ballMass u c rho ≤ _ at hmono
    linarith
  exact ⟨hlower.le, hupper.le, by linarith⟩

/-- Uniform q/8 restrictions of the limit, plus the q/8 strong error, give
m_n/64 controls and hence one eventual compact parameter box. -/
theorem relative_parameter_bounds {v : ℕ → EnergyState} {vLim : EnergyState}
    (hv : Tendsto v atTop (𝓝 vLim)) (hvLim : vLim ≠ 0)
    {rho : ℕ → ℝ} {c : ℕ → Space} (hg : ∀ n, Gauge (v n) (rho n) (c n)) :
    ∃ r > 0, ∃ S > 0, ∀ᶠ n in atTop,
      r ≤ rho n ∧ rho n ≤ 2*S ∧ ‖c n‖ ≤ 3*S := by
  let f : L6 := energyValue vLim
  let q : ℝ := ‖f‖
  have hq : 0 < q := by
    apply norm_pos_iff.mpr
    intro h
    apply hvLim
    apply energyValue_injective
    simpa only [map_zero] using h
  obtain ⟨r, hr, hsmall⟩ := exists_small_ball_norm f (show 0 < q/8 by positivity)
  obtain ⟨S, hS, htail⟩ := exists_exterior_norm f (show 0 < q/8 by positivity)
  have hvf : Tendsto (fun n => energyValue (v n)) atTop (𝓝 f) :=
    energyValue.continuous.tendsto vLim |>.comp hv
  have herr : Tendsto (fun n => ‖energyValue (v n)-f‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hvf.sub (tendsto_const_nhds (x := f))).norm
  refine ⟨r, hr, S, hS, ?_⟩
  filter_upwards [herr.eventually_lt_const (show 0 < q/8 by positivity)] with n hn
  have hnorm : q/2 ≤ ‖energyValue (v n)‖ := by
    have htri : q ≤ ‖energyValue (v n)-f‖ + ‖energyValue (v n)‖ := by
      calc
        q ≤ ‖energyValue (v n)‖ + ‖energyValue (v n)-f‖ :=
          norm_le_norm_add_norm_sub (energyValue (v n)) f
        _ = ‖energyValue (v n)-f‖ + ‖energyValue (v n)‖ := add_comm _ _
    linarith
  have hm : 0 < mass (v n) := pow_pos (by linarith : 0 < ‖energyValue (v n)‖) _
  apply bounds_of_mass_controls (hg n) hm
  · intro d
    apply restricted_mass_bound hq hnorm measurableSet_ball
    have ht := restrictLp_norm_triangle (ball d r) measurableSet_ball (energyValue (v n)) f
    have hs := hsmall d
    linarith
  · apply restricted_mass_bound hq hnorm measurableSet_ball.compl
    have ht := restrictLp_norm_triangle (ball (0 : Space) S)ᶜ
      measurableSet_ball.compl (energyValue (v n)) f
    linarith

end HartreeF.L6OrbitGauge
