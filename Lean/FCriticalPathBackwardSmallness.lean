import FCriticalPathPairSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathRestriction
open EnergySpace CriticalPathSpace CriticalPathBall IntervalTimeTransport TimeHolder
variable {a b : ℝ}

/-- Every time after the left endpoint ends a positive actual subpath with arbitrarily
small W norm. No density, representative, or regularity input is added. -/
theorem exists_backward_restriction_W_small {t0 : ℝ} (hat : a < t0) (htb : t0 ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℝ, ∃ had : a ≤ d, ∃ hdt : d < t0,
      ‖gradientCoordinates (intervalMeasure d t0) (restrictPath had hdt.le htb u)‖ ≤ eta ∧
      ‖energyPath (intervalMeasure d t0) (restrictPath had hdt.le htb u)‖ ≤
        ‖energyPath (intervalMeasure a b) u‖ ∧
      energyPath (intervalMeasure d t0) (restrictPath had hdt.le htb u)
        ⟨t0, hdt.le, le_rfl⟩ = energyPath (intervalMeasure a b) u ⟨t0, hat.le, htb⟩ := by
  let loc := actualPath_coordinates_local_smallness (hat.le.trans htb) u t0 eta heta
  let r : ℝ := Classical.choose loc
  have hr : 0 < r := (Classical.choose_spec loc).1
  have hs : ∀ j : Fin 3,
      eLpNorm (toLocalLp (hat.le.trans htb) 10 (criticalGradient (intervalMeasure a b) j u)) 10
        ((localMeasure a b).restrict (Metric.ball t0 r)) ≤ ENNReal.ofReal eta :=
    (Classical.choose_spec loc).2
  let δ := min r (t0 - a) / 2
  have hδ : 0 < δ := half_pos (lt_min hr (sub_pos.mpr hat))
  have hδr : δ < r := by
    have := min_le_left r (t0 - a)
    dsimp [δ]
    linarith
  have hδa : a ≤ t0 - δ := by
    have := min_le_right r (t0 - a)
    dsimp [δ]
    linarith
  have hsub : Set.Icc (t0 - δ) t0 ⊆ Set.Icc a b ∩ Metric.ball t0 r := by
    intro t ht
    refine ⟨⟨hδa.trans ht.1, ht.2.trans htb⟩, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith [ht.1]
  have hmeasure : localMeasure (t0 - δ) t0 ≤
      (localMeasure a b).restrict (Metric.ball t0 r) := by
    rw [localMeasure, localMeasure, Measure.restrict_restrict measurableSet_ball, Set.inter_comm]
    exact Measure.restrict_mono_set volume hsub
  have hdt : t0 - δ < t0 := by linarith
  refine ⟨t0 - δ, hδa, hdt, ?_, restrictPath_energy_norm_le hδa hdt.le htb u, rfl⟩
  apply (pi_norm_le_iff_of_nonneg heta.le).mpr
  intro j
  change ‖criticalGradient (intervalMeasure (t0 - δ) t0) j
    (restrictPath hδa hdt.le htb u)‖ ≤ eta
  apply (ENNReal.ofReal_le_ofReal_iff heta.le).mp
  have he := restrictIntervalLp_enorm_eq_local 10 hδa hdt.le htb
    (criticalGradient (intervalMeasure a b) j u)
  have hb := he.trans_le ((eLpNorm_mono_measure _ hmeasure).trans (hs j))
  simpa only [ofReal_norm, restrictPath_gradient] using hb


end HartreeF.CriticalPathRestriction
