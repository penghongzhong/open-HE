import FCriticalPathRestriction
import FTimeNormLocalization

/-! Arbitrarily small forward W subintervals of a given actual critical path.
The coordinates are the same canonical Bochner classes already identified with
its actual C43 gradients by the accepted CriticalPath construction. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathRestriction
open EnergySpace CriticalPathSpace CriticalPathBall IntervalTimeTransport TimeHolder

variable {a b c d : ℝ}

/-- Exact norm of the restricted actual Bochner class, measured in real time. -/
theorem restrictIntervalLp_enorm_eq_local {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (f : Lp E p (intervalMeasure a b)) :
    ‖restrictIntervalLp p hac hcd hdb f‖ₑ =
      eLpNorm (toLocalLp (hac.trans (hcd.trans hdb)) p f) p (localMeasure c d) := by
  let g := toLocalLp (hac.trans (hcd.trans hdb)) p f
  change ‖toIntervalLp c d p (shrinkLp p (localMeasure_mono hac hdb) g)‖ₑ = _
  calc
    _ = ‖shrinkLp p (localMeasure_mono hac hdb) g‖ₑ := by
      simpa only [ofReal_norm] using congrArg ENNReal.ofReal
        (toIntervalLp_norm c d p (shrinkLp p (localMeasure_mono hac hdb) g))
    _ = _ := Lp.enorm_toLp ((Lp.memLp g).mono_measure (localMeasure_mono hac hdb))

/-- The given path's three genuine Bochner coordinates share one arbitrarily small ball. -/
theorem actualPath_coordinates_local_smallness (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)) (t0 eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ j : Fin 3,
      eLpNorm (toLocalLp hab 10 (criticalGradient (intervalMeasure a b) j u)) 10
        ((localMeasure a b).restrict (Metric.ball t0 r)) ≤ ENNReal.ofReal eta := by
  let g (j : Fin 3) := toLocalLp hab 10 (criticalGradient (intervalMeasure a b) j u)
  have loc (j : Fin 3) : ∃ r : ℝ, 0 < r ∧
      eLpNorm (g j) 10 ((localMeasure a b).restrict (Metric.ball t0 r)) ≤ ENNReal.ofReal eta :=
    finite_eLpNorm_exists_small_ball (localMeasure a b) Measure.restrict_le_self
      10 (by norm_num) (by norm_num) (g j) (Lp.eLpNorm_ne_top (g j)) t0
        (ENNReal.ofReal eta) (ENNReal.ofReal_pos.mpr heta)
  let r (j : Fin 3) : ℝ := Classical.choose (loc j)
  have hr (j : Fin 3) : 0 < r j := (Classical.choose_spec (loc j)).1
  have hs (j : Fin 3) : eLpNorm (g j) 10
      ((localMeasure a b).restrict (Metric.ball t0 (r j))) ≤ ENNReal.ofReal eta :=
    (Classical.choose_spec (loc j)).2
  let R := min (r 0) (min (r 1) (r 2))
  have hR : 0 < R := lt_min (hr 0) (lt_min (hr 1) (hr 2))
  have hRj (j : Fin 3) : R ≤ r j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, hR, ?_⟩
  intro j
  exact (eLpNorm_mono_measure (g j) (Measure.restrict_mono_set (localMeasure a b)
    (Metric.ball_subset_ball (hRj j)))).trans (hs j)

/-- Every time before the right endpoint starts a positive actual subpath with arbitrarily
small W norm. No density, representative, or regularity input is added. -/
theorem exists_forward_restriction_W_small {t0 : ℝ} (hat : a ≤ t0) (htb : t0 < b)
    (u : CriticalPath (intervalMeasure a b)) (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℝ, ∃ htd : t0 < d, ∃ hdb : d ≤ b,
      ‖gradientCoordinates (intervalMeasure t0 d) (restrictPath hat htd.le hdb u)‖ ≤ eta ∧
      ‖energyPath (intervalMeasure t0 d) (restrictPath hat htd.le hdb u)‖ ≤
        ‖energyPath (intervalMeasure a b) u‖ ∧
      energyPath (intervalMeasure t0 d) (restrictPath hat htd.le hdb u)
        ⟨t0, le_rfl, htd.le⟩ = energyPath (intervalMeasure a b) u ⟨t0, hat, htb.le⟩ := by
  let loc := actualPath_coordinates_local_smallness (hat.trans htb.le) u t0 eta heta
  let r : ℝ := Classical.choose loc
  have hr : 0 < r := (Classical.choose_spec loc).1
  have hs : ∀ j : Fin 3,
      eLpNorm (toLocalLp (hat.trans htb.le) 10 (criticalGradient (intervalMeasure a b) j u)) 10
        ((localMeasure a b).restrict (Metric.ball t0 r)) ≤ ENNReal.ofReal eta :=
    (Classical.choose_spec loc).2
  let δ := min r (b - t0) / 2
  have hδ : 0 < δ := half_pos (lt_min hr (sub_pos.mpr htb))
  have hδr : δ < r := by
    have := min_le_left r (b - t0)
    dsimp [δ]
    linarith
  have hδb : t0 + δ ≤ b := by
    have := min_le_right r (b - t0)
    dsimp [δ]
    linarith
  have hsub : Set.Icc t0 (t0 + δ) ⊆ Set.Icc a b ∩ Metric.ball t0 r := by
    intro t ht
    refine ⟨⟨hat.trans ht.1, ht.2.trans hδb⟩, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hmeasure : localMeasure t0 (t0 + δ) ≤
      (localMeasure a b).restrict (Metric.ball t0 r) := by
    rw [localMeasure, localMeasure, Measure.restrict_restrict measurableSet_ball, Set.inter_comm]
    exact Measure.restrict_mono_set volume hsub
  have htd : t0 < t0 + δ := by linarith
  refine ⟨t0 + δ, htd, hδb, ?_, restrictPath_energy_norm_le hat htd.le hδb u, rfl⟩
  apply (pi_norm_le_iff_of_nonneg heta.le).mpr
  intro j
  change ‖criticalGradient (intervalMeasure t0 (t0 + δ)) j
    (restrictPath hat htd.le hδb u)‖ ≤ eta
  apply (ENNReal.ofReal_le_ofReal_iff heta.le).mp
  have he := restrictIntervalLp_enorm_eq_local 10 hat htd.le hδb
    (criticalGradient (intervalMeasure a b) j u)
  have hb := he.trans_le ((eLpNorm_mono_measure _ hmeasure).trans (hs j))
  simpa only [ofReal_norm, restrictPath_gradient] using hb

end HartreeF.CriticalPathRestriction
