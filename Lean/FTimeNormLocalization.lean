import FTimeFiniteNormBridge

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

/-- Absolute continuity of a finite extended Lp norm. No real-valued truncation
is used. The time exponent is strictly positive and finite. -/
theorem finite_eLpNorm_small_restrict {T E : Type*} [MeasurableSpace T]
    [ENorm E] [TopologicalSpace E] (mu : Measure T) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (f : T → E)
    (hfin : eLpNorm f p mu ≠ ∞) (epsilon : ℝ≥0∞) (hepsilon : 0 < epsilon) :
    ∃ d : ℝ≥0∞, 0 < d ∧ ∀ s : Set T, mu s < d →
      eLpNorm f p (mu.restrict s) ≤ epsilon := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hint := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpTop
    (lt_top_iff_ne_top.mpr hfin)
  have hepow : epsilon ^ p.toReal ≠ 0 := by
    intro hz
    exact hepsilon.ne' ((ENNReal.rpow_eq_zero_iff_of_pos hp).mp hz)
  obtain ⟨d, hd, hdsmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hint.ne hepow
  refine ⟨d, hd, fun s hs => ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
    (aestronglyMeasurable_of_eLpNorm_ne_top hfin).restrict]
  calc
    (∫⁻ t in s, ‖f t‖ₑ ^ p.toReal ∂mu) ^ (1 / p.toReal) ≤
        (epsilon ^ p.toReal) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow (hdsmall s hs).le (by positivity)
    _ = epsilon := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Every point has a ball of arbitrarily small positive Lebesgue measure. -/
theorem exists_volume_ball_lt (t0 : ℝ) (d : ℝ≥0∞) (hd : 0 < d) :
    ∃ r : ℝ, 0 < r ∧ volume (Metric.ball t0 r) < d := by
  obtain ⟨a, ha0, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
  have ha : 0 < (a : ℝ) := by exact_mod_cast ha0
  refine ⟨(a : ℝ) / 2, by positivity, ?_⟩
  rw [Real.volume_ball, show 2 * ((a : ℝ) / 2) = (a : ℝ) by ring,
    ENNReal.ofReal_coe_nnreal]
  exact had

/-- Local smallness for any time measure dominated by Lebesgue measure,
including volume and volume restricted to a time set. -/
theorem finite_eLpNorm_exists_small_ball {E : Type*} [ENorm E] [TopologicalSpace E]
    (mu : Measure ℝ) (hmu : mu ≤ volume) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (f : ℝ → E)
    (hfin : eLpNorm f p mu ≠ ∞) (t0 : ℝ)
    (epsilon : ℝ≥0∞) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ eLpNorm f p (mu.restrict (Metric.ball t0 r)) ≤ epsilon := by
  obtain ⟨d, hd, hsmall⟩ := finite_eLpNorm_small_restrict mu p hp0 hpTop f hfin epsilon hepsilon
  obtain ⟨r, hr, hball⟩ := exists_volume_ball_lt t0 d hd
  exact ⟨r, hr, hsmall _ ((hmu _).trans_lt hball)⟩

/-- Restricting the time measure cannot increase any mixed norm, including L∞. -/
theorem mixedNorm_restrict_le {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] (mu : Measure T) (nu : Measure X)
    (p q : ℝ≥0∞) (f : T → X → E) (s : Set T) :
    mixedNorm (mu.restrict s) nu p q f ≤ mixedNorm mu nu p q f :=
  eLpNorm_mono_measure _ Measure.restrict_le_self

/-- A finite extended mixed norm with finite positive time exponent becomes
arbitrarily small near every time. The output is the actual mixedNorm. -/
theorem finite_mixedNorm_exists_small_ball {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (mu : Measure ℝ) (hmu : mu ≤ volume) (nu : Measure X)
    (p q : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (f : ℝ → X → E)
    (hfin : mixedNorm mu nu p q f ≠ ∞) (t0 : ℝ)
    (epsilon : ℝ≥0∞) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ mixedNorm (mu.restrict (Metric.ball t0 r)) nu p q f ≤ epsilon :=
  finite_eLpNorm_exists_small_ball mu hmu p hp0 hpTop
    (fun t => eLpNorm (f t) q nu) hfin t0 epsilon hepsilon

/-- With a positive finite time exponent, finiteness of the extended mixed
norm forces almost every spatial slice to have finite Lq norm and to be
strongly measurable. This is proved before any potential real-norm bridge. -/
theorem finite_mixedNorm_ae_slice_memLp {T X E : Type*} [MeasurableSpace T]
    [MeasurableSpace X] [NormedAddCommGroup E] (mu : Measure T) (nu : Measure X)
    (p q : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (f : T → X → E)
    (hfin : mixedNorm mu nu p q f ≠ ∞) :
    ∀ᵐ t ∂mu, MemLp (f t) q nu := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hmeas := aestronglyMeasurable_of_eLpNorm_ne_top hfin
  have hint := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpTop
    (lt_top_iff_ne_top.mpr hfin)
  have hae := ae_lt_top' (hmeas.enorm.pow_const p.toReal) hint.ne
  filter_upwards [hae] with t ht
  exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp (by simpa only [enorm_eq_self] using ht)

/-- Joint a.e. strong measurability survives restriction of the time measure. -/
theorem joint_aestronglyMeasurable_time_restrict {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [TopologicalSpace E]
    (mu : Measure T) (nu : Measure X) [SFinite nu] (f : T → X → E)
    (hf : AEStronglyMeasurable (fun z : T × X => f z.1 z.2) (mu.prod nu))
    (s : Set T) :
    AEStronglyMeasurable (fun z : T × X => f z.1 z.2) ((mu.restrict s).prod nu) :=
  hf.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

/-- Domination by real Lebesgue measure supplies sigma-finiteness after
any time restriction; it is not an additional localization assumption. -/
theorem time_restrict_sigmaFinite_of_le_volume (mu : Measure ℝ) (hmu : mu ≤ volume)
    (s : Set ℝ) : SigmaFinite (mu.restrict s) :=
  Measure.sigmaFinite_of_le volume (Measure.restrict_le_self.trans hmu)

/-- An explicit interior premise is sufficient to choose the small ball
inside a prescribed time set. This asserts no PDE lifespan property. -/
theorem finite_mixedNorm_exists_small_ball_within {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (mu : Measure ℝ) (hmu : mu ≤ volume) (nu : Measure X)
    (p q : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (f : ℝ → X → E)
    (hfin : mixedNorm mu nu p q f ≠ ∞) (t0 : ℝ) (I : Set ℝ)
    (ht0 : t0 ∈ interior I) (epsilon : ℝ≥0∞) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball t0 r ⊆ I ∧
      mixedNorm (mu.restrict (Metric.ball t0 r)) nu p q f ≤ epsilon := by
  obtain ⟨a, ha, hasmall⟩ := finite_mixedNorm_exists_small_ball mu hmu nu p q hp0 hpTop
    f hfin t0 epsilon hepsilon
  obtain ⟨b, hb, hbI⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ht0)
  refine ⟨min a b, lt_min ha hb, (Metric.ball_subset_ball (min_le_right _ _)).trans hbI, ?_⟩
  exact (eLpNorm_mono_measure _ (mu.restrict_mono_set
    (Metric.ball_subset_ball (min_le_left _ _)))).trans hasmall

end HartreeF.TimeHolder
