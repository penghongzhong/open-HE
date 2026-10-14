import FTimeNormLocalization
import CutoffConvergence

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.ProfileApproximation
open TimeHolder CutoffApproximation

/-- Dominated convergence directly in the extended Lp norm; infinity is never totalized. -/
theorem ennreal_eLpNorm_dominated_zero {T : Type*} [MeasurableSpace T]
    (μ : Measure T) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    {a : ℕ → T → ℝ≥0∞} {b : T → ℝ≥0∞}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hb : eLpNorm b p μ ≠ ∞)
    (hab : ∀ n, ∀ᵐ t ∂μ, a n t ≤ b t)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n => a n t) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (a n) p μ) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hi : (∫⁻ t, b t ^ p.toReal ∂μ) ≠ ∞ := by
    simpa only [enorm_eq_self] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpTop (lt_top_iff_ne_top.mpr hb)).ne
  have hl : Tendsto (fun n => ∫⁻ t, a n t ^ p.toReal ∂μ) atTop (𝓝 0) := by
    simpa using
      (tendsto_lintegral_of_dominated_convergence' (f := fun _ : T => 0) (fun t => b t ^ p.toReal)
        (fun n => (ha n).aemeasurable.pow_const _)
        (fun n => (hab n).mono fun t ht => ENNReal.rpow_le_rpow ht hp.le) hi
        (hlim.mono fun t ht => by
          simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hp] using
            (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp ht))
  have hroot := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp hl
  simpa only [Function.comp_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop (ha _), enorm_eq_self,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using hroot

/-- Spatial tails of a genuinely finite mixed norm vanish by two successive dominated limits. -/
theorem mixed_spatial_tail_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞) (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume p q f ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume p q (fun t => exteriorTail n (f t)))
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z : ℝ × Space => exteriorTail n (f z.1) z.2) (volume.prod volume) := by
    exact hf.indicator (isOpen_lt continuous_const continuous_snd.norm).measurableSet
  apply ennreal_eLpNorm_dominated_zero volume hp0 hpTop
    (fun n => spatial_lp_time_measurable volume volume q hq0 hqTop _ (hm n)) hfin
  · intro n
    filter_upwards [] with t
    exact eLpNorm_indicator_le _
      (isOpen_lt continuous_const continuous_norm).measurableSet.nullMeasurableSet
  · filter_upwards [finite_mixedNorm_ae_slice_memLp volume volume p q hp0 hpTop f hfin]
      with t ht
    exact exteriorTail_eLpNorm_tendsto_zero ht hq0 hqTop

/-- Monotonicity of the mixed norm for a joint measurable field. -/
theorem mixed_mono {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    {f : ℝ → Space → E} {g : ℝ → Space → F}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfg : ∀ t x, ‖f t x‖ ≤ ‖g t x‖) :
    mixedNorm volume volume p q f ≤ mixedNorm volume volume p q g := by
  apply eLpNorm_mono_enorm_ae (spatial_lp_time_measurable volume volume q hq0 hqTop f hf)
  filter_upwards [hf.prodMk_left] with t ht
  simpa only [enorm_eq_self] using eLpNorm_mono ht (hfg t)

/-- The genuine spatial cutoff converges in any finite mixed exponent pair. -/
theorem mixed_spatial_cutoff_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞) (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume p q f ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume p q
      (fun t x => cutoff n x • f t x - f t x)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (mixed_spatial_tail_tendsto_zero hp0 hpTop hq0 hqTop f hf hfin)
  · intro n; exact bot_le
  · intro n
    exact mixed_mono hq0 hqTop
      ((((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hf).sub hf)
      (fun t x => cutoff_sub_norm_le_tail (f t) n x)

/-- Triangle inequality for the actual extended mixed norm. -/
theorem mixed_add_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqTop : q ≠ ∞)
    (f g : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => f t x + g t x) ≤
      mixedNorm volume volume p q f + mixedNorm volume volume p q g := by
  have hq0 : q ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hq)
  apply le_trans (eLpNorm_mono_enorm_ae
    (spatial_lp_time_measurable volume volume q hq0 hqTop _ (hf.add hg)) ?_)
    (eLpNorm_add_le hp)
  filter_upwards [] with t
  simpa only [enorm_eq_self, Pi.add_apply, Pi.add_def] using eLpNorm_add_le (f := f t) (g := g t) hq

#print axioms ennreal_eLpNorm_dominated_zero
#print axioms mixed_spatial_tail_tendsto_zero
#print axioms mixed_spatial_cutoff_tendsto_zero
#print axioms mixed_add_le
end HartreeF.ProfileApproximation
