import FActualFiniteSTail

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace HartreeF.ActualSTail
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalJointSources
open CriticalSourceBounds TimeHolder SobolevStretch StationarySelfTest MaximalTrajectory
open CriticalPathRestriction CutoffApproximation
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields
  pathValueLp globalPathValue

/-- Uniform finiteness of the genuine extended S norm on every compact prefix
of the actual infinite forward trajectory. No energy or W bound is assumed. -/
def UniformSNormAfter {alpha kernel s0 : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (a : ℝ) (M : ℝ≥0) : Prop :=
  ∀ (b : ℝ) (hab : a ≤ b), ∀ hI : Set.Icc a b ⊆ U.domain,
    pathValueSize (intervalMeasure a b) (U.path hab hI) ≤ (M : ℝ≥0∞)

/-- The actual path representatives on compact prefixes exhaust one genuine
global L10_t(L10_x) class on the infinite forward half-line. -/
theorem exists_global_value_of_uniform_s_after (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 a : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0)
    (hU : Set.Ici a ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormAfter U a M) :
    ∃ F : GlobalValueSpace, ‖F‖ ≤ (M : ℝ) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ici a),
        (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t)) ∧
      (∀ᵐ t ∂volume, t ∉ Set.Ici a → F t = 0) := by
  let b : ℕ → ℝ := fun n => a + n
  have hab : ∀ n, a ≤ b n := by
    intro n
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hbmono : Monotone b := by
    intro n m hnm
    have hcast : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    dsimp [b]
    linarith
  have hI : ∀ n, Set.Icc a (b n) ⊆ U.domain :=
    fun _ _ ht => hU ht.1
  let f : ℕ → GlobalValueSpace := fun n =>
    globalPathValue hDensity hSob (hab n) (U.path (hab n) (hI n))
  have hfbound : ∀ n, ‖f n‖ ≤ (M : ℝ) := by
    intro n
    change ‖globalPathValue hDensity hSob (hab n) (U.path (hab n) (hI n))‖ ≤ (M : ℝ)
    rw [globalPathValue_norm]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top
      (hbound (b n) (hab n) (hI n))).trans_eq (by simp)
  have hfsupport : ∀ n, ∀ᵐ t ∂volume, t ∉ Set.Icc a (b n) → f n t = 0 :=
    fun n => globalPathValue_support hDensity hSob (hab n) (U.path (hab n) (hI n))
  have hfactual : ∀ n, ∀ᵐ t ∂localMeasure a (b n),
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    fun n => globalPathValue_actual hDensity hSob U (hab n) (hI n)
  have hfcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂volume,
      t ∈ Set.Icc a (b n) → f m t = f n t := by
    intro n m hnm
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hfactual n,
      ae_mono (localMeasure_mono (a := a) le_rfl (hbmono hnm)) (hfactual m)]
      with t hn hm
    exact Lp.ext (hm.trans hn.symm)
  obtain ⟨F, hFM, hFlocal, hFzero⟩ := FEndpoint.exists_coherent_L10_exhaustion
    (fun n => Set.Icc a (b n)) f (M : ℝ) hfbound hfsupport hfcoherent
  have hcover : ∀ t : ℝ, ∃ n, t ≤ b n := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
    exact ⟨n, by dsimp [b]; linarith⟩
  have hactual : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc a (b n) →
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hfactual n)
  have hlocal : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc a (b n) → F t = f n t :=
    ae_all_iff.mpr hFlocal
  refine ⟨F, hFM, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hactual, ae_restrict_of_ae hlocal,
      ae_restrict_mem measurableSet_Ici] with t ht hl hm
    obtain ⟨n, hn⟩ := hcover t
    rw [hl n ⟨hm, hn⟩]
    exact ht n ⟨hm, hn⟩
  · filter_upwards [hFzero] with t ht
    intro htn
    apply ht
    intro hmem
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact htn hn.1

/-- Genuine L10 norms on the infinite tails vanish as the left endpoint tends
to positive infinity. Closed endpoints are included in the restricted measure. -/
theorem global_value_infinite_tail_tendsto (F : GlobalValueSpace)
    (b : ℕ → ℝ) (hblim : Tendsto b atTop atTop) :
    Tendsto (fun n => eLpNorm F 10 (volume.restrict (Set.Ici (b n))))
      atTop (𝓝 0) := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᶠ n in atTop, t ∉ Set.Ici (b n) := by
    filter_upwards [] with t
    filter_upwards [hblim.eventually (eventually_gt_atTop t)] with n hn
    exact not_le_of_gt hn
  have h := tendsto_eLpNorm_indicator_eventually_empty (Lp.memLp F)
    (by norm_num : (10 : ℝ≥0∞) ≠ 0) (by norm_num : (10 : ℝ≥0∞) ≠ ∞)
    (fun n => measurableSet_Ici (a := b n)) he
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici.nullMeasurableSet] using h

/-- Choose one restart time c before every later endpoint b. The actual S norm
is then small on all [c,b], including b=c, with no assumed small-tail premise. -/
theorem exists_uniform_small_s_tail_after (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 a : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0)
    (hU : Set.Ici a ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormAfter U a M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, a ≤ c ∧
      ∀ (b : ℝ) (hcb : c ≤ b), ∀ hI : Set.Icc c b ⊆ U.domain,
        pathValueSize (intervalMeasure c b) (U.path hcb hI) < ENNReal.ofReal epsilon := by
  obtain ⟨F, _, hF, _⟩ :=
    exists_global_value_of_uniform_s_after hDensity hSob U hU M hbound
  let d : ℕ → ℝ := fun n => a + n
  have had : ∀ n, a ≤ d n := by
    intro n
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hdlim : Tendsto d atTop atTop := by
    apply tendsto_atTop.2
    intro r
    obtain ⟨N, hN⟩ := exists_nat_ge (r - a)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    dsimp [d]
    linarith
  have heps : (0 : ℝ≥0∞) < ENNReal.ofReal epsilon := ENNReal.ofReal_pos.mpr hepsilon
  obtain ⟨n, hn⟩ := ((global_value_infinite_tail_tendsto F d hdlim).eventually
    (Iio_mem_nhds heps)).exists
  refine ⟨d n, had n, ?_⟩
  intro b hcb hI
  have hF' : ∀ᵐ t ∂localMeasure (d n) b,
      (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
    apply ae_mono (Measure.restrict_mono_set volume ?_) hF
    intro t ht
    exact (had n).trans ht.1
  rw [actual_pathValueSize_eq hDensity hSob U hcb hI F hF']
  exact (eLpNorm_mono_measure F
    (Measure.restrict_mono_set volume (fun _ ht => ht.1))).trans_lt hn

end HartreeF.ActualSTail
