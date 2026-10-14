import FActualFiniteSTail

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualLeftSTail
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalJointSources
open CriticalSourceBounds TimeHolder SobolevStretch StationarySelfTest MaximalTrajectory
open CriticalPathRestriction CutoffApproximation ActualSTail
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields
  pathValueLp globalPathValue

/-- Literal uniform finite S on compact terminal segments approaching a left endpoint. -/
def UniformSNormAfter {alpha kernel s0 : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (T c : ℝ) (M : ℝ≥0) : Prop :=
  ∀ (b : ℝ) (hbc : b ≤ c), T < b → ∀ hI : Set.Icc b c ⊆ U.domain,
    pathValueSize (intervalMeasure b c) (U.path hbc hI) ≤ (M : ℝ≥0∞)

/-- A decreasing compact exhaustion realizes the same actual states in global L10. -/
theorem exists_global_value_of_uniform_s_after (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 T c : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (hTc : T < c)
    (hU : Set.Ioc T c ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormAfter U T c M) :
    ∃ F : GlobalValueSpace, ‖F‖ ≤ (M : ℝ) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc T c),
        (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t)) ∧
      (∀ᵐ t ∂volume, t ∉ Set.Ioc T c → F t = 0) := by
  obtain ⟨b, hbmono, hbmem, hblim⟩ := exists_seq_strictAnti_tendsto' hTc
  have hbc : ∀ n, b n ≤ c := fun n => (hbmem n).2.le
  have hTb : ∀ n, T < b n := fun n => (hbmem n).1
  have hI : ∀ n, Set.Icc (b n) c ⊆ U.domain := by
    intro n t ht
    exact hU ⟨(hTb n).trans_le ht.1, ht.2⟩
  let f : ℕ → GlobalValueSpace := fun n =>
    globalPathValue hDensity hSob (hbc n) (U.path (hbc n) (hI n))
  have hfbound : ∀ n, ‖f n‖ ≤ (M : ℝ) := by
    intro n
    change ‖globalPathValue hDensity hSob (hbc n) (U.path (hbc n) (hI n))‖ ≤ (M : ℝ)
    rw [globalPathValue_norm]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top
      (hbound (b n) (hbc n) (hTb n) (hI n))).trans_eq (by simp)
  have hfsupport : ∀ n, ∀ᵐ t ∂volume, t ∉ Set.Icc (b n) c → f n t = 0 :=
    fun n => globalPathValue_support hDensity hSob (hbc n) (U.path (hbc n) (hI n))
  have hfactual : ∀ n, ∀ᵐ t ∂localMeasure (b n) c,
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    fun n => globalPathValue_actual hDensity hSob U (hbc n) (hI n)
  have hfcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂volume,
      t ∈ Set.Icc (b n) c → f m t = f n t := by
    intro n m hnm
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hfactual n,
      ae_mono (localMeasure_mono (hbmono.antitone hnm) (le_refl c)) (hfactual m)]
      with t hn hm
    exact Lp.ext (hm.trans hn.symm)
  obtain ⟨F, hFM, hFlocal, hFzero⟩ := FEndpoint.exists_coherent_L10_exhaustion
    (fun n => Set.Icc (b n) c) f (M : ℝ) hfbound hfsupport hfcoherent
  have hcover : ∀ t ∈ Set.Ioc T c, ∃ n, b n ≤ t := by
    intro t ht
    obtain ⟨n, hn⟩ := (hblim.eventually (Iio_mem_nhds ht.1)).exists
    exact ⟨n, hn.le⟩
  have hactual : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc (b n) c →
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hfactual n)
  have hlocal : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc (b n) c → F t = f n t :=
    ae_all_iff.mpr hFlocal
  refine ⟨F, hFM, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hactual, ae_restrict_of_ae hlocal,
      ae_restrict_mem measurableSet_Ioc] with t ht hl hm
    obtain ⟨n, hn⟩ := hcover t hm
    rw [hl n ⟨hn, hm.2⟩]
    exact ht n ⟨hn, hm.2⟩
  · filter_upwards [hFzero] with t ht
    intro htn
    apply ht
    intro hmem
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact htn ⟨(hTb n).trans_le hn.1, hn.2⟩

/-- Strong L10 mass tends to zero on intervals shrinking to a finite left endpoint. -/
theorem global_value_finite_left_tail_tendsto {T : ℝ} (F : GlobalValueSpace)
    (b : ℕ → ℝ) (hblim : Tendsto b atTop (𝓝 T)) :
    Tendsto (fun n => eLpNorm F 10 (localMeasure T (b n))) atTop (𝓝 0) := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᶠ n in atTop, t ∉ Set.Icc T (b n) := by
    filter_upwards [volume.ae_ne T] with t ht
    by_cases hlt : T < t
    · filter_upwards [hblim.eventually (Iio_mem_nhds hlt)] with n hn
      exact fun hm => (not_le_of_gt hn) hm.2
    · exact Eventually.of_forall fun _ hm => ht (le_antisymm (le_of_not_gt hlt) hm.1)
  have h := tendsto_eLpNorm_indicator_eventually_empty (Lp.memLp F)
    (by norm_num : (10 : ℝ≥0∞) ≠ 0) (by norm_num : (10 : ℝ≥0∞) ≠ ∞)
    (fun n => measurableSet_Icc (a := T) (b := b n)) he
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet] using h

/-- One terminal restart controls every compact segment between the left endpoint and it. -/
theorem exists_uniform_small_s_left_tail (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 T c : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (hTc : T < c)
    (hU : Set.Ioc T c ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormAfter U T c M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ d : ℝ, T < d ∧ d < c ∧
      ∀ (b : ℝ) (hbd : b ≤ d), T < b → ∀ hI : Set.Icc b d ⊆ U.domain,
        pathValueSize (intervalMeasure b d) (U.path hbd hI) < ENNReal.ofReal epsilon := by
  obtain ⟨F, _, hF, _⟩ := exists_global_value_of_uniform_s_after hDensity hSob U hTc hU M hbound
  obtain ⟨d, _, hdmem, hdlim⟩ := exists_seq_strictAnti_tendsto' hTc
  have heps : (0 : ℝ≥0∞) < ENNReal.ofReal epsilon := ENNReal.ofReal_pos.mpr hepsilon
  obtain ⟨n, hn⟩ := ((global_value_finite_left_tail_tendsto F d hdlim).eventually
    (Iio_mem_nhds heps)).exists
  refine ⟨d n, (hdmem n).1, (hdmem n).2, ?_⟩
  intro b hbd hTb hI
  have hF' : ∀ᵐ t ∂localMeasure b (d n),
      (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
    apply ae_mono (Measure.restrict_mono_set volume ?_) hF
    intro t ht
    exact ⟨hTb.trans_le ht.1, ht.2.trans (hdmem n).2.le⟩
  rw [actual_pathValueSize_eq hDensity hSob U hbd hI F hF']
  exact (eLpNorm_mono_measure F (localMeasure_mono hTb.le (le_refl (d n)))).trans_lt hn

#print axioms exists_global_value_of_uniform_s_after
#print axioms global_value_finite_left_tail_tendsto
#print axioms exists_uniform_small_s_left_tail
end HartreeF.ActualLeftSTail
