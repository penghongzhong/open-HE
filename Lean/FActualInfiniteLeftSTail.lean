import FActualInfiniteSTail

/-! The actual infinite left half-line L10 realization. This uses genuine
compact mild paths on [a-n,a], not a time-reversed PDE trajectory. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualInfiniteLeftSTail
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalJointSources
open CriticalSourceBounds TimeHolder SobolevStretch StationarySelfTest MaximalTrajectory
open CriticalPathRestriction CutoffApproximation ActualSTail
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields
  pathValueLp globalPathValue

/-- Uniform finite actual S on all compact terminal segments. -/
def UniformSNormBefore {alpha kernel s0 : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (a : ℝ) (M : ℝ≥0) : Prop :=
  ∀ (b : ℝ) (hba : b ≤ a), ∀ hI : Set.Icc b a ⊆ U.domain,
    pathValueSize (intervalMeasure b a) (U.path hba hI) ≤ (M : ℝ≥0∞)

/-- Compact terminal segments exhaust one real L10 class representing the
same actual state on the entire left half-line. -/
theorem exists_global_value_of_uniform_s_before (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 a : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0)
    (hU : Set.Iic a ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormBefore U a M) :
    ∃ F : GlobalValueSpace, ‖F‖ ≤ (M : ℝ) ∧
      (∀ᵐ t ∂volume.restrict (Set.Iic a),
        (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t)) ∧
      (∀ᵐ t ∂volume, t ∉ Set.Iic a → F t = 0) := by
  let b : ℕ → ℝ := fun n => a - n
  have hba : ∀ n, b n ≤ a := by
    intro n
    exact sub_le_self a (Nat.cast_nonneg n)
  have hbanti : Antitone b := by
    intro n m hnm
    have hcast : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    dsimp [b]
    linarith only [hcast]
  have hI : ∀ n, Set.Icc (b n) a ⊆ U.domain := fun _ _ ht => hU ht.2
  let f : ℕ → GlobalValueSpace := fun n =>
    globalPathValue hDensity hSob (hba n) (U.path (hba n) (hI n))
  have hfbound : ∀ n, ‖f n‖ ≤ (M : ℝ) := by
    intro n
    change ‖globalPathValue hDensity hSob (hba n) (U.path (hba n) (hI n))‖ ≤ (M : ℝ)
    rw [globalPathValue_norm]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top
      (hbound (b n) (hba n) (hI n))).trans_eq (by simp)
  have hfsupport : ∀ n, ∀ᵐ t ∂volume, t ∉ Set.Icc (b n) a → f n t = 0 :=
    fun n => globalPathValue_support hDensity hSob (hba n) (U.path (hba n) (hI n))
  have hfactual : ∀ n, ∀ᵐ t ∂localMeasure (b n) a,
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    fun n => globalPathValue_actual hDensity hSob U (hba n) (hI n)
  have hfcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂volume,
      t ∈ Set.Icc (b n) a → f m t = f n t := by
    intro n m hnm
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hfactual n,
      ae_mono (localMeasure_mono (hbanti hnm) (le_refl a)) (hfactual m)] with t hn hm
    exact Lp.ext (hm.trans hn.symm)
  obtain ⟨F, hFM, hFlocal, hFzero⟩ := FEndpoint.exists_coherent_L10_exhaustion
    (fun n => Set.Icc (b n) a) f (M : ℝ) hfbound hfsupport hfcoherent
  have hcover : ∀ t : ℝ, ∃ n, b n ≤ t := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge (a-t)
    exact ⟨n, by dsimp [b]; linarith only [hn]⟩
  have hactual : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc (b n) a →
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hfactual n)
  have hlocal : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc (b n) a → F t = f n t :=
    ae_all_iff.mpr hFlocal
  refine ⟨F, hFM, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hactual, ae_restrict_of_ae hlocal,
      ae_restrict_mem measurableSet_Iic] with t ht hl hm
    obtain ⟨n, hn⟩ := hcover t
    rw [hl n ⟨hn, hm⟩]
    exact ht n ⟨hn, hm⟩
  · filter_upwards [hFzero] with t ht
    intro htn
    apply ht
    intro hmem
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact htn hn.2

/-- Closed left tails vanish for a genuine global L10 class. -/
theorem global_value_infinite_left_tail_tendsto (F : GlobalValueSpace)
    (b : ℕ → ℝ) (hblim : Tendsto b atTop atBot) :
    Tendsto (fun n => eLpNorm F 10 (volume.restrict (Set.Iic (b n))))
      atTop (𝓝 0) := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᶠ n in atTop, t ∉ Set.Iic (b n) := by
    filter_upwards [] with t
    filter_upwards [hblim.eventually (eventually_lt_atBot t)] with n hn
    exact not_le_of_gt hn
  have h := tendsto_eLpNorm_indicator_eventually_empty (Lp.memLp F)
    (by norm_num : (10 : ℝ≥0∞) ≠ 0) (by norm_num : (10 : ℝ≥0∞) ≠ ∞)
    (fun n => measurableSet_Iic (a := b n)) he
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.nullMeasurableSet] using h

/-- One c controls every earlier compact [b,c], including b=c. -/
theorem exists_uniform_small_s_left_tail_before (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 a : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0)
    (hU : Set.Iic a ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormBefore U a M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, c ≤ a ∧ ∀ (b : ℝ) (hbc : b ≤ c), ∀ hI : Set.Icc b c ⊆ U.domain,
      pathValueSize (intervalMeasure b c) (U.path hbc hI) < ENNReal.ofReal epsilon := by
  obtain ⟨F, _, hF, _⟩ := exists_global_value_of_uniform_s_before hDensity hSob U hU M hbound
  let d : ℕ → ℝ := fun n => a-n
  have hda : ∀ n, d n ≤ a := fun n => sub_le_self a (Nat.cast_nonneg n)
  have hdlim : Tendsto d atTop atBot := by
    apply tendsto_atBot.2
    intro r
    obtain ⟨N, hN⟩ := exists_nat_ge (a-r)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    dsimp [d]
    linarith only [hN, hcast]
  have heps : (0 : ℝ≥0∞) < ENNReal.ofReal epsilon := ENNReal.ofReal_pos.mpr hepsilon
  obtain ⟨n, hn⟩ := ((global_value_infinite_left_tail_tendsto F d hdlim).eventually
    (Iio_mem_nhds heps)).exists
  refine ⟨d n, hda n, ?_⟩
  intro b hbc hI
  have hF' : ∀ᵐ t ∂localMeasure b (d n),
      (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
    apply ae_mono (Measure.restrict_mono_set volume ?_) hF
    intro t ht
    exact ht.2.trans (hda n)
  rw [actual_pathValueSize_eq hDensity hSob U hbc hI F hF']
  exact (eLpNorm_mono_measure F
    (Measure.restrict_mono_set volume (fun _ ht => ht.2))).trans_lt hn

set_option pp.universes true
#check @UniformSNormBefore
#print axioms UniformSNormBefore
#check @exists_global_value_of_uniform_s_before
#print axioms exists_global_value_of_uniform_s_before
#check @global_value_infinite_left_tail_tendsto
#print axioms global_value_infinite_left_tail_tendsto
#check @exists_uniform_small_s_left_tail_before
#print axioms exists_uniform_small_s_left_tail_before
end HartreeF.ActualInfiniteLeftSTail
