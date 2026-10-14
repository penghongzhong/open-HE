import FActualSValueRealization
import FCoherentL10Exhaustion
import FiniteLpTail
import Mathlib.Topology.Order.IsLUB

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

/-- Uniform finiteness of the genuine extended S norm on all compact prefixes.
There is no energy-coordinate or W-coordinate bound in this condition. -/
def UniformSNormBefore {alpha kernel s0 : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (a T : ℝ) (M : ℝ≥0) : Prop :=
  ∀ (b : ℝ) (hab : a ≤ b), b < T → ∀ hI : Set.Icc a b ⊆ U.domain,
    pathValueSize (intervalMeasure a b) (U.path hab hI) ≤ (M : ℝ≥0∞)

/-- Uniform actual S bounds produce one genuine L10_t(L10_x) realization of
this trajectory on the entire half-open interval, with no coherence input. -/
theorem exists_global_value_of_uniform_s (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 a T : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (haT : a < T)
    (hU : Set.Ico a T ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormBefore U a T M) :
    ∃ F : GlobalValueSpace, ‖F‖ ≤ (M : ℝ) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ico a T),
        (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t)) ∧
      (∀ᵐ t ∂volume, t ∉ Set.Ico a T → F t = 0) := by
  obtain ⟨b, hbmono, hbmem, hblim⟩ := exists_seq_strictMono_tendsto' haT
  have hab : ∀ n, a ≤ b n := fun n => (hbmem n).1.le
  have hbT : ∀ n, b n < T := fun n => (hbmem n).2
  have hI : ∀ n, Set.Icc a (b n) ⊆ U.domain := by
    intro n t ht
    exact hU ⟨ht.1, ht.2.trans_lt (hbT n)⟩
  let f : ℕ → GlobalValueSpace := fun n =>
    globalPathValue hDensity hSob (hab n) (U.path (hab n) (hI n))
  have hfbound : ∀ n, ‖f n‖ ≤ (M : ℝ) := by
    intro n
    change ‖globalPathValue hDensity hSob (hab n) (U.path (hab n) (hI n))‖ ≤ (M : ℝ)
    rw [globalPathValue_norm]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top
      (hbound (b n) (hab n) (hbT n) (hI n))).trans_eq (by simp)
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
      ae_mono (localMeasure_mono (a := a) le_rfl (hbmono.monotone hnm)) (hfactual m)]
      with t hn hm
    exact Lp.ext (hm.trans hn.symm)
  obtain ⟨F, hFM, hFlocal, hFzero⟩ := FEndpoint.exists_coherent_L10_exhaustion
    (fun n => Set.Icc a (b n)) f (M : ℝ) hfbound hfsupport hfcoherent
  have hcover : ∀ t ∈ Set.Ico a T, ∃ n, t ≤ b n := by
    intro t ht
    obtain ⟨n, hn⟩ := (hblim.eventually (Ioi_mem_nhds ht.2)).exists
    exact ⟨n, hn.le⟩
  have hactual : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc a (b n) →
      (f n t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hfactual n)
  have hlocal : ∀ᵐ t ∂volume, ∀ n, t ∈ Set.Icc a (b n) → F t = f n t :=
    ae_all_iff.mpr hFlocal
  refine ⟨F, hFM, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hactual, ae_restrict_of_ae hlocal,
      ae_restrict_mem measurableSet_Ico] with t ht hl hm
    obtain ⟨n, hn⟩ := hcover t hm
    rw [hl n ⟨hm.1, hn⟩]
    exact ht n ⟨hm.1, hn⟩
  · filter_upwards [hFzero] with t ht
    intro htn
    apply ht
    intro hmem
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact htn ⟨hn.1, hn.2.trans_lt (hbT n)⟩

/-- Strong L10 tails shrink at every finite right endpoint. The endpoint itself
is discarded by its zero Lebesgue measure. -/
theorem global_value_finite_tail_tendsto {T : ℝ} (F : GlobalValueSpace)
    (b : ℕ → ℝ) (hblim : Tendsto b atTop (𝓝 T)) :
    Tendsto (fun n => eLpNorm F 10 (localMeasure (b n) T)) atTop (𝓝 0) := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᶠ n in atTop, t ∉ Set.Icc (b n) T := by
    filter_upwards [volume.ae_ne T] with t ht
    by_cases hlt : t < T
    · filter_upwards [hblim.eventually (Ioi_mem_nhds hlt)] with n hn
      exact fun hm => (not_le_of_gt hn) hm.1
    · exact Eventually.of_forall fun _ hm => ht (le_antisymm hm.2 (le_of_not_gt hlt))
  have h := tendsto_eLpNorm_indicator_eventually_empty (Lp.memLp F)
    (by norm_num : (10 : ℝ≥0∞) ≠ 0) (by norm_num : (10 : ℝ≥0∞) ≠ ∞)
    (fun n => measurableSet_Icc (a := b n) (b := T)) he
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet] using h

/-- One restart c is chosen before the later endpoint b, and controls every
actual compact tail [c,b]. Only finite S on the prefixes is assumed. -/
theorem exists_uniform_small_s_tail (hDensity : OrdinaryH1Density)
    {K alpha kernel s0 a T : ℝ} (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (haT : a < T)
    (hU : Set.Ico a T ⊆ U.domain) (M : ℝ≥0) (hbound : UniformSNormBefore U a T M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, a < c ∧ c < T ∧
      ∀ (b : ℝ) (hcb : c ≤ b), b < T → ∀ hI : Set.Icc c b ⊆ U.domain,
        pathValueSize (intervalMeasure c b) (U.path hcb hI) < ENNReal.ofReal epsilon := by
  obtain ⟨F, _, hF, _⟩ := exists_global_value_of_uniform_s hDensity hSob U haT hU M hbound
  obtain ⟨d, _, hdmem, hdlim⟩ := exists_seq_strictMono_tendsto' haT
  have heps : (0 : ℝ≥0∞) < ENNReal.ofReal epsilon := ENNReal.ofReal_pos.mpr hepsilon
  obtain ⟨n, hn⟩ := ((global_value_finite_tail_tendsto F d hdlim).eventually
    (Iio_mem_nhds heps)).exists
  refine ⟨d n, (hdmem n).1, (hdmem n).2, ?_⟩
  intro b hcb hbT hI
  have hF' : ∀ᵐ t ∂localMeasure (d n) b,
      (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
    apply ae_mono (Measure.restrict_mono_set volume ?_) hF
    intro t ht
    exact ⟨(hdmem n).1.le.trans ht.1, ht.2.trans_lt hbT⟩
  rw [actual_pathValueSize_eq hDensity hSob U hcb hI F hF']
  exact (eLpNorm_mono_measure F (localMeasure_mono (a := d n) le_rfl hbT.le)).trans_lt hn

set_option pp.universes true in
#check @exists_uniform_small_s_tail
#print axioms exists_global_value_of_uniform_s
#print axioms global_value_finite_tail_tendsto
#print axioms exists_uniform_small_s_tail
end HartreeF.ActualSTail
