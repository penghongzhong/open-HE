import FLeftEndpointSources
import FLeftClosedEndpointPath
import Mathlib.Topology.Order.IsLUB

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FiniteEndpoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness MaximalTrajectory
open SobolevStretch StationarySelfTest ActualStrichartz
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource backwardHartreeDuhamelMap
  sourceGlobalValue sourceGlobalGradient leftClosedSourcePath

/-- One bound on all actual compact critical graph paths ending at c. -/
def UniformCriticalNormAfter {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (T c M : ℝ) : Prop :=
  ∀ (b : ℝ) (hbc : b ≤ c), T < b → ∀ hI : Set.Icc b c ⊆ U.domain,
    ‖U.path hbc hI‖ ≤ M

/-- A uniform actual graph bound constructs a closed left-endpoint path by
source exhaustion. The source, endpoint state, and backward mild equation are
outputs, with the literal Hartree nonlinearity unchanged. -/
theorem exists_closed_backward_mild_of_uniform_critical_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a T c M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hTc : T < c) (hU : Set.Ioc T c ⊆ U.domain)
    (hbound : UniformCriticalNormAfter U T c M) :
    ∃ w : CriticalPath (intervalMeasure T c),
      (∀ t : Set.Icc T c, T < (t : ℝ) → energyPath _ w t = U.state t) ∧
      IsBackwardMildHartreePath hTc.le alpha kernel (U.state c) w := by
  obtain ⟨b, hbmono, hbmem, hblim⟩ := exists_seq_strictAnti_tendsto' hTc
  have hbc : ∀ n, b n ≤ c := fun n => (hbmem n).2.le
  have hTb : ∀ n, T < b n := fun n => (hbmem n).1
  have hI : ∀ n, Set.Icc (b n) c ⊆ U.domain := by
    intro n t ht
    exact hU ⟨(hTb n).trans_le ht.1, ht.2⟩
  let u : (n : ℕ) → CriticalPath (intervalMeasure (b n) c) :=
    fun n => U.path (hbc n) (hI n)
  have hu : ∀ n, IsBackwardMildHartreePath (hbc n) alpha kernel (U.state c) (u n) := by
    intro n
    have hf := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      (hbc n) (U.state (b n)) (u n)).mp (U.path_mild (hbc n) (hI n))
    have hb := forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH
      (hbc n) (U.state (b n)) (u n) hf
    have he : energyPath _ (u n) ⟨c, hbc n, le_rfl⟩ = U.state c :=
      U.path_agrees (hbc n) (hI n) ⟨c, hbc n, le_rfl⟩
    apply (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      (hbc n) (U.state c) (u n)).mpr
    exact (congrArg (fun z : EnergyState =>
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (hbc n) z (u n)) he).symm.trans hb
  have hum : ∀ n, ‖u n‖ ≤ M := fun n => hbound (b n) (hbc n) (hTb n) (hI n)
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hum 0)
  have hcover : ∀ t ∈ Set.Ioc T c, ∃ n, b n ≤ t := by
    intro t ht
    have he : ∀ᶠ n in atTop, b n < t := hblim.eventually (Iio_mem_nhds ht.1)
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨n, hn.le⟩
  let F : (n : ℕ) → CompatibleIntervalSource (b n) c :=
    fun n => criticalPathIntervalSource hDensity hSob hH (hbc n) (u n) 0
  let boundChoice := exists_actual_source_uniform_bound_left hDensity hSob hH
    (a := c) (T := T) hM
  let D : ℝ := Classical.choose boundChoice
  have hvbound : ∀ n, ‖sourceGlobalValue (F n)‖ ≤ D :=
    fun n => ((Classical.choose_spec boundChoice).2 (hbc n) (hTb n).le (u n) (hum n)).1
  have hgbound : ∀ n j, ‖sourceGlobalGradient (F n) j‖ ≤ D :=
    fun n => ((Classical.choose_spec boundChoice).2 (hbc n) (hTb n).le (u n) (hum n)).2
  have hcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂localMeasure (b n) c,
      sourceGlobalValue (F n) t = sourceGlobalValue (F m) t ∧
      ∀ j : Fin 3, sourceGlobalGradient (F n) j t = sourceGlobalGradient (F m) j t := by
    intro n m hnm
    apply criticalPathIntervalSource_global_coherent_left hDensity hSob hH
      (hbc n) (hbmono.antitone hnm) (u n) (u m)
    intro t
    exact (U.path_agrees (hbc n) (hI n) t).trans
      (U.path_agrees (hbc m) (hI m)
        ⟨t, (hbmono.antitone hnm).trans t.property.1, t.property.2⟩).symm
  let sourceChoice := exists_compatibleIntervalSource_exhaustion_left
    b hTb hcover F D hvbound hgbound hcoherent
  let G : CompatibleIntervalSource T c := Classical.choose sourceChoice
  have hG : ∀ n, ∀ᵐ t ∂localMeasure (b n) c,
      G.value t = (F n).value t ∧ ∀ j : Fin 3, G.gradient j t = (F n).gradient j t :=
    (Classical.choose_spec sourceChoice).2.2
  let w : CriticalPath (intervalMeasure T c) :=
    leftClosedSourcePath hDensity hSob h0 hfree hret (U.state c) G
  have hw : ∀ n (t : Set.Icc (b n) c),
      energyPath _ w ⟨t, (hTb n).le.trans t.property.1, t.property.2⟩ =
        energyPath _ (u n) t := by
    intro n t
    exact leftClosedSourcePath_agrees hDensity hSob h0 hfree hret hH
      (hbc n) (hTb n).le (U.state c) G (u n) (hu n) ((hG n).mono fun _ ht => ht.1) t
  have hagree : ∀ t : Set.Icc T c, T < (t : ℝ) → energyPath _ w t = U.state t := by
    intro t ht
    obtain ⟨n, hn⟩ := hcover t ⟨ht, t.property.2⟩
    exact (hw n ⟨t, hn, t.property.2⟩).trans
      (U.path_agrees (hbc n) (hI n) ⟨t, hn, t.property.2⟩)
  have hactual : ∀ n, ∀ᵐ t ∂localMeasure (b n) c,
      (G.value t : Space → ℂ) =ᵐ[volume]
        forcing alpha kernel (energyValue (extendEnergyPath hTc.le (energyPath _ w) t)) := by
    intro n
    filter_upwards [hG n,
      criticalPathIntervalSource_single_coeFn hDensity hSob hH (hbc n) (u n),
      ae_restrict_mem measurableSet_Icc] with t ht hs htm
    have he : extendEnergyPath hTc.le (energyPath _ w) t =
        extendEnergyPath (hbc n) (energyPath _ (u n)) t := by
      exact (extendEnergyPath_val hTc.le (energyPath _ w)
        ⟨t, (hTb n).le.trans htm.1, htm.2⟩).trans
        ((hw n ⟨t, htm⟩).trans
          (extendEnergyPath_val (hbc n) (energyPath _ (u n)) ⟨t, htm⟩).symm)
    filter_upwards [hs] with x hx
    exact (congrArg (fun z : SourceSpace => z x) ht.1).trans
      (hx.trans (congrArg (fun z : EnergyState =>
        forcing alpha kernel (energyValue z) x) he.symm))
  have hsource : ∀ᵐ t ∂localMeasure T c, (G.value t : Space → ℂ) =ᵐ[volume]
      forcing alpha kernel (energyValue (extendEnergyPath hTc.le (energyPath _ w) t)) := by
    have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n, t ∈ Set.Icc (b n) c →
        (G.value t : Space → ℂ) =ᵐ[volume]
          forcing alpha kernel (energyValue (extendEnergyPath hTc.le (energyPath _ w) t)) :=
      ae_all_iff.mpr (fun n => (ae_restrict_iff' measurableSet_Icc).mp (hactual n))
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := (volume : Measure ℝ).ae_ne T
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_of_ae hne,
      ae_restrict_mem measurableSet_Icc] with t ht hn hm
    let hncover := hcover t ⟨lt_of_le_of_ne hm.1 (Ne.symm hn), hm.2⟩
    exact ht (Classical.choose hncover) ⟨Classical.choose_spec hncover, hm.2⟩
  exact ⟨w, hagree, leftClosedSourcePath_mild hDensity hSob h0 hfree hret
    hTc.le (U.state c) G hsource⟩

#print axioms HartreeF.FiniteEndpoint.exists_closed_backward_mild_of_uniform_critical_norm
end HartreeF.FiniteEndpoint
