import FFiniteEndpointSourceBounds
import FClosedEndpointPathFromSource
import FActualHartreeSourceCoherence
import FCompatibleSourceExhaustion
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
  energyDistribution criticalPathIntervalSource hartreeDuhamelMap
  sourceGlobalValue sourceGlobalGradient closedSourcePath

/-- The sole extra analytic premise in the finite-endpoint criterion: one bound
on the actual compact critical graph norms of this actual trajectory. -/
def UniformCriticalNormBefore {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (T M : ℝ) : Prop :=
  ∀ (b : ℝ) (hab : a ≤ b), b < T → ∀ hI : Set.Icc a b ⊆ U.domain,
    ‖U.path hab hI‖ ≤ M

/-- A bounded actual critical trajectory at a finite endpoint produces its
own closed critical path and the literal Hartree mild equation at that endpoint.
Neither a limiting energy state nor a global nonlinear source is assumed. -/
theorem exists_closed_mild_of_uniform_critical_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a T M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain)
    (hbound : UniformCriticalNormBefore U T M) :
    ∃ w : CriticalPath (intervalMeasure a T),
      (∀ t : Set.Icc a T, (t : ℝ) < T → energyPath _ w t = U.state t) ∧
      IsMildHartreePath haT.le alpha kernel u0 w := by
  obtain ⟨b, hbmono, hbmem, hblim⟩ := exists_seq_strictMono_tendsto' haT
  have hab : ∀ n, a ≤ b n := fun n => (hbmem n).1.le
  have hbT : ∀ n, b n < T := fun n => (hbmem n).2
  have hI : ∀ n, Set.Icc a (b n) ⊆ U.domain := by
    intro n t ht
    exact hU ⟨ht.1, ht.2.trans_lt (hbT n)⟩
  let u : (n : ℕ) → CriticalPath (intervalMeasure a (b n)) :=
    fun n => U.path (hab n) (hI n)
  have hu : ∀ n, IsMildHartreePath (hab n) alpha kernel u0 (u n) := by
    intro n
    simpa only [U.initial] using U.path_mild (hab n) (hI n)
  have hum : ∀ n, ‖u n‖ ≤ M := fun n => hbound (b n) (hab n) (hbT n) (hI n)
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hum 0)
  have hcover : ∀ t ∈ Set.Ico a T, ∃ n, t ≤ b n := by
    intro t ht
    have he : ∀ᶠ n in atTop, t < b n := hblim.eventually (Ioi_mem_nhds ht.2)
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨n, hn.le⟩
  let F : (n : ℕ) → CompatibleIntervalSource a (b n) :=
    fun n => criticalPathIntervalSource hDensity hSob hH (hab n) (u n) 0
  let boundChoice := exists_actual_source_uniform_bound hDensity hSob hH
    (a := a) (T := T) hM
  let D : ℝ := Classical.choose boundChoice
  have hvbound : ∀ n, ‖sourceGlobalValue (F n)‖ ≤ D :=
    fun n => ((Classical.choose_spec boundChoice).2 (hab n) (hbT n).le (u n) (hum n)).1
  have hgbound : ∀ n j, ‖sourceGlobalGradient (F n) j‖ ≤ D :=
    fun n => ((Classical.choose_spec boundChoice).2 (hab n) (hbT n).le (u n) (hum n)).2
  have hcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂localMeasure a (b n),
      sourceGlobalValue (F n) t = sourceGlobalValue (F m) t ∧
      ∀ j : Fin 3, sourceGlobalGradient (F n) j t = sourceGlobalGradient (F m) j t := by
    intro n m hnm
    apply criticalPathIntervalSource_global_coherent hDensity hSob hH
      (hab n) (hbmono.monotone hnm) (u n) (u m)
    intro t
    exact (U.path_agrees (hab n) (hI n) t).trans
      (U.path_agrees (hab m) (hI m)
        ⟨t, t.property.1, t.property.2.trans (hbmono.monotone hnm)⟩).symm
  let sourceChoice := exists_compatibleIntervalSource_exhaustion
    b hbT hcover F D hvbound hgbound hcoherent
  let G : CompatibleIntervalSource a T := Classical.choose sourceChoice
  have hG : ∀ n, ∀ᵐ t ∂localMeasure a (b n),
      G.value t = (F n).value t ∧ ∀ j : Fin 3, G.gradient j t = (F n).gradient j t :=
    (Classical.choose_spec sourceChoice).2.2
  let w : CriticalPath (intervalMeasure a T) :=
    closedSourcePath hDensity hSob h0 hfree hret u0 G
  have hw : ∀ n (t : Set.Icc a (b n)),
      energyPath _ w ⟨t, t.property.1, t.property.2.trans (hbT n).le⟩ =
        energyPath _ (u n) t := by
    intro n t
    exact closedSourcePath_agrees hDensity hSob h0 hfree hret hH
      (hab n) (hbT n).le u0 G (u n) (hu n) ((hG n).mono fun _ ht => ht.1) t
  have hagree : ∀ t : Set.Icc a T, (t : ℝ) < T → energyPath _ w t = U.state t := by
    intro t ht
    obtain ⟨n, hn⟩ := hcover t ⟨t.property.1, ht⟩
    exact (hw n ⟨t, t.property.1, hn⟩).trans
      (U.path_agrees (hab n) (hI n) ⟨t, t.property.1, hn⟩)
  have hactual : ∀ n, ∀ᵐ t ∂localMeasure a (b n),
      (G.value t : Space → ℂ) =ᵐ[volume]
        forcing alpha kernel (energyValue (extendEnergyPath haT.le (energyPath _ w) t)) := by
    intro n
    filter_upwards [hG n,
      criticalPathIntervalSource_single_coeFn hDensity hSob hH (hab n) (u n),
      ae_restrict_mem measurableSet_Icc] with t ht hs htm
    have he : extendEnergyPath haT.le (energyPath _ w) t =
        extendEnergyPath (hab n) (energyPath _ (u n)) t := by
      exact (extendEnergyPath_val haT.le (energyPath _ w)
        ⟨t, htm.1, htm.2.trans (hbT n).le⟩).trans
        ((hw n ⟨t, htm⟩).trans
          (extendEnergyPath_val (hab n) (energyPath _ (u n)) ⟨t, htm⟩).symm)
    filter_upwards [hs] with x hx
    exact (congrArg (fun z : SourceSpace => z x) ht.1).trans
      (hx.trans (congrArg (fun z : EnergyState =>
        forcing alpha kernel (energyValue z) x) he.symm))
  have hsource : ∀ᵐ t ∂localMeasure a T, (G.value t : Space → ℂ) =ᵐ[volume]
      forcing alpha kernel (energyValue (extendEnergyPath haT.le (energyPath _ w) t)) := by
    have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n, t ∈ Set.Icc a (b n) →
        (G.value t : Space → ℂ) =ᵐ[volume]
          forcing alpha kernel (energyValue (extendEnergyPath haT.le (energyPath _ w) t)) :=
      ae_all_iff.mpr (fun n => (ae_restrict_iff' measurableSet_Icc).mp (hactual n))
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := (volume : Measure ℝ).ae_ne T
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_of_ae hne,
      ae_restrict_mem measurableSet_Icc] with t ht hn hm
    let hncover := hcover t ⟨hm.1, lt_of_le_of_ne hm.2 hn⟩
    exact ht (Classical.choose hncover) ⟨hm.1, Classical.choose_spec hncover⟩
  exact ⟨w, hagree, closedSourcePath_mild hDensity hSob h0 hfree hret haT.le u0 G hsource⟩

#print axioms HartreeF.FiniteEndpoint.exists_closed_mild_of_uniform_critical_norm
end HartreeF.FiniteEndpoint
