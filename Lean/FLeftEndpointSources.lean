import FFiniteEndpointSourceBounds
import FActualHartreeSourceCoherence
import FCompatibleSourceExhaustion
import FActualIntervalSourceBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteEndpoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded CriticalSourceBounds ForcingDomain ForcingContinuity
open SobolevStretch StationarySelfTest
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalPathIntervalSource
  sourceGlobalValue sourceGlobalGradient

/-- A common finite time interval supplies a fixed scalar L² majorant. -/
theorem exists_zeroExtension_norm_bound_left {E : Type*} [NormedAddCommGroup E]
    (T a C : ℝ) (hC : 0 ≤ C) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ {b : ℝ}, T ≤ b → ∀ F : Lp E 2 (localMeasure b a),
      (∀ᵐ t ∂localMeasure b a, ‖F t‖ ≤ C) →
      ‖extendTimeLp (Set.Icc b a) measurableSet_Icc F‖ ≤ D := by
  let g : Lp ℝ 2 (localMeasure T a) :=
    (memLp_const C : MemLp (fun _ : ℝ => C) 2 (localMeasure T a)).toLp (fun _ => C)
  let G := extendTimeLp (Set.Icc T a) measurableSet_Icc g
  refine ⟨‖G‖, norm_nonneg _, ?_⟩
  intro b hb F hF
  apply Lp.norm_le_norm_of_ae_le
  have hg : (g : ℝ → ℝ) =ᵐ[localMeasure T a] fun _ => C :=
    (memLp_const C : MemLp (fun _ : ℝ => C) 2 (localMeasure T a)).coeFn_toLp
  filter_upwards [extendTimeLp_coeFn (Set.Icc b a) measurableSet_Icc F,
    extendTimeLp_coeFn (Set.Icc T a) measurableSet_Icc g,
    (ae_restrict_iff' measurableSet_Icc).mp hF,
    (ae_restrict_iff' measurableSet_Icc).mp hg] with t ht hG htF htg
  rw [ht, hG]
  by_cases hm : t ∈ Set.Icc b a
  · have hmT : t ∈ Set.Icc T a := ⟨hb.trans hm.1, hm.2⟩
    simpa only [Set.indicator_of_mem hm, Set.indicator_of_mem hmT,
      htg hmT, Real.norm_eq_abs, abs_of_nonneg hC] using htF hm
  · simp only [Set.indicator_of_notMem hm, norm_zero]
    exact norm_nonneg _

attribute [local irreducible] criticalGradient energyValue energyGradient

/-- One bound controls the actual value and all three actual weak derivative
sources for every shorter interval. The only path premise is its graph norm. -/
theorem exists_actual_source_uniform_bound_left (hDensity : OrdinaryH1Density)
    {K alpha c a T M : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {b : ℝ} (hab : b ≤ a), T ≤ b →
      ∀ u : CriticalPath (intervalMeasure b a), ‖u‖ ≤ M →
      ‖sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0)‖ ≤ D ∧
      ∀ j : Fin 3,
        ‖sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0) j‖ ≤ D := by
  obtain ⟨C, hC, hforce⟩ := exists_forcingLp_norm_bound hH hM
  let scalarChoice := @exists_zeroExtension_norm_bound_left SourceSpace inferInstance T a C hC
  let D : ℝ := Classical.choose scalarChoice
  have hD : 0 ≤ D := (Classical.choose_spec scalarChoice).1
  have hscalar : ∀ {b : ℝ}, T ≤ b → ∀ F : Lp SourceSpace 2 (localMeasure b a),
      (∀ᵐ t ∂localMeasure b a, ‖F t‖ ≤ C) →
      ‖extendTimeLp (Set.Icc b a) measurableSet_Icc F‖ ≤ D :=
    (Classical.choose_spec scalarChoice).2
  let gradientChoice := criticalPathIntervalSource_cap_single_bound hDensity hSob hH
  let A : ℝ≥0 := Classical.choose gradientChoice
  let B : ℝ := (A : ℝ) * M ^ (2 * alpha) * (normComparisonConstant K)^5 * M^5
  refine ⟨max D B, hD.trans (le_max_left _ _), ?_⟩
  intro b hab hb u hu
  constructor
  · rw [sourceGlobalValue, extendEndpointSource]
    apply (hscalar hb _ ?_).trans (le_max_left _ _)
    filter_upwards [criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u]
      with t ht
    have he : (criticalPathIntervalSource hDensity hSob hH hab u 0).value t =
        forcingLp hH (energyValue (extendEnergyPath hab (energyPath _ u) t)) := by
      apply Lp.ext
      exact ht.trans ((forcing_memLp hH
        (Lp.memLp (energyValue (extendEnergyPath hab (energyPath _ u) t)))).coeFn_toLp).symm
    rw [he]
    apply hforce
    exact (energyPath_value_norm_le (intervalMeasure b a) u (Set.projIcc b a hab t)).trans hu
  · intro j
    rw [sourceGlobalGradient, extendEndpointSource_norm]
    apply ((Classical.choose_spec gradientChoice) hab u M M hM hM
      ((energyPath_norm_le (intervalMeasure b a) u).trans hu) ?_ j).trans
      (le_max_right _ _)
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro k
    exact (criticalGradient_norm_le (intervalMeasure b a) u k).trans hu

#print axioms HartreeF.FiniteEndpoint.exists_zeroExtension_norm_bound_left
#print axioms HartreeF.FiniteEndpoint.exists_actual_source_uniform_bound_left
end HartreeF.FiniteEndpoint


namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open SobolevStretch StationarySelfTest Retarded ForcingDomain

/-- Coherent, uniformly L²-bounded compatible sources exhaust a finite time
interval. Spatial derivative compatibility is inherited on the countable
cover; the missing terminal time is Lebesgue null. -/
theorem exists_compatibleIntervalSource_exhaustion_left
    {a T : ℝ} (b : ℕ → ℝ) (hbt : ∀ n, T < b n)
    (hcover : ∀ t ∈ Set.Ioc T a, ∃ n, b n ≤ t)
    (F : (n : ℕ) → CompatibleIntervalSource (b n) a) (C : ℝ)
    (hvbound : ∀ n, ‖sourceGlobalValue (F n)‖ ≤ C)
    (hgbound : ∀ n j, ‖sourceGlobalGradient (F n) j‖ ≤ C)
    (hcoherent : ∀ n m, n ≤ m → ∀ᵐ t ∂localMeasure (b n) a,
      sourceGlobalValue (F n) t = sourceGlobalValue (F m) t ∧
        ∀ j : Fin 3, sourceGlobalGradient (F n) j t = sourceGlobalGradient (F m) j t) :
    ∃ G : CompatibleIntervalSource T a, ‖G.value‖ ≤ C ∧
      (∀ j, ‖G.gradient j‖ ≤ C) ∧
      ∀ n, ∀ᵐ t ∂localMeasure (b n) a, G.value t = (F n).value t ∧
        ∀ j : Fin 3, G.gradient j t = (F n).gradient j t := by
  have hvsupport (n : ℕ) : ∀ᵐ t ∂volume,
      t ∉ Set.Icc (b n) a → sourceGlobalValue (F n) t = 0 := by
    filter_upwards [extendEndpointSource_coeFn (Set.Icc (b n) a)
      measurableSet_Icc (F n).value] with t ht
    intro htn
    simpa only [sourceGlobalValue, Set.indicator_of_notMem htn] using ht
  have hgsupport (j : Fin 3) (n : ℕ) : ∀ᵐ t ∂volume,
      t ∉ Set.Icc (b n) a → sourceGlobalGradient (F n) j t = 0 := by
    filter_upwards [extendEndpointSource_coeFn (Set.Icc (b n) a)
      measurableSet_Icc ((F n).gradient j)] with t ht
    intro htn
    simpa only [sourceGlobalGradient, Set.indicator_of_notMem htn] using ht
  have hvcoherent (n m : ℕ) (hnm : n ≤ m) : ∀ᵐ t ∂volume,
      t ∈ Set.Icc (b n) a → sourceGlobalValue (F m) t = sourceGlobalValue (F n) t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp (hcoherent n m hnm)] with t ht
    exact fun htn => (ht htn).1.symm
  have hgcoherent (j : Fin 3) (n m : ℕ) (hnm : n ≤ m) : ∀ᵐ t ∂volume,
      t ∈ Set.Icc (b n) a → sourceGlobalGradient (F m) j t = sourceGlobalGradient (F n) j t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp (hcoherent n m hnm)] with t ht
    exact fun htn => ((ht htn).2 j).symm
  obtain ⟨v, hvb, hvl, _⟩ := FEndpoint.exists_coherent_L2_exhaustion
    (fun n => Set.Icc (b n) a) (fun n => sourceGlobalValue (F n)) C
    hvbound hvsupport hvcoherent
  have hge (j : Fin 3) := FEndpoint.exists_coherent_L2_exhaustion
    (fun n => Set.Icc (b n) a) (fun n => sourceGlobalGradient (F n) j) C
    (fun n => hgbound n j) (hgsupport j) (hgcoherent j)
  choose g hgb hgl _ using hge
  let v' : LocalEndpointSource (Set.Icc T a) :=
    shrinkLp 2 (Measure.restrict_le_self : localMeasure T a ≤ volume) v
  let g' : Fin 3 → LocalEndpointSource (Set.Icc T a) := fun j =>
    shrinkLp 2 (Measure.restrict_le_self : localMeasure T a ≤ volume) (g j)
  have hv' : ∀ᵐ t ∂localMeasure T a, v' t = v t := shrinkLp_coeFn 2 _ v
  have hg' : ∀ᵐ t ∂localMeasure T a, ∀ j, g' j t = g j t :=
    ae_all_iff.mpr fun j => shrinkLp_coeFn 2 _ (g j)
  have hvl' : ∀ᵐ t ∂volume, ∀ n,
      t ∈ Set.Icc (b n) a → v t = sourceGlobalValue (F n) t := ae_all_iff.mpr hvl
  have hgl' : ∀ᵐ t ∂volume, ∀ n j,
      t ∈ Set.Icc (b n) a → g j t = sourceGlobalGradient (F n) j t :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => hgl j n
  have hd' : ∀ᵐ t ∂volume, ∀ n j,
      ∂_{coordinate j} (Lp.toTemperedDistribution (sourceGlobalValue (F n) t)) =
        Lp.toTemperedDistribution (sourceGlobalGradient (F n) j t) :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => sourceGlobalDerivative (F n) j
  have hd : ∀ᵐ t ∂localMeasure T a, ∀ j,
      ∂_{coordinate j} (Lp.toTemperedDistribution (v' t)) =
        Lp.toTemperedDistribution (g' j t) := by
    filter_upwards [hv', hg', ae_restrict_of_ae hvl', ae_restrict_of_ae hgl',
      ae_restrict_of_ae hd', ae_restrict_of_ae (volume.ae_ne T),
      ae_restrict_mem measurableSet_Icc] with t htv htg htlv htlg htd htne htmem
    obtain ⟨n, htn⟩ := hcover t ⟨lt_of_le_of_ne htmem.1 (Ne.symm htne), htmem.2⟩
    intro j
    rw [htv, htg j, htlv n ⟨htn, htmem.2⟩, htlg n j ⟨htn, htmem.2⟩]
    exact htd n j
  let G : CompatibleIntervalSource T a := ⟨v', g', hd⟩
  refine ⟨G, (shrinkLp_norm_le 2
    (Measure.restrict_le_self : localMeasure T a ≤ volume) v).trans hvb,
    (fun j => (shrinkLp_norm_le 2
      (Measure.restrict_le_self : localMeasure T a ≤ volume) (g j)).trans (hgb j)), ?_⟩
  intro n
  have hmu : localMeasure (b n) a ≤ localMeasure T a :=
    localMeasure_mono (a := T) (hbt n).le le_rfl
  have hlocalv := extendEndpointSource_restrict_coeFn (Set.Icc (b n) a)
    measurableSet_Icc (F n).value
  have hlocalg : ∀ᵐ t ∂localMeasure (b n) a, ∀ j,
      sourceGlobalGradient (F n) j t = (F n).gradient j t :=
    ae_all_iff.mpr fun j => extendEndpointSource_restrict_coeFn
      (Set.Icc (b n) a) measurableSet_Icc ((F n).gradient j)
  filter_upwards [ae_mono hmu hv', ae_mono hmu hg', ae_restrict_of_ae hvl',
    ae_restrict_of_ae hgl', hlocalv, hlocalg, ae_restrict_mem measurableSet_Icc]
    with t htv htg htlv htlg hvn hgn htmem
  exact ⟨htv.trans ((htlv n htmem).trans hvn),
    fun j => (htg j).trans ((htlg n j htmem).trans (hgn j))⟩

end HartreeF.ActualDuhamelPath

#print axioms HartreeF.ActualDuhamelPath.exists_compatibleIntervalSource_exhaustion_left

namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open SobolevStretch StationarySelfTest Retarded ForcingDomain
attribute [local irreducible] criticalPathIntervalSource energyPath
  energySubmodule criticalPathSubmodule energyDistribution

/-- Literal Hartree sources on nested intervals with a common right endpoint
agree together with their three weak derivatives. -/
theorem criticalPathIntervalSource_global_coherent_left (hDensity : OrdinaryH1Density)
    {K alpha c a b d : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (hda : d ≤ a)
    (u : CriticalPath (intervalMeasure a b)) (v : CriticalPath (intervalMeasure d b))
    (hagree : ∀ t : Set.Icc a b, energyPath _ u t =
      energyPath _ v ⟨t, hda.trans t.property.1, t.property.2⟩) :
    ∀ᵐ t ∂localMeasure a b,
      sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0) t =
        sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH (hda.trans hab) v 0) t ∧
      ∀ j : Fin 3,
        sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0) j t =
          sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH (hda.trans hab) v 0) j t := by
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  let G := criticalPathIntervalSource hDensity hSob hH (hda.trans hab) v 0
  have hmu : localMeasure a b ≤ localMeasure d b := localMeasure_mono hda le_rfl
  have hv : ∀ᵐ t ∂localMeasure a b, F.value t = G.value t := by
    filter_upwards [criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u,
      ae_mono hmu (criticalPathIntervalSource_single_coeFn hDensity hSob hH (hda.trans hab) v),
      ae_restrict_mem measurableSet_Icc] with t hu hv ht
    have he : extendEnergyPath hab (energyPath _ u) t =
        extendEnergyPath (hda.trans hab) (energyPath _ v) t :=
      (extendEnergyPath_val hab (energyPath _ u) ⟨t, ht⟩).trans
        ((hagree ⟨t, ht⟩).trans (extendEnergyPath_val (hda.trans hab)
          (energyPath _ v) ⟨t, hda.trans ht.1, ht.2⟩).symm)
    apply Lp.ext
    rw [he] at hu
    exact hu.trans hv.symm
  have hg : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3, F.gradient j t = G.gradient j t := by
    filter_upwards [hv, F.derivative, ae_mono hmu G.derivative] with t ht hF hG
    intro j
    apply endpointSource_distribution_injective
    exact (hF j).symm.trans ((congrArg
      (fun f : SourceSpace => ∂_{coordinate j} (Lp.toTemperedDistribution f)) ht).trans (hG j))
  have hvF := extendEndpointSource_restrict_coeFn (Set.Icc a b) measurableSet_Icc F.value
  have hvG := ae_mono hmu
    (extendEndpointSource_restrict_coeFn (Set.Icc d b) measurableSet_Icc G.value)
  have hgF : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      sourceGlobalGradient F j t = F.gradient j t :=
    ae_all_iff.mpr (fun j => extendEndpointSource_restrict_coeFn
      (Set.Icc a b) measurableSet_Icc (F.gradient j))
  have hgG : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      sourceGlobalGradient G j t = G.gradient j t :=
    ae_all_iff.mpr (fun j => ae_mono hmu
      (extendEndpointSource_restrict_coeFn (Set.Icc d b) measurableSet_Icc (G.gradient j)))
  filter_upwards [hv, hg, hvF, hvG, hgF, hgG] with t hv hg hF hG hF' hG'
  exact ⟨hF.trans (hv.trans hG.symm), fun j => (hF' j).trans ((hg j).trans (hG' j).symm)⟩
end HartreeF.ActualDuhamelPath
#print axioms HartreeF.ActualDuhamelPath.criticalPathIntervalSource_global_coherent_left
