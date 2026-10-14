import FIntervalRetardedRestart
import FIntervalLpRestriction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open SobolevStretch StationarySelfTest Retarded ForcingDomain

attribute [local irreducible] criticalPathIntervalSource energyPath
  energySubmodule criticalPathSubmodule energyDistribution

/-- The endpoint spatial source class embeds injectively into distributions. -/
theorem endpointSource_distribution_injective :
    Function.Injective (Lp.toTemperedDistribution : SourceSpace → FreeFlow.TD) := by
  exact LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure FreeFlow.V)) (p := ENNReal.ofReal (6/5 : ℝ)))

/-- A compatible source's weak derivatives are determined by its scalar value,
including when the two source classes have different time supports. -/
theorem compatibleIntervalSource_gradient_coherent {a b d : ℝ} (hbd : b ≤ d)
    (F : CompatibleIntervalSource a b) (G : CompatibleIntervalSource a d)
    (hvalue : ∀ᵐ t ∂localMeasure a b, F.value t = G.value t) :
    ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3, F.gradient j t = G.gradient j t := by
  filter_upwards [hvalue, F.derivative,
    ae_mono (localMeasure_mono (a := a) le_rfl hbd) G.derivative] with t ht hF hG
  intro j
  apply endpointSource_distribution_injective
  exact (hF j).symm.trans ((congrArg
    (fun f : SourceSpace => ∂_{coordinate j} (Lp.toTemperedDistribution f)) ht).trans (hG j))

/-- Actual Hartree sources agree on a common interval whenever their actual
energy trajectories agree there. No source-equality hypothesis is assumed. -/
theorem criticalPathIntervalSource_value_coherent (hDensity : OrdinaryH1Density)
    {K alpha c a b d : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (hbd : b ≤ d)
    (u : CriticalPath (intervalMeasure a b)) (v : CriticalPath (intervalMeasure a d))
    (hagree : ∀ t : Set.Icc a b, energyPath _ u t =
      energyPath _ v ⟨t, t.property.1, t.property.2.trans hbd⟩) :
    ∀ᵐ t ∂localMeasure a b,
      (criticalPathIntervalSource hDensity hSob hH hab u 0).value t =
        (criticalPathIntervalSource hDensity hSob hH (hab.trans hbd) v 0).value t := by
  have hs : ∀ t : ℝ, t ∈ Set.Icc a b →
      extendEnergyPath hab (energyPath _ u) t =
        extendEnergyPath (hab.trans hbd) (energyPath _ v) t := by
    intro t ht
    have hu := extendEnergyPath_val hab (energyPath _ u) ⟨t, ht⟩
    have hv := extendEnergyPath_val (hab.trans hbd) (energyPath _ v)
      ⟨t, ht.1, ht.2.trans hbd⟩
    exact hu.trans ((hagree ⟨t, ht⟩).trans hv.symm)
  filter_upwards [criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u,
    ae_mono (localMeasure_mono (a := a) le_rfl hbd)
      (criticalPathIntervalSource_single_coeFn hDensity hSob hH (hab.trans hbd) v),
    ae_restrict_mem measurableSet_Icc] with t hu hv ht
  apply Lp.ext
  rw [hs t ht] at hu
  exact hu.trans hv.symm

/-- Both the scalar and all three weak derivative source classes are coherent. -/
theorem criticalPathIntervalSource_coherent (hDensity : OrdinaryH1Density)
    {K alpha c a b d : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (hbd : b ≤ d)
    (u : CriticalPath (intervalMeasure a b)) (v : CriticalPath (intervalMeasure a d))
    (hagree : ∀ t : Set.Icc a b, energyPath _ u t =
      energyPath _ v ⟨t, t.property.1, t.property.2.trans hbd⟩) :
    ∀ᵐ t ∂localMeasure a b,
      (criticalPathIntervalSource hDensity hSob hH hab u 0).value t =
        (criticalPathIntervalSource hDensity hSob hH (hab.trans hbd) v 0).value t ∧
      ∀ j : Fin 3,
        (criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j t =
          (criticalPathIntervalSource hDensity hSob hH (hab.trans hbd) v 0).gradient j t := by
  have hv := criticalPathIntervalSource_value_coherent hDensity hSob hH hab hbd u v hagree
  exact hv.and (compatibleIntervalSource_gradient_coherent hbd _ _ hv)

/-- Coherent local source classes have coherent global zero extensions on the
smaller interval; this does not identify them outside their common support. -/
theorem sourceGlobal_coherent {a b d : ℝ} (hbd : b ≤ d)
    (F : CompatibleIntervalSource a b) (G : CompatibleIntervalSource a d)
    (hvalue : ∀ᵐ t ∂localMeasure a b, F.value t = G.value t) :
    ∀ᵐ t ∂localMeasure a b, sourceGlobalValue F t = sourceGlobalValue G t ∧
      ∀ j : Fin 3, sourceGlobalGradient F j t = sourceGlobalGradient G j t := by
  have hgradient := compatibleIntervalSource_gradient_coherent hbd F G hvalue
  have hvF := extendEndpointSource_restrict_coeFn (Set.Icc a b) measurableSet_Icc F.value
  have hvG := ae_mono (localMeasure_mono (a := a) le_rfl hbd)
    (extendEndpointSource_restrict_coeFn (Set.Icc a d) measurableSet_Icc G.value)
  have hgF : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      sourceGlobalGradient F j t = F.gradient j t := by
    exact ae_all_iff.mpr (fun j => extendEndpointSource_restrict_coeFn
      (Set.Icc a b) measurableSet_Icc (F.gradient j))
  have hgG : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      sourceGlobalGradient G j t = G.gradient j t := by
    exact ae_all_iff.mpr (fun j => ae_mono (localMeasure_mono (a := a) le_rfl hbd)
      (extendEndpointSource_restrict_coeFn (Set.Icc a d) measurableSet_Icc (G.gradient j)))
  filter_upwards [hvalue, hgradient, hvF, hvG, hgF, hgG] with t hv hg hF hG hF' hG'
  exact ⟨hF.trans (hv.trans hG.symm), fun j => (hF' j).trans ((hg j).trans (hG' j).symm)⟩

/-- Restriction of the actual global zero extensions gives equal L2 classes. -/
theorem sourceGlobal_restriction_classes {a b d : ℝ} (hbd : b ≤ d)
    (F : CompatibleIntervalSource a b) (G : CompatibleIntervalSource a d)
    (hvalue : ∀ᵐ t ∂localMeasure a b, F.value t = G.value t) :
    shrinkLp 2 (Measure.restrict_le_self : localMeasure a b ≤ volume) (sourceGlobalValue F) =
      shrinkLp 2 (Measure.restrict_le_self : localMeasure a b ≤ volume) (sourceGlobalValue G) ∧
    ∀ j : Fin 3,
      shrinkLp 2 (Measure.restrict_le_self : localMeasure a b ≤ volume) (sourceGlobalGradient F j) =
        shrinkLp 2 (Measure.restrict_le_self : localMeasure a b ≤ volume) (sourceGlobalGradient G j) := by
  have hs := sourceGlobal_coherent hbd F G hvalue
  constructor
  · apply Lp.ext
    filter_upwards [shrinkLp_coeFn 2
      (Measure.restrict_le_self : localMeasure a b ≤ volume) (sourceGlobalValue F),
      shrinkLp_coeFn 2 (Measure.restrict_le_self : localMeasure a b ≤ volume)
        (sourceGlobalValue G), hs] with t hF hG ht
    exact hF.trans (ht.1.trans hG.symm)
  · intro j
    apply Lp.ext
    filter_upwards [shrinkLp_coeFn 2
      (Measure.restrict_le_self : localMeasure a b ≤ volume) (sourceGlobalGradient F j),
      shrinkLp_coeFn 2 (Measure.restrict_le_self : localMeasure a b ≤ volume)
        (sourceGlobalGradient G j), hs] with t hF hG ht
    exact hF.trans ((ht.2 j).trans hG.symm)

/-- Every scalar and derivative source extension vanishes off its own support. -/
theorem sourceGlobal_zero_compl {a b : ℝ} (F : CompatibleIntervalSource a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b)ᶜ, sourceGlobalValue F t = 0 ∧
      ∀ j : Fin 3, sourceGlobalGradient F j t = 0 := by
  exact (extendEndpointSource_zero_compl (Set.Icc a b) measurableSet_Icc F.value).and
    (ae_all_iff.mpr (fun j => extendEndpointSource_zero_compl
      (Set.Icc a b) measurableSet_Icc (F.gradient j)))

/-- The global source coherence assertion specialized to true Hartree sources. -/
theorem criticalPathIntervalSource_global_coherent (hDensity : OrdinaryH1Density)
    {K alpha c a b d : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (hbd : b ≤ d)
    (u : CriticalPath (intervalMeasure a b)) (v : CriticalPath (intervalMeasure a d))
    (hagree : ∀ t : Set.Icc a b, energyPath _ u t =
      energyPath _ v ⟨t, t.property.1, t.property.2.trans hbd⟩) :
    ∀ᵐ t ∂localMeasure a b,
      sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0) t =
        sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH (hab.trans hbd) v 0) t ∧
      ∀ j : Fin 3,
        sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0) j t =
          sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH (hab.trans hbd) v 0) j t :=
  sourceGlobal_coherent hbd _ _
    (criticalPathIntervalSource_value_coherent hDensity hSob hH hab hbd u v hagree)

end HartreeF.ActualDuhamelPath

#print axioms HartreeF.ActualDuhamelPath.endpointSource_distribution_injective
#print axioms HartreeF.ActualDuhamelPath.compatibleIntervalSource_gradient_coherent
#print axioms HartreeF.ActualDuhamelPath.criticalPathIntervalSource_value_coherent
#print axioms HartreeF.ActualDuhamelPath.criticalPathIntervalSource_coherent
#print axioms HartreeF.ActualDuhamelPath.sourceGlobal_coherent
#print axioms HartreeF.ActualDuhamelPath.sourceGlobal_restriction_classes
#print axioms HartreeF.ActualDuhamelPath.sourceGlobal_zero_compl
#print axioms HartreeF.ActualDuhamelPath.criticalPathIntervalSource_global_coherent
