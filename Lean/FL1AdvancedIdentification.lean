import FL1AdvancedCriticalPath
import FL1RetardedEndpointWitness
import FActualBackwardMildSolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz FreeTestBounds
open BackwardUniformData EndpointOutput ActualBackwardLocalFixedPoint
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energyPath energyGradient criticalGradient
  CompatibleL1IntervalSource.advancedCriticalPath
  CompatibleL1IntervalSource.retardedCriticalPath intervalAdvancedCriticalPath

namespace CompatibleL1IntervalSource
variable {a b : ℝ} (E : CompatibleL1IntervalSource a b)

/-- The scalar limit is the genuine future integral of the original L1 source. -/
theorem advancedCriticalPath_scalar (hDensity : OrdinaryH1Density) {K C0 Ch Cr : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (E.advancedCriticalPath hDensity hSob h0 hfree hret) t) φ =
      ∫ s in Set.Ioc (t : ℝ) b,
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  have hsub : Set.Ioc (t : ℝ) b ⊆ Set.Icc a b :=
    fun _ hs => ⟨t.2.1.trans hs.1.le, hs.2⟩
  have hmeasure := Measure.restrict_mono_set volume hsub
  have hL1 : Tendsto (fun n => eLpNorm (fun s => (E.approximation n).value s-E.value s)
      1 (volume.restrict (Set.Ioc (t : ℝ) b))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      E.approximation_value_eLpNorm_tendsto_zero (fun _ => bot_le)
    intro n
    exact eLpNorm_mono_measure _ hmeasure
  have hscalar := freeTestPair_integral_tendsto_of_L1 hDensity hSob
    (volume.restrict (Set.Ioc (t : ℝ) b)) t φ
    (fun n => (E.approximation n).value) E.value
    (fun n => (E.approximation_value_integrable n).mono_measure hmeasure)
    (E.value_integrable.mono_measure hmeasure) hL1
  have hpath := E.advanced_approximation_scalar_tendsto hDensity hSob h0 hfree hret t φ
  simp only [intervalAdvancedCriticalPath_scalar] at hpath
  exact tendsto_nhds_unique hpath hscalar

/-- The derivative is the actual future restricted L2 operator, at every time. -/
theorem advancedCriticalPath_actual_gradient (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (t : Set.Icc a b) (j : Fin 3) :
    energyGradient j (energyPath _ (E.advancedCriticalPath hDensity hSob h0 hfree hret) t) =
      restrictedL2 h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
        (extendEndpointSource (Set.Icc a b) measurableSet_Icc (E.gradient j)) := by
  have hg : Tendsto (fun n => energyGradient j (energyPath _
      (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret (E.approximation n)) t)) atTop
      (𝓝 (energyGradient j (energyPath _ (E.advancedCriticalPath hDensity hSob h0 hfree hret) t))) :=
    (energyGradient j).continuous.tendsto _ |>.comp
    (E.advanced_approximation_energy_tendsto hDensity hSob h0 hfree hret t)
  have hs : Tendsto (fun n => (E.approximation n).gradient j) atTop (𝓝 (E.gradient j)) :=
    (continuous_apply j).tendsto E.gradient |>.comp E.approximation_gradient_tendsto
  have hr := (restrictedL2CLM h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t).continuous.tendsto _
    |>.comp (extendEndpointSource_tendsto hs)
  simp only [intervalAdvancedCriticalPath_gradient] at hg
  apply tendsto_nhds_unique hg
  simpa only [sourceGlobalGradient, Function.comp_def, restrictedL2CLM_apply] using hr

/-- The advanced limit retains the actual continuous-energy estimate. -/
theorem advancedCriticalPath_energy_norm_le (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr) :
    ‖energyPath _ (E.advancedCriticalPath hDensity hSob h0 hfree hret)‖ ≤
      energyEndpointConstant K C0 * ‖E.gradient‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (energyEndpointConstant_nonneg h0) (norm_nonneg _))).mpr
  intro t
  apply le_of_tendsto' (E.advanced_approximation_energy_tendsto hDensity hSob h0 hfree hret t).norm
  intro n
  exact ((energyPath _ (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (E.approximation n))).norm_coe_le_norm t).trans
    ((intervalAdvancedCriticalPath_energy_norm hDensity hSob h0 hfree hret (E.approximation n)).trans
      (mul_le_mul_of_nonneg_left (E.approximation_gradient_norm_le n) (energyEndpointConstant_nonneg h0)))

/-- The advanced limit retains the unchanged sharp-W exponents. -/
theorem advancedCriticalPath_gradient_norm_le (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (j : Fin 3) :
    ‖criticalGradient _ j (E.advancedCriticalPath hDensity hSob h0 hfree hret)‖ ≤
      (Ch*C0+Cr) * ‖E.gradient j‖ := by
  apply le_of_tendsto_of_tendsto
    (((criticalGradient (intervalMeasure a b) j).continuous.tendsto _).comp
      (E.advanced_approximation_tendsto hDensity hSob h0 hfree hret)).norm
    (tendsto_const_nhds.mul (((continuous_apply j).tendsto E.gradient).comp
      E.approximation_gradient_tendsto).norm)
  exact Eventually.of_forall (fun n => intervalAdvancedCriticalPath_gradient_norm
    hDensity hSob h0 hfree hret (E.approximation n) j)

end CompatibleL1IntervalSource
end HartreeF.ActualDuhamelPath
