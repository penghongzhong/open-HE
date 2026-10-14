import FCompactLimitsMaximalRealization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction WaveCauchy
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest ActualStrichartz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath freeCriticalPath

/-- Pass the SAME baseline late-error bound to every fixed compact limit,
then to its actual energy values. Tolerance precedes the late time A;
S and the evaluation time are arbitrary afterward. -/
theorem compactLimits_uniform_late_energy_error (hDensity : OrdinaryH1Density)
    {K Ch T : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (phi : EnergyState)
    (U : ∀ R : ℝ, T≤R → CriticalPath (intervalMeasure T R))
    (V : ∀ S : ℝ, T≤S → CriticalPath (intervalMeasure T S))
    (hV : ∀ S (hTS : T≤S), Tendsto (terminalCompactSequence hTS U) atTop (𝓝 (V S hTS)))
    (hlate : ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hTA : T≤A,
      ∀ R (hAR : A≤R), ‖restrictPath hTA hAR le_rfl (U R (hTA.trans hAR))-
        freeCriticalPath hDensity hSob hfree A R phi‖≤delta/2) :
    ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hTA : T≤A,
      ∀ S (hAS : A≤S) (t : Icc A S),
        ‖energyPath _ (V S (hTA.trans hAS)) ⟨t,hTA.trans t.property.1,t.property.2⟩-
          freeEnergyState hDensity hSob t phi‖≤delta/2 := by
  intro delta hdelta
  let late := hlate delta hdelta
  let A : ℝ := Classical.choose late
  let hTA : T≤A := Classical.choose (Classical.choose_spec late)
  have herr := Classical.choose_spec (Classical.choose_spec late)
  refine ⟨A,hTA,?_⟩
  intro S hAS t
  let hTS := hTA.trans hAS
  let s : Icc T S := ⟨t,hTA.trans t.property.1,t.property.2⟩
  let u := terminalCompactSequence hTS U
  have hpoint : ∀ n, ‖energyPath _ (u n) s-freeEnergyState hDensity hSob t phi‖≤delta/2 := by
    intro n
    let R := max S (T+n)
    have hSR : S≤R := le_max_left _ _
    have hAR : A≤R := hAS.trans hSR
    let v := U R (hTA.trans hAR)
    have he := restrictPath_energy le_rfl hTS hSR v s
    have hb := terminal_late_error_at hDensity hSob hfree hTA hAR t.property.1
      (t.property.2.trans hSR) phi v (herr R hAR)
    exact (congrArg (fun z : EnergyState => ‖z-freeEnergyState hDensity hSob t phi‖) he).le.trans hb
  let eval : CriticalPath (intervalMeasure T S) →L[ℂ] EnergyState :=
    (ContinuousMap.evalCLM ℂ s).comp (energyPath _)
  have ht : Tendsto (fun n => eval (u n)) atTop (𝓝 (eval (V S hTS))) :=
    (eval.continuous.tendsto (V S hTS)).comp (hV S hTS)
  have hsub : Tendsto (fun n => eval (u n)-freeEnergyState hDensity hSob t phi) atTop
      (𝓝 (eval (V S hTS)-freeEnergyState hDensity hSob t phi)) := ht.sub tendsto_const_nhds
  have hn := Filter.Tendsto.norm (E := EnergyState) hsub
  exact le_of_tendsto hn (Eventually.of_forall hpoint)

/-- Any actual state curve identified with these compact limits has the
prescribed positive-time asymptote. The identification is discharged by
maximalState_agrees in the final producer. -/
theorem compactLimits_state_prescribed_asymptote (hDensity : OrdinaryH1Density)
    {K Ch T : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (phi : EnergyState)
    (U : ∀ R : ℝ, T≤R → CriticalPath (intervalMeasure T R))
    (V : ∀ S : ℝ, T≤S → CriticalPath (intervalMeasure T S))
    (hV : ∀ S (hTS : T≤S), Tendsto (terminalCompactSequence hTS U) atTop (𝓝 (V S hTS)))
    (hlate : ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hTA : T≤A,
      ∀ R (hAR : A≤R), ‖restrictPath hTA hAR le_rfl (U R (hTA.trans hAR))-
        freeCriticalPath hDensity hSob hfree A R phi‖≤delta/2)
    (state : ℝ → EnergyState)
    (hstate : ∀ S (hTS : T≤S) (t : Icc T S), state t=energyPath _ (V S hTS) t) :
    Tendsto (fun t => ‖state t-freeEnergyState hDensity hSob t phi‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let chosen := compactLimits_uniform_late_energy_error hDensity hSob hfree phi U V hV hlate
    epsilon hepsilon
  let A : ℝ := Classical.choose chosen
  let hTA : T≤A := Classical.choose (Classical.choose_spec chosen)
  have herr := Classical.choose_spec (Classical.choose_spec chosen)
  refine ⟨A,?_⟩
  intro t ht
  have hb : ‖state t-freeEnergyState hDensity hSob t phi‖≤epsilon/2 :=
    (congrArg (fun z : EnergyState => ‖z-freeEnergyState hDensity hSob t phi‖)
      (hstate t (hTA.trans ht) ⟨t,hTA.trans ht,le_rfl⟩)).le.trans
        (herr t ht ⟨t,ht,le_rfl⟩)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  exact hb.trans_lt (half_lt_self hepsilon)

end HartreeF.WaveRealization
