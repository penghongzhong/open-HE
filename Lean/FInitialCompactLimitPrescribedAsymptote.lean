import FInitialCompactLimitsMaximalRealization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.IncomingWaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction WaveInitialCauchy
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest ActualStrichartz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath freeCriticalPath

/-- The SAME baseline early error passes to every compact limit. Tolerance
and its cutoff A precede arbitrary S<=A and evaluation times in [S,A]. -/
theorem initialCompactLimits_uniform_early_energy_error (hDensity : OrdinaryH1Density)
    {K Ch T : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (phi : EnergyState)
    (U : ∀ R : ℝ, R≤T → CriticalPath (intervalMeasure R T))
    (V : ∀ S : ℝ, S≤T → CriticalPath (intervalMeasure S T))
    (hV : ∀ S (hST : S≤T), Tendsto (initialCompactSequence hST U) atTop (𝓝 (V S hST)))
    (hearly : ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hAT : A≤T,
      ∀ R (hRA : R≤A), ‖restrictPath le_rfl hRA hAT (U R (hRA.trans hAT))-
        freeCriticalPath hDensity hSob hfree R A phi‖≤delta/2) :
    ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hAT : A≤T,
      ∀ S (hSA : S≤A) (t : Icc S A),
        ‖energyPath _ (V S (hSA.trans hAT)) ⟨t,t.property.1,t.property.2.trans hAT⟩-
          freeEnergyState hDensity hSob t phi‖≤delta/2 := by
  intro delta hdelta
  let early := hearly delta hdelta
  let A : ℝ := Classical.choose early
  let hAT : A≤T := Classical.choose (Classical.choose_spec early)
  have herr := Classical.choose_spec (Classical.choose_spec early)
  refine ⟨A,hAT,?_⟩
  intro S hSA t
  let hST := hSA.trans hAT
  let s : Icc S T := ⟨t,t.property.1,t.property.2.trans hAT⟩
  let u := initialCompactSequence hST U
  have hpoint : ∀ n, ‖energyPath _ (u n) s-freeEnergyState hDensity hSob t phi‖≤delta/2 := by
    intro n
    let R := min S (T-n)
    have hRS : R≤S := min_le_left _ _
    have hRA : R≤A := hRS.trans hSA
    let v := U R (hRA.trans hAT)
    have he := restrictPath_energy hRS hST le_rfl v s
    have hb := initial_early_error_at hDensity hSob hfree hAT hRA
      (hRS.trans t.property.1) t.property.2 phi v (herr R hRA)
    exact (congrArg (fun z : EnergyState => ‖z-freeEnergyState hDensity hSob t phi‖) he).le.trans hb
  let eval : CriticalPath (intervalMeasure S T) →L[ℂ] EnergyState :=
    (ContinuousMap.evalCLM ℂ s).comp (energyPath _)
  have ht : Tendsto (fun n => eval (u n)) atTop (𝓝 (eval (V S hST))) :=
    (eval.continuous.tendsto (V S hST)).comp (hV S hST)
  have hsub : Tendsto (fun n => eval (u n)-freeEnergyState hDensity hSob t phi) atTop
      (𝓝 (eval (V S hST)-freeEnergyState hDensity hSob t phi)) := ht.sub tendsto_const_nhds
  have hn := Filter.Tendsto.norm (E := EnergyState) hsub
  exact le_of_tendsto hn (Eventually.of_forall hpoint)

/-- An actual state curve represented by these compact limits has the
prescribed atBot EnergyState asymptote. The final root produces this
representation on the canonical maximal trajectory. -/
theorem initialCompactLimits_state_prescribed_asymptote (hDensity : OrdinaryH1Density)
    {K Ch T : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (phi : EnergyState)
    (U : ∀ R : ℝ, R≤T → CriticalPath (intervalMeasure R T))
    (V : ∀ S : ℝ, S≤T → CriticalPath (intervalMeasure S T))
    (hV : ∀ S (hST : S≤T), Tendsto (initialCompactSequence hST U) atTop (𝓝 (V S hST)))
    (hearly : ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hAT : A≤T,
      ∀ R (hRA : R≤A), ‖restrictPath le_rfl hRA hAT (U R (hRA.trans hAT))-
        freeCriticalPath hDensity hSob hfree R A phi‖≤delta/2)
    (state : ℝ → EnergyState)
    (hstate : ∀ S (hST : S≤T) (t : Icc S T), state t=energyPath _ (V S hST) t) :
    Tendsto (fun t => ‖state t-freeEnergyState hDensity hSob t phi‖) atBot (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let chosen := initialCompactLimits_uniform_early_energy_error hDensity hSob hfree phi U V hV hearly
    epsilon hepsilon
  let A : ℝ := Classical.choose chosen
  let hAT : A≤T := Classical.choose (Classical.choose_spec chosen)
  have herr := Classical.choose_spec (Classical.choose_spec chosen)
  filter_upwards [eventually_le_atBot A] with t ht
  have hb : ‖state t-freeEnergyState hDensity hSob t phi‖≤epsilon/2 :=
    (congrArg (fun z : EnergyState => ‖z-freeEnergyState hDensity hSob t phi‖)
      (hstate t (ht.trans hAT) ⟨t,le_rfl,ht.trans hAT⟩)).le.trans
        (herr t ht ⟨t,le_rfl,ht⟩)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  exact hb.trans_lt (half_lt_self hepsilon)

end HartreeF.IncomingWaveRealization
