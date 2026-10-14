import FLocalMildTrajectory
import FActualIntervalSourceBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteEndpoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded CriticalSourceBounds ForcingDomain ForcingContinuity
open SobolevStretch StationarySelfTest
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalPathIntervalSource
  sourceGlobalValue sourceGlobalGradient

/-- A finite norm bound for the literal spatial forcing on an energy ball. -/
theorem exists_forcingLp_norm_bound {alpha c M : ℝ} (hH : OrdinaryHLS alpha c)
    (hM : 0 ≤ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EnergyState,
      ‖z‖ ≤ M → ‖forcingLp hH (energyValue z)‖ ≤ C := by
  obtain ⟨L, hL⟩ := forcingLp_lipschitzOn_norm_ball hH M hM
  refine ⟨(L : ℝ) * M + ‖forcingLp hH 0‖, by positivity, ?_⟩
  intro z hz
  have hv : ‖energyValue z‖ ≤ M := (energyState_value_norm_le z).trans hz
  have hb := hL.dist_le_mul (energyValue z) hv 0
    (show (0 : Lp ℂ 6 (volume : Measure Space)) ∈ {v | ‖v‖ ≤ M} by simpa using hM)
  calc
    ‖forcingLp hH (energyValue z)‖ ≤
        dist (forcingLp hH (energyValue z)) (forcingLp hH 0) + ‖forcingLp hH 0‖ := by
      simpa only [dist_eq_norm] using
        (norm_le_norm_sub_add (forcingLp hH (energyValue z)) (forcingLp hH 0))
    _ ≤ (L : ℝ) * M + ‖forcingLp hH 0‖ := by
      exact add_le_add (hb.trans
        (mul_le_mul_of_nonneg_left (by simpa using hv) L.coe_nonneg)) le_rfl

/-- A common finite time interval supplies a fixed scalar L² majorant. -/
theorem exists_zeroExtension_norm_bound {E : Type*} [NormedAddCommGroup E]
    (a T C : ℝ) (hC : 0 ≤ C) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ {b : ℝ}, b ≤ T → ∀ F : Lp E 2 (localMeasure a b),
      (∀ᵐ t ∂localMeasure a b, ‖F t‖ ≤ C) →
      ‖extendTimeLp (Set.Icc a b) measurableSet_Icc F‖ ≤ D := by
  let g : Lp ℝ 2 (localMeasure a T) :=
    (memLp_const C : MemLp (fun _ : ℝ => C) 2 (localMeasure a T)).toLp (fun _ => C)
  let G := extendTimeLp (Set.Icc a T) measurableSet_Icc g
  refine ⟨‖G‖, norm_nonneg _, ?_⟩
  intro b hb F hF
  apply Lp.norm_le_norm_of_ae_le
  have hg : (g : ℝ → ℝ) =ᵐ[localMeasure a T] fun _ => C :=
    (memLp_const C : MemLp (fun _ : ℝ => C) 2 (localMeasure a T)).coeFn_toLp
  filter_upwards [extendTimeLp_coeFn (Set.Icc a b) measurableSet_Icc F,
    extendTimeLp_coeFn (Set.Icc a T) measurableSet_Icc g,
    (ae_restrict_iff' measurableSet_Icc).mp hF,
    (ae_restrict_iff' measurableSet_Icc).mp hg] with t ht hG htF htg
  rw [ht, hG]
  by_cases hm : t ∈ Set.Icc a b
  · have hmT : t ∈ Set.Icc a T := ⟨hm.1, hm.2.trans hb⟩
    simpa only [Set.indicator_of_mem hm, Set.indicator_of_mem hmT,
      htg hmT, Real.norm_eq_abs, abs_of_nonneg hC] using htF hm
  · simp only [Set.indicator_of_notMem hm, norm_zero]
    exact norm_nonneg _

attribute [local irreducible] criticalGradient energyValue energyGradient

/-- One bound controls the actual value and all three actual weak derivative
sources for every shorter interval. The only path premise is its graph norm. -/
theorem exists_actual_source_uniform_bound (hDensity : OrdinaryH1Density)
    {K alpha c a T M : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {b : ℝ} (hab : a ≤ b), b ≤ T →
      ∀ u : CriticalPath (intervalMeasure a b), ‖u‖ ≤ M →
      ‖sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0)‖ ≤ D ∧
      ∀ j : Fin 3,
        ‖sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0) j‖ ≤ D := by
  obtain ⟨C, hC, hforce⟩ := exists_forcingLp_norm_bound hH hM
  let scalarChoice := @exists_zeroExtension_norm_bound SourceSpace inferInstance a T C hC
  let D : ℝ := Classical.choose scalarChoice
  have hD : 0 ≤ D := (Classical.choose_spec scalarChoice).1
  have hscalar : ∀ {b : ℝ}, b ≤ T → ∀ F : Lp SourceSpace 2 (localMeasure a b),
      (∀ᵐ t ∂localMeasure a b, ‖F t‖ ≤ C) →
      ‖extendTimeLp (Set.Icc a b) measurableSet_Icc F‖ ≤ D :=
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
    exact (energyPath_value_norm_le (intervalMeasure a b) u (Set.projIcc a b hab t)).trans hu
  · intro j
    rw [sourceGlobalGradient, extendEndpointSource_norm]
    apply ((Classical.choose_spec gradientChoice) hab u M M hM hM
      ((energyPath_norm_le (intervalMeasure a b) u).trans hu) ?_ j).trans
      (le_max_right _ _)
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro k
    exact (criticalGradient_norm_le (intervalMeasure a b) u k).trans hu

#print axioms HartreeF.FiniteEndpoint.exists_forcingLp_norm_bound
#print axioms HartreeF.FiniteEndpoint.exists_zeroExtension_norm_bound
#print axioms HartreeF.FiniteEndpoint.exists_actual_source_uniform_bound
end HartreeF.FiniteEndpoint
