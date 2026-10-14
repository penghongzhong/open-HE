import FNegativeInitialApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.WaveInitial
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource restrictPath IsMildHartreePath

/-- Any baseline family of actual initial solutions has uniformly vanishing
early restricted graph error. Its only premise is the actual fixed-point
equation. The same energy cap is chosen before the family and all tolerances.
This compares equal initial cutoffs only and asserts no initial-cutoff limit. -/
theorem initial_family_uniform_early_error (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B : ℝ, 0<B ∧
      (∀ delta : ℝ, 0<delta →
        ∃ eta T : ℝ, 0<eta ∧ eta≤delta ∧ ∀ R A : ℝ, A≤T → ∀ hRA : R≤A,
        ∃ u : CriticalPath (intervalMeasure R A),
          hartreeDuhamelMap hDensity hSob h0 hfree hret hH hRA
            (freeEnergyState hDensity hSob R phi) u=u ∧
          energyPath _ u ⟨R,le_rfl,hRA⟩=freeEnergyState hDensity hSob R phi ∧
          IsMildHartreePath hRA alpha kernel (freeEnergyState hDensity hSob R phi) u ∧
          ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤eta ∧
          ‖u-freeCriticalPath hDensity hSob hfree R A phi‖≤eta/2) ∧
      ∀ T0 : ℝ,
      ∀ U : ∀ R : ℝ, R≤T0 → CriticalPath (intervalMeasure R T0),
      (∀ R : ℝ, ∀ hR0 : R≤T0,
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hR0
          (freeEnergyState hDensity hSob R phi) (U R hR0)=U R hR0) →
      ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hA0 : A≤T0,
      ∀ R : ℝ, ∀ hRA : R≤A,
        let w := restrictPath le_rfl hRA hA0 (U R (hRA.trans hA0))
        ‖energyPath _ w‖≤B ∧ ‖fun j => criticalGradient _ j w‖≤delta ∧
        ‖w-freeCriticalPath hDensity hSob hfree R A phi‖≤delta/2 := by
  let produced := exists_negative_initial_approximations hDensity hSob h0 hfree hret hH phi
  let B : ℝ := Classical.choose produced
  have hB : 0<B := (Classical.choose_spec produced).1
  have hproducer := (Classical.choose_spec produced).2
  refine ⟨B,hB,hproducer,?_⟩
  intro T0 U hU delta hdelta
  let radiusChoice := hproducer delta hdelta
  let eta : ℝ := Classical.choose radiusChoice
  let tailChoice := Classical.choose_spec radiusChoice
  let T : ℝ := Classical.choose tailChoice
  have hetad : eta≤delta := (Classical.choose_spec tailChoice).2.1
  have hpaths := (Classical.choose_spec tailChoice).2.2
  let A := min T0 T
  have hA0 : A≤T0 := min_le_left _ _
  have hAT : A≤T := min_le_right _ _
  refine ⟨A,hA0,?_⟩
  intro R hRA
  let pathChoice := hpaths R A hAT hRA
  let v : CriticalPath (intervalMeasure R A) := Classical.choose pathChoice
  have hv : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hRA
      (freeEnergyState hDensity hSob R phi) v=v := (Classical.choose_spec pathChoice).1
  have hE : ‖energyPath _ v‖≤B := (Classical.choose_spec pathChoice).2.2.2.1
  have hW : ‖fun j => criticalGradient _ j v‖≤eta := (Classical.choose_spec pathChoice).2.2.2.2.1
  have herr : ‖v-freeCriticalPath hDensity hSob hfree R A phi‖≤eta/2 :=
    (Classical.choose_spec pathChoice).2.2.2.2.2
  let w := restrictPath le_rfl hRA hA0 (U R (hRA.trans hA0))
  have heq : w=v := initial_approximations_right_restriction
    hDensity hSob h0 hfree hret hH hRA hA0 phi (U R (hRA.trans hA0)) v
      (hU R (hRA.trans hA0)) hv
  exact ⟨(congrArg (fun z : CriticalPath (intervalMeasure R A) => ‖energyPath _ z‖) heq).le.trans hE,
    (congrArg (fun z : CriticalPath (intervalMeasure R A) => ‖fun j => criticalGradient _ j z‖)
      heq).le.trans (hW.trans hetad),
    (congrArg (fun z : CriticalPath (intervalMeasure R A) =>
      ‖z-freeCriticalPath hDensity hSob hfree R A phi‖) heq).le.trans
      (herr.trans (div_le_div_of_nonneg_right hetad (by norm_num)))⟩

end HartreeF.WaveInitial
