import FPositiveTerminalApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.TerminalFamilyLateErrorReview
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalPathRestriction WaveTerminal
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath backwardHartreeDuhamelMap hartreeDuhamelMap criticalPathIntervalSource restrictPath IsMildHartreePath

/-- Any baseline family of actual terminal solutions has uniformly vanishing
late restricted graph error. No cap or error estimate is assumed for that
family. The energy cap is chosen before the family and every tolerance.
This compares equal terminal cutoffs only and asserts no terminal-cutoff limit. -/
theorem terminal_family_uniform_late_error (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B : ℝ, 0<B ∧
      (∀ delta : ℝ, 0<delta →
        ∃ eta T : ℝ, 0<eta ∧ eta≤delta ∧ ∀ A R : ℝ, T≤A → ∀ hAR : A≤R,
        ∃ u : CriticalPath (intervalMeasure A R),
          backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hAR
            (freeEnergyState hDensity hSob R phi) u=u ∧
          energyPath _ u ⟨R,hAR,le_rfl⟩=freeEnergyState hDensity hSob R phi ∧
          IsMildHartreePath hAR alpha kernel (energyPath _ u ⟨A,le_rfl,hAR⟩) u ∧
          ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤eta ∧
          ‖u-freeCriticalPath hDensity hSob hfree A R phi‖≤eta/2) ∧
      ∀ T0 : ℝ,
      ∀ U : ∀ R : ℝ, T0≤R → CriticalPath (intervalMeasure T0 R),
      (∀ R : ℝ, ∀ h0R : T0≤R,
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH h0R
          (freeEnergyState hDensity hSob R phi) (U R h0R)=U R h0R) →
      ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ h0A : T0≤A,
      ∀ R : ℝ, ∀ hAR : A≤R,
        let w := restrictPath h0A hAR le_rfl (U R (h0A.trans hAR))
        ‖energyPath _ w‖≤B ∧ ‖fun j => criticalGradient _ j w‖≤delta ∧
        ‖w-freeCriticalPath hDensity hSob hfree A R phi‖≤delta/2 := by
  let produced := exists_positive_terminal_approximations hDensity hSob h0 hfree hret hH phi
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
  let A := max T0 T
  have h0A : T0≤A := le_max_left _ _
  have hTA : T≤A := le_max_right _ _
  refine ⟨A,h0A,?_⟩
  intro R hAR
  let pathChoice := hpaths A R hTA hAR
  let v : CriticalPath (intervalMeasure A R) := Classical.choose pathChoice
  have hv : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hAR
      (freeEnergyState hDensity hSob R phi) v=v := (Classical.choose_spec pathChoice).1
  have hE : ‖energyPath _ v‖≤B := (Classical.choose_spec pathChoice).2.2.2.1
  have hW : ‖fun j => criticalGradient _ j v‖≤eta := (Classical.choose_spec pathChoice).2.2.2.2.1
  have herr : ‖v-freeCriticalPath hDensity hSob hfree A R phi‖≤eta/2 :=
    (Classical.choose_spec pathChoice).2.2.2.2.2
  let w := restrictPath h0A hAR le_rfl (U R (h0A.trans hAR))
  have heq : w=v := terminal_approximations_left_restriction
    hDensity hSob h0 hfree hret hH h0A hAR phi (U R (h0A.trans hAR)) v
      (hU R (h0A.trans hAR)) hv
  exact ⟨(congrArg (fun z : CriticalPath (intervalMeasure A R) => ‖energyPath _ z‖) heq).le.trans hE,
    (congrArg (fun z : CriticalPath (intervalMeasure A R) => ‖fun j => criticalGradient _ j z‖)
      heq).le.trans (hW.trans hetad),
    (congrArg (fun z : CriticalPath (intervalMeasure A R) =>
      ‖z-freeCriticalPath hDensity hSob hfree A R phi‖) heq).le.trans
      (herr.trans (div_le_div_of_nonneg_right hetad (by norm_num)))⟩

#print axioms terminal_family_uniform_late_error
end HartreeF.TerminalFamilyLateErrorReview
