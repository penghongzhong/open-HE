import FTerminalFamilyCompactCauchy
import FTerminalLimitFixedPoint
import FIndependentTerminalFamilyLateError

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalPathRestriction TerminalFamilyLateErrorReview CriticalUniqueness
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource restrictPath IsMildHartreePath

/-- One genuine finite-terminal family, produced for arbitrary homogeneous
asymptotic data, is Cauchy on every fixed compact interval. All comparison,
cap and late-error properties are conclusions of the existing ordinary
analytic inputs; none is a wave-operator premise. The SAME B is used to
select the comparison radius before choosing the baseline family. -/
theorem exists_positive_terminal_cauchy_family (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B rho T : ℝ, 0<B ∧ 0<rho ∧ rho≤1 ∧
    ∃ U : ∀ R : ℝ, T≤R → CriticalPath (intervalMeasure T R),
      (∀ R (hTR : T≤R),
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hTR
          (freeEnergyState hDensity hSob R phi) (U R hTR)=U R hTR) ∧
      (∀ R (hTR : T≤R), ‖energyPath _ (U R hTR)‖≤B) ∧
      (∀ R (hTR : T≤R), ‖fun j => criticalGradient _ j (U R hTR)‖≤rho) ∧
      (∀ S (hTS : T≤S), CauchySeq (terminalCompactSequence hTS U)) ∧
      (∀ S (hTS : T≤S), ∃ u : CriticalPath (intervalMeasure T S),
        Tendsto (terminalCompactSequence hTS U) atTop (𝓝 u) ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤rho ∧
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hTS
          (energyPath _ u ⟨S,hTS,le_rfl⟩) u=u ∧
        IsMildHartreePath hTS alpha kernel (energyPath _ u ⟨T,le_rfl,hTS⟩) u) ∧
      (∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hTA : T≤A,
        ∀ R (hAR : A≤R),
          let w := restrictPath hTA hAR le_rfl (U R (hTA.trans hAR))
          ‖energyPath _ w‖≤B ∧ ‖fun j => criticalGradient _ j w‖≤delta ∧
          ‖w-freeCriticalPath hDensity hSob hfree A R phi‖≤delta/2) := by
  let produced := terminal_family_uniform_late_error hDensity hSob h0 hfree hret hH phi
  let B : ℝ := Classical.choose produced
  have hB : 0<B := (Classical.choose_spec produced).1
  let compared := exists_backward_two_data_comparison hDensity hSob h0 hfree hret hH hB.le
  let rho : ℝ := Classical.choose compared
  have hrho : 0<rho := (Classical.choose_spec compared).1
  have hrho1 : rho≤1 := (Classical.choose_spec compared).2.1
  let small := (Classical.choose_spec produced).2.1 rho hrho
  let eta : ℝ := Classical.choose small
  let tail := Classical.choose_spec small
  let T : ℝ := Classical.choose tail
  have hetarho : eta≤rho := (Classical.choose_spec tail).2.1
  let paths := (Classical.choose_spec tail).2.2
  let U : ∀ R : ℝ, T≤R → CriticalPath (intervalMeasure T R) :=
    fun R hTR => Classical.choose (paths T R le_rfl hTR)
  have hU : ∀ R (hTR : T≤R),
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hTR
        (freeEnergyState hDensity hSob R phi) (U R hTR)=U R hTR := by
    intro R hTR
    exact (Classical.choose_spec (paths T R le_rfl hTR)).1
  have hE : ∀ R (hTR : T≤R), ‖energyPath _ (U R hTR)‖≤B := by
    intro R hTR
    exact (Classical.choose_spec (paths T R le_rfl hTR)).2.2.2.1
  have hW : ∀ R (hTR : T≤R), ‖fun j => criticalGradient _ j (U R hTR)‖≤rho := by
    intro R hTR
    exact (Classical.choose_spec (paths T R le_rfl hTR)).2.2.2.2.1.trans hetarho
  have hlate := (Classical.choose_spec produced).2.2 T U hU
  have hcauchy : ∀ S (hTS : T≤S), CauchySeq (terminalCompactSequence hTS U) := by
    intro S hTS
    apply terminal_family_compact_cauchy hDensity hSob h0 hfree hret hH hrho phi
      (fun hab f g u v huE hvE huW hvW =>
        ((Classical.choose_spec compared).2.2 hab f g u v huE hvE huW hvW).2)
      U hU hE hW ?_ hTS
    intro delta hdelta
    let choice := hlate delta hdelta
    let A : ℝ := Classical.choose choice
    let hTA : T≤A := Classical.choose (Classical.choose_spec choice)
    refine ⟨A,hTA,?_⟩
    intro R hAR
    exact (Classical.choose_spec (Classical.choose_spec choice) R hAR).2.2
  refine ⟨B,rho,T,hB,hrho,hrho1,U,hU,hE,hW,hcauchy,?_,hlate⟩
  intro S hTS
  let converges := cauchySeq_tendsto_of_complete (hcauchy S hTS)
  let u : CriticalPath (intervalMeasure T S) := Classical.choose converges
  have hu : Tendsto (terminalCompactSequence hTS U) atTop (𝓝 u) :=
    Classical.choose_spec converges
  have hseq := terminalCompactSequence_caps_fixedPoint hDensity hSob h0 hfree hret hH
    hrho.le hTS phi U hU hE hW
  have hclosed := backward_fixedPoint_of_graph_limit hDensity hSob h0 hfree hret hH hTS
    (fun f g v w hvE hwE hvW hwW =>
      ((Classical.choose_spec compared).2.2 hTS f g v w hvE hwE hvW hwW).1)
    (terminalCompactSequence hTS U) u hu (fun n => (hseq n).1)
      (fun n => (hseq n).2.1) (fun n => (hseq n).2.2)
  refine ⟨u,hu,hclosed.1,hclosed.2.1,hclosed.2.2,?_⟩
  exact (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hTS
    (energyPath _ u ⟨T,le_rfl,hTS⟩) u).mpr
      (backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH
        hTS (energyPath _ u ⟨S,hTS,le_rfl⟩) u hclosed.2.2)

end HartreeF.WaveCauchy
