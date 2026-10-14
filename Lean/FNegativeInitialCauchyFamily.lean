import FInitialFamilyCompactCauchy
import FInitialLimitFixedPoint
import FInitialFamilyEarlyError

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveInitialCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalPathRestriction WaveInitial CriticalUniqueness
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource restrictPath IsMildHartreePath

/-- One genuine finite-initial family, produced for arbitrary homogeneous
asymptotic data, is Cauchy on every fixed compact interval. All comparison,
cap and early-error properties are conclusions of the existing ordinary
analytic inputs; none is a wave-operator premise. The SAME B is used to
select the comparison radius before choosing the baseline family. -/
theorem exists_negative_initial_cauchy_family (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B rho T : ℝ, 0<B ∧ 0<rho ∧ rho≤1 ∧
    ∃ U : ∀ R : ℝ, R≤T → CriticalPath (intervalMeasure R T),
      (∀ R (hRT : R≤T),
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hRT
          (freeEnergyState hDensity hSob R phi) (U R hRT)=U R hRT) ∧
      (∀ R (hRT : R≤T), ‖energyPath _ (U R hRT)‖≤B) ∧
      (∀ R (hRT : R≤T), ‖fun j => criticalGradient _ j (U R hRT)‖≤rho) ∧
      (∀ S (hST : S≤T), CauchySeq (initialCompactSequence hST U)) ∧
      (∀ S (hST : S≤T), ∃ u : CriticalPath (intervalMeasure S T),
        Tendsto (initialCompactSequence hST U) atTop (𝓝 u) ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤rho ∧
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hST
          (energyPath _ u ⟨S,le_rfl,hST⟩) u=u ∧
        IsMildHartreePath hST alpha kernel (energyPath _ u ⟨S,le_rfl,hST⟩) u) ∧
      (∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hAT : A≤T,
        ∀ R (hRA : R≤A),
          let w := restrictPath le_rfl hRA hAT (U R (hRA.trans hAT))
          ‖energyPath _ w‖≤B ∧ ‖fun j => criticalGradient _ j w‖≤delta ∧
          ‖w-freeCriticalPath hDensity hSob hfree R A phi‖≤delta/2) := by
  let produced := initial_family_uniform_early_error hDensity hSob h0 hfree hret hH phi
  let B : ℝ := Classical.choose produced
  have hB : 0<B := (Classical.choose_spec produced).1
  let compared := exists_forward_two_data_comparison hDensity hSob h0 hfree hret hH hB.le
  let rho : ℝ := Classical.choose compared
  have hrho : 0<rho := (Classical.choose_spec compared).1
  have hrho1 : rho≤1 := (Classical.choose_spec compared).2.1
  let small := (Classical.choose_spec produced).2.1 rho hrho
  let eta : ℝ := Classical.choose small
  let tail := Classical.choose_spec small
  let T : ℝ := Classical.choose tail
  have hetarho : eta≤rho := (Classical.choose_spec tail).2.1
  let paths := (Classical.choose_spec tail).2.2
  let U : ∀ R : ℝ, R≤T → CriticalPath (intervalMeasure R T) :=
    fun R hRT => Classical.choose (paths R T le_rfl hRT)
  have hU : ∀ R (hRT : R≤T),
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hRT
        (freeEnergyState hDensity hSob R phi) (U R hRT)=U R hRT := by
    intro R hRT
    exact (Classical.choose_spec (paths R T le_rfl hRT)).1
  have hE : ∀ R (hRT : R≤T), ‖energyPath _ (U R hRT)‖≤B := by
    intro R hRT
    exact (Classical.choose_spec (paths R T le_rfl hRT)).2.2.2.1
  have hW : ∀ R (hRT : R≤T), ‖fun j => criticalGradient _ j (U R hRT)‖≤rho := by
    intro R hRT
    exact (Classical.choose_spec (paths R T le_rfl hRT)).2.2.2.2.1.trans hetarho
  have hearly := (Classical.choose_spec produced).2.2 T U hU
  have hcauchy : ∀ S (hST : S≤T), CauchySeq (initialCompactSequence hST U) := by
    intro S hST
    apply initial_family_compact_cauchy hDensity hSob h0 hfree hret hH hrho phi
      (fun hab f g u v huE hvE huW hvW =>
        ((Classical.choose_spec compared).2.2 hab f g u v huE hvE huW hvW).2)
      U hU hE hW ?_ hST
    intro delta hdelta
    let choice := hearly delta hdelta
    let A : ℝ := Classical.choose choice
    let hAT : A≤T := Classical.choose (Classical.choose_spec choice)
    refine ⟨A,hAT,?_⟩
    intro R hRA
    exact (Classical.choose_spec (Classical.choose_spec choice) R hRA).2.2
  refine ⟨B,rho,T,hB,hrho,hrho1,U,hU,hE,hW,hcauchy,?_,hearly⟩
  intro S hST
  let converges := cauchySeq_tendsto_of_complete (hcauchy S hST)
  let u : CriticalPath (intervalMeasure S T) := Classical.choose converges
  have hu : Tendsto (initialCompactSequence hST U) atTop (𝓝 u) :=
    Classical.choose_spec converges
  have hseq := initialCompactSequence_caps_fixedPoint hDensity hSob h0 hfree hret hH
    hrho.le hST phi U hU hE hW
  have hclosed := forward_fixedPoint_of_graph_limit hDensity hSob h0 hfree hret hH hST
    (fun f g v w hvE hwE hvW hwW =>
      ((Classical.choose_spec compared).2.2 hST f g v w hvE hwE hvW hwW).1)
    (initialCompactSequence hST U) u hu (fun n => (hseq n).1)
      (fun n => (hseq n).2.1) (fun n => (hseq n).2.2)
  refine ⟨u,hu,hclosed.1,hclosed.2.1,hclosed.2.2,?_⟩
  exact (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hST
    (energyPath _ u ⟨S,le_rfl,hST⟩) u).mpr hclosed.2.2

end HartreeF.WaveInitialCauchy
