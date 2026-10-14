import FBackwardFullZForcedConsumer
import FActualHartreeBackwardLiteralPDE

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.BackwardPDEConsumer
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence TimeHolder
open ActualPerturbation BackwardPerturbation BackwardPerturbationConsumer
open HartreeDistributionalBridge LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  backwardHartreeDuhamelMap criticalPathIntervalSource freeCriticalPath freeEnergyState
  intervalAdvancedCriticalPath CompatibleL1IntervalSource.advancedCriticalPath

section Abstract
variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [TopologicalSpace T]
theorem complexAddition_map_eval (L : X →L[ℂ] C(T,Y)) (D : Y →L[ℂ] ℂ)
    (x y : X) (t : T) :
    D (L (x+Complex.I • y) t)=D (L x t)+Complex.I*D (L y t) := by
  simp only [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
end Abstract

/-- Exact source formula of the unchanged backward Hartree graph map. -/
theorem backwardHartreeDuhamelMap_source_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (g : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q) t) φ =
      FreeFlow.free ((t : ℝ)-b) (energyDistribution g) φ - Complex.I *
        ∫ s in Set.Ioc (t : ℝ) b,
          Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
            (freeTest ((t : ℝ)-s) φ) := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) g)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab q 0)
  let D : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have he := complexDecrement_map_eval (energyPath (intervalMeasure a b)) D f r t
  have hf : D (energyPath _ f t)=FreeFlow.free ((t : ℝ)-b) (energyDistribution g) φ := by
    change energyDistribution (energyPath _ f t) φ = _
    rw [freeCriticalPath_energy, ← freeEnergyState_add_time, freeEnergyState_distribution]
    rfl
  have hr := intervalAdvancedCriticalPath_scalar hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab q 0) t φ
  unfold backwardHartreeDuhamelMap
  change D (energyPath _ (f-Complex.I • r) t) = _
  exact he.trans (congrArg₂ (fun x y : ℂ => x-Complex.I*y) hf hr)

/-- The original compact distributional Hartree PDE yields the actual backward
forced graph identity with its own terminal trace. -/
theorem actual_backward_forced_graph_of_distributional (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
    (hgen : OrdinaryFreeDistributionScalarGenerator) (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E) :
    q = backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ q ⟨b,hab,le_rfl⟩) q + Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  ext φ
  let g := energyPath (intervalMeasure a b) q ⟨b,hab,le_rfl⟩
  let P := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q
  let A := E.advancedCriticalPath hDensity hSob h0 hfree hret
  let D : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have he := complexAddition_map_eval (energyPath (intervalMeasure a b)) D P A t
  have hp := backwardHartreeDuhamelMap_source_formula hDensity hSob h0 hfree hret hH hab g q t φ
  have ha := E.advancedCriticalPath_scalar hDensity hSob h0 hfree hret t φ
  have hm := actual_backward_literal_of_distributional hDensity hSob hH hab q E h0 hret hgen hUnique hPDE t φ
  exact hm.trans (he.trans (congrArg₂ (fun x y : ℂ => x+Complex.I*y) hp ha)).symm

/-- End-to-end terminal-data stability from the actual compact PDE, with the
original scalar-L1 error and actual gradient-L2 smallness. -/
theorem exists_actual_backward_solution_fullZ_of_small_PDE_error (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator) (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hB : 0 ≤ B) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      ForcedHartreeCompactTestIdentity alpha c hab q E →
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch * ‖f-energyPath _ q ⟨b,hab,le_rfl⟩‖ +
        max (energyEndpointConstant K C0) (Ch*C0+Cr) * ‖E.gradient‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsBackwardMildHartreePath hab alpha c f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
        energyPath _ u ⟨b,hab,le_rfl⟩=f ∧
        ‖u-q‖ ≤ 2*(max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch * ‖f-energyPath _ q ⟨b,hab,le_rfl⟩‖ +
          max (energyEndpointConstant K C0) (Ch*C0+Cr) * ‖E.gradient‖) ∧
        fullZSDifferenceSize u q ≤ ENNReal.ofReal (C*(‖f-energyPath _ q ⟨b,hab,le_rfl⟩‖+‖E.gradient‖)) ∧
        ∀ v : CriticalPath (intervalMeasure a b), IsBackwardMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_backward_solution_fullZ_of_small_forcing
    hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose choice
  let cc := Classical.choose_spec choice
  let C : ℝ := Classical.choose cc
  have hs := Classical.choose_spec cc
  refine ⟨r,C,hs.1,hs.2.1,hs.2.2.1,?_⟩
  intro a b hab f q E hPDE hqE hqW hsmall
  exact hs.2.2.2 hab f (energyPath _ q ⟨b,hab,le_rfl⟩) q E
    (actual_backward_forced_graph_of_distributional hDensity hSob h0 hfree hret hH hab q E hgen hUnique hPDE)
    hqE hqW hsmall

end HartreeF.BackwardPDEConsumer
