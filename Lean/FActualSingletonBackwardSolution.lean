import FBackwardPDEForcedConsumer
import FDirectionalHartreeRebasing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.BackwardFinitePerturbation
open EnergySpace CriticalPathSpace ActualDuhamelPath SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain CriticalUniqueness EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource

/-- A genuine critical path with arbitrary prescribed energy terminal datum on [b,b]. -/
def singletonBackwardPath (hDensity : OrdinaryH1Density) {K Ch : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (b : ℝ) (f : EnergyState) :
    CriticalPath (intervalMeasure b b) :=
  freeCriticalPath hDensity hSob hfree b b (freeEnergyState hDensity hSob (-b) f)

theorem singletonBackwardPath_terminal (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch) (b : ℝ) (f : EnergyState) :
    energyPath _ (singletonBackwardPath hDensity hSob hfree b f) ⟨b,le_rfl,le_rfl⟩=f :=
  backwardFreeCriticalPath_terminal hDensity hSob hfree le_rfl f

/-- The same actual free path is a true backward Hartree fixed point on the singleton. -/
theorem singletonBackwardPath_fixed (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c) (b : ℝ) (f : EnergyState) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH le_rfl f
      (singletonBackwardPath hDensity hSob hfree b f) = singletonBackwardPath hDensity hSob hfree b f := by
  let u := singletonBackwardPath hDensity hSob hfree b f
  let P := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH le_rfl f u
  apply energyPath_injective _
  apply ContinuousMap.ext
  intro t
  have ht : t=(⟨b,le_rfl,le_rfl⟩ : Set.Icc b b) := Subtype.ext (le_antisymm t.property.2 t.property.1)
  have hp := backwardHartreeDuhamelMap_terminal hDensity hSob h0 hfree hret hH le_rfl f u
  have hu := singletonBackwardPath_terminal hDensity hSob hfree b f
  exact (congrArg (fun s : Set.Icc b b => energyPath _ P s) ht).trans
    (hp.trans (hu.symm.trans (congrArg (fun s : Set.Icc b b => energyPath _ u s) ht.symm)))

/-- The singleton path retains full-Z membership and its potentially nonzero energy value. -/
theorem singletonBackwardPath_fullZ (hDensity : OrdinaryH1Density) {K Ch Che : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (b : ℝ) (f : EnergyState) :
    FullZPath (singletonBackwardPath hDensity hSob hfree b f) :=
  ⟨freeCriticalPath_endpointWitness hDensity hSob hfree hefree b b (freeEnergyState hDensity hSob (-b) f)⟩

end HartreeF.BackwardFinitePerturbation
