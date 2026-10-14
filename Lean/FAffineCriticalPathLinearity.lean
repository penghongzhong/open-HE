import FActualAffineCriticalPath
import FStateFreeAffineCovariance
import FActualFreePathDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath IntervalTimeTransport AffinePath AffineMixed CriticalAffine FreeAffine
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  affineCriticalPath freeCriticalPath freeEnergyState

variable {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
  (u v : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

theorem affineCriticalPath_add : affineCriticalPath ha b c A B hAB (u+v)=
    affineCriticalPath ha b c A B hAB u+affineCriticalPath ha b c A B hAB v := by
  apply energyPath_injective (intervalMeasure A B)
  apply ContinuousMap.ext
  intro t
  simp only [map_add,ContinuousMap.add_apply,affineCriticalPath_energy_apply]
  exact map_add (affineStateEquiv ha b) _ _

theorem affineCriticalPath_smul (z : ℂ) : affineCriticalPath ha b c A B hAB (z • u)=
    z • affineCriticalPath ha b c A B hAB u := by
  apply energyPath_injective (intervalMeasure A B)
  apply ContinuousMap.ext
  intro t
  simp only [map_smul,ContinuousMap.smul_apply,affineCriticalPath_energy_apply]
  exact affineState_smul ha b z _

theorem affineCriticalPath_sub : affineCriticalPath ha b c A B hAB (u-v)=
    affineCriticalPath ha b c A B hAB u-affineCriticalPath ha b c A B hAB v := by
  have hs : u-v=u+(-1:ℂ) • v :=
    (sub_eq_add_neg u v).trans (congrArg (fun z => u+z) (neg_one_smul ℂ v).symm)
  calc
    _ = affineCriticalPath ha b c A B hAB (u+(-1:ℂ) • v) :=
      congrArg (affineCriticalPath ha b c A B hAB) hs
    _ = affineCriticalPath ha b c A B hAB u+
        affineCriticalPath ha b c A B hAB ((-1:ℂ) • v) :=
      affineCriticalPath_add ha b c A B hAB u ((-1:ℂ) • v)
    _ = affineCriticalPath ha b c A B hAB u+(-1:ℂ) • affineCriticalPath ha b c A B hAB v :=
      congrArg (fun z : CriticalPath (intervalMeasure A B) =>
        affineCriticalPath ha b c A B hAB u+z) (affineCriticalPath_smul ha b c A B hAB v (-1))
    _ = _ := (congrArg (fun z : CriticalPath (intervalMeasure A B) =>
        affineCriticalPath ha b c A B hAB u+z)
        (neg_one_smul ℂ (affineCriticalPath ha b c A B hAB v))).trans
      (sub_eq_add_neg (affineCriticalPath ha b c A B hAB u)
        (affineCriticalPath ha b c A B hAB v)).symm

/-- Full actual shifted free CriticalPaths, with the same transformed datum. -/
theorem shifted_free_affine_covariance (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch) (u0 : EnergyState) :
    freeCriticalPath hDensity hSob hfree A B
      (freeEnergyState hDensity hSob (-A) (affineState ha b u0))=
    affineCriticalPath ha b c A B hAB
      (freeCriticalPath hDensity hSob hfree (timeAffine a c A) (timeAffine a c B)
        (freeEnergyState hDensity hSob (-timeAffine a c A) u0)) := by
  apply energyPath_injective (intervalMeasure A B)
  apply ContinuousMap.ext
  intro t
  rw [freeCriticalPath_energy,affineCriticalPath_energy_apply,freeCriticalPath_energy,
    ← freeEnergyState_add_time,← freeEnergyState_add_time]
  have ht : (intervalAffineHomeomorph ha c A B t:ℝ)+(-timeAffine a c A)=a^2*((t:ℝ)+(-A)) := by
    rw [intervalAffineHomeomorph_coe]
    unfold timeAffine
    ring
  rw [ht]
  exact freeEnergyState_affine hDensity hSob ha b ((t:ℝ)+(-A)) u0

#print axioms affineCriticalPath_add
#print axioms affineCriticalPath_sub
#print axioms affineCriticalPath_smul
#print axioms shifted_free_affine_covariance
end HartreeF.NonlinearAffine
