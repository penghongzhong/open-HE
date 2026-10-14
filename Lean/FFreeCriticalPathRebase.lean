import FActualBackwardHartreeMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport Retarded
open SobolevStretch StationarySelfTest ActualStrichartz
local instance rebaseEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance rebaseGraphNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath freeEnergyState criticalPathIntervalSource

/-- Linearity belongs to the actual graph-valued free path. -/
theorem freeCriticalPath_add (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (x y : EnergyState) :
    freeCriticalPath hDensity hSob hfree a b (x+y) =
      freeCriticalPath hDensity hSob hfree a b x + freeCriticalPath hDensity hSob hfree a b y := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  let L := energyPath (intervalMeasure a b)
  let f := freeCriticalPath hDensity hSob hfree a b
  have hp : L (f x + f y) t = L (f x) t + L (f y) t :=
    congrArg (fun q : C(Set.Icc a b, EnergyState) => q t) (L.map_add (f x) (f y))
  exact (freeCriticalPath_energy hDensity hSob hfree a b (x+y) t).trans
    ((freeEnergyState_add hDensity hSob t x y).trans
      ((congrArg₂ (fun v w : EnergyState => v+w)
        (freeCriticalPath_energy hDensity hSob hfree a b x t).symm
        (freeCriticalPath_energy hDensity hSob hfree a b y t).symm).trans hp.symm))

/-- Scalar multiplication is proved on the full graph, using energy injectivity. -/
theorem freeCriticalPath_smul (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (z : ℂ) (x : EnergyState) :
    freeCriticalPath hDensity hSob hfree a b (z • x) =
      z • freeCriticalPath hDensity hSob hfree a b x := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  let L := energyPath (intervalMeasure a b)
  let f := freeCriticalPath hDensity hSob hfree a b
  have hp : L (z • f x) t = z • L (f x) t :=
    congrArg (fun q : C(Set.Icc a b, EnergyState) => q t) (L.map_smul z (f x))
  exact (freeCriticalPath_energy hDensity hSob hfree a b (z • x) t).trans
    ((freeEnergyState_smul hDensity hSob t z x).trans
      ((congrArg (fun v : EnergyState => z • v)
        (freeCriticalPath_energy hDensity hSob hfree a b x t).symm).trans hp.symm))

/-- The linear map packages the already constructed actual free path. -/
def freeCriticalPathLinear (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) : EnergyState →ₗ[ℂ] CriticalPath (intervalMeasure a b) where
  toFun := freeCriticalPath hDensity hSob hfree a b
  map_add' := freeCriticalPath_add hDensity hSob hfree a b
  map_smul' := freeCriticalPath_smul hDensity hSob hfree a b

/-- Evolve the actual energy value at t by the true free group, on the same interval. -/
def criticalPathFreeRebase (hDensity : OrdinaryH1Density) {K Ch a b : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (t : Set.Icc a b) : CriticalPath (intervalMeasure a b) →ₗ[ℂ] CriticalPath (intervalMeasure a b) :=
  (freeCriticalPathLinear hDensity hSob hfree a b).comp
    ((freeEnergyCLM hDensity hSob (-(t : ℝ))).toLinearMap.comp
      (((ContinuousMap.evalCLM ℂ t).comp (energyPath (intervalMeasure a b))).toLinearMap))

theorem criticalPathFreeRebase_apply (hDensity : OrdinaryH1Density) {K Ch a b : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (t : Set.Icc a b) (u : CriticalPath (intervalMeasure a b)) :
    criticalPathFreeRebase hDensity hSob hfree t u =
      freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-(t : ℝ)) (energyPath _ u t)) := rfl

/-- Endpoint rebasing fixes every true free graph path by the EnergyState group law. -/
theorem criticalPathFreeRebase_free (hDensity : OrdinaryH1Density) {K Ch a b : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (t : Set.Icc a b) (x : EnergyState) :
    criticalPathFreeRebase hDensity hSob hfree t
      (freeCriticalPath hDensity hSob hfree a b x) =
        freeCriticalPath hDensity hSob hfree a b x := by
  have hinv : freeEnergyState hDensity hSob (-(t : ℝ))
      (freeEnergyState hDensity hSob (t : ℝ) x) = x := by
    simpa only [neg_neg] using freeEnergyState_inverse hDensity hSob (-(t : ℝ)) x
  exact (criticalPathFreeRebase_apply hDensity hSob hfree t _).trans
    (congrArg (freeCriticalPath hDensity hSob hfree a b)
      ((congrArg (freeEnergyState hDensity hSob (-(t : ℝ)))
        (freeCriticalPath_energy hDensity hSob hfree a b x t)).trans hinv))

theorem criticalPathFreeRebase_of_energy_zero (hDensity : OrdinaryH1Density) {K Ch a b : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (t : Set.Icc a b) (u : CriticalPath (intervalMeasure a b))
    (hu : energyPath _ u t = 0) :
    criticalPathFreeRebase hDensity hSob hfree t u = 0 := by
  change freeCriticalPathLinear hDensity hSob hfree a b
    (freeEnergyCLM hDensity hSob (-(t : ℝ)) (energyPath _ u t)) = 0
  let L := freeCriticalPathLinear hDensity hSob hfree a b
  let U := freeEnergyCLM hDensity hSob (-(t : ℝ))
  exact (congrArg (fun x : EnergyState => L (U x)) hu).trans
    ((congrArg L U.map_zero).trans L.map_zero)

section Algebra
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
/-- Pure algebra applied later to the actual endpoint projection and source path. -/
theorem rebase_forward_algebra (P : G →ₗ[ℂ] G) (x q r : G)
    (hx : P x = x) (hq : P q = q) (hz : P (q-r) = 0) :
    P (x + Complex.I • r) - Complex.I • (q-r) = x + Complex.I • r := by
  have hr : P r = q := by
    rw [map_sub, hq, sub_eq_zero] at hz
    exact hz.symm
  rw [map_add, map_smul, hx, hr, smul_sub]
  abel

theorem rebase_backward_algebra (P : G →ₗ[ℂ] G) (x q r : G)
    (hx : P x = x) (hq : P q = q) (hz : P r = 0) :
    P (x - Complex.I • (q-r)) + Complex.I • r = x - Complex.I • (q-r) := by
  rw [map_sub, map_smul, map_sub, hx, hq, hz, sub_zero, smul_sub]
  abel
end Algebra
end HartreeF.ActualDuhamelPath
