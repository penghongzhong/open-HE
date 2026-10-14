import FCriticalPathSourceBudgets
import FIndependentCanonicalAffineForcing
import FActualAffineCriticalPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace CriticalJointSources CriticalTimeSobolev
open SobolevStretch StationarySelfTest IntervalTimeTransport
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields

/-- All critical spatial slice domains of the canonical curve follow from the
actual path coordinates and the already proved homogeneous Sobolev producer. -/
theorem canonical_path_critical_slices (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] (μ : Measure T) [SigmaFinite μ]
    (u : CriticalPath μ) :
    ∀ᵐ t ∂μ,
      MemLp (energyValue (energyPath μ u t)) 10 volume ∧
      MemLp (energyProjectedGradient Complex.reCLM (energyPath μ u t)) criticalExponent volume ∧
      MemLp (energyProjectedGradient Complex.imCLM (energyPath μ u t)) criticalExponent volume := by
  filter_upwards [joint_slices μ hDensity hSob u u, (jointFields μ u).slice_eq] with t hs he
  exact ⟨hs.2.2.1.ae_eq he.1, hs.2.2.2.2.1.ae_eq he.2.1,
    hs.2.2.2.2.2.1.ae_eq he.2.2⟩

/-- The same canonical domains on real time, restricted to the actual interval.
No extra L10 or weak-gradient hypothesis is imposed on the input path. -/
theorem canonical_local_critical_slices (hDensity : OrdinaryH1Density) {K A B : ℝ}
    (hSob : OrdinarySobolev K) (hAB : A≤B) (u : CriticalPath (intervalMeasure A B)) :
    ∀ᵐ t ∂localMeasure A B,
      MemLp (energyValue (extendEnergyPath hAB (energyPath _ u) t)) 10 volume ∧
      MemLp (energyProjectedGradient Complex.reCLM
        (extendEnergyPath hAB (energyPath _ u) t)) criticalExponent volume ∧
      MemLp (energyProjectedGradient Complex.imCLM
        (extendEnergyPath hAB (energyPath _ u) t)) criticalExponent volume :=
  ae_clamp hAB (canonical_path_critical_slices hDensity hSob (intervalMeasure A B) u)

#print axioms canonical_path_critical_slices
#print axioms canonical_local_critical_slices
end HartreeF.NonlinearAffine
