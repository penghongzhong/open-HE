import FCriticalPathL2Forcing
import FHartreeL2DifferenceRealization
import FHartreeL2Budget
import FHartreeL2FixedMeasure
import FCriticalPathQuantitativeNorms

/-! The constructed actual Hartree L² source is locally Lipschitz on the
canonical CriticalPath. This is an analytic source theorem, not conservation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingL2
open ForcingDomain TimeHolder EnergySpace CriticalPathSpace CriticalJointSources
open SobolevStretch StationarySelfTest CriticalSourceBounds ForcingL2Difference
attribute [local irreducible] jointFields l2Source criticalL2Source energyPath energyValue
  energySubmodule criticalPathSubmodule criticalGradient energyGradient

universe uTime
variable {T : Type uTime} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (mu : Measure T) [SigmaFinite mu]

/-- A direct representation on the measurable joint field for norm estimates. -/
theorem criticalL2Source_joint_coeFn (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (u : CriticalPath mu) :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, criticalL2Source mu hDensity hSob hH u t x =
      forcing alpha c ((jointFields mu u).u t) x := by
  unfold criticalL2Source
  exact l2Source_coeFn mu hH (jointFields mu u).u
    (jointFields mu u).joint_u.aestronglyMeasurable
    (critical_joint_l2_inputs mu hDensity hSob u) (joint_value_energy_finite mu u)
    (joint_value_critical mu hDensity hSob u).2

/-- Distances in the produced Bochner space are actual forcing differences. -/
theorem criticalL2Source_difference_enorm (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (u v : CriticalPath mu) :
    ‖criticalL2Source mu hDensity hSob hH u - criticalL2Source mu hDensity hSob hH v‖ₑ =
      mixedNorm mu volume 2 2 (fun t x =>
        forcing alpha c (energyValue (energyPath mu u t)) x -
        forcing alpha c (energyValue (energyPath mu v t)) x) :=
  represented_l2_difference_enorm mu _ _ _ _
    (criticalL2Source_coeFn mu hDensity hSob hH u)
    (criticalL2Source_coeFn mu hDensity hSob hH v)

/-- The exact two-term budget, instantiated on the actual CriticalPath source. -/
theorem criticalL2Source_difference_bound (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ u v : CriticalPath mu,
      ‖criticalL2Source mu hDensity hSob hH u - criticalL2Source mu hDensity hSob hH v‖ₑ ≤
        (C : ℝ≥0∞) * forcingBudget alpha
          (pathEnergySize mu u + pathEnergySize mu v) (pathValueSize mu u + pathValueSize mu v)
          (mixedNorm mu volume ∞ 6 (fun t => (jointFields mu u).u t - (jointFields mu v).u t))
          (mixedNorm mu volume 10 10 (fun t => (jointFields mu u).u t - (jointFields mu v).u t)) := by
  refine (forcing_l2_difference_bound_fixed_measure mu hH).imp ?_
  intro C hC u v
  have hn := represented_l2_difference_enorm mu
    (criticalL2Source mu hDensity hSob hH u) (criticalL2Source mu hDensity hSob hH v)
    (fun t => forcing alpha c ((jointFields mu u).u t))
    (fun t => forcing alpha c ((jointFields mu v).u t))
    (criticalL2Source_joint_coeFn mu hDensity hSob hH u)
    (criticalL2Source_joint_coeFn mu hDensity hSob hH v)
  apply hn.le.trans
  exact hC (jointFields mu u).u (jointFields mu v).u
    (jointFields mu u).joint_u.aestronglyMeasurable (jointFields mu v).joint_u.aestronglyMeasurable
    (critical_joint_l2_inputs mu hDensity hSob u) (critical_joint_l2_inputs mu hDensity hSob v)

/-- Both controlling input norms and both differences have a common explicit
bound in the complete CriticalPath norm. -/
theorem critical_common_l2_input_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧
      (∀ u : CriticalPath mu, pathEnergySize mu u ≤ A * ENNReal.ofReal ‖u‖ ∧
        pathValueSize mu u ≤ A * ENNReal.ofReal ‖u‖) ∧
      (∀ u v : CriticalPath mu,
        mixedNorm mu volume ∞ 6 (fun t => (jointFields mu u).u t - (jointFields mu v).u t) ≤
          A * ENNReal.ofReal ‖u-v‖ ∧
        mixedNorm mu volume 10 10 (fun t => (jointFields mu u).u t - (jointFields mu v).u t) ≤
          A * ENNReal.ofReal ‖u-v‖) := by
  let A : ℝ≥0∞ := 1 + ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * 6
  have hA : A ≠ ∞ := by dsimp [A]; finiteness
  have h1 : (1 : ℝ≥0∞) ≤ A := le_self_add
  have h6 : ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * 6 ≤ A := le_add_self
  refine ⟨A, hA, ?_, ?_⟩
  · intro u
    constructor
    · exact (joint_value_energy_bound mu u).trans (by
        simpa only [one_mul] using mul_le_mul' h1 (le_refl (ENNReal.ofReal ‖u‖)))
    · exact (joint_value_critical_bound mu hDensity hSob u).trans
        ((mul_le_mul' le_rfl (joint_gradient_bound mu u)).trans
          (by simpa only [mul_assoc] using mul_le_mul' h6 (le_refl (ENNReal.ofReal ‖u‖))))
  · intro u v
    constructor
    · exact (joint_value_difference_energy_bound mu u v).trans (by
        simpa only [one_mul] using mul_le_mul' h1 (le_refl (ENNReal.ofReal ‖u-v‖)))
    · exact (joint_value_difference_critical_bound mu hDensity hSob u v).trans
        (mul_le_mul' h6 le_rfl)

#print axioms criticalL2Source_joint_coeFn
#print axioms criticalL2Source_difference_enorm
#print axioms criticalL2Source_difference_bound
#print axioms critical_common_l2_input_bound
end HartreeF.ForcingL2
