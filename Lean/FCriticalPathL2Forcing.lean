import FHartreeL2SourceRealization
import FCriticalPathSourceBudgets
import FScalarSourceRepresentatives

/-! Actual canonical CriticalPath consumer, with no assumption u ∈ L²_x. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2
open ForcingDomain TimeHolder EnergySpace CriticalPathSpace CriticalJointSources
open SobolevStretch StationarySelfTest LocalScalarSource
attribute [local irreducible] jointFields l2Source energyPath energyValue

universe uTime
variable {T : Type uTime} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (mu : Measure T) [SigmaFinite mu]

theorem critical_joint_l2_inputs (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : CriticalPath mu) :
    ∀ᵐ t ∂mu, MemLp ((jointFields mu u).u t) 6 volume ∧
      MemLp ((jointFields mu u).u t) 10 volume := by
  filter_upwards [(jointFields mu u).inDotH1,
    (joint_value_critical mu hDensity hSob u).1] with t ht h10
  exact ⟨ht.function_L6, h10⟩

/-- The L² source is constructed from the same canonical energy path. -/
def criticalL2Source (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (u : CriticalPath mu) :
    Lp (Lp ℂ 2 (volume : Measure Space)) 2 mu :=
  l2Source mu hH (jointFields mu u).u (jointFields mu u).joint_u.aestronglyMeasurable
    (critical_joint_l2_inputs mu hDensity hSob u) (joint_value_energy_finite mu u)
    (joint_value_critical mu hDensity hSob u).2

/-- Nested AE equality is with the actual L6 EnergyState representative. -/
theorem criticalL2Source_coeFn (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (u : CriticalPath mu) :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, criticalL2Source mu hDensity hSob hH u t x =
      forcing alpha c (energyValue (energyPath mu u t)) x := by
  have hf := l2Source_coeFn mu hH (jointFields mu u).u
    (jointFields mu u).joint_u.aestronglyMeasurable
    (critical_joint_l2_inputs mu hDensity hSob u) (joint_value_energy_finite mu u)
    (joint_value_critical mu hDensity hSob u).2
  filter_upwards [hf, (jointFields mu u).slice_eq] with t ht hs
  exact Filter.EventuallyEq.trans ht (forcing_ae_of_ae (alpha := alpha) (c := c) hs.1)

/-- No measurability of an arbitrary canonical product representative is asserted:
its slice norms equal the norms of the constructed measurable source. -/
theorem criticalL2Source_enorm (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (u : CriticalPath mu) :
    ‖criticalL2Source mu hDensity hSob hH u‖ₑ =
      mixedNorm mu volume 2 2 (fun t => forcing alpha c (energyValue (energyPath mu u t))) := by
  calc
    _ = mixedNorm mu volume 2 2 (fun t => forcing alpha c ((jointFields mu u).u t)) :=
      l2Source_enorm mu hH (jointFields mu u).u (jointFields mu u).joint_u.aestronglyMeasurable
        (critical_joint_l2_inputs mu hDensity hSob u) (joint_value_energy_finite mu u)
        (joint_value_critical mu hDensity hSob u).2
    _ = _ := by
      apply eLpNorm_congr_ae
      filter_upwards [(jointFields mu u).slice_eq] with t ht
      exact eLpNorm_congr_ae (forcing_ae_of_ae (alpha := alpha) (c := c) ht.1)

/-- The actual CriticalPath has a literal L²_t L²_x forcing norm. -/
theorem critical_forcing_l2_finite (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (u : CriticalPath mu) :
    mixedNorm mu volume 2 2 (fun t => forcing alpha c (energyValue (energyPath mu u t))) ≠ ∞ := by
  rw [← criticalL2Source_enorm mu hDensity hSob hH u]
  exact enorm_ne_top

#print axioms critical_joint_l2_inputs
#print axioms criticalL2Source
#print axioms criticalL2Source_coeFn
#print axioms criticalL2Source_enorm
#print axioms critical_forcing_l2_finite
end HartreeF.ForcingL2
