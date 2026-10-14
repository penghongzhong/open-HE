import FGeneralApproximationTransfer
import FGeneralProfileValueBridge
import FGeneralGradientCoordinates

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing EnergySpace SobolevStretch
  CriticalTimeSobolev CutoffApproximation
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- The chosen approximation precisions are uniformly bounded by one. -/
theorem smoothingPrecision_le_one (n : ℕ) : smoothingPrecision n ≤ 1 := by
  change ENNReal.ofReal ((n : ℝ) + 1)⁻¹ ≤ 1
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ) ≤ (n : ℝ) + 1 by exact le_add_of_nonneg_left (Nat.cast_nonneg n))
  simpa only [one_div, inv_one] using hh

/-- A comparison field is bounded by its genuine mixed-norm error and the original field. -/
theorem mixedNorm_le_error_add {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqTop : q ≠ ∞)
    (f g : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q f ≤
      mixedNorm volume volume p q (fun t x => f t x - g t x) + mixedNorm volume volume p q g := by
  simpa only [sub_zero] using mixed_sub_triangle hp hq hqTop f g (fun _ _ => 0)
    hf hg aestronglyMeasurable_const

#print axioms smoothingPrecision_le_one
#print axioms mixedNorm_le_error_add
end HartreeF.GeneralProfileCross
