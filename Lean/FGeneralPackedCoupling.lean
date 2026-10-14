import FGeneralPackedFrame

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing SobolevStretch CompactCross CriticalAffine AffineMixed EnergySpace

/-- Framing the actual packed weak gradient agrees pointwise with packing its two
real framed weak gradients. This is a field identity, not a norm comparison. -/
theorem gradientFrame_is_packed (a : ℝ) (y : Space) (s : ℝ)
    (U V : ℝ → Space → Space) :
    gradientFrame a y s (fun t => complexGradient (U t) (V t)) =
      (fun t => complexGradient (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) U t)
        (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) V t)) := by
  funext t x
  ext j
  simp [gradientFrame, parabolicField, complexGradient, Complex.real_smul, mul_left_comm]

/-- The physical actual-profile value and its weight-3/2 gradient remain genuinely
coupled in the weak homogeneous Sobolev domain at every original time. -/
theorem actual_seedFrame_inDotH1 (g : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (s t : ℝ) :
    InDotH1 (seedFrame a y s (1/2) (stateValueField g) t)
      (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) (stateRealGradientField g) t)
      (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) (stateImagGradientField g) t) :=
  seedFrame_inDotH1 ha y s (fun t => energyState_inDotH1 (g t)) t

#print axioms gradientFrame_is_packed
#print axioms actual_seedFrame_inDotH1
end HartreeF.GeneralProfileCross
