import FFreeHartreeEnergyTails
import FCriticalAffineIsometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.FreeFrameIndependentReview
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz
open EnergyVariation StateEnergy ForcingDomain CriticalAffine FreeTimeDecay

/-- The actual critical spatial frame preserves the canonical value L6 norm. -/
theorem critical_frame_value_norm (lambda : ℝ) (hlambda : 0 < lambda)
    (y : Space) (u : EnergyState) :
    ‖energyValue (criticalAffineState lambda hlambda y u)‖ = ‖energyValue u‖ :=
  affineState_value_norm (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u

/-- Spatial framing after free propagation preserves the original kinetic norm,
with no affine/free commutation assertion. -/
theorem free_spatial_frame_gradientSquared (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (phi : EnergyState)
    (t lambda : ℝ) (hlambda : 0 < lambda) (y : Space) :
    gradientSquared (criticalAffineState lambda hlambda y
      (freeEnergyState hDensity hSob t phi)) = gradientSquared phi := by
  rw [criticalAffineState_gradientSquared, freeEnergyState_gradientSquared]

/-- Any positive spatial frames may vary with the sequence index. Divergent free
 times of either sign give actual L6 and Hartree tails and the kinetic energy
 limit. The datum is only a canonical homogeneous EnergyState. -/
theorem divergent_free_spatial_frame_tails (hDensity : OrdinaryH1Density)
    {alpha K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (phi : EnergyState) (t lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n)
    (y : ℕ → Space) (ht : Tendsto t atTop atTop ∨ Tendsto t atTop atBot) :
    (∀ n, gradientSquared (criticalAffineState (lambda n) (hlambda n) (y n)
      (freeEnergyState hDensity hSob (t n) phi)) = gradientSquared phi) ∧
    Tendsto (fun n => ‖energyValue (criticalAffineState (lambda n) (hlambda n) (y n)
      (freeEnergyState hDensity hSob (t n) phi))‖) atTop (𝓝 0) ∧
    Tendsto (fun n => interactionLp alpha (energyValue
      (criticalAffineState (lambda n) (hlambda n) (y n)
        (freeEnergyState hDensity hSob (t n) phi)))) atTop (𝓝 0) ∧
    Tendsto (fun n => totalEnergy alpha (criticalAffineState (lambda n) (hlambda n) (y n)
      (freeEnergyState hDensity hSob (t n) phi))) atTop (𝓝 (gradientSquared phi / 2)) := by
  refine ⟨fun n => free_spatial_frame_gradientSquared hDensity hSob phi (t n)
    (lambda n) (hlambda n) (y n), ?_⟩
  simp only [critical_frame_value_norm, criticalAffineState_interaction hOrd,
    criticalAffineState_totalEnergy hOrd]
  rcases ht with ht | ht
  · exact ⟨(freeEnergyState_value_norm_tendsto_zero_atTop hDensity hSob hS phi).comp ht,
      (freeEnergyState_interaction_tendsto_zero_atTop hDensity hSob hS hOrd phi).comp ht,
      (freeEnergyState_totalEnergy_tendsto_kinetic_atTop hDensity hSob hS hOrd phi).comp ht⟩
  · exact ⟨(freeEnergyState_value_norm_tendsto_zero_atBot hDensity hSob hS phi).comp ht,
      (freeEnergyState_interaction_tendsto_zero_atBot hDensity hSob hS hOrd phi).comp ht,
      (freeEnergyState_totalEnergy_tendsto_kinetic_atBot hDensity hSob hS hOrd phi).comp ht⟩

#print axioms critical_frame_value_norm
#print axioms free_spatial_frame_gradientSquared
#print axioms divergent_free_spatial_frame_tails
end HartreeF.FreeFrameIndependentReview
