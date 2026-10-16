import F121AffineCutoffSchwartz
import F121CompactFrequencySmall

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Paper121AffineCutoff
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open CriticalAffine FreeAffine Paper121SmallFrequency Paper121CutoffMaps

theorem highEnergy_affine (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (b : Space) (u : EnergyState) :
    highEnergyCLM hD hS q hM (affineState ha b u) =
      affineState ha b (highEnergyCLM hD hS q (div_pos hM ha) u) := by
  have he : (fun v => highEnergyCLM hD hS q hM (affineStateEquiv ha b v)) =
      (fun v => affineStateEquiv ha b (highEnergyCLM hD hS q (div_pos hM ha) v)) := by
    apply (schwartzEnergyState_denseRange hD hS).equalizer
      ((highEnergyCLM hD hS q hM).continuous.comp (affineStateEquiv ha b).continuous)
      ((affineStateEquiv ha b).continuous.comp (highEnergyCLM hD hS q (div_pos hM ha)).continuous)
    funext φ
    change highEnergyCLM hD hS q hM (affineState ha b (schwartzEnergyState φ)) =
      affineState ha b (highEnergyCLM hD hS q (div_pos hM ha) (schwartzEnergyState φ))
    rw [affineState_schwartz, highEnergy_schwartz, highSchwartz_affine q ha hM,
      highEnergy_schwartz, affineState_schwartz]
  exact congrFun he u

theorem lowEnergy_affine (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (b : Space) (u : EnergyState) :
    lowEnergyCLM hD hS q hM (affineState ha b u) =
      affineState ha b (lowEnergyCLM hD hS q (div_pos hM ha) u) := by
  change affineStateEquiv ha b u-highEnergyCLM hD hS q hM (affineState ha b u) =
    affineStateEquiv ha b (u-highEnergyCLM hD hS q (div_pos hM ha) u)
  rw [map_sub, highEnergy_affine]
  rfl

theorem highValue_norm_affine (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {a M : ℝ} (ha : 0 < a) (hM : 0 < M) (b : Space) (u : EnergyState) :
    ‖highValueL2CLM hD hS q hM (affineState ha b u)‖ =
      a⁻¹*‖highValueL2CLM hD hS q (div_pos hM ha) u‖ := by
  have he : (fun v => ‖highValueL2CLM hD hS q hM (affineStateEquiv ha b v)‖) =
      (fun v => a⁻¹*‖highValueL2CLM hD hS q (div_pos hM ha) v‖) := by
    apply (schwartzEnergyState_denseRange hD hS).equalizer
      (((highValueL2CLM hD hS q hM).continuous.comp (affineStateEquiv ha b).continuous).norm)
      (continuous_const.mul (highValueL2CLM hD hS q (div_pos hM ha)).continuous.norm)
    funext φ
    change ‖highValueL2CLM hD hS q hM (affineState ha b (schwartzEnergyState φ))‖ =
      a⁻¹*‖highValueL2CLM hD hS q (div_pos hM ha) (schwartzEnergyState φ)‖
    simp only [affineState_schwartz, high_schwartz_identification,
      ← highSchwartz_toL2 q hM, ← highSchwartz_toL2 q (div_pos hM ha),
      highSchwartz_affine q ha hM, affineSchwartz_L2_norm]
  exact congrFun he u

theorem low_gradient_critical (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {r M : ℝ} (hr : 0 < r) (hM : 0 < M) (y : Space) (u : EnergyState) :
    pureGradientNorm (lowEnergyCLM hD hS q hM (criticalAffineState r hr y u)) =
      pureGradientNorm (lowEnergyCLM hD hS q (mul_pos hM hr) u) := by
  change pureGradientNorm (lowEnergyCLM hD hS q hM
    (affineState (inv_pos.mpr hr) (-(r⁻¹ • y)) u)) = _
  rw [lowEnergy_affine, affineState_pureGradientNorm]
  simp only [div_inv_eq_mul]

theorem weighted_high_critical (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {r M : ℝ} (hr : 0 < r) (hM : 0 < M) (y : Space) (u : EnergyState) :
    M*‖highValueL2CLM hD hS q hM (criticalAffineState r hr y u)‖ =
      (M*r)*‖highValueL2CLM hD hS q (mul_pos hM hr) u‖ := by
  change M*‖highValueL2CLM hD hS q hM (affineState (inv_pos.mpr hr) (-(r⁻¹ • y)) u)‖ = _
  rw [highValue_norm_affine]
  simp only [inv_inv, div_inv_eq_mul, mul_assoc]

end HartreeF.Paper121AffineCutoff
