import FHighpassH1Path

/-! Sharp L2 highpass contraction and the complementary actual low-energy state.
The cutoff is smooth, so no idempotence is asserted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
namespace HartreeF.EnergySpace.Highpass
open HartreeF.EnergySpace SobolevStretch StationarySelfTest

theorem highL2_fourier_coe (q : Cutoff) (L : ℝ) (f : L2) :
    ((𝓕 (highL2 q L f) : L2) : V → ℂ) =ᵐ[volume]
      (fun ξ => (1 - lowSymbol q L ξ) * (𝓕 f) ξ) := by
  have he : 𝓕 (highL2 q L f) = 𝓕 f - lowMultiply q L (𝓕 f) := by
    change (fourierCLM ℂ L2) (f - lowL2 q L f) = _
    rw [map_sub]
    change 𝓕 f - 𝓕 (lowL2 q L f) = _
    rw [lowL2_fourier]
  rw [he]
  filter_upwards [Lp.coeFn_sub (𝓕 f) (lowMultiply q L (𝓕 f)),
    lowMultiply_coe q L (𝓕 f)] with ξ h1 h2
  rw [h1]
  simp only [Pi.sub_apply]
  rw [h2]
  ring

theorem highL2_contraction (q : Cutoff) (L : ℝ) (f : L2) :
    ‖highL2 q L f‖ ≤ ‖f‖ := by
  rw [← Lp.norm_fourier_eq (highL2 q L f), ← Lp.norm_fourier_eq f]
  have hb : ‖𝓕 (highL2 q L f)‖ ≤ 1 * ‖𝓕 f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [highL2_fourier_coe q L f] with ξ hξ
    rw [hξ, norm_mul]
    exact mul_le_mul_of_nonneg_right (highSymbol_norm_le_one q L ξ) (norm_nonneg _)
  simpa only [one_mul] using hb

theorem highEnergyState_pureGradient_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    pureGradientNorm (highEnergyState hDensity hSob q hL u) ≤ pureGradientNorm u := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  rw [highEnergyState_gradient]
  exact pow_le_pow_left₀ (norm_nonneg _) (highL2_contraction q L _) 2

def lowEnergyState (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) : EnergyState :=
  u - highEnergyState hDensity hSob q hL u

theorem lowEnergyState_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    energyDistribution (lowEnergyState hDensity hSob q hL u) = low q L (energyDistribution u) := by
  simp only [lowEnergyState, map_sub, highEnergyState_distribution]
  change energyDistribution u - (energyDistribution u - low q L (energyDistribution u)) = _
  abel

theorem lowEnergyState_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) :
    energyGradient j (lowEnergyState hDensity hSob q hL u) = lowL2 q L (energyGradient j u) := by
  simp only [lowEnergyState, map_sub, highEnergyState_gradient]
  change energyGradient j u - (energyGradient j u - lowL2 q L (energyGradient j u)) = _
  abel

end HartreeF.EnergySpace.Highpass
