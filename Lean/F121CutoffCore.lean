import FHighpassContraction
import FPhysicalCutoffKernelBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
namespace HartreeF.Paper121CutoffCore
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open PhysicalLowpass YoungSource

local instance : (6 : ℝ≥0∞).HolderConjugate sourceExponent := by
  have h : Real.HolderConjugate 6 (6/5) := by norm_num [Real.holderConjugate_iff]
  simpa [sourceExponent] using h.ennrealOfReal

theorem low_gradient_contraction (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    pureGradientNorm (lowEnergyState hDensity hSob q hM u) ≤ pureGradientNorm u := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  rw [lowEnergyState_gradient]
  exact pow_le_pow_left₀ (norm_nonneg _) (lowL2_norm q M _) 2

theorem gradient_pair_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    pureGradientNorm (lowEnergyState hDensity hSob q hM u) +
      pureGradientNorm (highEnergyState hDensity hSob q hM u) ≤ 2*pureGradientNorm u := by
  linarith [low_gradient_contraction hDensity hSob q hM u,
    highEnergyState_pureGradient_bound hDensity hSob q hM u]

/-- The actual scalar convolution and the homogeneous low pass are one distribution. -/
theorem low_convolution_same_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    Lp.toTemperedDistribution
      (convolutionInfinity (r := sourceExponent) (cutoffKernel q hM) (energyValue u)) =
      energyDistribution (lowEnergyState hDensity hSob q hM u) := by
  exact (cutoff_convolution_distribution (r := sourceExponent)
    (by norm_num : (6 : ℝ≥0∞) ≠ ∞) q hM (energyValue u)).trans
      (lowEnergyState_distribution hDensity hSob q hM u).symm

/-- Pointwise bound, with a constant independent of the frequency and the state. -/
theorem low_convolution_gradient_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) (x : V) :
    ‖convolutionValue (cutoffKernel q hM) (energyValue u) x‖ ≤
      (cutoffYoungConstant q*K^((6 : ℝ)⁻¹))*Real.sqrt M*pureGradientNorm u := by
  exact (cutoff_convolution_six_bound q hM (energyValue u) x).trans
    ((mul_le_mul_of_nonneg_left (energyValue_le_pureGradient hSob u)
      (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg M))).trans_eq (by ring))

/-- Literal smooth annular symbols; this is the identity m_M q_M = m_M. -/
theorem annular_symbol_reproduction (q : Cutoff) {M : ℝ} (hM : 0 < M) (ξ : V) :
    (lowSymbol q M ξ-lowSymbol q (M/2) ξ) *
      (lowSymbol q (2*M) ξ-lowSymbol q (M/4) ξ) =
    lowSymbol q M ξ-lowSymbol q (M/2) ξ := by
  by_cases hlo : 2*Real.pi*‖ξ‖ ≤ M/2
  · rw [lowSymbol_one q hM ξ (by linarith),
      lowSymbol_one q (by linarith : 0 < M/2) ξ hlo]
    simp
  · by_cases hhi : 2*M ≤ 2*Real.pi*‖ξ‖
    · rw [lowSymbol_zero q hM ξ hhi,
        lowSymbol_zero q (by linarith : 0 < M/2) ξ (by linarith)]
      simp
    · rw [lowSymbol_one q (by linarith : 0 < 2*M) ξ (by linarith),
        lowSymbol_zero q (by linarith : 0 < M/4) ξ (by linarith)]
      simp

end HartreeF.Paper121CutoffCore
