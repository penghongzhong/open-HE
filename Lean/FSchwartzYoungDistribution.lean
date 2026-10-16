import FYoungKernelScaling

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.AnnularL1
open EnergySpace EnergySpace.Highpass YoungSource MassRecovery ProfileSpatialSmoothing

/-- Exact transpose of convolution by an arbitrary complex Schwartz kernel.
No evenness, positivity or reality condition is imposed. -/
def kernelTranspose (k : Test) : Test →L[ℂ] Test :=
  fourierCLM ℂ Test ∘L SchwartzMap.smulLeftCLM ℂ (𝓕 k : Test) ∘L fourierInvCLM ℂ Test

theorem schwartzKernel_pairing (k φ : Test) (y : V) :
    (∫ x : V, φ x * k (x-y)) = kernelTranspose k φ y := by
  have h := SchwartzMap.integral_fourier_mul_eq (𝓕⁻ φ)
    (SchwartzMap.compSubConstCLM ℂ y k)
  rw [fourier_fourierInv_eq] at h
  calc
    _ = ∫ ξ : V, 𝓕⁻ φ ξ * 𝓕 (SchwartzMap.compSubConstCLM ℂ y k) ξ := h
    _ = kernelTranspose k φ y := by
      change _ = 𝓕 (SchwartzMap.smulLeftCLM ℂ (𝓕 k : Test) (𝓕⁻ φ)) y
      conv_rhs => rw [SchwartzMap.fourier_coe, Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [fourier_translate, SchwartzMap.smulLeftCLM_apply_apply (𝓕 k : Test).hasTemperateGrowth]
      simp only [Circle.smul_def, smul_eq_mul, real_inner_comm]
      ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Young Lp output has precisely the Fourier multiplier distribution
of the same kernel and actual L1 input. This also applies to odd complex inverse-
gradient kernels; it does not rely on special cutoff symmetry. -/
theorem young_schwartz_distribution (hp : p ≠ ∞) (k : Test) (f : OneSpace) :
    Lp.toTemperedDistribution (youngCLM hp (k.toLp p volume) f) =
      TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 k : Test) (Lp.toTemperedDistribution f) := by
  ext φ
  let T := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
    (Lp.toTemperedDistributionCLM ℂ volume p)
  change T (youngCLM hp (k.toLp p volume) f) = _
  rw [youngCLM_apply, ← T.integral_comp_comm (young_integrable hp _ f),
    TemperedDistribution.fourierMultiplierCLM_apply_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul, shift_schwartz_toLp]
  change f y • Lp.toTemperedDistribution ((SchwartzMap.compSubConstCLM ℂ y k).toLp p volume) φ = _
  rw [Lp.toTemperedDistribution_toLp_eq]
  change f y • (∫ x : V, φ x • k (x-y)) = kernelTranspose k φ y • f y
  simp only [smul_eq_mul]
  rw [schwartzKernel_pairing, mul_comm]

end HartreeF.AnnularL1
