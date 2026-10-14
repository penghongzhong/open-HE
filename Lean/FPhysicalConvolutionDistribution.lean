import FPhysicalConvolutionBound
import Mathlib.Analysis.Fourier.Convolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap Convolution
namespace HartreeF.PhysicalLowpass
open EnergySpace YoungSource

/-- Fourier identifies the actual Schwartz convolution, with the original complex kernel. -/
theorem schwartzConvolution_multiplier (k φ : Test) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) φ k =
      SchwartzMap.fourierMultiplierCLM ℂ (𝓕 k : Test) φ := by
  change 𝓕⁻ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 φ) (𝓕 k)) =
    𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (𝓕 k : Test) (𝓕 φ))
  congr 1
  ext ξ
  rw [SchwartzMap.pairing_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply (𝓕 k : Test).hasTemperateGrowth]
  simp only [ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/- Equality holds at EVERY spatial point after replacing the input by its Lp representative. -/
omit [Fact (1 ≤ p)] in
theorem convolutionValue_schwartz (k φ : Test) (x : V) :
    convolutionValue k (φ.toLp p volume) x =
      SchwartzMap.fourierMultiplierCLM ℂ (𝓕 k : Test) φ x := by
  calc
    _ = ∫ y : V, φ y * k (x - y) := by
      apply integral_congr_ae
      filter_upwards [φ.coeFn_toLp p volume] with y hy
      rw [hy]
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) φ k x :=
      (SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ k x).symm
    _ = _ := congrArg (fun ψ : Test => ψ x) (schwartzConvolution_multiplier k φ)

variable {r : ℝ≥0∞} [Fact (1 ≤ r)] [p.HolderConjugate r]

theorem convolutionInfinity_schwartz (k φ : Test) :
    convolutionInfinity (p := p) (r := r) k (φ.toLp p volume) =
      (SchwartzMap.fourierMultiplierCLM ℂ (𝓕 k : Test) φ).toLp ∞ volume := by
  apply Lp.ext
  filter_upwards [convolutionInfinity_coe (r := r) k (φ.toLp p volume),
    (SchwartzMap.fourierMultiplierCLM ℂ (𝓕 k : Test) φ).coeFn_toLp ∞ volume] with x hx hφ
  rw [hx, hφ, convolutionValue_schwartz]

theorem convolutionInfinity_schwartz_distribution (k φ : Test) :
    Lp.toTemperedDistribution (convolutionInfinity (p := p) (r := r) k (φ.toLp p volume)) =
      TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 k : Test)
        (Lp.toTemperedDistribution (φ.toLp p volume)) := by
  rw [convolutionInfinity_schwartz, Lp.toTemperedDistribution_toLp_eq,
    Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
      (𝓕 k : Test).hasTemperateGrowth]

/-- Genuine Lp Schwartz density gives the same original distribution for all finite p.
No ordinary density, Sobolev or Young witness is an input. -/
theorem convolutionInfinity_distribution (hp : p ≠ ∞) (k : Test)
    (f : Lp ℂ p (volume : Measure V)) :
    Lp.toTemperedDistribution (convolutionInfinity (r := r) k f) =
      TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 k : Test) (Lp.toTemperedDistribution f) := by
  have he := (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := V) (p := p)
    (μ := (volume : Measure V)) hp).equalizer
    ((Lp.toTemperedDistributionCLM ℂ volume ∞).continuous.comp
      (convolutionInfinityCLM (p := p) (r := r) k).continuous)
    ((TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 k : Test)).continuous.comp
      (Lp.toTemperedDistributionCLM ℂ volume p).continuous) (by
        funext φ
        exact convolutionInfinity_schwartz_distribution (r := r) k φ)
  exact congrFun he f

end HartreeF.PhysicalLowpass
