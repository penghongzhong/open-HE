import FPhysicalConvolutionDistribution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.PhysicalLowpass
open EnergySpace EnergySpace.Highpass YoungSource

private instance six_source_holder : (6 : ℝ≥0∞).HolderConjugate sourceExponent := by
  have h : Real.HolderConjugate 6 (6 / 5) := by
    norm_num [Real.holderConjugate_iff]
  simpa [sourceExponent] using h.ennrealOfReal

theorem cutoffKernel_norm_scaling (q : Cutoff) {L : ℝ} (hL : 0 < L) (p : ℝ≥0∞) :
    ‖(cutoffKernel q hL).toLp p volume‖ =
      L ^ (3 - 3 * AffineMixed.reciprocalExponent p) *
        ‖(cutoffKernel q (L := 1) (by norm_num)).toLp p volume‖ := by
  have h := AffineMixed.spatial_eLpNorm_affine hL (0 : V) (3 : ℝ) p
    (cutoffKernel q (L := 1) (by norm_num) : V → ℂ)
  simp only [CriticalAffine.affine, add_zero, Real.rpow_ofNat] at h
  have hk : (cutoffKernel q hL : V → ℂ) =
      fun x => L ^ 3 • cutoffKernel q (L := 1) (by norm_num) (L • x) :=
    funext (cutoffKernel_scale q hL)
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, hk, h,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hL.le _)]

def cutoffL2Constant (q : Cutoff) : ℝ :=
  ‖(cutoffKernel q (L := 1) (by norm_num)).toLp 2 volume‖

theorem cutoffL2Constant_nonneg (q : Cutoff) : 0 ≤ cutoffL2Constant q := norm_nonneg _

theorem cutoffKernel_norm_two (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    ‖(cutoffKernel q hL).toLp 2 volume‖ = cutoffL2Constant q * L ^ (3 / 2 : ℝ) := by
  have h := cutoffKernel_norm_scaling q hL (2 : ℝ≥0∞)
  have he : 3 - 3 * AffineMixed.reciprocalExponent (2 : ℝ≥0∞) = (3 / 2 : ℝ) := by
    norm_num [AffineMixed.reciprocalExponent]
  rw [he] at h
  exact h.trans (mul_comm _ _)

theorem cutoff_convolution_six_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : L6) (x : V) :
    ‖convolutionValue (cutoffKernel q hL) f x‖ ≤
      cutoffYoungConstant q * Real.sqrt L * ‖f‖ := by
  have h := convolutionValue_norm (r := sourceExponent) (cutoffKernel q hL) f x
  rwa [cutoffKernel_norm] at h

theorem cutoff_convolution_two_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : L2) (x : V) :
    ‖convolutionValue (cutoffKernel q hL) f x‖ ≤
      cutoffL2Constant q * L ^ (3 / 2 : ℝ) * ‖f‖ := by
  have h := convolutionValue_norm (r := 2) (cutoffKernel q hL) f x
  rwa [cutoffKernel_norm_two] at h

theorem cutoff_convolution_distribution {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    [p.HolderConjugate r] (hp : p ≠ ∞) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : Lp ℂ p (volume : Measure V)) :
    Lp.toTemperedDistribution (convolutionInfinity (r := r) (cutoffKernel q hL) f) =
      low q L (Lp.toTemperedDistribution f) := by
  rw [convolutionInfinity_distribution hp, cutoffKernel_fourier]
  rfl

end HartreeF.PhysicalLowpass
