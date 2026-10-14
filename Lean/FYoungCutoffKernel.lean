import FLowpassNoWasteTranspose
import FYoungLpKernel
import Mathlib.Analysis.Fourier.Convolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.YoungSource
open EnergySpace EnergySpace.Highpass MassRecovery ProfileSpatialSmoothing

def symbolSchwartz (q : Cutoff) {L : ℝ} (hL : 0 < L) : 𝓢(V, ℂ) :=
  (lowSymbol_compact q hL).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (q.smooth.comp (by fun_prop)))

theorem symbolSchwartz_apply (q : Cutoff) {L : ℝ} (hL : 0 < L) (ξ : V) :
    symbolSchwartz q hL ξ = lowSymbol q L ξ := rfl

/-- The inverse Fourier kernel of the precise 2*pi-normalized cutoff. -/
def cutoffKernel (q : Cutoff) {L : ℝ} (hL : 0 < L) : 𝓢(V, ℂ) :=
  𝓕⁻ (symbolSchwartz q hL)

theorem cutoffKernel_fourier (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    𝓕 (cutoffKernel q hL) = symbolSchwartz q hL := fourier_fourierInv_eq _

theorem fourier_translate (k : 𝓢(V, ℂ)) (y ξ : V) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ y k) ξ =
      Real.fourierChar (-inner ℝ y ξ) • 𝓕 k ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ V) (k : V → ℂ) (-y)) ξ
  change (∫ x : V, Real.fourierChar (-inner ℝ x ξ) • k (x + -y)) =
    Real.fourierChar (inner ℝ (-y) ξ) • (∫ x : V, Real.fourierChar (-inner ℝ x ξ) • k x) at h
  change (∫ x : V, Real.fourierChar (-inner ℝ x ξ) • k (x - y)) =
    Real.fourierChar (-inner ℝ y ξ) • (∫ x : V, Real.fourierChar (-inner ℝ x ξ) • k x)
  simpa only [sub_eq_add_neg, inner_neg_left] using h

theorem cutoffKernel_pairing (q : Cutoff) {L : ℝ} (hL : 0 < L) (φ : 𝓢(V, ℂ)) (y : V) :
    (∫ x : V, φ x * cutoffKernel q hL (x - y)) = lowTest q L φ y := by
  have h := SchwartzMap.integral_fourier_mul_eq (𝓕⁻ φ)
    (SchwartzMap.compSubConstCLM ℂ y (cutoffKernel q hL))
  rw [fourier_fourierInv_eq] at h
  calc
    _ = ∫ ξ : V, 𝓕⁻ φ ξ * 𝓕 (SchwartzMap.compSubConstCLM ℂ y (cutoffKernel q hL)) ξ := h
    _ = lowTest q L φ y := by
      change _ = 𝓕 (SchwartzMap.smulLeftCLM ℂ (lowSymbol q L) (𝓕⁻ φ)) y
      conv_rhs => rw [SchwartzMap.fourier_coe, Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [fourier_translate, cutoffKernel_fourier, symbolSchwartz_apply,
        SchwartzMap.smulLeftCLM_apply_apply (lowSymbol_temperate q hL)]
      simp only [Circle.smul_def, smul_eq_mul, real_inner_comm]
      ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
theorem shift_schwartz_toLp (k : 𝓢(V, ℂ)) (y : V) :
    lpShift (-y) (k.toLp p volume) =
      (SchwartzMap.compSubConstCLM ℂ y k).toLp p volume := by
  apply Lp.ext
  have hk := (measurePreserving_add_right (volume : Measure V) (-y)).quasiMeasurePreserving.tendsto_ae.eventually
    (k.coeFn_toLp p volume)
  filter_upwards [lpShift_coe_ae (-y) (k.toLp p volume), hk,
    (SchwartzMap.compSubConstCLM ℂ y k).coeFn_toLp p volume] with x h1 h2 h3
  exact h1.trans (h2.trans (by simpa only [SchwartzMap.compSubConstCLM_apply, sub_eq_add_neg] using h3.symm))

/-- The genuine Young construction has exactly the pre-existing lowpass distribution. -/
theorem young_cutoff_distribution (hp : p ≠ ∞) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : OneSpace) :
    Lp.toTemperedDistribution (youngCLM hp ((cutoffKernel q hL).toLp p volume) f) =
      low q L (Lp.toTemperedDistribution f) := by
  ext φ
  let T := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
    (Lp.toTemperedDistributionCLM ℂ volume p)
  change T (youngCLM hp ((cutoffKernel q hL).toLp p volume) f) = _
  rw [youngCLM_apply, ← T.integral_comp_comm (young_integrable hp _ f), low_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul, shift_schwartz_toLp]
  change f y • Lp.toTemperedDistribution ((SchwartzMap.compSubConstCLM ℂ y (cutoffKernel q hL)).toLp p volume) φ = _
  rw [Lp.toTemperedDistribution_toLp_eq]
  change f y • (∫ x : V, φ x • cutoffKernel q hL (x - y)) = lowTest q L φ y • f y
  simp only [smul_eq_mul]
  rw [cutoffKernel_pairing, mul_comm]

end HartreeF.YoungSource
