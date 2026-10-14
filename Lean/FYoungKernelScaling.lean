import FYoungCutoffKernel
import FAffineMixedNormIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.YoungSource
open EnergySpace EnergySpace.Highpass

/-- Exact physical dilation, retaining the already fixed 2*pi symbol normalization. -/
theorem cutoffKernel_scale (q : Cutoff) {L : ℝ} (hL : 0 < L) (x : V) :
    cutoffKernel q hL x = L^3 • cutoffKernel q (L := 1) (by norm_num) (L • x) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
    (fun ξ : V => Real.fourierChar (inner ℝ ξ (L • x)) • lowSymbol q 1 ξ) hL.le
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h
  simp only [cutoffKernel, SchwartzMap.fourierInv_coe, Real.fourierInv_eq, symbolSchwartz_apply]
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  · congr 1
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  · unfold lowSymbol
    congr 2
    rw [smul_smul]
    congr 1
    field_simp

abbrev sourceExponent : ℝ≥0∞ := ENNReal.ofReal (6 / 5 : ℝ)
instance sourceExponent_ge_one : Fact (1 ≤ sourceExponent) := ⟨by norm_num [sourceExponent]⟩

def cutoffYoungConstant (q : Cutoff) : ℝ :=
  ‖(cutoffKernel q (L := 1) (by norm_num)).toLp sourceExponent volume‖

theorem cutoffYoungConstant_nonneg (q : Cutoff) : 0 ≤ cutoffYoungConstant q := norm_nonneg _

/-- Exact L^(6/5) kernel scaling; the constant depends only on the literal cutoff. -/
theorem cutoffKernel_norm (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    ‖(cutoffKernel q hL).toLp sourceExponent volume‖ = cutoffYoungConstant q * Real.sqrt L := by
  have h := AffineMixed.spatial_eLpNorm_affine hL (0 : V) (3 : ℝ) sourceExponent
    (cutoffKernel q (L := 1) (by norm_num) : V → ℂ)
  have he : 3 - 3 * AffineMixed.reciprocalExponent sourceExponent = (1/2 : ℝ) := by
    norm_num [AffineMixed.reciprocalExponent, sourceExponent]
  rw [he, ← Real.sqrt_eq_rpow] at h
  simp only [CriticalAffine.affine, add_zero, Real.rpow_ofNat] at h
  have hk : (cutoffKernel q hL : V → ℂ) =
      fun x => L^3 • cutoffKernel q (L := 1) (by norm_num) (L • x) :=
    funext (cutoffKernel_scale q hL)
  rw [SchwartzMap.norm_toLp, cutoffYoungConstant, SchwartzMap.norm_toLp, hk, h,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg L), mul_comm]

end HartreeF.YoungSource
