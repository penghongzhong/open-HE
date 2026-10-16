import FAnnularInverseSymbols

/-!
Exact spatial and L1 scaling of the literal annular inverse-gradient kernels.
The degree-minus-one multiplier contributes L⁻¹, and the native three-dimensional
Haar change of variables contributes L³. All integrability comes from the
Schwartz kernel already constructed in FAnnularInverseSymbols.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.AnnularL1
open EnergySpace EnergySpace.Highpass

/-- Exact physical dilation of the actual inverse-Fourier kernel. Both scalar
multiplications in the statement are the ordinary real scalar action. -/
theorem inverseKernel_scale (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (x : V) :
    inverseKernel q hL j x =
      L ^ 2 • inverseKernel q (L := 1) (by norm_num) j (L • x) := by
  have hJ := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
    (fun ξ : V => Real.fourierChar (inner ℝ ξ (L • x)) •
      inverseSymbol q 1 j ξ) hL.le
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hJ
  have hinner (ξ : V) : inner ℝ (L⁻¹ • ξ) (L • x) = inner ℝ ξ x := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp [hL.ne']
  have hscalar : L⁻¹ * L ^ 3 = L ^ 2 := by
    calc
      _ = (L⁻¹ * L) * L ^ 2 := by ring
      _ = L ^ 2 := by rw [inv_mul_cancel₀ hL.ne', one_mul]
  simp only [inverseKernel, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    inverseSchwartz_apply]
  calc
    _ = ∫ ξ : V, L⁻¹ •
        (Real.fourierChar (inner ℝ (L⁻¹ • ξ) (L • x)) •
          inverseSymbol q 1 j (L⁻¹ • ξ)) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [hinner, inverseSymbol_scale q hL j ξ]
      exact smul_comm _ _ _
    _ = L⁻¹ • (∫ ξ : V,
        Real.fourierChar (inner ℝ (L⁻¹ • ξ) (L • x)) •
          inverseSymbol q 1 j (L⁻¹ • ξ)) := integral_smul _ _
    _ = L⁻¹ • (L ^ 3 • (∫ ξ : V,
        Real.fourierChar (inner ℝ ξ (L • x)) • inverseSymbol q 1 j ξ)) := by
      rw [hJ]
    _ = L ^ 2 • (∫ ξ : V,
        Real.fourierChar (inner ℝ ξ (L • x)) • inverseSymbol q 1 j ξ) := by
      rw [smul_smul, hscalar]

/-- The extended L1 norm scales exactly by L⁻¹. This uses the actual affine
change-of-variables theorem, rather than an assumed realization bound. -/
theorem inverseKernel_eLpNorm_one (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) :
    eLpNorm (inverseKernel q hL j : V → ℂ) 1 volume =
      ENNReal.ofReal L⁻¹ *
        eLpNorm (inverseKernel q (L := 1) (by norm_num) j : V → ℂ) 1 volume := by
  have h := AffineMixed.spatial_eLpNorm_affine hL (0 : V) (2 : ℝ) (1 : ℝ≥0∞)
    (inverseKernel q (L := 1) (by norm_num) j : V → ℂ)
  have he : 2 - 3 * AffineMixed.reciprocalExponent (1 : ℝ≥0∞) = (-1 : ℝ) := by
    norm_num [AffineMixed.reciprocalExponent]
  rw [he, Real.rpow_neg_one] at h
  simp only [CriticalAffine.affine, add_zero, Real.rpow_ofNat] at h
  have hk : (inverseKernel q hL j : V → ℂ) =
      fun x => L ^ 2 • inverseKernel q (L := 1) (by norm_num) j (L • x) :=
    funext (inverseKernel_scale q hL j)
  rw [hk]
  exact h

/-- Exact real L1 norm identity for the native Schwartz-to-Lp realization. -/
theorem inverseKernel_norm_one (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) :
    ‖(inverseKernel q hL j).toLp 1 volume‖ =
      L⁻¹ * ‖(inverseKernel q (L := 1) (by norm_num) j).toLp 1 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
    inverseKernel_eLpNorm_one q hL j, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)]

/-- Equivalent Bochner-integral spelling of the exact L1 scaling. -/
theorem inverseKernel_integral_norm (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) :
    (∫ x : V, ‖inverseKernel q hL j x‖) =
      L⁻¹ * (∫ x : V, ‖inverseKernel q (L := 1) (by norm_num) j x‖) := by
  simpa only [SchwartzMap.norm_toLp_one] using inverseKernel_norm_one q hL j

/-- The finite unit-scale constant depends only on the fixed cutoff and the
coordinate. It is defined by the genuine kernel norm. -/
def inverseKernelL1Constant (q : Cutoff) (j : Fin 3) : ℝ :=
  ‖(inverseKernel q (L := 1) (by norm_num) j).toLp 1 volume‖

theorem inverseKernelL1Constant_nonneg (q : Cutoff) (j : Fin 3) :
    0 ≤ inverseKernelL1Constant q j := norm_nonneg _

theorem inverseKernel_norm (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) :
    ‖(inverseKernel q hL j).toLp 1 volume‖ = L⁻¹ * inverseKernelL1Constant q j :=
  inverseKernel_norm_one q hL j

end HartreeF.AnnularL1
