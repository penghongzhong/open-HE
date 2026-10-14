import FHighpassFourierCore

/-! Native inverse-gradient highpass estimate on actual Schwartz functions.
The low-frequency support radius is measured in angular frequency 2*pi*xi. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap ContDiff RealInnerProductSpace
namespace HartreeF.EnergySpace.Highpass
open HartreeF.EnergySpace

theorem highSymbol_norm_le_one (q : Cutoff) (L : ℝ) (ξ : V) :
    ‖1 - lowSymbol q L ξ‖ ≤ 1 := by
  have h0 := q.nonneg ((2 * Real.pi / L) • ξ)
  have h1 := q.le_one ((2 * Real.pi / L) • ξ)
  have he : (1 : ℂ) - lowSymbol q L ξ =
      ((1 - q.φ ((2 * Real.pi / L) • ξ) : ℝ) : ℂ) := by simp [lowSymbol]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem highSchwartz_fourier (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ : Test) (ξ : V) :
    𝓕 (highSchwartz q L φ) ξ = (1 - lowSymbol q L ξ) * 𝓕 φ ξ := by
  change (𝓕 (φ - SchwartzMap.fourierMultiplierCLM ℂ (lowSymbol q L) φ)) ξ = _
  rw [sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg]
  simp [SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (lowSymbol_temperate q hL), sub_eq_add_neg, add_mul]

theorem schwartz_fourier_gradient_sq (φ : Test) (ξ : V) :
    (∑ j : Fin 3, ‖𝓕 (∂_{coordinate j} φ) ξ‖ ^ 2) =
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
  have he (j : Fin 3) : ‖𝓕 (∂_{coordinate j} φ) ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (ξ j) ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
    have hi : (fun x : V => inner ℝ x (coordinate j)).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    change ‖(2 * Real.pi * Complex.I : ℂ) •
      (SchwartzMap.smulLeftCLM ℂ (fun x : V => inner ℝ x (coordinate j)) (𝓕 φ)) ξ‖ ^ 2 = _
    rw [SchwartzMap.smulLeftCLM_apply_apply hi]
    simp [coordinate, EuclideanSpace.inner_single_right,
      mul_pow, Real.norm_eq_abs, sq_abs, mul_assoc]
  simp_rw [he]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.mul_sum, Finset.sum_mul]

theorem highSchwartz_fourier_sq_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ : Test) (ξ : V) :
    ‖𝓕 (highSchwartz q L φ) ξ‖ ^ 2 ≤
      L⁻¹ ^ 2 * ∑ j : Fin 3, ‖𝓕 (∂_{coordinate j} φ) ξ‖ ^ 2 := by
  rw [highSchwartz_fourier q hL]
  by_cases h : 2 * Real.pi * ‖ξ‖ ≤ L
  · rw [lowSymbol_one q hL ξ h, sub_self, zero_mul, norm_zero, zero_pow (by decide)]
    positivity
  · rw [schwartz_fourier_gradient_sq]
    have hb : ‖(1 - lowSymbol q L ξ) * 𝓕 φ ξ‖ ≤ ‖𝓕 φ ξ‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (highSymbol_norm_le_one q L ξ)
        (norm_nonneg _)).trans_eq (one_mul _)
    have hr : 1 ≤ L⁻¹ * (2 * Real.pi * ‖ξ‖) := by
      rw [← div_eq_inv_mul]
      exact (one_le_div hL).mpr (le_of_not_ge h)
    calc
      _ ≤ ‖𝓕 φ ξ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ ≤ (L⁻¹ * (2 * Real.pi * ‖ξ‖)) ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
        nlinarith [sq_nonneg ‖𝓕 φ ξ‖, sq_nonneg (L⁻¹ * (2 * Real.pi * ‖ξ‖) - 1)]
      _ = _ := by ring

theorem schwartz_toL2_norm_sq (φ : Test) :
    ‖φ.toLp 2 volume‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  rw [energyLp_norm_pow (n := 2) (by decide)]
  exact integral_congr_ae ((φ.coeFn_toLp 2 volume).mono (fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h))

theorem schwartz_toL2_fourier_norm_sq (φ : Test) :
    ‖φ.toLp 2 volume‖ ^ 2 = ∫ x, ‖𝓕 φ x‖ ^ 2 := by
  rw [← SchwartzMap.norm_fourier_toL2_eq φ]
  exact schwartz_toL2_norm_sq (𝓕 φ)

theorem highSchwartz_l2_sq_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ : Test) :
    ‖(highSchwartz q L φ).toLp 2 volume‖ ^ 2 ≤
      L⁻¹ ^ 2 * gradientSquared (schwartzEnergyState φ) := by
  rw [schwartz_toL2_fourier_norm_sq]
  have hi (j : Fin 3) : Integrable (fun ξ => ‖𝓕 (∂_{coordinate j} φ) ξ‖ ^ 2) :=
    ((𝓕 (∂_{coordinate j} φ)).memLp 2 volume).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  calc
    _ ≤ ∫ ξ, L⁻¹ ^ 2 * ∑ j : Fin 3, ‖𝓕 (∂_{coordinate j} φ) ξ‖ ^ 2 :=
      integral_mono (((𝓕 (highSchwartz q L φ)).memLp 2 volume).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
        ((integrable_finsetSum _ (fun j _ => hi j)).const_mul _)
        (highSchwartz_fourier_sq_bound q hL φ)
    _ = L⁻¹ ^ 2 * ∑ j : Fin 3, ∫ ξ, ‖𝓕 (∂_{coordinate j} φ) ξ‖ ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
    _ = _ := by
      simp only [gradientSquared, schwartzEnergyState_gradient,
        schwartz_toL2_fourier_norm_sq]

theorem highSchwartz_l2_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ : Test) :
    ‖(highSchwartz q L φ).toLp 2 volume‖ ≤
      L⁻¹ * pureGradientNorm (schwartzEnergyState φ) := by
  have hb := highSchwartz_l2_sq_bound q hL φ
  rw [← pureGradientNorm_sq] at hb
  have hp := pureGradientNorm_nonneg (schwartzEnergyState φ)
  have hn := norm_nonneg ((highSchwartz q L φ).toLp 2 volume)
  have hx : 0 ≤ L⁻¹ * pureGradientNorm (schwartzEnergyState φ) := mul_nonneg (inv_nonneg.mpr hL.le) hp
  nlinarith [sq_nonneg (‖(highSchwartz q L φ).toLp 2 volume‖ - L⁻¹ * pureGradientNorm (schwartzEnergyState φ))]

end HartreeF.EnergySpace.Highpass
