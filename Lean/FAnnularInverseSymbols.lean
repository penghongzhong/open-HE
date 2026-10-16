import FYoungKernelScaling
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Literal annular inverse-gradient symbols for the already fixed Hartree cutoff.
The total quotient is zero at the origin, and is identically zero on an actual
small ball. Smoothness at the origin is proved from that local identity.
No realization, Young bound, or PDE hypothesis is assumed here.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap ContDiff

namespace HartreeF.AnnularL1
open EnergySpace EnergySpace.Highpass

/-- The precise standard dyadic band from the manuscript cutoff. -/
def annularSymbol (q : Cutoff) (L : ℝ) (ξ : V) : ℂ :=
  lowSymbol q L ξ - lowSymbol q (L / 2) ξ

/-- A literal enlarged band that is one on the support of the standard band. -/
def enlargedAnnularSymbol (q : Cutoff) (L : ℝ) (ξ : V) : ℂ :=
  lowSymbol q (2 * L) ξ - lowSymbol q (L / 4) ξ

theorem annularSymbol_smooth (q : Cutoff) (L : ℝ) :
    ContDiff ℝ ∞ (annularSymbol q L) := by
  exact (Complex.ofRealCLM.contDiff.comp (q.smooth.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (q.smooth.comp (by fun_prop)))

theorem annularSymbol_zero (q : Cutoff) (L : ℝ) :
    annularSymbol q L 0 = 0 := by
  simp [annularSymbol, lowSymbol]

theorem annularSymbol_eq_zero_of_small (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (ξ : V) (hξ : 2 * Real.pi * ‖ξ‖ ≤ L / 2) :
    annularSymbol q L ξ = 0 := by
  unfold annularSymbol
  rw [lowSymbol_one q hL ξ (by linarith),
    lowSymbol_one q (by positivity : 0 < L / 2) ξ hξ, sub_self]

theorem annularSymbol_eq_zero_of_large (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (ξ : V) (hξ : 2 * L ≤ 2 * Real.pi * ‖ξ‖) :
    annularSymbol q L ξ = 0 := by
  unfold annularSymbol
  rw [lowSymbol_zero q hL ξ hξ,
    lowSymbol_zero q (by positivity : 0 < L / 2) ξ (by linarith), sub_self]

/-- An explicit open ball on which the annular symbol is exactly zero. -/
theorem annularSymbol_eq_zero_on_ball (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (ξ : V) (hξ : ‖ξ‖ < L / (4 * Real.pi)) :
    annularSymbol q L ξ = 0 := by
  apply annularSymbol_eq_zero_of_small q hL ξ
  have hh := (lt_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp hξ
  nlinarith

theorem annularSymbol_compact (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (annularSymbol q L) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : V) (L / Real.pi))
  intro ξ hξ
  by_contra hn
  have hn' : L / Real.pi < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  have hh := (div_lt_iff₀ Real.pi_pos).mp hn'
  exact hξ (annularSymbol_eq_zero_of_large q hL ξ (by nlinarith))

theorem annularSymbol_temperate (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    (annularSymbol q L).HasTemperateGrowth :=
  (annularSymbol_compact q hL).hasTemperateGrowth (annularSymbol_smooth q L)

/-- The enlarged band absorbs the exact standard band, without an idempotence
assumption on the smooth cutoff. -/
theorem annularSymbol_mul_enlarged (q : Cutoff) {L : ℝ} (hL : 0 < L) (ξ : V) :
    annularSymbol q L ξ * enlargedAnnularSymbol q L ξ = annularSymbol q L ξ := by
  by_cases hs : 2 * Real.pi * ‖ξ‖ ≤ L / 2
  · rw [annularSymbol_eq_zero_of_small q hL ξ hs, zero_mul]
  by_cases hl : 2 * L ≤ 2 * Real.pi * ‖ξ‖
  · rw [annularSymbol_eq_zero_of_large q hL ξ hl, zero_mul]
  have hbig : lowSymbol q (2 * L) ξ = 1 :=
    lowSymbol_one q (by positivity) ξ (le_of_not_ge hl)
  have hsmall : lowSymbol q (L / 4) ξ = 0 :=
    lowSymbol_zero q (by positivity) ξ (by linarith)
  simp only [enlargedAnnularSymbol, hbig, hsmall, sub_zero, mul_one]

/-- Three standard dyadic bands telescope to the literal enlarged cutoff. -/
theorem enlargedAnnularSymbol_eq_sum (q : Cutoff) (L : ℝ) (ξ : V) :
    enlargedAnnularSymbol q L ξ = annularSymbol q (2 * L) ξ +
      annularSymbol q L ξ + annularSymbol q (L / 2) ξ := by
  have h₁ : 2 * L / 2 = L := by ring
  have h₂ : L / 2 / 2 = L / 4 := by ring
  simp only [enlargedAnnularSymbol, annularSymbol, h₁, h₂]
  ring

/-- The exact inverse derivative symbol. Division is total; the numerator
vanishes on an open neighborhood of the only singular point. -/
def inverseSymbol (q : Cutoff) (L : ℝ) (j : Fin 3) (ξ : V) : ℂ :=
  (-Complex.I) * (ξ j : ℂ) * annularSymbol q L ξ /
    (2 * (Real.pi : ℂ) * (‖ξ‖ : ℂ) ^ 2)

theorem inverseSymbol_zero (q : Cutoff) (L : ℝ) (j : Fin 3) :
    inverseSymbol q L j 0 = 0 := by
  simp [inverseSymbol]

theorem inverseSymbol_eq_zero_of_small (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) (hξ : 2 * Real.pi * ‖ξ‖ ≤ L / 2) :
    inverseSymbol q L j ξ = 0 := by
  simp only [inverseSymbol, annularSymbol_eq_zero_of_small q hL ξ hξ, mul_zero,
    zero_div]

theorem inverseSymbol_eq_zero_on_ball (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) (hξ : ‖ξ‖ < L / (4 * Real.pi)) :
    inverseSymbol q L j ξ = 0 := by
  simp only [inverseSymbol, annularSymbol_eq_zero_on_ball q hL ξ hξ, mul_zero,
    zero_div]

theorem inverseSymbol_eventually_zero (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) : inverseSymbol q L j =ᶠ[𝓝 (0 : V)] fun _ => 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : V)
    (by positivity : 0 < L / (4 * Real.pi))] with ξ hξ
  apply inverseSymbol_eq_zero_on_ball q hL j ξ
  simpa only [Metric.mem_ball, dist_zero_right] using hξ

theorem inverseSymbol_smooth (q : Cutoff) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    ContDiff ℝ ∞ (inverseSymbol q L j) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : V => (0 : ℂ)) 0).congr_of_eventuallyEq (inverseSymbol_eventually_zero q hL j)
  · have hcoord : ContDiff ℝ ∞ (fun η : V => (η j : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
    have hsquare : ContDiff ℝ ∞ (fun η : V => (‖η‖ : ℂ) ^ 2) := by
      have hr : ContDiff ℝ ∞ (fun η : V => ((‖η‖ ^ 2 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp
          (contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun η : V => ‖η‖ ^ 2))
      simpa only [Complex.ofReal_pow] using hr
    have hnum : ContDiff ℝ ∞
        (fun η : V => (-Complex.I) * (η j : ℂ) * annularSymbol q L η) :=
      (contDiff_const.mul hcoord).mul (annularSymbol_smooth q L)
    have hden : ContDiff ℝ ∞
        (fun η : V => 2 * (Real.pi : ℂ) * (‖η‖ : ℂ) ^ 2) :=
      contDiff_const.mul hsquare
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hn : (‖ξ‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hξ)
    have hden0 : 2 * (Real.pi : ℂ) * (‖ξ‖ : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hpi) (pow_ne_zero 2 hn)
    have hh : ContDiffAt ℝ ∞
        (fun η : V => ((-Complex.I) * (η j : ℂ) * annularSymbol q L η) *
          (2 * (Real.pi : ℂ) * (‖η‖ : ℂ) ^ 2)⁻¹) ξ :=
      hnum.contDiffAt.mul (hden.contDiffAt.fun_inv hden0)
    unfold inverseSymbol
    simpa only [div_eq_mul_inv] using hh

theorem inverseSymbol_compact (q : Cutoff) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    HasCompactSupport (inverseSymbol q L j) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : V) (L / Real.pi))
  intro ξ hξ
  by_contra hn
  have hn' : L / Real.pi < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  have hh := (div_lt_iff₀ Real.pi_pos).mp hn'
  have hz := annularSymbol_eq_zero_of_large q hL ξ (by nlinarith)
  apply hξ
  simp only [inverseSymbol, hz, mul_zero, zero_div]

theorem inverseSymbol_temperate (q : Cutoff) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    (inverseSymbol q L j).HasTemperateGrowth :=
  (inverseSymbol_compact q hL j).hasTemperateGrowth (inverseSymbol_smooth q hL j)

/-- Genuine Schwartz inverse symbols, obtained from their actual compact support
and smoothness, including smoothness at zero. -/
def inverseSchwartz (q : Cutoff) {L : ℝ} (hL : 0 < L) (j : Fin 3) : 𝓢(V, ℂ) :=
  (inverseSymbol_compact q hL j).toSchwartzMap (inverseSymbol_smooth q hL j)

theorem inverseSchwartz_apply (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) : inverseSchwartz q hL j ξ = inverseSymbol q L j ξ := rfl

/-- The literal inverse-Fourier kernel; its Schwartz class in particular supplies
all finite Lp integrability, rather than assuming an L1 realization. -/
def inverseKernel (q : Cutoff) {L : ℝ} (hL : 0 < L) (j : Fin 3) : 𝓢(V, ℂ) :=
  𝓕⁻ (inverseSchwartz q hL j)

theorem inverseKernel_fourier (q : Cutoff) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    𝓕 (inverseKernel q hL j) = inverseSchwartz q hL j := fourier_fourierInv_eq _

/-- Exact inverse-gradient reconstruction, with the native 2*pi*i multiplier. -/
theorem inverseSymbol_reconstruction (q : Cutoff) (L : ℝ) (ξ : V) :
    (∑ j : Fin 3, inverseSymbol q L j ξ *
      (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ))) = annularSymbol q L ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [inverseSymbol_zero, zero_mul, Finset.sum_const_zero, annularSymbol_zero]
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hξ)
    have hnorm : (∑ j : Fin 3, (ξ j : ℂ) ^ 2) = (‖ξ‖ : ℂ) ^ 2 := by
      exact_mod_cast (EuclideanSpace.real_norm_sq_eq ξ).symm
    calc
      _ = (annularSymbol q L ξ / (‖ξ‖ : ℂ) ^ 2) *
          ∑ j : Fin 3, (ξ j : ℂ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        unfold inverseSymbol
        field_simp [hpi, hn]
        ring_nf
        simp [Complex.I_sq]
      _ = annularSymbol q L ξ := by
        rw [hnorm]
        exact div_mul_cancel₀ _ (pow_ne_zero 2 hn)

theorem inverseSymbol_mul_enlarged (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) :
    inverseSymbol q L j ξ * enlargedAnnularSymbol q L ξ = inverseSymbol q L j ξ := by
  unfold inverseSymbol
  calc
    _ = ((-Complex.I) * (ξ j : ℂ) *
        (annularSymbol q L ξ * enlargedAnnularSymbol q L ξ)) /
          (2 * (Real.pi : ℂ) * (‖ξ‖ : ℂ) ^ 2) := by ring
    _ = _ := by rw [annularSymbol_mul_enlarged q hL ξ]

/-- Low-symbol scaling with exactly the pre-existing angular normalization. -/
theorem lowSymbol_dilate (q : Cutoff) (c L : ℝ) (ξ : V) :
    lowSymbol q (c * L) ξ = lowSymbol q c (L⁻¹ • ξ) := by
  unfold lowSymbol
  congr 2
  rw [smul_smul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem annularSymbol_scale (q : Cutoff) (L : ℝ) (ξ : V) :
    annularSymbol q L ξ = annularSymbol q 1 (L⁻¹ • ξ) := by
  unfold annularSymbol
  rw [← lowSymbol_dilate q 1 L ξ, ← lowSymbol_dilate q (1 / 2) L ξ]
  congr 1 <;> congr 1 <;> ring

/-- The complex-multiplication spelling of the inverse-symbol dilation. -/
theorem inverseSymbol_scale_mul (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) :
    inverseSymbol q L j ξ = ((L⁻¹ : ℝ) : ℂ) *
      inverseSymbol q 1 j (L⁻¹ • ξ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [inverseSymbol_zero, smul_zero, mul_zero]
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hξ)
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hcoord : ((L⁻¹ • ξ) j : ℂ) = (L : ℂ)⁻¹ * (ξ j : ℂ) := by
      simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    have hnorm : (‖L⁻¹ • ξ‖ : ℂ) = (L : ℂ)⁻¹ * (‖ξ‖ : ℂ) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL),
        Complex.ofReal_mul, Complex.ofReal_inv]
    rw [inverseSymbol, inverseSymbol, annularSymbol_scale q L ξ, hcoord, hnorm]
    push_cast
    field_simp [hpi, hn, hLc]

/-- Both scalar actions in this equality are the ordinary real scalar action. -/
theorem inverseSymbol_scale (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) :
    inverseSymbol q L j ξ = L⁻¹ • inverseSymbol q 1 j (L⁻¹ • ξ) := by
  simpa only [Complex.real_smul] using inverseSymbol_scale_mul q hL j ξ

end HartreeF.AnnularL1
