import FYoungKernelScaling
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap ContDiff
namespace HartreeF.GeneralAnnular
open EnergySpace

/-- An arbitrary fixed smooth complex symbol supported in a compact annulus.
No radiality, reality, positivity, or cutoff-difference representation is required. -/
structure Symbol where
  value : V → ℂ
  smooth : ContDiff ℝ ∞ value
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  outer_pos : 0 < outerRadius
  zero_small : ∀ ξ : V, ‖ξ‖ < innerRadius → value ξ = 0
  zero_large : ∀ ξ : V, outerRadius ≤ ‖ξ‖ → value ξ = 0

/-- The literal multiplier profile at frequency scale L. -/
def annularSymbol (q : Symbol) (L : ℝ) (ξ : V) : ℂ :=
  q.value (L⁻¹ • ξ)

theorem annularSymbol_smooth (q : Symbol) (L : ℝ) :
    ContDiff ℝ ∞ (annularSymbol q L) :=
  q.smooth.comp (by fun_prop)

theorem annularSymbol_zero (q : Symbol) (L : ℝ) : annularSymbol q L 0 = 0 := by
  simp only [annularSymbol, smul_zero]
  exact q.zero_small 0 (by simpa using q.inner_pos)

theorem annularSymbol_eq_zero_on_ball (q : Symbol) {L : ℝ} (hL : 0 < L)
    (ξ : V) (hξ : ‖ξ‖ < q.innerRadius * L) :
    annularSymbol q L ξ = 0 := by
  apply q.zero_small
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
  have hh := (div_lt_iff₀ hL).mpr hξ
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem annularSymbol_eq_zero_of_large (q : Symbol) {L : ℝ} (hL : 0 < L)
    (ξ : V) (hξ : q.outerRadius * L ≤ ‖ξ‖) :
    annularSymbol q L ξ = 0 := by
  apply q.zero_large
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
  have hh := (le_div_iff₀ hL).mpr hξ
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem annularSymbol_compact (q : Symbol) {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (annularSymbol q L) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : V) (q.outerRadius * L))
  intro ξ hξ
  by_contra hn
  have hn' : q.outerRadius * L < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  exact hξ (annularSymbol_eq_zero_of_large q hL ξ hn'.le)

theorem annularSymbol_temperate (q : Symbol) {L : ℝ} (hL : 0 < L) :
    (annularSymbol q L).HasTemperateGrowth :=
  (annularSymbol_compact q hL).hasTemperateGrowth (annularSymbol_smooth q L)

/-- The exact inverse derivative symbol. Division is total; the numerator
vanishes on an open neighborhood of the only singular point. -/
def inverseSymbol (q : Symbol) (L : ℝ) (j : Fin 3) (ξ : V) : ℂ :=
  (-Complex.I) * (ξ j : ℂ) * annularSymbol q L ξ /
    (2 * (Real.pi : ℂ) * (‖ξ‖ : ℂ) ^ 2)

theorem inverseSymbol_zero (q : Symbol) (L : ℝ) (j : Fin 3) :
    inverseSymbol q L j 0 = 0 := by
  simp [inverseSymbol]

theorem inverseSymbol_eq_zero_on_ball (q : Symbol) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) (hξ : ‖ξ‖ < q.innerRadius * L) :
    inverseSymbol q L j ξ = 0 := by
  simp only [inverseSymbol, annularSymbol_eq_zero_on_ball q hL ξ hξ, mul_zero,
    zero_div]

theorem inverseSymbol_eventually_zero (q : Symbol) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) : inverseSymbol q L j =ᶠ[𝓝 (0 : V)] fun _ => 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : V)
    (mul_pos q.inner_pos hL)] with ξ hξ
  apply inverseSymbol_eq_zero_on_ball q hL j ξ
  simpa only [Metric.mem_ball, dist_zero_right] using hξ

theorem inverseSymbol_smooth (q : Symbol) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
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

theorem inverseSymbol_compact (q : Symbol) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    HasCompactSupport (inverseSymbol q L j) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : V) (q.outerRadius * L))
  intro ξ hξ
  by_contra hn
  have hn' : q.outerRadius * L < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  have hz := annularSymbol_eq_zero_of_large q hL ξ hn'.le
  apply hξ
  simp only [inverseSymbol, hz, mul_zero, zero_div]

theorem inverseSymbol_temperate (q : Symbol) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    (inverseSymbol q L j).HasTemperateGrowth :=
  (inverseSymbol_compact q hL j).hasTemperateGrowth (inverseSymbol_smooth q hL j)

/-- Genuine Schwartz inverse symbols, obtained from their actual compact support
and smoothness, including smoothness at zero. -/
def inverseSchwartz (q : Symbol) {L : ℝ} (hL : 0 < L) (j : Fin 3) : 𝓢(V, ℂ) :=
  (inverseSymbol_compact q hL j).toSchwartzMap (inverseSymbol_smooth q hL j)

theorem inverseSchwartz_apply (q : Symbol) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) : inverseSchwartz q hL j ξ = inverseSymbol q L j ξ := rfl

/-- The literal inverse-Fourier kernel; its Schwartz class in particular supplies
all finite Lp integrability, rather than assuming an L1 realization. -/
def inverseKernel (q : Symbol) {L : ℝ} (hL : 0 < L) (j : Fin 3) : 𝓢(V, ℂ) :=
  𝓕⁻ (inverseSchwartz q hL j)

theorem inverseKernel_fourier (q : Symbol) {L : ℝ} (hL : 0 < L) (j : Fin 3) :
    𝓕 (inverseKernel q hL j) = inverseSchwartz q hL j := fourier_fourierInv_eq _

/-- Exact inverse-gradient reconstruction, with the native 2*pi*i multiplier. -/
theorem inverseSymbol_reconstruction (q : Symbol) (L : ℝ) (ξ : V) :
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

theorem annularSymbol_scale (q : Symbol) (L : ℝ) (ξ : V) :
    annularSymbol q L ξ = annularSymbol q 1 (L⁻¹ • ξ) := by
  simp only [annularSymbol, inv_one, one_smul]

/-- The complex-multiplication spelling of the inverse-symbol dilation. -/
theorem inverseSymbol_scale_mul (q : Symbol) {L : ℝ} (hL : 0 < L)
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
theorem inverseSymbol_scale (q : Symbol) {L : ℝ} (hL : 0 < L)
    (j : Fin 3) (ξ : V) :
    inverseSymbol q L j ξ = L⁻¹ • inverseSymbol q 1 j (L⁻¹ • ξ) := by
  simpa only [Complex.real_smul] using inverseSymbol_scale_mul q hL j ξ

end HartreeF.GeneralAnnular
