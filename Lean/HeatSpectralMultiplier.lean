import HeatRieszPointwise

/-! The exact heat-time spectral multiplier in the paper-frequency convention.
Its actual time integral is computed only at nonzero frequency; the exceptional
frequency singleton is separately shown null. No time-frequency Fubini is used. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace HartreeF.HeatRiesz

def spectralHeatMixtureIntegrand (α : ℝ) (ξ : Space) (t : ℝ) : ℝ :=
  t^(α/2-1) * Real.exp (-t*‖ξ‖^2) / Real.Gamma (α/2)

theorem spectralHeatMixtureIntegrand_nonneg {α : ℝ} (hα : 0 < α)
    (ξ : Space) {t : ℝ} (ht : 0 < t) :
    0 ≤ spectralHeatMixtureIntegrand α ξ t := by
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    (Real.Gamma_pos_of_pos (by linarith : 0 < α/2)).le

theorem spectralHeatMixture_integrable_nonzero {α : ℝ} (hα : 0 < α)
    {ξ : Space} (hξ : ξ ≠ 0) :
    IntegrableOn (spectralHeatMixtureIntegrand α ξ) (Ioi 0) := by
  have hβ : 0 < α/2 := by linarith
  have hA := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have h := (gammaRate_integrable hβ hA).div_const (Real.Gamma (α/2))
  apply h.congr
  filter_upwards [] with t
  unfold spectralHeatMixtureIntegrand
  congr 2
  congr 1
  ring

theorem spectralHeatMixture_integral_nonzero {α : ℝ} (hα : 0 < α)
    {ξ : Space} (hξ : ξ ≠ 0) :
    (∫ t in Ioi 0, spectralHeatMixtureIntegrand α ξ t) = ‖ξ‖^(-α) := by
  have hβ : 0 < α/2 := by linarith
  have hA := sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have hΓ := (Real.Gamma_pos_of_pos hβ).ne'
  have he : (fun t : ℝ => t^(α/2-1) * Real.exp (-t*‖ξ‖^2)) =
      (fun t => t^(α/2-1) * Real.exp (-(‖ξ‖^2*t))) := by
    funext t
    congr 2
    ring
  unfold spectralHeatMixtureIntegrand
  rw [integral_div, he, Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hA,
    mul_div_cancel_right₀ _ hΓ, one_div, ← Real.rpow_neg_eq_inv_rpow,
    ← Real.rpow_natCast_mul (norm_nonneg ξ)]
  congr 1
  push_cast
  ring

theorem frequency_ne_zero_ae : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := volume.ae_ne 0

theorem spectralHeatMixture_integral_ae {α : ℝ} (hα : 0 < α) :
    (fun ξ : Space => ∫ t in Ioi 0, spectralHeatMixtureIntegrand α ξ t) =ᵐ[volume]
      (fun ξ => ‖ξ‖^(-α)) := by
  filter_upwards [frequency_ne_zero_ae] with ξ hξ
  exact spectralHeatMixture_integral_nonzero hα hξ

#print axioms spectralHeatMixtureIntegrand_nonneg
#print axioms spectralHeatMixture_integrable_nonzero
#print axioms spectralHeatMixture_integral_nonzero
#print axioms frequency_ne_zero_ae
#print axioms spectralHeatMixture_integral_ae
end HartreeF.HeatRiesz
