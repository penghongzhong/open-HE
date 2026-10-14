import PhysicalHeatTonelli
import HeatSpectralMultiplier

/-!
Absolute time-frequency integrability for the actual heat spectral pair is
produced from the physical heat-energy domain. The fixed-time C6 identity
controls the outer L1 norm, then C7 evaluates the time integral away from
the null zero-frequency singleton. No Riesz-Fourier identity is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace HartreeF.HeatRiesz
open GaussianFourierBridge BWork.Gaussian

def spectralHeatPair (α : ℝ) (b : Space → ℝ) (t : ℝ) (ξ : Space) : ℝ :=
  spectralHeatMixtureIntegrand α ξ t * ‖paperFourier b ξ‖^2

theorem spectralHeatPair_nonneg {α : ℝ} (hα : 0 < α) (b : Space → ℝ)
    {t : ℝ} (ht : 0 < t) (ξ : Space) : 0 ≤ spectralHeatPair α b t ξ :=
  mul_nonneg (spectralHeatMixtureIntegrand_nonneg hα ξ ht) (sq_nonneg _)

theorem spectralHeatPair_aestronglyMeasurable (α : ℝ) {b : Space → ℝ}
    (hb : Integrable b volume) :
    AEStronglyMeasurable (Function.uncurry (spectralHeatPair α b))
      (positiveTimeMeasure.prod volume) := by
  have hw : AEStronglyMeasurable (timeWeight α) positiveTimeMeasure := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    unfold timeWeight
    exact (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).div_const _
  have hg : Continuous (fun p : ℝ × Space => Real.exp (-p.1*‖p.2‖^2)) := by fun_prop
  have hF := (paperFourier_aestronglyMeasurable hb).norm.pow 2
  apply ((hw.comp_fst.mul hg.aestronglyMeasurable).mul hF.comp_snd).congr
  filter_upwards [] with p
  simp only [Pi.mul_apply, Pi.pow_apply]
  unfold Function.uncurry spectralHeatPair spectralHeatMixtureIntegrand timeWeight
  ring

theorem spectralHeatPair_frequency_integrable (α : ℝ) {b : Space → ℝ}
    (hb : Integrable b volume) {t : ℝ} (ht : 0 < t) :
    Integrable (spectralHeatPair α b t) volume := by
  apply ((gaussianFourierEnergy_integrable ht hb).const_mul (timeWeight α t)).congr
  filter_upwards [] with ξ
  unfold spectralHeatPair spectralHeatMixtureIntegrand timeWeight gaussianRate
  ring

theorem physicalHeatEnergy_eq_spectralHeatPair (α : ℝ) {b : Space → ℝ}
    (hb : Integrable b volume) {t : ℝ} (ht : 0 < t) :
    physicalHeatEnergy α b t = paperInverseFactor * ∫ ξ, spectralHeatPair α b t ξ := by
  have hswap : (fun q : Space × Space => heatKernel t (q.1-q.2) * b q.2 * b q.1) =
      (fun q => heatKernel t (q.1-q.2) * b q.1 * b q.2) := by
    funext q
    ring
  have he : spectralHeatPair α b t =
      (fun ξ => timeWeight α t * (Real.exp (-t*‖ξ‖^2) * ‖paperFourier b ξ‖^2)) := by
    funext ξ
    unfold spectralHeatPair spectralHeatMixtureIntegrand timeWeight
    ring
  rw [physicalHeatEnergy, hswap, heat_L1_pair_fourier ht hb, he, integral_const_mul]
  ring

theorem spectralHeatPair_integrable {α : ℝ} (hα : 0 < α) {b : Space → ℝ}
    (hb : Integrable b volume) (htime : Integrable (physicalHeatEnergy α b) positiveTimeMeasure) :
    Integrable (Function.uncurry (spectralHeatPair α b))
      (positiveTimeMeasure.prod volume) := by
  apply (integrable_prod_iff (spectralHeatPair_aestronglyMeasurable α hb)).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact spectralHeatPair_frequency_integrable α hb ht
  · apply (htime.div_const paperInverseFactor).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hn : (fun ξ => ‖spectralHeatPair α b t ξ‖) = spectralHeatPair α b t := by
      funext ξ
      exact Real.norm_of_nonneg (spectralHeatPair_nonneg hα b ht ξ)
    simp only [Function.uncurry_apply_pair, hn]
    rw [physicalHeatEnergy_eq_spectralHeatPair α hb ht,
      mul_div_cancel_left₀ _ paperInverseFactor_pos.ne']

theorem spectralHeatPair_time_integral_ae {α : ℝ} (hα : 0 < α) (b : Space → ℝ) :
    (fun ξ : Space => ∫ t, spectralHeatPair α b t ξ ∂positiveTimeMeasure) =ᵐ[volume]
      (fun ξ => ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2) := by
  filter_upwards [spectralHeatMixture_integral_ae hα] with ξ hξ
  change (∫ t in Ioi 0, spectralHeatMixtureIntegrand α ξ t * ‖paperFourier b ξ‖^2) = _
  rw [integral_mul_const, hξ]

theorem weightedFourierEnergy_integrable_of_heatEnergy {α : ℝ} (hα : 0 < α)
    {b : Space → ℝ} (hb : Integrable b volume)
    (htime : Integrable (physicalHeatEnergy α b) positiveTimeMeasure) :
    Integrable (fun ξ : Space => ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2) volume := by
  exact (spectralHeatPair_integrable hα hb htime).integral_prod_right.congr
    (spectralHeatPair_time_integral_ae hα b)

theorem weightedFourierEnergy_eq_heatEnergy {α : ℝ} (hα : 0 < α)
    {b : Space → ℝ} (hb : Integrable b volume)
    (htime : Integrable (physicalHeatEnergy α b) positiveTimeMeasure) :
    paperInverseFactor * (∫ ξ : Space, ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2) =
      ∫ t, physicalHeatEnergy α b t ∂positiveTimeMeasure := by
  have hprod := spectralHeatPair_integrable hα hb htime
  calc
    _ = paperInverseFactor * ∫ ξ, ∫ t, spectralHeatPair α b t ξ ∂positiveTimeMeasure := by
      rw [integral_congr_ae (spectralHeatPair_time_integral_ae hα b)]
    _ = paperInverseFactor * ∫ t, (∫ ξ : Space, spectralHeatPair α b t ξ) ∂positiveTimeMeasure := by
      rw [integral_integral_swap hprod]
    _ = ∫ t, paperInverseFactor * (∫ ξ, spectralHeatPair α b t ξ) ∂positiveTimeMeasure := by
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (physicalHeatEnergy_eq_spectralHeatPair α hb ht).symm

#print axioms spectralHeatPair_nonneg
#print axioms spectralHeatPair_aestronglyMeasurable
#print axioms spectralHeatPair_frequency_integrable
#print axioms physicalHeatEnergy_eq_spectralHeatPair
#print axioms spectralHeatPair_integrable
#print axioms spectralHeatPair_time_integral_ae
#print axioms weightedFourierEnergy_integrable_of_heatEnergy
#print axioms weightedFourierEnergy_eq_heatEnergy
end HartreeF.HeatRiesz
