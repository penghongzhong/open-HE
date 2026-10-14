import PhysicalPairDiagonal
import HeatSpectralMultiplier
import PhysicalDensityTruncation

/-!
The actual nonnegative physical heat-time pair domain is produced from the
original finite standard-Riesz pair domain. The a.e. nonzero separation from
checkpoint07 is used before evaluating the time integral. This is nonnegative
Tonelli/integrable_prod_iff, never an oscillatory time-space Fourier exchange.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
namespace HartreeF.HeatRiesz
open GaussianFourierBridge PhysicalDensity

abbrev positiveTimeMeasure : Measure ℝ := volume.restrict (Ioi 0)

def timeWeight (α t : ℝ) : ℝ := t^(α/2-1) / Real.Gamma (α/2)

def standardRieszPair (α : ℝ) (b : Space → ℝ) : Space × Space → ℝ :=
  pairDensity (fun q => rieszKernel α (standardRieszConstant α) (q.1-q.2)) b

def physicalHeatPair (α : ℝ) (b : Space → ℝ) (p : (Space × Space) × ℝ) : ℝ :=
  heatMixtureIntegrand α (p.1.1-p.1.2) p.2 * b p.1.2 * b p.1.1

def physicalHeatEnergy (α : ℝ) (b : Space → ℝ) (t : ℝ) : ℝ :=
  timeWeight α t * ∫ q : Space × Space,
    heatKernel t (q.1-q.2) * b q.2 * b q.1 ∂volume.prod volume

theorem timeWeight_nonneg {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 0 < t) :
    0 ≤ timeWeight α t :=
  div_nonneg (Real.rpow_nonneg ht.le _) (Real.Gamma_pos_of_pos (by linarith : 0 < α/2)).le

theorem timeWeight_measurable (α : ℝ) : Measurable (timeWeight α) := by
  unfold timeWeight
  exact (measurable_id.pow_const _).div_const _

theorem heatMixture_eq_timeWeight (α t : ℝ) (z : Space) :
    heatMixtureIntegrand α z t = timeWeight α t * heatKernel t z := by
  unfold heatMixtureIntegrand timeWeight
  ring

theorem physicalHeatPair_nonneg {α : ℝ} (hα : 0 < α)
    {b : Space → ℝ} (hb0 : ∀ x, 0 ≤ b x) (q : Space × Space)
    {t : ℝ} (ht : 0 < t) : 0 ≤ physicalHeatPair α b (q,t) :=
  mul_nonneg (mul_nonneg (heatMixtureIntegrand_nonneg hα (q.1-q.2) ht) (hb0 q.2)) (hb0 q.1)

theorem physicalHeatPair_aestronglyMeasurable (α : ℝ)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (physicalHeatPair α b) ((volume.prod volume).prod positiveTimeMeasure) := by
  have hk : Measurable (fun p : (Space × Space) × ℝ =>
      heatMixtureIntegrand α (p.1.1-p.1.2) p.2) := by
    unfold heatMixtureIntegrand heatKernel
    fun_prop
  exact (hk.aestronglyMeasurable.mul hb.comp_snd.comp_fst).mul hb.comp_fst.comp_fst

theorem physicalHeatPair_time_integrable_ae {α : ℝ} (hα3 : α < 3) (b : Space → ℝ) :
    ∀ᵐ q : Space × Space ∂volume.prod volume,
      Integrable (fun t => physicalHeatPair α b (q,t)) positiveTimeMeasure := by
  filter_upwards [heatMixture_pair_integrable_time_ae hα3] with q hq
  exact (hq.mul_const (b q.2)).mul_const (b q.1)

theorem physicalHeatPair_time_integral_ae {α : ℝ} (hα3 : α < 3) (b : Space → ℝ) :
    (fun q : Space × Space => ∫ t, physicalHeatPair α b (q,t) ∂positiveTimeMeasure) =ᵐ[volume.prod volume]
      standardRieszPair α b := by
  filter_upwards [heatMixture_pair_eq_riesz_ae hα3] with q hq
  unfold physicalHeatPair standardRieszPair pairDensity
  dsimp only
  rw [integral_mul_const, integral_mul_const]
  exact congrArg (fun v => v * b q.2 * b q.1) hq

/-- Absolute pair-times-time integrability follows from positivity and the actual base-pair domain. -/
theorem physicalHeatPair_integrable {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    Integrable (physicalHeatPair α b) ((volume.prod volume).prod positiveTimeMeasure) := by
  apply (integrable_prod_iff (physicalHeatPair_aestronglyMeasurable α hb)).mpr
  refine ⟨physicalHeatPair_time_integrable_ae hα3 b, ?_⟩
  apply hpair.congr
  filter_upwards [physicalHeatPair_time_integral_ae hα3 b] with q hq
  rw [← hq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (Real.norm_of_nonneg (physicalHeatPair_nonneg hα hb0 q ht)).symm

theorem physicalHeatPair_space_integral (α t : ℝ) (b : Space → ℝ) :
    (∫ q : Space × Space, physicalHeatPair α b (q,t) ∂volume.prod volume) =
      physicalHeatEnergy α b t := by
  have he : (fun q : Space × Space => physicalHeatPair α b (q,t)) =
      (fun q => timeWeight α t * (heatKernel t (q.1-q.2) * b q.2 * b q.1)) := by
    funext q
    unfold physicalHeatPair
    rw [heatMixture_eq_timeWeight]
    ring
  rw [he, integral_const_mul]
  rfl

theorem physicalHeatEnergy_integrable {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    Integrable (physicalHeatEnergy α b) positiveTimeMeasure := by
  apply (physicalHeatPair_integrable hα hα3 hb hb0 hpair).integral_prod_right.congr
  exact Eventually.of_forall (fun t => physicalHeatPair_space_integral α t b)

/-- The original actual Riesz energy equals the nonnegative heat-time integral. -/
theorem physicalRieszEnergy_eq_heatTime {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    (∫ q, standardRieszPair α b q ∂volume.prod volume) =
      ∫ t, physicalHeatEnergy α b t ∂positiveTimeMeasure := by
  have hp := physicalHeatPair_integrable hα hα3 hb hb0 hpair
  calc
    _ = ∫ q : Space × Space, (∫ t, physicalHeatPair α b (q,t) ∂positiveTimeMeasure)
        ∂volume.prod volume := integral_congr_ae (physicalHeatPair_time_integral_ae hα3 b).symm
    _ = ∫ p : (Space × Space) × ℝ, physicalHeatPair α b p
        ∂(volume.prod volume).prod positiveTimeMeasure := (integral_prod _ hp).symm
    _ = ∫ t, (∫ q : Space × Space, physicalHeatPair α b (q,t) ∂volume.prod volume)
        ∂positiveTimeMeasure := integral_prod_symm _ hp
    _ = _ := integral_congr_ae (Eventually.of_forall (fun t => physicalHeatPair_space_integral α t b))

#print axioms timeWeight_nonneg
#print axioms timeWeight_measurable
#print axioms heatMixture_eq_timeWeight
#print axioms physicalHeatPair_nonneg
#print axioms physicalHeatPair_aestronglyMeasurable
#print axioms physicalHeatPair_time_integrable_ae
#print axioms physicalHeatPair_time_integral_ae
#print axioms physicalHeatPair_integrable
#print axioms physicalHeatPair_space_integral
#print axioms physicalHeatEnergy_integrable
#print axioms physicalRieszEnergy_eq_heatTime
end HartreeF.HeatRiesz
