import PositiveBetaIntegral
import GammaBracketProfile

/-! The actual transformed positive Gaussian parameter integral. Its product
L1 domain is supplied by a native Beta-times-Gamma majorant before Fubini. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
namespace HartreeF.BubbleProfile
open HeatRiesz

/-- Tuple order is (t,s), where the original Riesz rate is r=s*t. -/
def transformedParameter (a R : ℝ) (q : ℝ × ℝ) : ℝ :=
  q.1^(a-1)*(1+q.1)^(-(3/2:ℝ))*q.2^(1/2:ℝ)*
    Real.exp (-((1+(q.1/(1+q.1))*R)*q.2))

theorem positiveTimePair_ae :
    ∀ᵐ q : ℝ × ℝ ∂positiveTimeMeasure.prod positiveTimeMeasure, 0<q.1 ∧ 0<q.2 := by
  change ∀ᵐ q : ℝ × ℝ ∂(volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)),
    q ∈ Ioi 0 ×ˢ Ioi 0
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

theorem transformedParameter_nonneg (a R : ℝ) {t s : ℝ} (ht : 0<t) (hs : 0<s) :
    0 ≤ transformedParameter a R (t,s) := by
  unfold transformedParameter
  positivity

theorem transformedParameter_bound (a : ℝ) {R t s : ℝ} (hR : 0≤R) (ht : 0<t) (hs : 0<s) :
    ‖transformedParameter a R (t,s)‖ ≤
      betaRateIntegrand a (3/2-a) 1 t * (s^(1/2:ℝ)*Real.exp (-s)) := by
  have hq : 0 ≤ t/(1+t) := div_nonneg ht.le (by linarith)
  have he : Real.exp (-((1+(t/(1+t))*R)*s)) ≤ Real.exp (-s) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_nonneg hq hR
    nlinarith
  rw [Real.norm_of_nonneg (transformedParameter_nonneg a R ht hs)]
  unfold transformedParameter betaRateIntegrand
  simp only [one_mul, show a+(3/2-a) = (3/2:ℝ) by ring]
  have hm : 0 ≤ t^(a-1)*(1+t)^(-(3/2:ℝ))*s^(1/2:ℝ) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he hm

theorem transformedParameter_measurable (a R : ℝ) :
    AEStronglyMeasurable (transformedParameter a R)
      (positiveTimeMeasure.prod positiveTimeMeasure) := by
  apply Measurable.aestronglyMeasurable
  unfold transformedParameter
  fun_prop

theorem transformedParameter_integrable {a R : ℝ} (ha : 0<a) (ha3 : a<3/2) (hR : 0≤R) :
    Integrable (transformedParameter a R) (positiveTimeMeasure.prod positiveTimeMeasure) := by
  have hb := betaRate_integrable ha (sub_pos.mpr ha3) (by norm_num : (0:ℝ)<1)
  have hg : Integrable (fun s : ℝ => s^(1/2:ℝ)*Real.exp (-s)) positiveTimeMeasure := by
    simpa only [IntegrableOn, positiveTimeMeasure, show (3/2-1:ℝ) = 1/2 by norm_num, one_mul]
      using (gammaRate_integrable (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1))
  apply (hb.mul_prod hg).mono' (transformedParameter_measurable a R)
  filter_upwards [positiveTimePair_ae] with q hq
  exact transformedParameter_bound a hR hq.1 hq.2

theorem transformedParameter_s_integral (a : ℝ) {R t : ℝ} (hR : 0≤R) (ht : 0<t) :
    (∫ s, transformedParameter a R (t,s) ∂positiveTimeMeasure) =
      Real.Gamma (3/2:ℝ)*betaRateIntegrand a (3/2-a) (1+R) t := by
  have ht1 : 0 < 1+t := by linarith
  have hA : 0 < 1+(t/(1+t))*R := by
    have hh := mul_nonneg (div_nonneg ht.le ht1.le) hR
    linarith
  have hg : (∫ s, s^(1/2:ℝ)*Real.exp (-((1+(t/(1+t))*R)*s)) ∂positiveTimeMeasure) =
      (1+(t/(1+t))*R)^(-(3/2:ℝ))*Real.Gamma (3/2:ℝ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ)<3/2) hA
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at h
    simpa only [show (3/2-1:ℝ)=1/2 by norm_num] using h
  have hp : (1+t)*(1+(t/(1+t))*R) = 1+(1+R)*t := by
    field_simp
    ring
  unfold transformedParameter
  simp only [mul_assoc, integral_const_mul]
  rw [hg]
  unfold betaRateIntegrand
  rw [show a+(3/2-a) = (3/2:ℝ) by ring]
  calc
    _ = Real.Gamma (3/2:ℝ)*t^(a-1)*
        ((1+t)^(-(3/2:ℝ))*(1+(t/(1+t))*R)^(-(3/2:ℝ))) := by ring
    _ = _ := by rw [← Real.mul_rpow ht1.le hA.le, hp]; ring

theorem transformedParameter_integral {a R : ℝ} (ha : 0<a) (ha3 : a<3/2) (hR : 0≤R) :
    (∫ q, transformedParameter a R q ∂positiveTimeMeasure.prod positiveTimeMeasure) =
      (1+R)^(-a)*Real.Gamma a*Real.Gamma (3/2-a) := by
  rw [integral_prod _ (transformedParameter_integrable ha ha3 hR)]
  have he : (∫ t, (∫ s, transformedParameter a R (t,s) ∂positiveTimeMeasure)
      ∂positiveTimeMeasure) =
      ∫ t, Real.Gamma (3/2:ℝ)*betaRateIntegrand a (3/2-a) (1+R) t ∂positiveTimeMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact transformedParameter_s_integral a hR ht
  rw [he, integral_const_mul]
  have hb := betaRate_integral ha (sub_pos.mpr ha3) (show 0<1+R by linarith)
  rw [show a+(3/2-a) = (3/2:ℝ) by ring] at hb
  change Real.Gamma (3/2:ℝ)*(∫ t in Ioi 0, betaRateIntegrand a (3/2-a) (1+R) t) = _
  rw [hb]
  have hG := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<3/2)).ne'
  field_simp

#print axioms positiveTimePair_ae
#print axioms transformedParameter_nonneg
#print axioms transformedParameter_bound
#print axioms transformedParameter_measurable
#print axioms transformedParameter_integrable
#print axioms transformedParameter_s_integral
#print axioms transformedParameter_integral
end HartreeF.BubbleProfile
