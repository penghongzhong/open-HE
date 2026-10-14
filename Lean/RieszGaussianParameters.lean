import RieszParameterTransform

/-! The original positive Gaussian parameters, in tuple order `(s,r)`.
The actual product L1 domain is transported from the Beta/Gamma majorant by
positive linear scaling of the inner rate, before invoking Fubini. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
namespace HartreeF.BubbleProfile
open HeatRiesz

/-- Tuple order is `(s,r)`: the bubble rate precedes the Riesz rate. -/
def parameterKernel (a R : ℝ) (q : ℝ × ℝ) : ℝ :=
  q.2^(a-1)*q.1^(2-a)*(q.2+q.1)^(-(3/2:ℝ))*Real.exp (-q.1)*
    Real.exp (-(q.2*q.1/(q.2+q.1))*R)

theorem parameterKernel_measurable (a R : ℝ) :
    AEStronglyMeasurable (parameterKernel a R)
      (positiveTimeMeasure.prod positiveTimeMeasure) := by
  apply Measurable.aestronglyMeasurable
  unfold parameterKernel
  fun_prop

theorem parameterKernel_nonneg (a R : ℝ) {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    0 ≤ parameterKernel a R (s,r) := by
  unfold parameterKernel
  positivity

theorem parameterKernel_rescale (a R : ℝ) {s t : ℝ} (hs : 0<s) (ht : 0<t) :
    s*parameterKernel a R (s,s*t) = transformedParameter a R (t,s) := by
  have ht1 : 0 < 1+t := by linarith
  have hsum : s*t+s = s*(1+t) := by ring
  have hfrac : s*t*s/(s*t+s) = s*(t/(1+t)) := by
    rw [hsum]
    field_simp
  have hp : s*s^(a-1)*s^(2-a)*s^(-(3/2:ℝ)) = s^(1/2:ℝ) := by
    calc
      _ = s^((1+(a-1)+(2-a)) + -(3/2:ℝ)) := by
        rw [Real.rpow_add hs, Real.rpow_add hs, Real.rpow_add hs, Real.rpow_one]
      _ = _ := by congr 1; ring
  have he : Real.exp (-s)*Real.exp (-(s*(t/(1+t)))*R) =
      Real.exp (-((1+(t/(1+t))*R)*s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold parameterKernel transformedParameter
  dsimp only
  rw [hfrac, hsum, Real.mul_rpow hs.le ht.le, Real.mul_rpow hs.le ht1.le]
  calc
    _ = (s*s^(a-1)*s^(2-a)*s^(-(3/2:ℝ)))*
        (t^(a-1)*(1+t)^(-(3/2:ℝ)))*
        (Real.exp (-s)*Real.exp (-(s*(t/(1+t)))*R)) := by ring
    _ = _ := by rw [hp, he]; ring

theorem parameterKernel_inner_integral (a R : ℝ) {s : ℝ} (hs : 0<s) :
    (∫ r, parameterKernel a R (s,r) ∂positiveTimeMeasure) =
      ∫ t, transformedParameter a R (t,s) ∂positiveTimeMeasure := by
  calc
    _ = s*(∫ t, parameterKernel a R (s,s*t) ∂positiveTimeMeasure) := by
      symm
      simpa only [mul_zero, smul_eq_mul] using
        integral_comp_mul_left_Ioi' (fun r => parameterKernel a R (s,r)) 0 hs
    _ = ∫ t, s*parameterKernel a R (s,s*t) ∂positiveTimeMeasure :=
      (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact parameterKernel_rescale a R hs ht

theorem parameterKernel_inner_norm_integral (a R : ℝ) {s : ℝ} (hs : 0<s) :
    (∫ r, ‖parameterKernel a R (s,r)‖ ∂positiveTimeMeasure) =
      ∫ t, ‖transformedParameter a R (t,s)‖ ∂positiveTimeMeasure := by
  calc
    _ = s*(∫ t, ‖parameterKernel a R (s,s*t)‖ ∂positiveTimeMeasure) := by
      symm
      simpa only [mul_zero, smul_eq_mul] using
        integral_comp_mul_left_Ioi' (fun r => ‖parameterKernel a R (s,r)‖) 0 hs
    _ = ∫ t, s*‖parameterKernel a R (s,s*t)‖ ∂positiveTimeMeasure :=
      (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← parameterKernel_rescale a R hs ht, norm_mul, Real.norm_of_nonneg hs.le]

theorem parameterKernel_inner_integrable (a R : ℝ) {s : ℝ} (hs : 0<s)
    (h : Integrable (fun t => transformedParameter a R (t,s)) positiveTimeMeasure) :
    Integrable (fun r => parameterKernel a R (s,r)) positiveTimeMeasure := by
  have hm : Integrable (fun t => s*parameterKernel a R (s,s*t)) positiveTimeMeasure := by
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (parameterKernel_rescale a R hs ht).symm
  have hc : Integrable (fun t => parameterKernel a R (s,s*t)) positiveTimeMeasure := by
    exact (integrable_fun_smul_iff hs.ne' _).mp hm
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
    (fun r => parameterKernel a R (s,r)) 0 hs).mp hc
  simpa only [mul_zero, IntegrableOn, positiveTimeMeasure] using hscale

/-- Genuine L1 integrability in both original Gaussian parameters. -/
theorem parameterKernel_integrable {a R : ℝ} (ha : 0<a) (ha3 : a<3/2) (hR : 0≤R) :
    Integrable (parameterKernel a R) (positiveTimeMeasure.prod positiveTimeMeasure) := by
  have h := transformedParameter_integrable ha ha3 hR
  apply (integrable_prod_iff (parameterKernel_measurable a R)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi, h.prod_left_ae] with s hs hslice
    exact parameterKernel_inner_integrable a R hs hslice
  · apply h.integral_norm_prod_right.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (parameterKernel_inner_norm_integral a R hs).symm

/-- The original positive Gaussian parameter integral, with its L1 domain proved above. -/
theorem parameterKernel_integral {a R : ℝ} (ha : 0<a) (ha3 : a<3/2) (hR : 0≤R) :
    (∫ q, parameterKernel a R q ∂positiveTimeMeasure.prod positiveTimeMeasure) =
      (1+R)^(-a)*Real.Gamma a*Real.Gamma (3/2-a) := by
  rw [integral_prod _ (parameterKernel_integrable ha ha3 hR)]
  calc
    _ = ∫ s, ∫ t, transformedParameter a R (t,s)
        ∂positiveTimeMeasure ∂positiveTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact parameterKernel_inner_integral a R hs
    _ = ∫ q, transformedParameter a R q ∂positiveTimeMeasure.prod positiveTimeMeasure := by
      exact (integral_prod_symm _ (transformedParameter_integrable ha ha3 hR)).symm
    _ = _ := transformedParameter_integral ha ha3 hR

#print axioms parameterKernel_measurable
#print axioms parameterKernel_nonneg
#print axioms parameterKernel_rescale
#print axioms parameterKernel_inner_integral
#print axioms parameterKernel_inner_norm_integral
#print axioms parameterKernel_inner_integrable
#print axioms parameterKernel_integrable
#print axioms parameterKernel_integral
end HartreeF.BubbleProfile
