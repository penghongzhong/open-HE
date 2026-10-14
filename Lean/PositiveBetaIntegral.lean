import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The positive half-line Beta integral, including its actual integrability. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Real

namespace HartreeF.BubbleProfile

def betaRateIntegrand (a b A t : ℝ) : ℝ :=
  t ^ (a - 1) * (1 + A * t) ^ (-(a + b))

def unitBeta (a b x : ℝ) : ℝ := x ^ (a - 1) * (1 - x) ^ (b - 1)

theorem unitBeta_cast (a b : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (unitBeta a b x : ℂ) = (x : ℂ) ^ ((a : ℂ) - 1) *
      (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by
  unfold unitBeta
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem unitBeta_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (unitBeta a b) (Ioo 0 1) := by
  have hc := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hc
  apply (integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioo).mp h.re
  exact congrArg Complex.re (unitBeta_cast a b hx).symm

theorem unitBeta_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioo (0 : ℝ) 1, unitBeta a b x = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = ∫ x in Ioo (0 : ℝ) 1,
        (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1) :=
      setIntegral_congr_fun measurableSet_Ioo (fun x hx => unitBeta_cast a b hx)
    _ = Complex.betaIntegral (a : ℂ) (b : ℂ) := by
      rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
      push_cast
      rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        Complex.Gamma_ofReal]

theorem betaChange_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t / (1 + t)) ((1 + x) ^ 2)⁻¹ x := by
  convert (hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1) (by linarith : 1 + x ≠ 0) using 1
  · ext t
    simp [add_comm]
  · simp

theorem betaChange_inj : InjOn (fun t : ℝ => t / (1 + t)) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have h := (div_eq_div_iff (by linarith : 1 + x ≠ 0) (by linarith : 1 + y ≠ 0)).mp hxy
  nlinarith

theorem betaChange_image : (fun t : ℝ => t / (1 + t)) '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : 0 < 1 + t := by linarith [mem_Ioi.mp ht]
    exact ⟨div_pos ht ht', (div_lt_one ht').mpr (by linarith)⟩
  · intro hx
    refine ⟨x / (1 - x), div_pos hx.1 (sub_pos.mpr hx.2), ?_⟩
    have h : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
    field_simp
    nlinarith

theorem betaChange_integrand (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    |((1 + x) ^ 2)⁻¹| • unitBeta a b (x / (1 + x)) = betaRateIntegrand a b 1 x := by
  have hp : 0 < 1 + x := by linarith
  have hs : 1 - x / (1 + x) = 1 / (1 + x) := by field_simp; ring
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), smul_eq_mul, unitBeta, hs,
    Real.div_rpow hx.le hp.le, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hp.le,
    Real.one_rpow, betaRateIntegrand, one_mul]
  calc
    _ = x ^ (a - 1) * ((1 + x) ^ (-2 : ℝ) *
        ((1 + x) ^ (-(a - 1)) * (1 + x) ^ (-(b - 1)))) := by
      simp only [Real.rpow_neg hp.le, Real.rpow_two, div_eq_mul_inv]
      ring
    _ = x ^ (a - 1) * (1 + x) ^ (-(a + b)) := by
      rw [← Real.rpow_add hp, ← Real.rpow_add hp]
      congr 2
      ring

theorem betaOne_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaRateIntegrand a b 1) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (betaChange_deriv hx).hasDerivWithinAt) betaChange_inj (unitBeta a b)
  rw [betaChange_image] at h
  exact (integrableOn_congr_fun (fun x hx => betaChange_integrand a b hx) measurableSet_Ioi).mp
    (h.mp (unitBeta_integrable ha hb))

theorem betaOne_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), betaRateIntegrand a b 1 x =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (betaChange_deriv hx).hasDerivWithinAt) betaChange_inj (unitBeta a b)
  rw [betaChange_image] at h
  calc
    _ = ∫ x in Ioi (0 : ℝ), |((1 + x) ^ 2)⁻¹| • unitBeta a b (x / (1 + x)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => (betaChange_integrand a b hx).symm)
    _ = ∫ x in Ioo (0 : ℝ) 1, unitBeta a b x := h.symm
    _ = _ := unitBeta_integral ha hb

theorem betaRate_scale (a b : ℝ) {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    betaRateIntegrand a b A t = A ^ (1 - a) * betaRateIntegrand a b 1 (A * t) := by
  unfold betaRateIntegrand
  rw [one_mul, Real.mul_rpow hA.le ht.le]
  symm
  calc
    _ = (A ^ (1 - a) * A ^ (a - 1)) *
        (t ^ (a - 1) * (1 + A * t) ^ (-(a + b))) := by ring
    _ = _ := by rw [← Real.rpow_add hA]; simp

/-- Genuine integrability of the positive-rate Beta density on the positive half-line. -/
theorem betaRate_integrable {a b A : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) :
    IntegrableOn (betaRateIntegrand a b A) (Ioi 0) := by
  have h : IntegrableOn (fun t => betaRateIntegrand a b 1 (A * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (betaRateIntegrand a b 1) 0 hA).mpr
    simpa only [mul_zero] using betaOne_integrable ha hb
  exact (integrableOn_congr_fun (fun t ht => betaRate_scale a b hA ht)
    measurableSet_Ioi).mpr (h.const_mul (A ^ (1 - a)))

/-- Evaluation of the positive-rate Beta integral by the native Beta/Gamma relation. -/
theorem betaRate_integral {a b A : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) :
    ∫ t in Ioi (0 : ℝ), betaRateIntegrand a b A t =
      A ^ (-a) * Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), A ^ (1 - a) * betaRateIntegrand a b 1 (A * t) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => betaRate_scale a b hA ht)
    _ = A ^ (1 - a) * (A⁻¹ *
        (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 hA, mul_zero,
        smul_eq_mul, betaOne_integral ha hb]
    _ = _ := by
      have h : A ^ (1 - a) * A⁻¹ = A ^ (-a) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hA]
        congr 1
        ring
      rw [← mul_assoc, h]
      ring

#print axioms unitBeta_cast
#print axioms unitBeta_integrable
#print axioms unitBeta_integral
#print axioms betaChange_deriv
#print axioms betaChange_inj
#print axioms betaChange_image
#print axioms betaChange_integrand
#print axioms betaOne_integrable
#print axioms betaOne_integral
#print axioms betaRate_scale
#print axioms betaRate_integrable
#print axioms betaRate_integral

end HartreeF.BubbleProfile
