import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
A genuine reciprocal-Gamma integral on (0,infinity), including its absolute
integrability. The reciprocal substitution uses Mathlib's proved one-variable
Jacobian theorem through the rpow substitution p=-1. No heat/Riesz identity is
assumed, and no conclusion is asserted at a zero spatial parameter A.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace HartreeF.HeatRiesz

def reciprocalGammaIntegrand (γ A t : ℝ) : ℝ := t^(-γ-1) * Real.exp (-A/t)

theorem gammaRate_integrable {γ A : ℝ} (hγ : 0 < γ) (hA : 0 < A) :
    IntegrableOn (fun t : ℝ => t^(γ-1) * Real.exp (-(A*t))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (show -1 < γ-1 by linarith)
      (by norm_num : (0:ℝ)<1) hA

theorem reciprocalGamma_change_integrand (γ A : ℝ) {t : ℝ} (ht : 0 < t) :
    (|(-1:ℝ)| * t^((-1:ℝ)-1)) •
      ((t^(-1:ℝ))^(γ-1) * Real.exp (-(A*t^(-1:ℝ)))) =
      reciprocalGammaIntegrand γ A t := by
  norm_num only [abs_neg, abs_one, one_mul]
  rw [smul_eq_mul, ← Real.rpow_mul ht.le, ← mul_assoc, ← Real.rpow_add ht]
  unfold reciprocalGammaIntegrand
  rw [Real.rpow_neg_one, div_eq_mul_inv]
  congr 2 <;> ring

theorem reciprocalGamma_integrable {γ A : ℝ} (hγ : 0 < γ) (hA : 0 < A) :
    IntegrableOn (reciprocalGammaIntegrand γ A) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun t : ℝ => t^(γ-1) * Real.exp (-(A*t))) (p := -1) (by norm_num)).2
      (gammaRate_integrable hγ hA)
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  exact reciprocalGamma_change_integrand γ A ht

theorem reciprocalGamma_integral {γ A : ℝ} (hγ : 0 < γ) (hA : 0 < A) :
    (∫ t in Ioi 0, reciprocalGammaIntegrand γ A t) = A^(-γ) * Real.Gamma γ := by
  have h := integral_comp_rpow_Ioi
    (fun t : ℝ => t^(γ-1) * Real.exp (-(A*t))) (p := -1) (by norm_num)
  calc
    _ = ∫ t in Ioi 0, (|(-1:ℝ)| * t^((-1:ℝ)-1)) •
        ((t^(-1:ℝ))^(γ-1) * Real.exp (-(A*t^(-1:ℝ)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (reciprocalGamma_change_integrand γ A ht).symm
    _ = ∫ t in Ioi 0, t^(γ-1) * Real.exp (-(A*t)) := h
    _ = (1/A)^γ * Real.Gamma γ := Real.integral_rpow_mul_exp_neg_mul_Ioi hγ hA
    _ = _ := by rw [one_div, ← Real.rpow_neg_eq_inv_rpow]

#print axioms gammaRate_integrable
#print axioms reciprocalGamma_change_integrand
#print axioms reciprocalGamma_integrable
#print axioms reciprocalGamma_integral
end HartreeF.HeatRiesz
