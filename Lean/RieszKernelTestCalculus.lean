import HartreeDensitySplitDomain
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Genuine convolution calculus against compact smooth tests for the locally
integrable Riesz kernel. Derivatives act on the test, never on the singular kernel. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Convolution
namespace HartreeF.RieszWeakDerivative
open ForcingDomain

theorem rieszKernel_measurable (α c : ℝ) : Measurable (rieszKernel α c) :=
  measurable_const.mul (continuous_norm.measurable.pow_const (α-3))

theorem rieszKernel_locallyIntegrable {α : ℝ} (hα : 0 < α) (c : ℝ) :
    LocallyIntegrable (rieszKernel α c) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := |c|) (α := 3-α)
    (by simp [Space]) (by simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat]; linarith)
  · filter_upwards [] with x
    simp only [rieszKernel,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [show -(3-α) = α-3 by ring]
  · exact (rieszKernel_measurable α c).aestronglyMeasurable

theorem rieszConvolution_eq_mathlib (α c : ℝ) (f : Space → ℝ) :
    rieszConvolution α c f = (rieszKernel α c ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] f) := by
  funext x
  rw [MeasureTheory.convolution_eq_swap]
  rfl

theorem riesz_test_contDiff {α c : ℝ} (hα : 0 < α) {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszConvolution α c φ) := by
  rw [rieszConvolution_eq_mathlib]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (rieszKernel_locallyIntegrable hα c) hφ

theorem riesz_test_fderiv {α c : ℝ} (hα : 0 < α) {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (x v : Space) :
    fderiv ℝ (rieszConvolution α c φ) x v =
      rieszConvolution α c (fun y => fderiv ℝ φ y v) x := by
  rw [rieszConvolution_eq_mathlib,rieszConvolution_eq_mathlib]
  have hc1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (rieszKernel_locallyIntegrable hα c) hc1 x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    (rieszKernel_locallyIntegrable hα c) (hc.fderiv ℝ)
      (hc1.continuous_fderiv (by simp)) x v

#print axioms rieszKernel_measurable
#print axioms rieszKernel_locallyIntegrable
#print axioms rieszConvolution_eq_mathlib
#print axioms riesz_test_contDiff
#print axioms riesz_test_fderiv
end HartreeF.RieszWeakDerivative
