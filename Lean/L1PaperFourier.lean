import Gaussian_4_2_Fourier
import HartreePhase
import Mathlib.MeasureTheory.Integral.Prod

/-!
The genuine absolutely convergent paper-frequency Fourier integral on real L1
data. The convention is exp(-i xi dot x), with no silently inserted 2*pi.
No L2/Plancherel or Riesz energy identity is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace HartreeF.GaussianFourierBridge
open BWork.Gaussian

def fourierPhase (ξ x : Space) : ℂ := Complex.exp (-Complex.I * (⟪ξ,x⟫ : ℂ))

theorem fourierPhase_continuous :
    Continuous (fun q : Space × Space => fourierPhase q.1 q.2) := by
  unfold fourierPhase
  fun_prop

@[simp] theorem norm_fourierPhase (ξ x : Space) : ‖fourierPhase ξ x‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp]

theorem fourierPhase_neg (ξ x : Space) : fourierPhase (-ξ) x = conj (fourierPhase ξ x) := by
  simp only [fourierPhase, inner_neg_left, Complex.ofReal_neg, ← Complex.exp_conj,
    map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  ring

theorem fourierPhase_sub (ξ x y : Space) :
    fourierPhase ξ (x-y) = fourierPhase ξ x * fourierPhase (-ξ) y := by
  unfold fourierPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_right, inner_neg_left]
  push_cast
  ring

theorem fourierPhase_symm (ξ x : Space) : fourierPhase ξ x = fourierPhase x ξ := by
  simp only [fourierPhase, real_inner_comm ξ x]

theorem paperFourier_integrable {f : Space → ℝ} (hf : Integrable f volume) (ξ : Space) :
    Integrable (fun x => fourierPhase ξ x * (f x : ℂ)) volume := by
  have hm : AEStronglyMeasurable (fun x : Space => fourierPhase ξ x) volume :=
    (fourierPhase_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply hf.norm.mono' (hm.mul hf.ofReal.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖fourierPhase ξ x * (f x : ℂ)‖ ≤ ‖f x‖
  simp only [norm_mul, norm_fourierPhase, one_mul, Complex.norm_real, le_refl]

theorem paperFourier_neg (f : Space → ℝ) (ξ : Space) :
    paperFourier f (-ξ) = conj (paperFourier f ξ) := by
  unfold paperFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  change fourierPhase (-ξ) x * (f x : ℂ) = conj (fourierPhase ξ x * (f x : ℂ))
  rw [fourierPhase_neg, map_mul, Complex.conj_ofReal]

theorem paperFourier_norm_le {f : Space → ℝ} (hf : Integrable f volume) (ξ : Space) :
    ‖paperFourier f ξ‖ ≤ ∫ x, ‖f x‖ := by
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards [] with x
  change ‖fourierPhase ξ x * (f x : ℂ)‖ ≤ ‖f x‖
  simp only [norm_mul, norm_fourierPhase, one_mul, Complex.norm_real, le_refl]

theorem paperFourier_aestronglyMeasurable {f : Space → ℝ} (hf : Integrable f volume) :
    AEStronglyMeasurable (paperFourier f) volume := by
  have hm : AEStronglyMeasurable (fun q : Space × Space =>
      fourierPhase q.1 q.2 * (f q.2 : ℂ)) (volume.prod volume) :=
    fourierPhase_continuous.aestronglyMeasurable.mul hf.ofReal.aestronglyMeasurable.comp_snd
  exact hm.integral_prod_right'

theorem gaussianRate_continuous (t : ℝ) : Continuous (gaussianRate t : Space → ℝ) := by
  unfold gaussianRate
  fun_prop

theorem gaussianRate_nonneg (t : ℝ) (x : Space) : 0 ≤ gaussianRate t x := (Real.exp_pos _).le

theorem gaussianRate_le_one {t : ℝ} (ht : 0 ≤ t) (x : Space) : gaussianRate t x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _)

theorem gaussianRate_real_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianRate t : Space → ℝ) volume := by
  have h : Integrable (fun x : Space => (gaussianRate t x : ℂ)) volume := by
    simpa only [inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using
      gaussianRate_fourier_integrable ht (0 : Space)
  exact h.re

/-- The actual Gaussian-weighted Fourier energy is finite for arbitrary real L1 data. -/
theorem gaussianFourierEnergy_integrable {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    Integrable (fun ξ => gaussianRate t ξ * ‖paperFourier f ξ‖^2) volume := by
  have hg := gaussianRate_real_integrable ht
  have hF := paperFourier_aestronglyMeasurable hf
  apply (hg.const_mul ((∫ x, ‖f x‖)^2)).mono'
    (hg.aestronglyMeasurable.mul (hF.norm.pow 2))
  filter_upwards [] with ξ
  change ‖gaussianRate t ξ * ‖paperFourier f ξ‖^2‖ ≤ (∫ x, ‖f x‖)^2 * gaussianRate t ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianRate_nonneg t ξ) (sq_nonneg _))]
  have h := paperFourier_norm_le hf ξ
  have ha := norm_nonneg (paperFourier f ξ)
  have hs : ‖paperFourier f ξ‖^2 ≤ (∫ x, ‖f x‖)^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hs (gaussianRate_nonneg t ξ)).trans_eq (by ring)

#print axioms fourierPhase_continuous
#print axioms norm_fourierPhase
#print axioms fourierPhase_neg
#print axioms fourierPhase_sub
#print axioms fourierPhase_symm
#print axioms paperFourier_integrable
#print axioms paperFourier_neg
#print axioms paperFourier_norm_le
#print axioms paperFourier_aestronglyMeasurable
#print axioms gaussianRate_continuous
#print axioms gaussianRate_nonneg
#print axioms gaussianRate_le_one
#print axioms gaussianRate_real_integrable
#print axioms gaussianFourierEnergy_integrable
end HartreeF.GaussianFourierBridge
