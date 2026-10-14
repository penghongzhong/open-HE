import DerivativeActionDifference
import HartreeMajorantPositivity

/-! Actual positive-kernel domination, with every Bochner integral domain
produced before integral subtraction or norm estimates. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.DerivativeMajorization
open ForcingDomain

theorem riesz_fibre_measurable (α c : ℝ) (x : Space) :
    Measurable (fun y => rieszKernel α c (x-y)) :=
  measurable_const.mul ((measurable_const.sub measurable_id).norm.pow_const _)

theorem riesz_kernel_nonneg {α c : ℝ} (hc : 0≤c) (z : Space) :
    0≤rieszKernel α c z := mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _)

theorem riesz_fibre_norm_domination {α c : ℝ} (hc : 0≤c) (x : Space)
    {f B : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (hB : Integrable (fun y => rieszKernel α c (x-y)*B y) volume)
    (hb : ∀ y, ‖f y‖ ≤ B y) :
    Integrable (fun y => rieszKernel α c (x-y)*f y) volume ∧
    ‖rieszConvolution α c f x‖ ≤ rieszConvolution α c B x := by
  have hm := (riesz_fibre_measurable α c x).aestronglyMeasurable.mul hf
  have hbound : ∀ᵐ y ∂volume, ‖rieszKernel α c (x-y)*f y‖ ≤ rieszKernel α c (x-y)*B y := by
    filter_upwards [] with y
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (riesz_kernel_nonneg hc _)]
    exact mul_le_mul_of_nonneg_left (hb y) (riesz_kernel_nonneg hc _)
  have hi := hB.mono' hm hbound
  refine ⟨hi,?_⟩
  exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hi.norm hB hbound)

theorem riesz_fibre_norm_const_domination {α c C : ℝ} (hc : 0≤c) (x : Space)
    {f B : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (hB : Integrable (fun y => rieszKernel α c (x-y)*B y) volume)
    (hb : ∀ y, ‖f y‖ ≤ C*B y) :
    Integrable (fun y => rieszKernel α c (x-y)*f y) volume ∧
    ‖rieszConvolution α c f x‖ ≤ C*rieszConvolution α c B x := by
  have hi : Integrable (fun y => rieszKernel α c (x-y)*(C*B y)) volume := by
    convert hB.const_mul C using 1
    funext y
    ring
  obtain ⟨hd,hbnd⟩ := riesz_fibre_norm_domination hc x hf hi hb
  refine ⟨hd,?_⟩
  have he : rieszConvolution α c (fun y => C*B y) x=C*rieszConvolution α c B x := by
    unfold rieszConvolution
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by ring)
  simpa only [he] using hbnd

theorem riesz_difference_norm_const_domination {α c C : ℝ} (hc : 0≤c) (x : Space)
    {f g B : Space → ℝ} (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hfi : Integrable (fun y => rieszKernel α c (x-y)*f y) volume)
    (hgi : Integrable (fun y => rieszKernel α c (x-y)*g y) volume)
    (hB : Integrable (fun y => rieszKernel α c (x-y)*B y) volume)
    (hb : ∀ y, ‖f y-g y‖ ≤ C*B y) :
    ‖rieszConvolution α c f x-rieszConvolution α c g x‖ ≤ C*rieszConvolution α c B x := by
  have h := (riesz_fibre_norm_const_domination hc x (hf.sub hg) hB hb).2
  have he : rieszConvolution α c (f-g) x=rieszConvolution α c f x-rieszConvolution α c g x := by
    unfold rieszConvolution
    simp only [Pi.sub_apply,mul_sub]
    exact integral_sub hfi hgi
  simpa only [he] using h

#print axioms riesz_fibre_measurable
#print axioms riesz_kernel_nonneg
#print axioms riesz_fibre_norm_domination
#print axioms riesz_fibre_norm_const_domination
#print axioms riesz_difference_norm_const_domination
end HartreeF.DerivativeMajorization
