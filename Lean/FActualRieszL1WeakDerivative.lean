import FRieszL1TestIntegrability
import FRieszL1CutoffDomains
import WeakSmoothProduct
import FRieszConvolutionWeakDerivative

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.RieszL1LocalDomains
open ForcingDomain RieszWeakDerivative RieszKernelDerivative RieszConvolutionDerivative
open SobolevStretch

/-- One full-measure set for the two genuine convolution sections of the same L1 density. -/
theorem actual_riesz_sections_L1 {α c : ℝ} {h : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => h y * rieszKernel α c (x-y)) volume ∧
      Integrable (fun y => h y • rieszKernelGradient α c (x-y)) volume := by
  have hP := near_far_convolution_ae hh (rieszKernel_measurable α c).aestronglyMeasurable
    (near_rieszKernel_integrable (by linarith : 0<α)) (far_rieszKernel_norm_le hα3 hc)
  have hG := near_far_convolution_ae hh (rieszKernelGradient_measurable α c).aestronglyMeasurable
    (near_rieszKernelGradient_integrable hα1 hα3 hc) (far_rieszKernelGradient_norm_le hα3 hc)
  filter_upwards [hP,hG] with x hxP hxG
  exact ⟨hxP.2.2.1,hxG.2.2.1⟩

/-- The actual potential and the literal gradient integral are locally integrable.
This uses actual L1 data and the proved near/far kernel split only. -/
theorem actual_riesz_locallyIntegrable_L1 {α c : ℝ} {h : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume) :
    LocallyIntegrable (rieszConvolution α c h) volume ∧
      LocallyIntegrable (gradientConvolution α c h) volume := by
  constructor
  · rw [rieszConvolution_eq_actualConvolution]
    exact near_far_convolution_locallyIntegrable hh
      (rieszKernel_measurable α c).aestronglyMeasurable
      (near_rieszKernel_integrable (by linarith : 0<α)) (far_rieszKernel_norm_le hα3 hc)
  · exact near_far_convolution_locallyIntegrable hh
      (rieszKernelGradient_measurable α c).aestronglyMeasurable
      (near_rieszKernelGradient_integrable hα1 hα3 hc) (far_rieszKernelGradient_norm_le hα3 hc)

/-- Genuine differentiation of the same Riesz convolution for arbitrary actual real L1 data.
No HLS premise at the original or shifted order occurs. -/
theorem actual_riesz_hasWeakGradient_L1 {α c : ℝ} {h : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume) :
    HasWeakGradient (rieszConvolution α c h) (gradientConvolution α c h) := by
  obtain ⟨hp,hg⟩ := actual_riesz_locallyIntegrable_L1 hα1 hα3 hc hh
  refine ⟨hp,hg,?_⟩
  intro v φ hφ hφc
  have hDcont := (hφ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  have hleft := rieszTestPair_integrable_L1 (by linarith : 0<α) hα3 hc hh
    hDcont (hφc.fderiv_apply ℝ v)
  have hright := gradientTestPair_integrable_L1 hα1 hα3 hc hh hφ.continuous hφc v
  calc
    _ = ∫ x, ∫ y, rieszTestPair α c h (fun z => fderiv ℝ φ z v) (x,y) := by
      unfold rieszTestPair rieszConvolution
      simp only [integral_mul_const]
    _ = ∫ y, ∫ x, rieszTestPair α c h (fun z => fderiv ℝ φ z v) (x,y) :=
      integral_integral_swap hleft
    _ = -(∫ y, ∫ x, gradientTestPair α c h φ v (x,y)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [rieszTestPair, gradientTestPair]
      calc
        _ = h y * (∫ x, rieszKernel α c (x-y) * fderiv ℝ φ x v) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        _ = _ := by
          rw [translated_kernel_integration_by_parts hα1 hα3 hc hφ hφc y v,
            mul_neg, ← integral_const_mul]
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    _ = -(∫ x, ∫ y, gradientTestPair α c h φ v (x,y)) := by
      congr 1
      exact (integral_integral_swap (f := fun (x y : Space) =>
        gradientTestPair α c h φ v (x,y)) hright).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [actual_riesz_sections_L1 hα1 hα3 hc hh] with x hx
      simp only [gradientTestPair, integral_mul_const]
      rw [gradientConvolution_inner hx.2 v]

/-- Complete local weak-Sobolev producer, including the endpoint α=2.
Both local Lp statements and the weak derivative refer to the same literal integrals. -/
theorem actual_riesz_L1_local_weak_domains {α c : ℝ} {h : Space → ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (s : Set Space) (hμs : volume s < ∞) :
    HasWeakGradient (rieszConvolution α c h) (gradientConvolution α c h) ∧
      MemLp (rieszConvolution α c h) 2 (volume.restrict s) ∧
      MemLp (gradientConvolution α c h) (ENNReal.ofReal (6/5:ℝ)) (volume.restrict s) :=
  ⟨actual_riesz_hasWeakGradient_L1 (by linarith) hα3 hc hh,
    actual_riesz_local_domains hα2 hα3 hc hh s hμs⟩

/-- Same actual compact-cutoff potential: the candidate gradient is now proved to be
its weak derivative and has the exact domains needed by asymmetric weak Leibniz. -/
theorem actual_riesz_cutoff_weak_domains {α c : ℝ} {h χ : Space → ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    HasWeakGradient (fun x => χ x * rieszConvolution α c h x)
      (fun x => χ x • gradientConvolution α c h x + rieszConvolution α c h x • gradient χ x) ∧
    MemLp (fun x => χ x * rieszConvolution α c h x) 2 volume ∧
    MemLp (fun x => χ x • gradientConvolution α c h x + rieszConvolution α c h x • gradient χ x)
      (ENNReal.ofReal (6/5:ℝ)) volume :=
  ⟨(actual_riesz_hasWeakGradient_L1 (by linarith) hα3 hc hh).mul_smooth hχ,
    actual_riesz_cutoff_domains hα2 hα3 hc hh hχ hχc⟩

end HartreeF.RieszL1LocalDomains
