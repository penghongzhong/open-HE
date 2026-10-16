import FRieszGradientConvolutionDomain
import FRieszTranslatedKernelTests

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace HartreeF.RieszConvolutionDerivative
open ForcingDomain RieszWeakDerivative RieszKernelDerivative SobolevStretch GradientMajorants

theorem gradientConvolution_inner {α c : ℝ} {f : Space → ℝ} {x : Space}
    (hx : Integrable (fun y => f y • rieszKernelGradient α c (x-y)) volume) (v : Space) :
    ⟪gradientConvolution α c f x,v⟫ =
      ∫ y, f y * ⟪rieszKernelGradient α c (x-y),v⟫ := by
  rw [real_inner_comm, gradientConvolution, ← integral_inner hx v]
  simp only [inner_smul_right, real_inner_comm v]

/-- Genuine kernel differentiation of an arbitrary real Lp density. -/
theorem rieszConvolution_hasWeakGradient {α c c' s : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α-1) c')
    (hs : α/3 < s) (hs1 : s < 1) {f : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (1/s)) volume) :
    HasWeakGradient (rieszConvolution α c f) (gradientConvolution α c f) := by
  have hα1 : 1 < α := by linarith [hL.order_pos]
  have hsL : (α-1)/3 < s := by linarith
  obtain ⟨hp,hpα,hq,hrel⟩ := reciprocal_hls_range hH.order_pos hs hs1
  obtain ⟨_,hpL,hqL,hrelL⟩ := reciprocal_hls_range hL.order_pos hsL hs1
  obtain ⟨C,hC⟩ := hH.strong_bound _ _ hp hpα hq hrel
  obtain ⟨D,hD⟩ := gradientConvolution_bound hH.order_lt_three hH.normalization_pos hL
    hp hpL hqL hrelL
  have hTf := (hC f hf).2.1
  have hG := (hD f hf).2.1
  have haq1 : 1 ≤ ENNReal.ofReal (1/(s-α/3)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ (sub_pos.mpr hs)).mpr (by linarith [hH.order_pos])
  have hbq1 : 1 ≤ ENNReal.ofReal (1/(s-(α-1)/3)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ (sub_pos.mpr hsL)).mpr (by linarith [hL.order_pos])
  refine ⟨hTf.locallyIntegrable haq1, hG.locallyIntegrable hbq1, ?_⟩
  intro v φ hφ hc
  let : ENNReal.HolderTriple (ENNReal.ofReal (1/(s-α/3)))
      (ENNReal.ofReal (1/(1-s+α/3))) 1 :=
    riesz_output_test_holder hH.order_pos hs hs1
  let : ENNReal.HolderTriple (ENNReal.ofReal (1/(s-(α-1)/3)))
      (ENNReal.ofReal (1/(1-s+(α-1)/3))) 1 :=
    riesz_output_test_holder hL.order_pos hsL hs1
  have hφD : MemLp (fun x => fderiv ℝ φ x v)
      (ENNReal.ofReal (1/(1-s+α/3))) volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hφL : MemLp φ (ENNReal.ofReal (1/(1-s+(α-1)/3))) volume :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have hleft := rieszTestPair_integrable hH hp hpα hq hrel hf hφD
  have hright := gradientTestPair_integrable hH.order_lt_three hH.normalization_pos hL
    hp hpL hqL hrelL hf hφL v
  calc
    _ = ∫ x, ∫ y, rieszTestPair α c f (fun z => fderiv ℝ φ z v) (x,y) := by
      unfold rieszTestPair rieszConvolution
      simp only [integral_mul_const]
    _ = ∫ y, ∫ x, rieszTestPair α c f (fun z => fderiv ℝ φ z v) (x,y) :=
      integral_integral_swap hleft
    _ = -(∫ y, ∫ x, gradientTestPair α c f φ v (x,y)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [rieszTestPair, gradientTestPair]
      calc
        _ = f y * (∫ x, rieszKernel α c (x-y) * fderiv ℝ φ x v) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        _ = _ := by
          rw [translated_kernel_integration_by_parts hα1 hH.order_lt_three
            hH.normalization_pos hφ hc y v, mul_neg, ← integral_const_mul]
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    _ = -(∫ x, ∫ y, gradientTestPair α c f φ v (x,y)) := by
      congr 1
      exact (integral_integral_swap (f := fun (x y : Space) =>
        gradientTestPair α c f φ v (x,y)) hright).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(hD f hf).1] with x hx
      simp only [gradientTestPair, integral_mul_const]
      rw [gradientConvolution_inner hx v]

#print axioms rieszConvolution_hasWeakGradient
end HartreeF.RieszConvolutionDerivative
