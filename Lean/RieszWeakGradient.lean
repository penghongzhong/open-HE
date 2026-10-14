import RieszVectorDomain
import NoncompactWeakTests

/-! Actual weak differentiation of the Riesz convolution. The proof uses
compact-test convolution calculus, real absolute Fubini domains, HLS dual tests,
and the proved noncompact weak-test extension. No derivative of the singular
kernel and no convolution-commutation interface is assumed. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.RieszWeakDerivative
open ForcingDomain GradientMajorants SobolevStretch

theorem riesz_hasWeakGradient {α c a b : ℝ} (hH : OrdinaryHLS α c)
    (ha : α/3 < a) (ha1 : a < 1) (hb : α/3 < b) (hb1 : b < 1)
    {f : Space → ℝ} {G : Space → Space} (hw : HasWeakGradient f G)
    (hf : MemLp f (ENNReal.ofReal (1/a)) volume)
    (hG : MemLp G (ENNReal.ofReal (1/b)) volume) :
    HasWeakGradient (rieszConvolution α c f) (rieszVectorConvolution α c G) := by
  have hα := hH.order_pos
  have ha0 : 0 < a := lt_trans (by positivity : 0 < α/3) ha
  have hb0 : 0 < b := lt_trans (by positivity : 0 < α/3) hb
  obtain ⟨hap,hapα,haq,harel⟩ := reciprocal_hls_range hH.order_pos ha ha1
  obtain ⟨hbp,hbpα,hbq,hbrel⟩ := reciprocal_hls_range hH.order_pos hb hb1
  obtain ⟨C,hC⟩ := hH.strong_bound _ _ hap hapα haq harel
  have hTf := (hC f hf).2.1
  have hTG := (rieszVectorConvolution_domain hH hb hb1 hG).2
  have haq1 : 1 ≤ ENNReal.ofReal (1/(a-α/3)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ (sub_pos.mpr ha)).mpr (by linarith [hH.order_pos])
  have hbq1 : 1 ≤ ENNReal.ofReal (1/(b-α/3)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ (sub_pos.mpr hb)).mpr (by linarith [hH.order_pos])
  refine ⟨hTf.locallyIntegrable haq1,hTG.locallyIntegrable hbq1,?_⟩
  intro v φ hφ hc
  let : ENNReal.HolderTriple (ENNReal.ofReal (1/a)) (ENNReal.ofReal (1/(1-a))) 1 := reciprocal_holder ha0 ha1
  let : ENNReal.HolderTriple (ENNReal.ofReal (1/b)) (ENNReal.ofReal (1/(1-b))) 1 := reciprocal_holder hb0 hb1
  let : ENNReal.HolderTriple (ENNReal.ofReal (1/(a-α/3)))
    (ENNReal.ofReal (1/(1-a+α/3))) 1 := riesz_output_test_holder hH.order_pos ha ha1
  let : ENNReal.HolderTriple (ENNReal.ofReal (1/(b-α/3)))
    (ENNReal.ofReal (1/(1-b+α/3))) 1 := riesz_output_test_holder hH.order_pos hb hb1
  have hGv : MemLp (fun x => ⟪G x,v⟫) (ENNReal.ofReal (1/b)) volume := by
    simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using (innerSL ℝ v).comp_memLp' hG
  have hψa := riesz_compact_dual_memLp hH ha ha1 hφ.continuous hc
  have hψb := riesz_compact_dual_memLp hH hb hb1 hφ.continuous hc
  have hdψa := riesz_test_dual_derivative_memLp hH ha ha1 hφ hc v
  have hweak := weak_gradient_noncompact_test hw (riesz_test_contDiff hH.order_pos hφ hc) v
    (hf.integrable_mul hψa) (hf.integrable_mul hdψa) (hGv.integrable_mul hψb)
  have hleft := riesz_test_transpose hH hap hapα haq harel hf
    (show MemLp (fun x => fderiv ℝ φ x v) (ENNReal.ofReal (1/(1-a+α/3))) volume from
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ v))
  have hright := riesz_test_transpose hH hbp hbpα hbq hbrel hGv
    (show MemLp φ (ENNReal.ofReal (1/(1-b+α/3))) volume from hφ.continuous.memLp_of_hasCompactSupport hc)
  calc
    _ = ∫ x, f x*rieszConvolution α c (fun y => fderiv ℝ φ y v) x := hleft
    _ = ∫ x, f x*fderiv ℝ (rieszConvolution α c φ) x v := by
      simp_rw [riesz_test_fderiv hH.order_pos hφ hc]
    _ = -(∫ x, ⟪G x,v⟫*rieszConvolution α c φ x) := hweak
    _ = -(∫ x, rieszConvolution α c (fun y => ⟪G y,v⟫) x*φ x) := by rw [hright]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [rieszVectorConvolution_inner hH hb hb1 hG v] with x hx
      rw [hx]

#print axioms riesz_hasWeakGradient
end HartreeF.RieszWeakDerivative
