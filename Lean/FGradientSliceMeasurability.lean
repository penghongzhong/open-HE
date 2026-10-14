import FCoordinateGradientPack
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

theorem pack_slice_norm_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu]
    (F G : Fin 3 → T → Space → ℂ)
    (hG : ∀ i, AEStronglyMeasurable (fun z : T × Space => G i z.1 z.2) (mu.prod volume))
    (heq : ∀ i, ∀ᵐ t ∂mu, F i t =ᵐ[volume] G i t) :
    AEStronglyMeasurable (fun t => eLpNorm
      (fun x => packGradient (F 0 t x) (F 1 t x) (F 2 t x))
      (ENNReal.ofReal (6/5 : ℝ)) volume) mu := by
  have hg := ((hG 0).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 0)).add
    ((hG 1).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 1))
  have hg3 := hg.add ((hG 2).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 2))
  have hm := spatial_lp_time_measurable mu volume (ENNReal.ofReal (6/5 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top
    (fun t x => packGradient (G 0 t x) (G 1 t x) (G 2 t x)) hg3
  apply hm.congr
  filter_upwards [heq 0, heq 1, heq 2] with t h0 h1 h2
  apply eLpNorm_congr_ae
  filter_upwards [h0, h1, h2] with x h0x h1x h2x
  simp only [h0x, h1x, h2x]

end HartreeF.TimeHolder
