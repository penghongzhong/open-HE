import RieszTestTransposition
import RieszTestDualDomains

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.RieszWeakDerivative
open ForcingDomain GradientMajorants

def rieszVectorConvolution (α c : ℝ) (G : Space → Space) (x : Space) : Space :=
  ∫ y, rieszKernel α c (x-y) • G y

theorem rieszVectorConvolution_aestronglyMeasurable {α c : ℝ} {G : Space → Space}
    (hG : AEStronglyMeasurable G volume) : AEStronglyMeasurable (rieszVectorConvolution α c G) volume := by
  have hk := (rieszKernel_measurable α c).comp (continuous_fst.sub continuous_snd).measurable
  exact (hk.aestronglyMeasurable.smul hG.comp_snd).integral_prod_right'

theorem rieszVectorConvolution_norm_le {α c : ℝ} (hc : 0 ≤ c) (G : Space → Space) (x : Space) :
    ‖rieszVectorConvolution α c G x‖ ≤ rieszConvolution α c (fun y => ‖G y‖) x := by
  calc
    _ ≤ ∫ y, ‖rieszKernel α c (x-y) • G y‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (rieszKernel_nonneg hc _)]

theorem rieszVectorConvolution_domain {α c s : ℝ} (hH : OrdinaryHLS α c)
    (hs : α/3 < s) (hs1 : s < 1) {G : Space → Space}
    (hG : MemLp G (ENNReal.ofReal (1/s)) volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) • G y) volume) ∧
    MemLp (rieszVectorConvolution α c G) (ENNReal.ofReal (1/(s-α/3))) volume := by
  obtain ⟨hp1,hpα,hq,hrel⟩ := reciprocal_hls_range hH.order_pos hs hs1
  obtain ⟨C,hC⟩ := hH.strong_bound _ _ hp1 hpα hq hrel
  have hd := hC (fun y => ‖G y‖) hG.norm
  constructor
  · filter_upwards [hd.1] with x hx
    apply hx.mono'
      (((rieszKernel_measurable α c).comp (continuous_const.sub continuous_id).measurable).aestronglyMeasurable.smul
        hG.aestronglyMeasurable)
    filter_upwards [] with y
    change ‖rieszKernel α c (x-y) • G y‖ ≤ rieszKernel α c (x-y)*‖G y‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (rieszKernel_nonneg hH.normalization_pos.le _)]
  · apply hd.2.1.of_le (rieszVectorConvolution_aestronglyMeasurable hG.aestronglyMeasurable)
    filter_upwards [] with x
    exact (rieszVectorConvolution_norm_le hH.normalization_pos.le G x).trans (le_abs_self _)

theorem rieszVectorConvolution_inner {α c s : ℝ} (hH : OrdinaryHLS α c)
    (hs : α/3 < s) (hs1 : s < 1) {G : Space → Space}
    (hG : MemLp G (ENNReal.ofReal (1/s)) volume) (v : Space) :
    (fun x => ⟪rieszVectorConvolution α c G x,v⟫) =ᵐ[volume]
      rieszConvolution α c (fun y => ⟪G y,v⟫) := by
  filter_upwards [(rieszVectorConvolution_domain hH hs hs1 hG).1] with x hx
  rw [real_inner_comm,rieszVectorConvolution,← integral_inner hx v]
  simp only [inner_smul_right,real_inner_comm v]
  rfl

#print axioms rieszVectorConvolution_aestronglyMeasurable
#print axioms rieszVectorConvolution_norm_le
#print axioms rieszVectorConvolution_domain
#print axioms rieszVectorConvolution_inner
end HartreeF.RieszWeakDerivative
